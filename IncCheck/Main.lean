import IncCheck.Key
import IncCheck.Store
import IncCheck.Replay
import IncCheck.Sha256
import IncCheck.IdCache

/-!
`leanchecker-inc` replays the given modules and everything they import into an empty kernel environment, like
`leanchecker --fresh`, and skips the kernel for declarations whose check key is in the verdict store.
-/

open Lean System

namespace IncCheck.Cli

/-- Where the store and the id cache live by default, relative to the project root. -/
def stateDir : FilePath := ".lake" / "leanchecker-inc"

def help : String := "leanchecker-inc: check a Lean project with Lean's kernel, reusing earlier verdicts

usage: lake exe leanchecker-inc [OPTIONS] [MODULE...]

Imports MODULE (default: the project's root module, from lake-manifest.json) and everything it imports, and replays
every declaration into an empty kernel environment, like `leanchecker --fresh`. A declaration whose check key is in
the verdict store is added without the kernel. After a run in which the kernel accepts everything, the new verdicts
are added to the store. Exit code 0: accepted. 1: the kernel rejected something. 2: usage error.

options:
  --store FILE        verdict store (default: .lake/leanchecker-inc/verdicts.bin)
  --no-store          check every declaration, and neither read nor write a store
  --no-record         read the store but do not add verdicts to it
  --id-cache FILE     cache of declaration ids per module (default: .lake/leanchecker-inc/ids.bin)
  --no-id-cache       hash every declaration again
  -j, --threads N     threads for reading and hashing .olean files (default: all hardware threads)
  -q, --quiet         print only the result
  -h, --help          show this text

diagnostics:
  --log-checked FILE  write the names of the declarations and inductive blocks the kernel checked
  --dump-keys FILE    write every check key as `name hex` lines
  --hash-only         compute the keys and stop before the replay
  --pure-sha          hash with the pure-Lean SHA-256 instead of the C one (same keys, slower)

The store and the id cache are trusted: keep them where only this tool writes, and run with --no-store from time
to time."

structure Options where
  modules : Array Name := #[]
  store : Option FilePath := some (stateDir / "verdicts.bin")
  record : Bool := true
  idCache : Option FilePath := some (stateDir / "ids.bin")
  quiet : Bool := false
  help : Bool := false
  logChecked : Option FilePath := none
  dumpKeys : Option FilePath := none
  hashOnly : Bool := false
  pureSha : Bool := false
  /-- Threads for hashing `.olean` files. -/
  threads : Nat := max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--store" :: p :: rest, o => parseArgs rest { o with store := some p }
  | "--no-store" :: rest, o => parseArgs rest { o with store := none }
  | "--no-record" :: rest, o => parseArgs rest { o with record := false }
  | "--id-cache" :: p :: rest, o => parseArgs rest { o with idCache := some p }
  | "--no-id-cache" :: rest, o => parseArgs rest { o with idCache := none }
  | "-q" :: rest, o | "--quiet" :: rest, o => parseArgs rest { o with quiet := true }
  | "-h" :: rest, o | "--help" :: rest, o => parseArgs rest { o with help := true }
  | "--log-checked" :: p :: rest, o => parseArgs rest { o with logChecked := some p }
  | "--dump-keys" :: p :: rest, o => parseArgs rest { o with dumpKeys := some p }
  | "--hash-only" :: rest, o => parseArgs rest { o with hashOnly := true }
  | "--pure-sha" :: rest, o => parseArgs rest { o with pureSha := true }
  | "-j" :: k :: rest, o | "--threads" :: k :: rest, o => match k.toNat? with
    | some j => parseArgs rest { o with threads := max 1 j }
    | none => .error s!"-j expects a number, got {k}"
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown option {arg}"
    else parseArgs rest { o with modules := o.modules.push arg.toName }

/-- The root module of the project in the current directory: its package name from `lake-manifest.json`,
capitalized, as `leanchecker` does. -/
def rootModule : IO Name := do
  let path : FilePath := "lake-manifest.json"
  unless ← path.pathExists do
    throw <| .userError "no MODULE given, and no lake-manifest.json here to find the project's root module"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let name ← IO.ofExcept <| json.getObjValAs? String "name"
  return name.capitalize.toName

/-- `1234567` as `1,234,567`. -/
def fmt (n : Nat) : String :=
  let rec go (cs : List Char) : List Char :=
    if cs.length ≤ 3 then cs else go (cs.take (cs.length - 3)) ++ [','] ++ cs.drop (cs.length - 3)
  termination_by cs.length
  String.ofList (go (toString n).toList)

def secs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100} s"

unsafe def run (o : Options) : IO Unit := do
  let say (msg : String) : IO Unit := unless o.quiet do IO.eprintln s!"leanchecker-inc: {msg}"
  initSearchPath (← findSysroot)
  let modules ← if o.modules.isEmpty then pure #[← rootModule] else pure o.modules
  let what := ", ".intercalate (modules.map toString).toList
  let hasher := if o.pureSha then CA.SHA256.pureHasher else nativeHasher
  say s!"importing {what}"
  let t0 ← IO.monoMsNow
  Lean.withImportModules (modules.map ({ module := · })) {} fun env => do
    let mut constants : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in env.constants.map₁ do
      constants := constants.insert n ci
    let t1 ← IO.monoMsNow
    say s!"{fmt constants.size} constants imported in {secs (t1 - t0)}, computing declaration ids"
    let (decls, refs, inexact) ← match o.idCache with
      | some p =>
        let c ← computeIdsCached env (← loadIdCache p) hasher o.threads
        saveIdCache p c.cache
        say s!"ids: {fmt c.reused} modules reused from the id cache, {fmt c.hashed} hashed"
        pure (c.decls, c.refs, c.inexact)
      | none =>
        let (ids, refs) ← CA.RefHash.computeIds constants.toArray {} hasher (withProofs := true)
        let exact := ids.filter (·.unresolved.isEmpty)
        pure (exact.map fun i => (i.name, i.decl), refs, ids.size - exact.size)
    let pre ← keyPrefix hasher refs
    let mut keys : Std.HashMap Name ByteArray := {}
    for (n, d) in decls do
      if let some ci := constants[n]? then
        keys := keys.insert n (← checkKey hasher pre d ci.levelParams)
    -- An inductive block is the types of one `all` list, their constructors, and the recursors generated for them.
    let mut recursorsOf : Std.HashMap (List Name) (Array Name) := {}
    for (n, ci) in constants do
      if let .recInfo v := ci then
        recursorsOf := recursorsOf.insert v.all ((recursorsOf.getD v.all #[]).push n)
    let mut blocks : Std.HashMap Name InductiveBlock := {}
    for (n, ci) in constants do
      if let .inductInfo v := ci then
        if v.all.head? == some n then
          let recursors := recursorsOf.getD v.all #[]
          let ctors := v.all.foldl (init := []) fun acc t => match constants[t]? with
            | some (.inductInfo tv) => acc ++ tv.ctors
            | _ => acc
          let members := (v.all ++ ctors ++ recursors.toList).toArray
          if members.all keys.contains then
            let key ← blockKey hasher (members.map fun m => (m, keys[m]!))
            for t in v.all do
              blocks := blocks.insert t { key, recursors }
    let t2 ← IO.monoMsNow
    if inexact > 0 then
      say s!"{fmt inexact} declarations have no exact key and will always be checked"
    if let some p := o.dumpKeys then
      let hex (b : ByteArray) : String := b.foldl (fun acc x =>
        let d := "0123456789abcdef".toList
        acc.push d[(x / 16).toNat]! |>.push d[(x % 16).toNat]!) ""
      IO.FS.writeFile p <| String.join <| (keys.toList.map fun (n, k) => s!"{n} {hex k}\n").mergeSort (· ≤ ·)
    if o.hashOnly then
      IO.println s!"{what}: {fmt keys.size} keys for {fmt constants.size} constants in {secs (t2 - t0)}"
      return
    let store ← match o.store with
      | some p => loadStore p
      | none => pure {}
    say s!"keys computed in {secs (t2 - t1)}, {fmt store.size} stored verdicts, replaying into the kernel"
    let s ← replay constants keys store (← mkEmptyEnvironment).toKernelEnv blocks
    let t3 ← IO.monoMsNow
    if let some p := o.logChecked then
      let lines := s.checkedNames.toList.map (·.toString) ++ s.checkedBlocks.toList.map (s!"inductive {·}")
      IO.FS.writeFile p <| String.join <| (lines.map (· ++ "\n")).mergeSort (· ≤ ·)
    let recorded := o.record && o.store.isSome
    -- Declarations with identical content share a key, so keep each new key once.
    let (newKeys, _) := s.accepted.foldl (init := (#[], store)) fun (acc, seen) k =>
      if seen.contains k then (acc, seen) else (acc.push k, seen.insert k)
    if recorded then
      if let some p := o.store then appendStore p newKeys
    IO.println s!"{what}: accepted. The kernel checked {fmt s.checkedNames.size} definitions and theorems and \
      {fmt s.checkedBlocks.size} inductive blocks \
      (and {fmt (s.checked - s.checkedNames.size - s.checkedBlocks.size)} quotient declarations), and skipped {fmt s.skipped} declarations and \
      {fmt s.skippedBlocks} inductive blocks with stored verdicts\
      {if recorded then s!"; {fmt newKeys.size} new verdicts stored" else ""} ({secs (t3 - t0)})."

end IncCheck.Cli

open IncCheck.Cli in
unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"leanchecker-inc: {e}\nRun with --help for usage."
    return 2
  | .ok o =>
    if o.help then
      IO.println help
      return 0
    try
      run o
      return 0
    catch e =>
      IO.eprintln s!"leanchecker-inc: the check failed.\n{e}"
      return 1
