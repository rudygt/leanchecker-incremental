import IncCheck.Key
import IncCheck.Store
import IncCheck.Replay
import IncCheck.Sha256
import IncCheck.IdCache

/-!
`leanchecker-inc` replays every constant of a module and its imports into a fresh kernel environment, like
`leanchecker --fresh`, but skips the kernel for declarations whose check key is in the verdict store.
-/

open Lean

def usage : String :=
  "usage: leanchecker-inc [--store FILE] [--no-record] MODULE\n\
  Replays MODULE and everything it imports into a fresh kernel environment. With --store, declarations whose\n\
  check key is in FILE skip the kernel, and after a complete successful run the new verdicts are appended to FILE\n\
  (unless --no-record)."

structure CliOptions where
  store : Option System.FilePath := none
  record : Bool := true
  module : Option Name := none
  /-- Hash with CA's pure-Lean SHA-256 instead of the C one (for cross-checking). -/
  pureSha : Bool := false
  /-- Write every check key to this file as `name hex` lines (for cross-checking). -/
  dumpKeys : Option System.FilePath := none
  /-- Write the names of the axioms, definitions, theorems and opaques the kernel checked to this file. -/
  logChecked : Option System.FilePath := none
  /-- Compute the keys and stop before the replay (to measure the fixed cost). -/
  hashOnly : Bool := false
  /-- Reuse the CA ids of modules whose `.olean` files and outside references are unchanged. -/
  idCache : Option System.FilePath := none

def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => .ok o
  | "--store" :: p :: rest, o => parseArgs rest { o with store := some p }
  | "--no-record" :: rest, o => parseArgs rest { o with record := false }
  | "--log-checked" :: p :: rest, o => parseArgs rest { o with logChecked := some p }
  | "--id-cache" :: p :: rest, o => parseArgs rest { o with idCache := some p }
  | "--hash-only" :: rest, o => parseArgs rest { o with hashOnly := true }
  | "--pure-sha" :: rest, o => parseArgs rest { o with pureSha := true }
  | "--dump-keys" :: p :: rest, o => parseArgs rest { o with dumpKeys := some p }
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown flag {arg}"
    else if o.module.isSome then .error "only one module"
    else parseArgs rest { o with module := some arg.toName }

unsafe def check (o : CliOptions) (module : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  let hasher := if o.pureSha then CA.SHA256.pureHasher else IncCheck.nativeHasher
  let t0 ← IO.monoMsNow
  Lean.withImportModules #[{ module }] {} fun env => do
    let t1 ← IO.monoMsNow
    let mut constants : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in env.constants.map₁ do
      constants := constants.insert n ci
    let (decls, refs, inexact) ← match o.idCache with
      | some p =>
        let c ← IncCheck.computeIdsCached env (← IncCheck.loadIdCache p) hasher
        IncCheck.saveIdCache p c.cache
        IO.println s!"id cache: {c.reused} modules reused, {c.hashed} hashed"
        pure (c.decls, c.refs, c.inexact)
      | none =>
        let (ids, refs) ← CA.RefHash.computeIds constants.toArray {} hasher (withProofs := true)
        let exact := ids.filter (·.unresolved.isEmpty)
        pure (exact.map fun i => (i.name, i.decl), refs, ids.size - exact.size)
    let t2 ← IO.monoMsNow
    let pre ← IncCheck.keyPrefix hasher refs
    let mut keys : Std.HashMap Name ByteArray := {}
    for (n, d) in decls do
      keys := keys.insert n (← IncCheck.checkKey hasher pre d)
    if let some p := o.dumpKeys then
      let hex (b : ByteArray) : String := b.foldl (fun acc x =>
        let d := "0123456789abcdef".toList
        acc.push d[(x / 16).toNat]! |>.push d[(x % 16).toNat]!) ""
      IO.FS.writeFile p <| String.join <| (keys.toList.map fun (n, k) => s!"{n} {hex k}\n").mergeSort (· ≤ ·)
    let store ← match o.store with
      | some p => IncCheck.loadStore p
      | none => pure {}
    let t3 ← IO.monoMsNow
    if o.hashOnly then
      IO.println s!"{module}: {constants.size} constants, {keys.size} keys, {inexact} without an exact key"
      IO.println s!"time: import {t1 - t0} ms, ids {t2 - t1} ms, keys {t3 - t2} ms"
      return
    let s ← IncCheck.replay constants keys store (← mkEmptyEnvironment).toKernelEnv
    let t4 ← IO.monoMsNow
    if let some p := o.logChecked then
      IO.FS.writeFile p <| String.join <| (s.checkedNames.toList.map (·.toString ++ "\n")).mergeSort (· ≤ ·)
    if o.record then
      if let some p := o.store then IncCheck.appendStore p s.accepted
    IO.println s!"{module}: {constants.size} constants, {s.checked} checked by the kernel, {s.skipped} skipped, \
      {s.accepted.size} new verdicts, {inexact} without an exact key"
    IO.println s!"time: import {t1 - t0} ms, ids {t2 - t1} ms, keys {t3 - t2} ms, replay {t4 - t3} ms"

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"{e}\n{usage}"
    return 2
  | .ok { module := none, .. } =>
    IO.eprintln usage
    return 2
  | .ok o@{ module := some m, .. } =>
    try
      check o m
      return 0
    catch e =>
      IO.eprintln s!"leanchecker-inc found a problem in {m}:\n{e}"
      return 1
