import IncCheck.CA.RefHash
import IncCheck.Sha256
import IncCheck.Key

/-!
# Per-module cache of CA ids

Hashing every constant of Mathlib, proofs included, takes about 5 minutes. Between two commits almost every module's
`.olean` files are byte-identical, and a module's ids depend only on its own content and on the `ref` ids of the
constants it refers to in other modules. So for each module the cache records:

* a digest of its `.olean`, `.olean.server` and `.olean.private` files,
* the constants in other modules that it refers to, and a digest of their `ref` ids as seen when its ids were computed,
* the `decl` and `ref` id of each of its constants.

A module is reused when its digest and the digest of those outside ids are unchanged. The cache is a trusted input,
like the verdict store.

On disk, every name is stored once, as the index of its prefix and one component, and modules refer to names by index.
A `ref` id is stored only when it differs from the `decl` id, which happens only for theorems.
-/

open Lean CA.RefHash

namespace IncCheck

structure ModEntry where
  digest : ByteArray
  /-- The constants in other modules that this module's constants refer to. -/
  extRefs : Array Name
  /-- SHA-256 over the `ref` ids of `extRefs`, in order. -/
  extDigest : ByteArray
  /-- `(name, decl, ref)` for each constant of the module. -/
  ids : Array (Name × ByteArray × ByteArray)
  deriving Inhabited

abbrev IdCache := Std.HashMap Name ModEntry

/-- The digest of the `ref` ids of `names`, or `none` if one of them has no id. -/
def extDigestOf (lookup : Name → Option ByteArray) (names : Array Name) : Option ByteArray := Id.run do
  let mut b := ByteArray.empty
  for n in names do
    match lookup n with
    | some r => b := b ++ r
    | none => return none
  return some (sha256Native b)

/-! ## Encoding -/

/-- Gives every name an index, prefixes first, so a name is stored as its prefix's index and one component. -/
structure NameTable where
  index : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert .anonymous 0
  names : Array Name := #[.anonymous]

partial def NameTable.intern (t : NameTable) (n : Name) : NameTable × Nat :=
  match t.index[n]? with
  | some i => (t, i)
  | none =>
    let t := match n with
      | .str p _ | .num p _ => (t.intern p).1
      | .anonymous => t
    let i := t.names.size
    ({ index := t.index.insert n i, names := t.names.push n }, i)

private def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  (((b.push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

/-- Ties a cache file to the id rules of `keyScheme` and to this format. -/
def magic : ByteArray := s!"{keyScheme} ids, format 2\n".toUTF8

def encode (c : IdCache) : ByteArray := Id.run do
  let mut t : NameTable := {}
  for (mod, e) in c do
    t := (t.intern mod).1
    for n in e.extRefs do t := (t.intern n).1
    for (n, _, _) in e.ids do t := (t.intern n).1
  let idx (n : Name) : Nat := t.index[n]!
  let mut b := pushU32 magic (t.names.size - 1)
  for n in t.names[1:] do
    match n with
    | .str p s =>
      let bs := s.toUTF8
      b := pushU32 (pushU32 (b.push 0) (idx p)) bs.size ++ bs
    | .num p k => b := pushU32 (pushU32 (b.push 1) (idx p)) k
    | .anonymous => pure ()
  b := pushU32 b c.size
  for (mod, e) in c do
    b := pushU32 b (idx mod) ++ e.digest
    b := pushU32 b e.extRefs.size
    for n in e.extRefs do b := pushU32 b (idx n)
    b := b ++ e.extDigest
    b := pushU32 b e.ids.size
    for (n, d, r) in e.ids do
      b := pushU32 b (idx n) ++ d
      b := if r == d then b.push 0 else b.push 1 ++ r
  return b

abbrev Reader := StateT Nat (Except String)

private def readU8 (bs : ByteArray) : Reader UInt8 := do
  let i ← get
  unless i < bs.size do throw "unexpected end of id cache"
  set (i + 1)
  return bs[i]!

private def readU32 (bs : ByteArray) : Reader Nat := do
  let a ← readU8 bs; let b ← readU8 bs; let c ← readU8 bs; let d ← readU8 bs
  return a.toNat ||| (b.toNat <<< 8) ||| (c.toNat <<< 16) ||| (d.toNat <<< 24)

private def readFixed (bs : ByteArray) (n : Nat) : Reader ByteArray := do
  let i ← get
  unless i + n ≤ bs.size do throw "unexpected end of id cache"
  set (i + n)
  return bs.extract i (i + n)

def decode (bs : ByteArray) : Except String IdCache := do
  unless bs.extract 0 magic.size == magic do throw "not an id cache"
  let go : Reader IdCache := do
    let mut names : Array Name := #[.anonymous]
    for _ in [0:← readU32 bs] do
      let tag ← readU8 bs
      let some p := names[← readU32 bs]? | throw "bad name index in id cache"
      if tag == 0 then
        let len ← readU32 bs
        names := names.push (.str p (String.fromUTF8! (← readFixed bs len)))
      else
        names := names.push (.num p (← readU32 bs))
    let name (i : Nat) : Reader Name := do
      let some n := names[i]? | throw "bad name index in id cache"
      return n
    let mut c : IdCache := {}
    for _ in [0:← readU32 bs] do
      let mod ← name (← readU32 bs)
      let digest ← readFixed bs 32
      let mut extRefs := #[]
      for _ in [0:← readU32 bs] do
        extRefs := extRefs.push (← name (← readU32 bs))
      let extDigest ← readFixed bs 32
      let mut ids := #[]
      for _ in [0:← readU32 bs] do
        let n ← name (← readU32 bs)
        let d ← readFixed bs 32
        let r ← if (← readU8 bs) == 0 then pure d else readFixed bs 32
        ids := ids.push (n, d, r)
      c := c.insert mod { digest, extRefs, extDigest, ids }
    return c
  return (← go.run magic.size).1

/-- The cache at `path`, or an empty one when the file is missing or was written under other id rules. -/
def loadIdCache (path : System.FilePath) : IO IdCache := do
  unless ← path.pathExists do return {}
  let bytes ← IO.FS.readBinFile path
  unless bytes.extract 0 magic.size == magic do return {}
  match decode bytes with
  | .ok c => return c
  | .error e => throw <| .userError s!"{path}: {e}"

def saveIdCache (path : System.FilePath) (c : IdCache) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  let tmp := path.addExtension "tmp"
  IO.FS.writeBinFile tmp (encode c)
  IO.FS.rename tmp path

/-! ## Computing ids with the cache -/

/-- SHA-256 over the SHA-256 of each `.olean` part of `mod` that exists. -/
def moduleDigest (mod : Name) : IO ByteArray := do
  let olean ← findOLean mod
  let mut b := ByteArray.empty
  for f in [olean, OLeanLevel.server.adjustFileName olean, OLeanLevel.private.adjustFileName olean] do
    if ← f.pathExists then
      b := b ++ sha256Native (← IO.FS.readBinFile f)
    else
      b := b.push 0
  return sha256Native b

/-- The digests of `mods`, hashed by `threads` dedicated tasks over contiguous slices. -/
def moduleDigests (mods : Array Name) (threads : Nat) : IO (Array ByteArray) := do
  let threads := max 1 (min threads mods.size)
  let chunk := (mods.size + threads - 1) / threads
  let tasks ← (Array.range threads).mapM fun t => IO.asTask (prio := .dedicated) do
    let mut out := #[]
    for m in mods[t * chunk : min mods.size ((t + 1) * chunk)] do
      out := out.push (← moduleDigest m)
    return out
  let mut all := #[]
  for task in tasks do
    all := all ++ (← IO.ofExcept task.get)
  return all

structure CachedIds where
  /-- `(name, decl id)` for every constant whose ids are exact. -/
  decls : Array (Name × ByteArray)
  refs : RefTable
  cache : IdCache
  reused : Nat
  hashed : Nat
  inexact : Nat

/-- CA ids of every imported constant, reusing the ids of modules that `old` shows unchanged.

Modules are hashed in the order of the references between them, not in import order: a constant generated on demand
(an equation lemma, a `match` splitter) can be copied into several modules, and the environment takes it from one of
them, which can come after a module that uses it. Modules that reference each other are hashed together. Every name is
hashed once, in the module the environment took it from. -/
def computeIdsCached (env : Environment) (old : IdCache) (hasher : CA.SHA256.Hasher) (threads : Nat := 1) :
    IO CachedIds := do
  let n := env.header.moduleNames.size
  let allDigests ← moduleDigests env.header.moduleNames threads
  let owner (c : Name) : Option Name := (env.getModuleIdxFor? c).map fun j => env.header.moduleNames[j.toNat]!
  -- Per module: digest, owned constants, and the outside constants it refers to.
  let mut digests : Std.HashMap Name ByteArray := {}
  let mut owned : Std.HashMap Name (Array (Name × ConstantInfo)) := {}
  let mut ext : Std.HashMap Name (Array Name) := {}
  for h : idx in [0:n] do
    let mod := env.header.moduleNames[idx]
    let digest := allDigests[idx]!
    digests := digests.insert mod digest
    let names := env.header.moduleData[idx]!.constNames.filter fun c => owner c == some mod
    let infos := names.filterMap fun c => (env.find? c).map (c, ·)
    owned := owned.insert mod infos
    match old[mod]? with
    | some e =>
      if e.digest == digest then
        ext := ext.insert mod e.extRefs
        continue
    | none => pure ()
    let mut refs : NameSet := {}
    for (_, ci) in infos do
      for r in refsOf ci (withProofs := true) do
        if owner r != some mod then refs := refs.insert r
    ext := ext.insert mod refs.toArray
  let succ (m : Name) : Array Name :=
    (ext.getD m #[]).filterMap owner |>.filter (· != m)
  let comps := sccs env.header.moduleNames succ
  let mut table : RefTable := {}
  let mut decls : Array (Name × ByteArray) := #[]
  let mut cache : IdCache := {}
  let mut reused := 0
  let mut hashed := 0
  let mut inexact := 0
  for comp in comps do
    -- Outside references into another module of the same component resolve to that module's cached ids, which are
    -- valid if every module of the component is unchanged.
    let compIds : Std.HashMap Name ByteArray := comp.foldl (init := {}) fun s m => match old[m]? with
      | some e => e.ids.foldl (fun s (c, _, r) => s.insert c r) s
      | none => s
    let lookup (r : Name) : Option ByteArray := table[r]? <|> compIds[r]?
    let reusable := comp.all fun m => match old[m]? with
      | some e => e.digest == digests[m]! && extDigestOf lookup e.extRefs == some e.extDigest
      | none => false
    if reusable then
      for m in comp do
        let e := old[m]!
        for (c, d, r) in e.ids do
          table := table.insert c r
          decls := decls.push (c, d)
        cache := cache.insert m e
      reused := reused + comp.size
      continue
    let infos := comp.foldl (fun acc m => acc ++ owned.getD m #[]) #[]
    let (ids, table') ← computeIds infos table hasher (withProofs := true)
    table := table'
    hashed := hashed + comp.size
    let mut exact := true
    for i in ids do
      if i.unresolved.isEmpty then
        decls := decls.push (i.name, i.decl)
      else
        exact := false
        inexact := inexact + 1
        if (← IO.getEnv "INCCHECK_DEBUG").isSome then
          IO.eprintln s!"inexact {i.name}: {i.unresolved.toList}"
    if exact then
      let idsOf : Std.HashMap Name DeclIds := ids.foldl (fun s i => s.insert i.name i) {}
      for m in comp do
        let extRefs := ext.getD m #[]
        let mine := (owned.getD m #[]).filterMap fun (c, _) => idsOf[c]?.map fun i => (c, i.decl, i.ref)
        if let some extDigest := extDigestOf (table[·]?) extRefs then
          cache := cache.insert m { digest := digests[m]!, extRefs, extDigest, ids := mine }
  return { decls, refs := table, cache, reused, hashed, inexact }

end IncCheck
