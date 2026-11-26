import IncCheck.CA.RefHash
import IncCheck.Sha256

/-!
# Per-module cache of CA ids

Hashing every constant of Mathlib, proofs included, takes about 5 minutes. Between two commits almost every module's
`.olean` files are byte-identical, and a module's ids depend only on its own content and on the `ref` ids of the
constants it refers to in other modules. So for each module the cache records:

* a digest of its `.olean`, `.olean.server` and `.olean.private` files,
* the `ref` id of every constant in another module that it refers to, as seen when its ids were computed,
* the `decl` and `ref` id of each of its constants.

A module is reused when its digest and all those outside ids are unchanged. Modules are visited in import order, so the
outside ids are final when a module is visited. The cache is a trusted input, like the verdict store.
-/

open Lean CA.RefHash

namespace IncCheck

structure ModEntry where
  digest : ByteArray
  extRefs : Array (Name × ByteArray)
  /-- `(name, decl, ref)` for each constant of the module. -/
  ids : Array (Name × ByteArray × ByteArray)
  deriving Inhabited

abbrev IdCache := Std.HashMap Name ModEntry

/-! ## Encoding -/

private def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  (((b.push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

private def pushBytes (b bs : ByteArray) : ByteArray := pushU32 b bs.size ++ bs

/-- Names are encoded by component, so numeric components (as in `_private.M.0.x`) round-trip exactly. -/
private def pushName (b : ByteArray) (n : Name) : ByteArray :=
  let cs := n.components
  cs.foldl (init := pushU32 b cs.length) fun b c =>
    match c with
    | .str _ s => pushBytes (b.push 0) s.toUTF8
    | .num _ k => pushU32 (b.push 1) k
    | .anonymous => b.push 2

def magic : ByteArray := "leanchecker-inc ids 1\n".toUTF8

def encode (c : IdCache) : ByteArray := Id.run do
  let mut b := pushU32 magic c.size
  for (mod, e) in c do
    b := pushName b mod
    b := pushBytes b e.digest
    b := pushU32 b e.extRefs.size
    for (n, r) in e.extRefs do
      b := pushBytes (pushName b n) r
    b := pushU32 b e.ids.size
    for (n, d, r) in e.ids do
      b := pushBytes (pushBytes (pushName b n) d) r
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

private def readBytes (bs : ByteArray) : Reader ByteArray := do
  let n ← readU32 bs
  let i ← get
  unless i + n ≤ bs.size do throw "unexpected end of id cache"
  set (i + n)
  return bs.extract i (i + n)

private def readName (bs : ByteArray) : Reader Name := do
  let k ← readU32 bs
  let mut n := Name.anonymous
  for _ in [0:k] do
    match ← readU8 bs with
    | 0 => n := .str n (String.fromUTF8! (← readBytes bs))
    | 1 => n := .num n (← readU32 bs)
    | _ => pure ()
  return n

def decode (bs : ByteArray) : Except String IdCache := do
  unless bs.extract 0 magic.size == magic do throw "not an id cache"
  let go : Reader IdCache := do
    let mods ← readU32 bs
    let mut c : IdCache := {}
    for _ in [0:mods] do
      let mod ← readName bs
      let digest ← readBytes bs
      let mut extRefs := #[]
      for _ in [0:← readU32 bs] do
        extRefs := extRefs.push (← readName bs, ← readBytes bs)
      let mut ids := #[]
      for _ in [0:← readU32 bs] do
        ids := ids.push (← readName bs, ← readBytes bs, ← readBytes bs)
      c := c.insert mod { digest, extRefs, ids }
    return c
  return (← go.run magic.size).1

def loadIdCache (path : System.FilePath) : IO IdCache := do
  unless ← path.pathExists do return {}
  match decode (← IO.FS.readBinFile path) with
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
def computeIdsCached (env : Environment) (old : IdCache) (hasher : CA.SHA256.Hasher) : IO CachedIds := do
  let n := env.header.moduleNames.size
  let owner (c : Name) : Option Name := (env.getModuleIdxFor? c).map fun j => env.header.moduleNames[j.toNat]!
  -- Per module: digest, owned constants, and the outside constants it refers to.
  let mut digests : Std.HashMap Name ByteArray := {}
  let mut owned : Std.HashMap Name (Array (Name × ConstantInfo)) := {}
  let mut ext : Std.HashMap Name (Array Name) := {}
  for h : idx in [0:n] do
    let mod := env.header.moduleNames[idx]
    let digest ← moduleDigest mod
    digests := digests.insert mod digest
    let names := env.header.moduleData[idx]!.constNames.filter fun c => owner c == some mod
    let infos := names.filterMap fun c => (env.find? c).map (c, ·)
    owned := owned.insert mod infos
    match old[mod]? with
    | some e =>
      if e.digest == digest then
        ext := ext.insert mod (e.extRefs.map (·.1))
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
    let inComp (c : Name) : Bool := (owner c).any comp.contains
    let reusable := comp.all fun m => match old[m]? with
      | some e => e.digest == digests[m]! &&
          e.extRefs.all fun (r, id) => inComp r || table[r]? == some id
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
        let extRefs := (ext.getD m #[]).filterMap fun r => table[r]?.map (r, ·)
        let mine := (owned.getD m #[]).filterMap fun (c, _) => idsOf[c]?.map fun i => (c, i.decl, i.ref)
        cache := cache.insert m { digest := digests[m]!, extRefs, ids := mine }
  return { decls, refs := table, cache, reused, hashed, inexact }

end IncCheck
