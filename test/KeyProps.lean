import IncCheck.Key
import IncCheck.Sha256
import IncCheck.CA.RefHash

/-!
# Mutation tests for check keys

Each test changes one thing about one real declaration of `Init`, recomputes every key, and compares the set of keys
that changed with the set that must change. That set is computed from the reference graph alone, independently of the
hashes:

* the mutated declaration, if the change is visible to its own kernel check;
* if the change is visible to the declaration's users (anything but a theorem's proof), every declaration whose type,
  definition body or structure refers to it, transitively;
* every declaration whose kernel check reads one of those, its proof included;
* the whole mutually dependent block of each of these, since a block is hashed as one unit;
* every key, if a constant the kernel uses by name is affected.

A test fails if a key that must change does not (a soundness bug) or if any other key changes (lost reuse).
-/

open Lean IncCheck CA.RefHash

structure Snapshot where
  keys : Std.HashMap Name ByteArray

def snapshot (consts : Array (Name × ConstantInfo)) : IO Snapshot := do
  let (ids, refs) ← computeIds consts {} nativeHasher (withProofs := true)
  let pre ← keyPrefix nativeHasher refs
  let info : Std.HashMap Name ConstantInfo := consts.foldl (fun m (n, c) => m.insert n c) {}
  let mut keys : Std.HashMap Name ByteArray := {}
  for i in ids do
    if i.unresolved.isEmpty then
      keys := keys.insert i.name (← checkKey nativeHasher pre i.decl info[i.name]!.levelParams)
  return { keys }

/-- The graph facts the expected sets are computed from. -/
structure Graph where
  names : Array Name
  /-- What a user of a constant can observe through it: everything but a theorem's proof. -/
  iface : Array (Name × Array Name)
  /-- Everything a constant's own kernel check reads. -/
  own : Array (Name × Array Name)
  block : Std.HashMap Name Nat
  blocks : Array (Array Name)

def graph (consts : Array (Name × ConstantInfo)) : Graph := Id.run do
  let own := consts.map fun (n, c) => (n, (refsOf c (withProofs := true)).toArray)
  let iface := consts.map fun (n, c) => (n, (refsOf c (withProofs := false)).toArray)
  let ownMap : Std.HashMap Name (Array Name) := own.foldl (fun m (n, rs) => m.insert n rs) {}
  let names := consts.map (·.1)
  let blocks := sccs names (fun n => ownMap.getD n #[])
  let mut block : Std.HashMap Name Nat := {}
  for h : i in [0:blocks.size] do
    for n in blocks[i] do
      block := block.insert n i
  return { names, iface, own, block, blocks }

def Graph.expand (g : Graph) (s : NameSet) : NameSet :=
  s.foldl (fun acc n => match g.block[n]? with
    | some i => g.blocks[i]!.foldl (·.insert ·) acc
    | none => acc.insert n) {}

/-- Everything whose user-visible content depends on `seed`, with whole blocks. -/
def Graph.affected (g : Graph) (seed : NameSet) : NameSet := Id.run do
  let mut s := g.expand seed
  let mut grew := true
  while grew do
    grew := false
    for (n, rs) in g.iface do
      if !s.contains n && rs.any s.contains then
        s := s.insert n
        grew := true
    let s' := g.expand s
    if s'.size != s.size then
      s := s'
      grew := true
  return s

def Graph.mustChange (g : Graph) (target : Name) (ownVisible usersVisible : Bool) : NameSet := Id.run do
  let affected := if usersVisible then g.affected {target} else {}
  if kernelBuiltins.any affected.contains then
    return g.names.foldl (·.insert ·) {}
  let mut must := affected
  if ownVisible then must := must.insert target
  for (n, rs) in g.own do
    if rs.any affected.contains then must := must.insert n
  return g.expand must

/-- A change to one declaration: the new constant, and whether the kernel check of the declaration itself and of its
users can observe it. -/
structure Mutation where
  title : String
  target : Name
  apply : ConstantInfo → ConstantInfo
  ownVisible : Bool
  usersVisible : Bool

def setTV (ci : ConstantInfo) (ty : Expr) (val? : Option Expr) (lps : List Name) : ConstantInfo :=
  match ci with
  | .defnInfo v => .defnInfo { v with type := ty, value := val?.getD v.value, levelParams := lps }
  | .thmInfo v => .thmInfo { v with type := ty, value := val?.getD v.value, levelParams := lps }
  | .opaqueInfo v => .opaqueInfo { v with type := ty, value := val?.getD v.value, levelParams := lps }
  | .axiomInfo v => .axiomInfo { v with type := ty, levelParams := lps }
  | c => c

def bumpLits (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .lit (.natVal n) => some (.lit (.natVal (n + 1)))
    | _ => none

def hasLit (e : Expr) : Bool := (e.find? fun s => s.isLit).isSome

partial def renameBinders (e : Expr) : Expr :=
  match e with
  | .lam _ t b bi => .lam `renamed (renameBinders t) (renameBinders b) bi
  | .forallE _ t b bi => .forallE `renamed (renameBinders t) (renameBinders b) bi
  | .app f a => .app (renameBinders f) (renameBinders a)
  | e => e

def swapMax (e : Expr) : Expr :=
  e.replaceLevel fun l => match l with
    | .max a b => some (.max b a)
    | _ => none

def hasAsymMax (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .sort (.max a b) => a != b
    | .const _ ls => ls.any fun l => match l with | .max a b => a != b | _ => false
    | _ => false).isSome

def value? (ci : ConstantInfo) : Option Expr := ci.value? (allowOpaque := true)

/-- The declaration satisfying `p` that the most other declarations refer to, so that each test exercises
propagation. Ties go to the smaller name. -/
def pick (consts : Array (Name × ConstantInfo)) (users : Std.HashMap Name Nat) (p : ConstantInfo → Bool) :
    IO Name := do
  let mut best : Option (Name × Nat) := none
  for (n, c) in consts do
    if p c then
      let k := users.getD n 0
      best := match best with
        | some (m, j) => if k > j || (k == j && n.quickLt m) then some (n, k) else some (m, j)
        | none => some (n, k)
  match best with
  | some (n, _) => return n
  | none => throw <| .userError "no declaration fits the mutation"

def mutations (consts : Array (Name × ConstantInfo)) (g : Graph) : IO (Array Mutation) := do
  let users : Std.HashMap Name Nat := g.own.foldl (init := {}) fun m (_, rs) =>
    rs.foldl (fun m r => m.insert r (m.getD r 0 + 1)) m
  let pick := pick consts users
  let isDef (c : ConstantInfo) := c matches .defnInfo { safety := .safe, .. }
  let isThm (c : ConstantInfo) := c matches .thmInfo _
  let defLit ← pick fun c => isDef c && (value? c).any hasLit
  let defRegular ← pick fun c => match c with
    | .defnInfo { hints := .regular _, safety := .safe, .. } => true | _ => false
  let thmProofLit ← pick fun c => isThm c && !hasLit c.type && (value? c).any hasLit
  let thmTypeLit ← pick fun c => isThm c && hasLit c.type
  let thmBinders ← pick fun c => isThm c && c.type.isForall
  let defAny ← pick isDef
  let maxLevel ← pick fun c => (isDef c || isThm c) && hasAsymMax c.type
  let oneParam ← pick fun c => isThm c && c.levelParams.length == 1
  let twoParams ← pick fun c => isThm c && c.levelParams.length == 2
  return #[
    { title := "a definition's body changes", target := defLit, ownVisible := true, usersVisible := true
      apply := fun c => setTV c c.type ((value? c).map bumpLits) c.levelParams },
    { title := "a definition's reducibility hints change", target := defRegular, ownVisible := true,
      usersVisible := true
      apply := fun c => match c with
        | .defnInfo v => .defnInfo { v with hints := match v.hints with | .regular h => .regular (h + 1) | h => h }
        | c => c },
    { title := "a theorem's proof changes: its users keep their keys", target := thmProofLit, ownVisible := true,
      usersVisible := false
      apply := fun c => setTV c c.type ((value? c).map bumpLits) c.levelParams },
    { title := "a theorem's statement changes", target := thmTypeLit, ownVisible := true, usersVisible := true
      apply := fun c => setTV c (bumpLits c.type) none c.levelParams },
    { title := "binder names change: no key changes", target := thmBinders, ownVisible := false,
      usersVisible := false
      apply := fun c => setTV c (renameBinders c.type) none c.levelParams },
    { title := "mdata is added: no key changes", target := defAny, ownVisible := false, usersVisible := false
      apply := fun c => setTV c c.type ((value? c).map (.mdata {})) c.levelParams },
    { title := "`max a b` becomes `max b a`", target := maxLevel, ownVisible := true, usersVisible := true
      apply := fun c => setTV c (swapMax c.type) none c.levelParams },
    { title := "a universe parameter is renamed: only the declaration itself is re-checked", target := oneParam,
      ownVisible := true, usersVisible := false
      apply := fun c =>
        let u := c.levelParams.head!
        let r (e : Expr) := e.instantiateLevelParams [u] [.param `renamedUniverse]
        setTV c (r c.type) ((value? c).map r) [`renamedUniverse] },
    { title := "a universe parameter is listed twice", target := twoParams, ownVisible := true, usersVisible := true
      apply := fun c => setTV c c.type none [c.levelParams.head!, c.levelParams.head!] },
    { title := "a constant the kernel uses by name changes: every key changes", target := ``Nat.add,
      ownVisible := true, usersVisible := true
      apply := fun c => match c with
        | .defnInfo v => .defnInfo { v with hints := match v.hints with | .regular h => .regular (h + 1) | h => h }
        | c => c },
    { title := "an inductive type's constructor changes shape", target := ``Option.some, ownVisible := true,
      usersVisible := true
      apply := fun c => match c with
        | .ctorInfo v => .ctorInfo { v with numFields := v.numFields + 1 }
        | c => c }]

def changedKeys (a b : Snapshot) : NameSet :=
  let names := a.keys.keys ++ b.keys.keys
  names.foldl (fun s n => if a.keys[n]? != b.keys[n]? then s.insert n else s) {}

def sample (s : NameSet) : String := ", ".intercalate (s.toList.take 3 |>.map toString)

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Init }] {} fun env => do
    let mut consts : Array (Name × ConstantInfo) := #[]
    for (n, ci) in env.constants.map₁ do
      consts := consts.push (n, ci)
    let g := graph consts
    let base ← snapshot consts
    IO.println s!"{consts.size} declarations of Init, {base.keys.size} keys"
    let mut failures := 0
    for m in ← mutations consts g do
      let mutated := consts.map fun (n, c) => if n == m.target then (n, m.apply c) else (n, c)
      let after ← snapshot mutated
      let changed := changedKeys base after
      let must := g.mustChange m.target m.ownVisible m.usersVisible
      let missing := must.foldl (fun s n => if changed.contains n then s else s.insert n) ({} : NameSet)
      let extra := changed.foldl (fun s n => if must.contains n then s else s.insert n) ({} : NameSet)
      let ok := missing.isEmpty && extra.isEmpty
      unless ok do failures := failures + 1
      IO.println s!"{if ok then "ok  " else "FAIL"} {m.title} ({m.target}): {changed.size} keys changed, \
        {must.size} must change\
        {if missing.isEmpty then "" else s!"; NOT changed: {missing.size} ({sample missing})"}\
        {if extra.isEmpty then "" else s!"; changed without cause: {extra.size} ({sample extra})"}"
    IO.println (if failures == 0 then "all key properties hold" else s!"{failures} failures")
    return if failures == 0 then 0 else 1
