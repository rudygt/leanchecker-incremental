import IncCheck.Key

/-!
# Mutation tests for check keys

First, the C SHA-256 is checked against standard test vectors, including the padding boundaries.

Then each test changes one thing about one real declaration of `Init`, recomputes every key, and compares the set of
keys that changed with the set that must change. That set is computed from the reference graph alone, independently of
the hashes:

* the mutated declaration, if the change is visible to its own kernel check;
* if the change is visible to other declarations (anything but a theorem's proof or an opaque body), the declaration's
  whole unit (its inductive block or mutual group), and every declaration whose type, definition body or structure
  names an affected constant, transitively, with their units;
* every declaration whose own kernel check reads an affected constant, its proof included;
* every key, if a constant the kernel uses by name is affected.

A test fails if a key that must change does not (a soundness bug) or if any other key changes (lost reuse).
-/

open Lean IncCheck

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s.push "0123456789abcdef".toList[(x / 16).toNat]! |>.push "0123456789abcdef".toList[(x % 16).toNat]!) ""

def shaVectors : List (String × ByteArray × String) :=
  let a (k : Nat) : ByteArray := ⟨Array.replicate k 97⟩
  [("empty", .empty, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
   ("abc", "abc".toUTF8, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
   ("56 bytes", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8,
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
   ("55 × a", a 55, "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"),
   ("64 × a", a 64, "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"),
   ("65 × a", a 65, "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"),
   ("119 × a", a 119, "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"),
   ("1,000,000 × a", a 1000000, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")]

structure Snapshot where
  keys : Std.HashMap Name ByteArray

def snapshot (consts : Array (Name × ConstantInfo)) : Snapshot :=
  let info : Std.HashMap Name ConstantInfo := consts.foldl (fun m (n, c) => m.insert n c) {}
  let (ids, interfaces, _) := hashGroup consts {} (info[·]?)
  let pre := keyPrefix interfaces
  { keys := ids.fold (fun m n i => m.insert n (checkKey pre i.decl)) {} }

/-- What other declarations can observe through `c`: everything but a theorem's proof or an opaque body. -/
def visibleRefs (c : ConstantInfo) : Array Name :=
  let more : Array Name := match c with
    | .defnInfo v => v.value.getUsedConstants ++ v.all.toArray
    | .thmInfo v => v.all.toArray
    | .opaqueInfo v => v.all.toArray
    | .inductInfo v => (v.all ++ v.ctors).toArray
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.rules.toArray.foldl (fun acc r => acc.push r.ctor ++ r.rhs.getUsedConstants) v.all.toArray
    | _ => #[]
  (c.type.getUsedConstants ++ more).filter (· != c.name)

/-- Everything `c`'s own kernel check reads. -/
def readRefs (c : ConstantInfo) : Array Name :=
  visibleRefs c ++ match c with
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | _ => #[]

/-- The graph facts the expected sets are computed from. -/
structure Graph where
  names : Array Name
  visible : Array (Name × Array Name)
  reads : Array (Name × Array Name)
  unitOf : Std.HashMap Name Name
  members : Std.HashMap Name (Array Name)

def graph (consts : Array (Name × ConstantInfo)) : Graph := Id.run do
  let info : Std.HashMap Name ConstantInfo := consts.foldl (fun m (n, c) => m.insert n c) {}
  -- An inductive block (types, constructors, recursors) or a mutual group is one unit, named by its first member.
  let unitName (c : ConstantInfo) : Name := match c with
    | .inductInfo v => v.all.headD c.name
    | .ctorInfo v => match info[v.induct]? with
      | some (.inductInfo iv) => iv.all.headD v.induct
      | _ => v.induct
    | .recInfo v => v.all.headD c.name
    | .defnInfo v | .thmInfo v | .opaqueInfo v => if v.all.length > 1 then v.all.headD c.name else c.name
    | _ => c.name
  let mut unitOf : Std.HashMap Name Name := {}
  let mut members : Std.HashMap Name (Array Name) := {}
  for (n, c) in consts do
    let u := unitName c
    unitOf := unitOf.insert n u
    members := members.insert u ((members.getD u #[]).push n)
  return { names := consts.map (·.1), visible := consts.map fun (n, c) => (n, visibleRefs c)
           reads := consts.map fun (n, c) => (n, readRefs c), unitOf, members }

def Graph.expand (g : Graph) (s : NameSet) : NameSet :=
  s.foldl (fun acc n => (g.members.getD (g.unitOf.getD n n) #[n]).foldl (·.insert ·) acc) {}

/-- Everything whose user-visible content depends on `seed`, with whole units. -/
def Graph.affected (g : Graph) (seed : NameSet) : NameSet := Id.run do
  let mut s := g.expand seed
  let mut grew := true
  while grew do
    grew := false
    for (n, rs) in g.visible do
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
  for (n, rs) in g.reads do
    if rs.any affected.contains then must := must.insert n
  return must

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
  let users : Std.HashMap Name Nat := g.reads.foldl (init := {}) fun m (_, rs) =>
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
    { title := "a universe parameter is renamed: names are hashed as written, so its users are re-checked too",
      target := oneParam, ownVisible := true, usersVisible := true
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
  let mut shaFailures := 0
  for (label, input, expected) in shaVectors do
    unless hex (sha256Native input) == expected do
      shaFailures := shaFailures + 1
      IO.println s!"FAIL SHA-256 of {label}"
  IO.println s!"{if shaFailures == 0 then "ok  " else "FAIL"} SHA-256 test vectors ({shaVectors.length})"
  if shaFailures > 0 then return 1
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Init }] {} fun env => do
    let mut consts : Array (Name × ConstantInfo) := #[]
    for (n, ci) in env.constants.map₁ do
      consts := consts.push (n, ci)
    let g := graph consts
    let base := snapshot consts
    IO.println s!"{consts.size} declarations of Init, {base.keys.size} keys"
    let mut failures := 0
    for m in ← mutations consts g do
      let mutated := consts.map fun (n, c) => if n == m.target then (n, m.apply c) else (n, c)
      let after := snapshot mutated
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
    -- Two axioms with the same type differ only in their names, and the kernel tells them apart. So `a = a` and
    -- `a = b`, with the same proof, must get different keys.
    let nat := mkConst ``Nat
    let eq (x y : Name) := mkApp3 (mkConst ``Eq [1]) nat (mkConst x) (mkConst y)
    let proof := mkApp2 (mkConst ``rfl [1]) nat (mkConst `collideA)
    let tySame := eq `collideA `collideA
    let tyOther := eq `collideA `collideB
    let ax (n : Name) : ConstantInfo :=
      .axiomInfo { name := n, levelParams := [], type := nat, isUnsafe := false }
    let th (n : Name) (ty : Expr) : ConstantInfo :=
      .thmInfo { name := n, levelParams := [], type := ty, value := proof, all := [n] }
    let extra : Array (Name × ConstantInfo) := #[(`collideA, ax `collideA), (`collideB, ax `collideB),
      (`collideSame, th `collideSame tySame), (`collideOther, th `collideOther tyOther)]
    let s := snapshot (consts ++ extra)
    let distinct := s.keys[`collideSame]? != s.keys[`collideOther]?
    unless distinct do failures := failures + 1
    IO.println s!"{if distinct then "ok  " else "FAIL"} two axioms with the same type: `a = a` and `a = b` get different keys"
    IO.println (if failures == 0 then "all key properties hold" else s!"{failures} failures")
    return if failures == 0 then 0 else 1
