import Lean
import IncCheck.Sha256

/-!
# Declaration ids

Every constant gets two SHA-256 ids:

* Its **interface id** covers what a kernel check of another declaration can observe through it: its name, kind,
  universe parameters and type, a definition's body, reducibility hints and safety, and the structure of an inductive
  type, constructor or recursor. It also covers the interface ids of every constant those name. A theorem's proof and
  an opaque constant's body are left out, because the kernel never unfolds them.
* Its **declaration id** covers what the kernel reads when it checks the constant itself: the interface id, the
  theorem's proof or the opaque body, and the interface ids of every constant those name.

Expressions are hashed with constants referred to by name, so two constants with the same content but different names
never share an id. Universe levels and parameters are hashed as written. Binder names, binder info and the `nondep`
flag of `let` are left out, and `mdata` is skipped: the kernel reads none of them.

References form cycles only inside an inductive block (its types, constructors and recursors) and inside a mutual
group of definitions, and each of those is hashed as one unit. Any other cycle merges the units involved into one, and
a reference without an interface id leaves the constant, and everything that refers to it, without ids. Those are
always checked.
-/

open Lean

namespace IncCheck

/-! ## Encoding -/

def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  (((b.push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

def pushBytes (b bs : ByteArray) : ByteArray := pushU32 b bs.size ++ bs

/-- A natural number as length-prefixed big-endian bytes, so that literals of any size are encoded exactly. -/
def pushNat (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut digits : Array UInt8 := #[]
  let mut k := n
  while k > 0 do
    digits := digits.push (k % 256).toUInt8
    k := k / 256
  return pushBytes b ⟨digits.reverse⟩

def pushString (b : ByteArray) (s : String) : ByteArray := pushBytes b s.toUTF8

def pushBool (b : ByteArray) (x : Bool) : ByteArray := b.push (if x then 1 else 0)

/-- A name, component by component, so that `` `a.b `` and `` «a.b» `` differ. -/
def pushName (b : ByteArray) (n : Name) : ByteArray :=
  let cs := n.components
  cs.foldl (init := pushU32 b cs.length) fun b c => match c with
    | .str _ s => pushString (b.push 0) s
    | .num _ k => pushNat (b.push 1) k
    | .anonymous => b

def pushNames (b : ByteArray) (ns : List Name) : ByteArray := ns.foldl pushName (pushU32 b ns.length)

partial def pushLevel (b : ByteArray) : Level → ByteArray
  | .zero => b.push 0x20
  | .succ l => pushLevel (b.push 0x21) l
  | .max l₁ l₂ => pushLevel (pushLevel (b.push 0x22) l₁) l₂
  | .imax l₁ l₂ => pushLevel (pushLevel (b.push 0x23) l₁) l₂
  | .param n => pushName (b.push 0x24) n
  | .mvar m => pushName (b.push 0x25) m.name

/-- The whole term, for small terms. -/
partial def pushExpr (b : ByteArray) : Expr → ByteArray
  | .bvar i => pushNat (b.push 0x01) i
  | .fvar x => pushName (b.push 0x02) x.name
  | .mvar m => pushName (b.push 0x03) m.name
  | .sort l => pushLevel (b.push 0x04) l
  | .const n ls => ls.foldl pushLevel (pushU32 (pushName (b.push 0x05) n) ls.length)
  | .app f a => pushExpr (pushExpr (b.push 0x06) f) a
  | .lam _ t body _ => pushExpr (pushExpr (b.push 0x07) t) body
  | .forallE _ t body _ => pushExpr (pushExpr (b.push 0x08) t) body
  | .letE _ t v body _ => pushExpr (pushExpr (pushExpr (b.push 0x09) t) v) body
  | .lit (.natVal n) => pushNat (b.push 0x0A) n
  | .lit (.strVal s) => pushString (b.push 0x0B) s
  | .mdata _ e => pushExpr b e
  | .proj s i e => pushExpr (pushNat (pushName (b.push 0x0C) s) i) e

/-! ## Expressions -/

/-- Digests of the large subterms seen so far. The key is compared with `Expr.eqv`, which ignores binder names and
binder info, and so does the digest. -/
abbrev HashM := StateM (Std.HashMap Expr ByteArray)

/-- Subterms this shallow are hashed whole, in one SHA-256. Deeper ones are hashed from the digests of their children,
with a memo, so that a proof term shared as a DAG costs its size as a DAG. -/
def flatDepth : UInt32 := 8

/-- The digest of a term. Whole-term digests start with `0xF0` and node digests with `0x86` to `0x8C`, so the two
kinds never encode the same bytes. `mdata` is skipped, but not stripped first: rebuilding terms would break the pointer
sharing that makes memo lookups cheap. An `mdata` node can still move a subterm across `flatDepth` and so change a
digest, which only ever causes an extra check. `Expr.eqv` compares `mdata`, so the memo never mixes such terms. -/
partial def digest (e : Expr) : HashM ByteArray := do
  if e.approxDepth ≤ flatDepth then
    return sha256Native (pushExpr (ByteArray.empty.push 0xF0) e)
  if let some d := (← get)[e]? then
    return d
  let node (tag : UInt8) (parts : List ByteArray) : ByteArray :=
    sha256Native (parts.foldl (· ++ ·) (ByteArray.empty.push tag))
  -- `pure`, not `return`: `return` would leave `digest` before the memo below is written.
  let d ← match e with
    | .app f a => pure (node 0x86 [← digest f, ← digest a])
    | .lam _ t body _ => pure (node 0x87 [← digest t, ← digest body])
    | .forallE _ t body _ => pure (node 0x88 [← digest t, ← digest body])
    | .letE _ t v body _ => pure (node 0x89 [← digest t, ← digest v, ← digest body])
    | .proj s i inner => pure (node 0x8C [pushNat (pushName .empty s) i, ← digest inner])
    | .mdata _ inner => digest inner
    | e => pure (sha256Native (pushExpr (ByteArray.empty.push 0xF0) e))
  modify (·.insert e d)
  return d

def exprDigest (e : Expr) : HashM ByteArray := digest e

/-! ## Constants -/

def kindTag : ConstantInfo → UInt8
  | .axiomInfo _ => 1 | .defnInfo _ => 2 | .thmInfo _ => 3 | .opaqueInfo _ => 4
  | .quotInfo _ => 5 | .inductInfo _ => 6 | .ctorInfo _ => 7 | .recInfo _ => 8

/-- Everything other declarations can observe through `c`, without the ids of the constants it names. -/
def interfaceContent (c : ConstantInfo) : HashM ByteArray := do
  let mut b := pushNames (pushName (ByteArray.empty.push (kindTag c)) c.name) c.levelParams
  b := b ++ (← exprDigest c.type)
  match c with
  | .axiomInfo v => b := pushBool b v.isUnsafe
  | .defnInfo v =>
    b := b ++ (← exprDigest v.value)
    b := match v.hints with
      | .opaque => b.push 0
      | .abbrev => b.push 1
      | .regular h => pushNat (b.push 2) h.toNat
    b := b.push (match v.safety with | .safe => 0 | .unsafe => 1 | .partial => 2)
    b := pushNames b v.all
  | .thmInfo v => b := pushNames b v.all
  | .opaqueInfo v => b := pushNames (pushBool b v.isUnsafe) v.all
  | .quotInfo v => b := b.push (match v.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)
  | .inductInfo v =>
    b := pushNames (pushNames (pushNat (pushNat b v.numParams) v.numIndices) v.all) v.ctors
    b := pushBool (pushBool (pushBool (pushNat b v.numNested) v.isRec) v.isUnsafe) v.isReflexive
  | .ctorInfo v =>
    b := pushBool (pushNat (pushNat (pushNat (pushName b v.induct) v.cidx) v.numParams) v.numFields) v.isUnsafe
  | .recInfo v =>
    b := pushNat (pushNat (pushNat (pushNat (pushNames b v.all) v.numParams) v.numIndices) v.numMotives) v.numMinors
    b := pushU32 (pushBool (pushBool b v.k) v.isUnsafe) v.rules.length
    for r in v.rules do
      b := pushNat (pushName b r.ctor) r.nfields ++ (← exprDigest r.rhs)
  return sha256Native b

/-- What only `c`'s own check reads: a theorem's proof or an opaque constant's body. -/
def ownContent (c : ConstantInfo) : HashM ByteArray :=
  match c with
  | .thmInfo v => exprDigest v.value
  | .opaqueInfo v => exprDigest v.value
  | _ => pure .empty

def addConsts (s : NameSet) (e : Expr) : NameSet := e.foldConsts s fun n s => s.insert n

def addNames (s : NameSet) (ns : List Name) : NameSet := ns.foldl (fun (s : NameSet) n => s.insert n) s

/-- The constants `interfaceContent` names. -/
def interfaceRefs (c : ConstantInfo) : NameSet :=
  let s := addConsts {} c.type
  let s := match c with
    | .defnInfo v => addNames (addConsts s v.value) v.all
    | .thmInfo v => addNames s v.all
    | .opaqueInfo v => addNames s v.all
    | .inductInfo v => addNames s (v.all ++ v.ctors)
    | .ctorInfo v => s.insert v.induct
    | .recInfo v =>
      v.rules.foldl (fun (s : NameSet) (r : RecursorRule) => addConsts (s.insert r.ctor) r.rhs) (addNames s v.all)
    | _ => s
  s.erase c.name

/-- Every constant `c`'s own check reads. -/
def ownRefs (c : ConstantInfo) : NameSet :=
  let s := interfaceRefs c
  let s := match c with
    | .thmInfo v => addConsts s v.value
    | .opaqueInfo v => addConsts s v.value
    | _ => s
  s.erase c.name

/-- The unit `c` is hashed in, named by its first member: an inductive block (its types, constructors and recursors),
a mutual group, or `c` alone. -/
def unitOf (find : Name → Option ConstantInfo) (c : ConstantInfo) : Name :=
  match c with
  | .inductInfo v => v.all.headD c.name
  | .ctorInfo v => match find v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | .recInfo v => v.all.headD c.name
  | .defnInfo v => if v.all.length > 1 then v.all.headD c.name else c.name
  | .thmInfo v => if v.all.length > 1 then v.all.headD c.name else c.name
  | .opaqueInfo v => if v.all.length > 1 then v.all.headD c.name else c.name
  | _ => c.name

/-! ## Groups of constants -/

/-- Strongly connected components of `succ` over `nodes`, each listed after every component it has an edge into.
Iterative Tarjan, because reference chains can be deep. -/
def sccs (nodes : Array Name) (succ : Name → Array Name) : Array (Array Name) := Id.run do
  let inSet : Std.HashSet Name := nodes.foldl (·.insert ·) {}
  let succIn (v : Name) : Array Name := (succ v).filter inSet.contains
  let mut index : Std.HashMap Name Nat := {}
  let mut low : Std.HashMap Name Nat := {}
  let mut onStack : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  let mut out : Array (Array Name) := #[]
  let mut counter := 0
  for root in nodes do
    if index.contains root then continue
    index := index.insert root counter
    low := low.insert root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.insert root
    let mut work : Array (Name × Array Name × Nat) := #[(root, succIn root, 0)]
    while work.size > 0 do
      let (v, ss, i) := work.back!
      if h : i < ss.size then
        work := work.pop.push (v, ss, i + 1)
        let w := ss[i]
        if !index.contains w then
          index := index.insert w counter
          low := low.insert w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.insert w
          work := work.push (w, succIn w, 0)
        else if onStack.contains w then
          low := low.insert v (min low[v]! index[w]!)
      else
        work := work.pop
        if let some (u, _, _) := work.back? then
          low := low.insert u (min low[u]! low[v]!)
        if low[v]! == index[v]! then
          let mut comp := #[]
          let mut more := true
          while more do
            let x := stack.back!
            stack := stack.pop
            onStack := onStack.erase x
            comp := comp.push x
            more := x != v
          out := out.push comp
  return out

/-- The ids of one constant. -/
structure Ids where
  interface : ByteArray
  decl : ByteArray

/-- The ids of `infos`, given the interface ids in `table` of every constant outside `infos` that they refer to.
`find` looks up constants by name. Returns the ids of every constant whose ids are exact, `table` extended with their
interface ids, and how many constants got no ids. -/
def hashGroup (infos : Array (Name × ConstantInfo)) (table : Std.HashMap Name ByteArray)
    (find : Name → Option ConstantInfo) : Std.HashMap Name Ids × Std.HashMap Name ByteArray × Nat := Id.run do
  let byName : Std.HashMap Name ConstantInfo := infos.foldl (fun m (n, c) => m.insert n c) {}
  let mut members : Std.HashMap Name (Array Name) := {}
  for (n, c) in infos do
    let u := unitOf find c
    members := members.insert u ((members.getD u #[]).push n)
  let unitOfName (n : Name) : Option Name := byName[n]?.map (unitOf find)
  let unitRefs (u : Name) : NameSet :=
    (members.getD u #[]).foldl (fun s m => (interfaceRefs byName[m]!).foldl (·.insert ·) s) {}
  let succ (u : Name) : Array Name :=
    (unitRefs u).toArray.filterMap fun r => (unitOfName r).filter (· != u)
  let units := members.keys.toArray.qsort (Name.cmp · · == .lt)
  let mut table := table
  let mut ids : Std.HashMap Name Ids := {}
  let mut interface : Std.HashMap Name ByteArray := {}
  let mut inexact := 0
  let mut memo : Std.HashMap Expr ByteArray := {}
  for comp in sccs units succ do
    let names := (comp.foldl (fun acc u => acc ++ members.getD u #[]) #[]).qsort (Name.cmp · · == .lt)
    let inComp : NameSet := names.foldl (·.insert ·) {}
    let refs := (comp.foldl (fun s u => (unitRefs u).foldl (·.insert ·) s) ({} : NameSet)).toArray.filter
      (!inComp.contains ·)
    let mut b := pushU32 (ByteArray.empty.push 0x31) names.size
    for n in names do
      let (d, memo') := (interfaceContent byName[n]!).run memo
      memo := memo'
      b := pushName b n ++ d
    let mut exact := true
    for r in refs do
      match table[r]? with
      | some id => b := pushName b r ++ id
      | none => exact := false
    if exact then
      let unitDigest := sha256Native b
      for n in names do
        let id := sha256Native (pushName (ByteArray.empty.push 0x32) n ++ unitDigest)
        table := table.insert n id
        interface := interface.insert n id
    else
      inexact := inexact + names.size
  for (n, c) in infos do
    let some iface := interface[n]? | continue
    let (extra, memo') := (ownContent c).run memo
    memo := memo'
    let iRefs := interfaceRefs c
    let mut b := (ByteArray.empty.push 0x33) ++ iface ++ extra
    let mut exact := true
    for r in (ownRefs c).toArray do
      unless iRefs.contains r do
        match table[r]? with
        | some id => b := pushName b r ++ id
        | none => exact := false
    if exact then
      ids := ids.insert n { interface := iface, decl := sha256Native b }
    else
      inexact := inexact + 1
  return (ids, table, inexact)

end IncCheck
