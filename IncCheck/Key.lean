import IncCheck.Hash

/-!
# Check keys

A check key names one kernel verdict: "this kernel accepted this declaration, given everything it refers to". It is
the SHA-256 of:

* the key scheme,
* `Lean.githash`, the commit of the running kernel, so verdicts from different kernels never mix,
* the `LEAN_NAT_MAX_SIZE` environment variable, which sets the largest `Nat` literal the kernel accepts,
* the interface id of each constant the kernel uses by name without the declaration referring to it,
* the declaration id (`IncCheck.Hash`), which covers the declaration itself and the interface ids of everything it
  refers to.
-/

open Lean

namespace IncCheck

/-- Constants the kernel looks up by name (`docs/kernel-builtins.md`). -/
def kernelBuiltins : Array Name := #[
  ``Nat, ``String, ``Nat.zero, ``Nat.succ,
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``Bool.true, ``Bool.false, ``String.ofList, ``Char, ``Char.ofNat, ``List.cons, ``List.nil,
  ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, `eagerReduce]

def keyScheme : String := "leanchecker-inc/5"

/-- The digest that every check key of one run starts with, given the interface ids of all constants with exact ids
and the set of constants present. `none` if a constant the kernel uses by name is present without an exact id: its
content would then be in no key, so no declaration of the run may skip the kernel. -/
def keyPrefix (interfaces : Std.HashMap Name ByteArray) (present : Name → Bool) (natMaxSize : Option String) :
    Option ByteArray := Id.run do
  if kernelBuiltins.any fun n => present n && !interfaces.contains n then return none
  let mut b := pushString (pushString .empty keyScheme) Lean.githash
  -- The kernel rejects `Nat` literals larger than `LEAN_NAT_MAX_SIZE` bytes, read from the environment when it starts
  -- (`src/kernel/type_checker.cpp`), so verdicts under different limits must not mix.
  b := match natMaxSize with
    | some v => pushString (b.push 1) v
    | none => b.push 0
  for n in kernelBuiltins do
    b := match interfaces[n]? with
      | some id => pushName (b.push 1) n ++ id
      | none => pushName (b.push 0) n
  return some (sha256Native b)

/-- The check key of a declaration with declaration id `decl`. -/
def checkKey (pre decl : ByteArray) : ByteArray := sha256Native (pre ++ decl)

/-- The recursors the kernel generates for the block of `v`: `T.rec` for each type `T`, and `rec_1`, `rec_2`, ...
after the first type's name for the auxiliary types of nested occurrences (`mk_rec_name` and `mk_aux_rec_name_map` in
`src/kernel/inductive.cpp`). A block may skip the kernel only if it stores exactly these. Otherwise a name the kernel
would have generated stays free for another constant to take, which `leanchecker --fresh` rejects as a duplicate. -/
def generatedRecursors (v : InductiveVal) : List Name :=
  let main := v.all.headD v.name
  v.all.map (Name.str · "rec") ++ (List.range v.numNested).map fun i => .str main s!"rec_{i + 1}"

/-- The verdict key of an inductive block: the check keys of its types, constructors and recursors, by name. -/
def blockKey (members : Array (Name × ByteArray)) : ByteArray := Id.run do
  let sorted := members.qsort fun a b => Name.cmp a.1 b.1 == .lt
  let mut b := pushString .empty s!"{keyScheme} inductive block"
  for (n, key) in sorted do
    b := pushName b n ++ key
  return sha256Native b

end IncCheck
