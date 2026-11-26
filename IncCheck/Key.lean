import IncCheck.Hash

/-!
# Check keys

A check key names one kernel verdict: "this kernel accepted this declaration, given everything it refers to". It is
the SHA-256 of:

* the key scheme,
* `Lean.githash`, the commit of the running kernel, so verdicts from different kernels never mix,
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
  ``Bool.true, ``String.ofList, ``Char, ``Char.ofNat, ``List.cons, ``List.nil,
  ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, `eagerReduce]

def keyScheme : String := "leanchecker-inc/4"

/-- The digest that every check key of one run starts with, given the interface ids of all constants. -/
def keyPrefix (interfaces : Std.HashMap Name ByteArray) : ByteArray := Id.run do
  let mut b := pushString (pushString .empty keyScheme) Lean.githash
  for n in kernelBuiltins do
    b := match interfaces[n]? with
      | some id => pushName (b.push 1) n ++ id
      | none => pushName (b.push 0) n
  return sha256Native b

/-- The check key of a declaration with declaration id `decl`. -/
def checkKey (pre decl : ByteArray) : ByteArray := sha256Native (pre ++ decl)

/-- The verdict key of an inductive block: the check keys of its types, constructors and recursors, by name. -/
def blockKey (members : Array (Name × ByteArray)) : ByteArray := Id.run do
  let sorted := members.qsort fun a b => Name.cmp a.1 b.1 == .lt
  let mut b := pushString .empty s!"{keyScheme} inductive block"
  for (n, key) in sorted do
    b := pushName b n ++ key
  return sha256Native b

end IncCheck
