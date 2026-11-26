import CA.RefHash

/-!
# Check keys

A check key names one kernel verdict: "this kernel accepted this declaration, given the content of everything it
refers to". It hashes:

* the key scheme,
* `Lean.githash`, the commit of the running kernel, so verdicts from different kernels never mix,
* the `ref` id of each constant the kernel uses by name without the declaration referring to it,
* CA's `decl` id, which covers the declaration's type, value (proofs included) and structural fields, with every
  referenced constant replaced by its `ref` id: the statement for theorems, the full declaration otherwise.
-/

open Lean CA.RefHash CA.SHA256

namespace IncCheck

/-- Constants the kernel looks up by name (`research/incremental-leanchecker/kernel-builtins.md` in LeanMR). -/
def kernelBuiltins : Array Name := #[
  ``Nat, ``String, ``Nat.zero, ``Nat.succ,
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``Bool.true, ``String.ofList, ``Char, ``Char.ofNat, ``List.cons, ``List.nil,
  ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, `eagerReduce]

def keyScheme : String := "leanchecker-inc/1"

private def pushBytes (b bs : ByteArray) : ByteArray := Id.run do
  let mut b := b
  let n := bs.size.toUInt64
  for i in [0:8] do
    b := b.push (n >>> (8 * i).toUInt64).toUInt8
  return b ++ bs

/-- The digest that every check key of one run starts with. -/
def keyPrefix (hasher : Hasher) (refs : RefTable) : IO ByteArray := do
  let mut b := pushBytes .empty keyScheme.toUTF8
  b := pushBytes b Lean.githash.toUTF8
  for n in kernelBuiltins do
    b := pushBytes b n.toString.toUTF8
    b := match refs[n]? with
      | some r => pushBytes (b.push 1) r
      | none => b.push 0
  hasher b

/-- The check key of a declaration, or `none` when CA had to hash a reference by name, so the ids are not exact. -/
def checkKey (hasher : Hasher) (pre : ByteArray) (ids : DeclIds) : IO (Option ByteArray) := do
  if ids.unresolved.isEmpty then
    return some (← hasher (pre ++ ids.decl))
  else
    return none

end IncCheck
