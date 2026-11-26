-- Two axioms and two inductive types with identical content but different names, and valid declarations about them.
axiom a : Nat
axiom b : Nat

theorem good : a = a := rfl

inductive A where
  | mk

inductive B where
  | mk

def g : A → A := fun x => x
