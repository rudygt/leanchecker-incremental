module

public section

@[expose] def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double; omega

inductive Color where
  | red | green
deriving DecidableEq

structure Box where
  val : Nat

@[expose] def Box.twice (b : Box) : Box := ⟨double b.val⟩

end
