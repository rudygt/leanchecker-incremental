module

public import Toy.A

public section

theorem twice_val (b : Box) : b.twice.val = 2 * b.val := by
  simp [Box.twice, double_eq]

theorem colors_differ : Color.red ≠ Color.green := by decide

def quadruple (n : Nat) : Nat := double (double n)

theorem quadruple_eq (n : Nat) : quadruple n = 4 * n := by
  unfold quadruple; rw [double_eq, double_eq]; omega

end
