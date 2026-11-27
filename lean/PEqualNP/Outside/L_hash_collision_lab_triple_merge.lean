import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_triple_merge :
    ∀ a b:ℕ, Nat.choose (a+b) 3=Nat.choose a 3+Nat.choose b 3+Nat.choose a 2*b+a*Nat.choose b 2 := by
  intro a b
  rw [Nat.add_choose_eq a b 3]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_zero_right, Nat.choose_one_right]
  ring

