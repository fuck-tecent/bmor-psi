import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_pair_defect :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n), 2*‖∑ i,a i‖≤∑ i,‖a i+a (e i)‖ := by
  intro n a e
  have hsum : ∑ i, (a i + a (e i)) = (2 : ℂ) * (∑ i, a i) := by
    rw [Finset.sum_add_distrib, e.sum_comp, two_mul]
  calc
    2 * ‖∑ i, a i‖ = ‖∑ i, (a i + a (e i))‖ := by simp [hsum]
    _ ≤ _ := norm_sum_le _ _
