import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_zero_blocks_block_energy :
    ∀ (n : ℕ) (a : Fin n → ℂ), ‖∑ i, a i‖^2≤(n:ℝ)*∑ i,‖a i‖^2 := by
  intro n a
  have htri : ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hcs : (∑ i, ‖a i‖) ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * (n : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin n => ‖a i‖) (fun _ : Fin n => (1 : ℝ))
    simpa using h
  calc
    ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := htri
    _ ≤ (∑ i, ‖a i‖ ^ 2) * (n : ℝ) := hcs
    _ = (n : ℝ) * ∑ i, ‖a i‖ ^ 2 := by ring

end PEqualNP.Outside
