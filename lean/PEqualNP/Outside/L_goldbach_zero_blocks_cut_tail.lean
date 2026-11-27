import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_cut_tail :
    ∀ (n : ℕ) (ρ a : Fin n → ℂ) (T : ℝ), ‖(∑ i,a i)-(∑ i, if abs (ρ i).im≤T then a i else 0)‖ ≤ ∑ i, if T<abs (ρ i).im then ‖a i‖ else 0 := by
  intro n ρ a T
  have hsplit : (∑ i, a i) - (∑ i, if abs (ρ i).im ≤ T then a i else 0)
      = ∑ i, (a i - if abs (ρ i).im ≤ T then a i else 0) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  calc ‖∑ i, (a i - if abs (ρ i).im ≤ T then a i else 0)‖
      ≤ ∑ i, ‖a i - if abs (ρ i).im ≤ T then a i else 0‖ := norm_sum_le _ _
    _ ≤ ∑ i, if T < abs (ρ i).im then ‖a i‖ else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hle : abs (ρ i).im ≤ T
        · rw [if_pos hle, if_neg (not_lt.mpr hle), sub_self, norm_zero]
        · rw [if_neg hle, if_pos (not_le.mp hle), sub_zero]
