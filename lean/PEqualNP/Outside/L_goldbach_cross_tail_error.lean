import Mathlib

theorem PEqualNP.Outside.L_goldbach_cross_tail_error :
    ∀ a b : ℂ, |‖a+b‖^2-‖a‖^2| ≤ 2*‖a‖*‖b‖+‖b‖^2 := by
  intro a b
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hleft : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have hsub : ‖(a + b) - b‖ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le (a + b) b
    simpa using hsub
  have h2 : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have h3 : ‖a + b‖ + ‖a‖ ≤ 2 * ‖a‖ + ‖b‖ := by linarith
  have hnonneg : 0 ≤ ‖a + b‖ + ‖a‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have h4 : |‖a + b‖ ^ 2 - ‖a‖ ^ 2| = |‖a + b‖ - ‖a‖| * (‖a + b‖ + ‖a‖) := by
    rw [show ‖a + b‖ ^ 2 - ‖a‖ ^ 2 = (‖a + b‖ - ‖a‖) * (‖a + b‖ + ‖a‖) by ring]
    rw [abs_mul, abs_of_nonneg hnonneg]
  calc |‖a + b‖ ^ 2 - ‖a‖ ^ 2|
      = |‖a + b‖ - ‖a‖| * (‖a + b‖ + ‖a‖) := h4
    _ ≤ ‖b‖ * (2 * ‖a‖ + ‖b‖) := by
        exact mul_le_mul h2 h3 hnonneg (norm_nonneg _)
    _ = 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring
