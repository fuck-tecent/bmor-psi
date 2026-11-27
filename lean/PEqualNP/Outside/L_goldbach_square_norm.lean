import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_square_norm :
    ∀ (S M : ℂ) (E : ℝ), ‖S-M‖≤E → ‖S^2-M^2‖≤E*(2*‖M‖+E) := by
  intro S M E hE
  have hsum : ‖S + M‖ ≤ 2 * ‖M‖ + E := calc
    ‖S + M‖ = ‖(S - M) + (M + M)‖ := by rw [show S + M = (S - M) + (M + M) by ring]
    _ ≤ ‖S - M‖ + ‖M + M‖ := norm_add_le _ _
    _ ≤ E + (‖M‖ + ‖M‖) := add_le_add hE (norm_add_le M M)
    _ = _ := by ring
  rw [show S ^ 2 - M ^ 2 = (S - M) * (S + M) by ring, Complex.norm_mul]
  exact mul_le_mul hE hsum (norm_nonneg _) ((norm_nonneg _).trans hE)
