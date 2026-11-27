import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_square_asymmetric_error : ∀ (x y : ℂ) (M E : ℝ), 0 ≤ M → 0 ≤ E → ‖y‖ ≤ M → ‖x-y‖ ≤ E → |‖x‖^2-‖y‖^2| ≤ E*(2*M+E) := by
  intro x y M E hM hE hy hxy
  have hx : ‖x‖ ≤ M + E := by
    calc ‖x‖ = ‖y + (x - y)‖ := by ring_nf
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      _ ≤ M + E := add_le_add hy hxy
  have h1 : |‖x‖ - ‖y‖| ≤ E := (abs_norm_sub_norm_le x y).trans hxy
  have h2 : |‖x‖ + ‖y‖| ≤ 2*M + E := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  calc |‖x‖^2 - ‖y‖^2| = |(‖x‖ - ‖y‖) * (‖x‖ + ‖y‖)| := by
        rw [show ‖x‖^2 - ‖y‖^2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) by ring]
    _ = |‖x‖ - ‖y‖| * |‖x‖ + ‖y‖| := abs_mul _ _
    _ ≤ E * (2*M + E) := by
        exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)