import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_inverse_floor :
    ∀ s : ℂ, s.re=1/2 → ‖s⁻¹‖≤2 := by
  intro s h
  have hsq : ‖s‖^2 = 1/4 + s.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h]
    ring
  have hnorm : (1/2:ℝ) ≤ ‖s‖ := by nlinarith [sq_nonneg s.im, norm_nonneg s]
  have hpos : (0:ℝ) < ‖s‖ := by linarith
  rw [norm_inv]
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith
