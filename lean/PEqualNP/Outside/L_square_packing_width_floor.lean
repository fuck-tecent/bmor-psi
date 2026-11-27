import Mathlib

theorem PEqualNP.Outside.L_square_packing_width_floor :
    ∀ c s:ℝ,c^2+s^2=1 → 1≤|c|+|s| := by
  intro c s h
  have hsq : (|c| + |s|)^2 = c^2 + s^2 + 2 * |c| * |s| := by
    rw [add_sq, sq_abs, sq_abs]
    ring
  have hb : (0:ℝ) ≤ |c| + |s| := by positivity
  have hge : (1:ℝ)^2 ≤ (|c|+|s|)^2 := by
    rw [hsq, one_pow]
    nlinarith [h, mul_nonneg (abs_nonneg c) (abs_nonneg s)]
  have hle := sq_le_sq.mp hge
  rwa [abs_one, abs_of_nonneg hb] at hle
