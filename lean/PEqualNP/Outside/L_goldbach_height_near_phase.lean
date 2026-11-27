import Mathlib

theorem PEqualNP.Outside.L_goldbach_height_near_phase :
    ∀ a b x : ℝ, ‖Complex.exp ((((a-b)*x : ℝ) : ℂ)*Complex.I)-1‖ ≤ |a-b| * |x| := by
  intro a b x
  rw [mul_comm _ Complex.I]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (a - b) * x))
