import Mathlib

theorem PEqualNP.Outside.L_goldbach_height_quadratic_loss :
    ∀ a b x : ℝ, 1-Real.cos ((a-b)*x) ≤ (a-b)^2*x^2/2 := by
  intro a b x
  have h := Real.one_sub_sq_div_two_le_cos (x := (a - b) * x)
  rw [mul_pow] at h
  linarith only [h]
