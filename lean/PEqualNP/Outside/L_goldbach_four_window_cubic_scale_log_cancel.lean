import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_cubic_scale_log_cancel :
    ∀ X a b : ℝ, 0 < X → (a*Real.log X+b)-3*(a*Real.log (X/2)+b)+3*(a*Real.log (X/4)+b)-(a*Real.log (X/8)+b)=0 := by
  intro X a b hX
  have hX0 : X ≠ 0 := ne_of_gt hX
  have h2 : Real.log (X/2) = Real.log X - Real.log 2 := Real.log_div hX0 (by norm_num)
  have h4 : Real.log (X/4) = Real.log X - Real.log 4 := Real.log_div hX0 (by norm_num)
  have h8 : Real.log (X/8) = Real.log X - Real.log 8 := Real.log_div hX0 (by norm_num)
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    have h : (4:ℝ) = 2^2 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    have h : (8:ℝ) = 2^3 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  rw [h2, h4, h8, l4, l8]
  ring
