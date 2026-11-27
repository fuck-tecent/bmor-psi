import Mathlib

/-- Transport the strict gap using three one-sided consequences of the error bounds. -/
theorem PEqualNP.Outside.L_goldbach_rallis_gap_budget :
    ∀ A C B P M U V e f g : ℝ, 0 < A → |(P-M)-4*A*C| ≤ e → |P-U| ≤ f → |M-V| ≤ g → 4*A*B+e+f+g < U-V → B < C := by
  intro A C B P M U V e f g hA hPM hPU hMV hgap
  have h₁ := (abs_le.mp hPM).2
  have h₂ := (abs_le.mp hPU).1
  have h₃ := (abs_le.mp hMV).2
  have hmul : (4 * A) * B < (4 * A) * C := by
    nlinarith only [h₁, h₂, h₃, hgap]
  have hpos : 0 < 4 * A := mul_pos (by norm_num) hA
  by_contra hn
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (le_of_not_gt hn) hpos.le)) hmul
