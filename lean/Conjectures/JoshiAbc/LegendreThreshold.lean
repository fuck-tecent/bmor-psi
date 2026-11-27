import Mathlib

theorem Conjectures.JoshiAbc.LegendreThreshold :
  ∀ l Q : ℝ, 7 ≤ l → (l*(l+1)/12-1)*Q ≤ (l+5)/4*Real.log Real.pi → 2*l*Q ≤ 126/11*Real.log Real.pi := by
  intro l Q hl hQ
  have hc : 0 < l * (l + 1) / 12 - 1 := by nlinarith [sq_nonneg (l - 7)]
  have hlog : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hcoeff : 2 * l * ((l + 5) / 4) ≤ (l * (l + 1) / 12 - 1) * (126 / 11) := by
    nlinarith [sq_nonneg (l - 7)]
  have hmul :
      (l * (l + 1) / 12 - 1) * (2 * l * Q) ≤
        (l * (l + 1) / 12 - 1) * (126 / 11 * Real.log Real.pi) := calc
    (l * (l + 1) / 12 - 1) * (2 * l * Q)
      = 2 * l * ((l * (l + 1) / 12 - 1) * Q) := by ring
    _ ≤ 2 * l * ((l + 5) / 4 * Real.log Real.pi) :=
        mul_le_mul_of_nonneg_left hQ (by linarith)
    _ = 2 * l * ((l + 5) / 4) * Real.log Real.pi := by ring
    _ ≤ (l * (l + 1) / 12 - 1) * (126 / 11) * Real.log Real.pi :=
        mul_le_mul_of_nonneg_right hcoeff hlog
    _ = (l * (l + 1) / 12 - 1) * (126 / 11 * Real.log Real.pi) := by ring
  exact le_of_mul_le_mul_left hmul hc