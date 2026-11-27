import Mathlib

theorem Conjectures.JoshiAbc.ConstantHull :
    ∀ l Q R U δ : ℝ, 3 < l → -Q-δ ≤ R → R ≤ -(l*(l+1)/12)*Q+U →
      2*l*Q/6 ≤ 4*l/((l-3)*(l+4))*(U+δ) := by
  intro l Q R U δ hl hlower hupper
  have hD : 0 < (l - 3) * (l + 4) := by
    nlinarith
  have hkey : (l - 3) * (l + 4) * Q ≤ 12 * (U + δ) := by
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ l)]
