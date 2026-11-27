import Mathlib

theorem Conjectures.JoshiAbc.LinearHull : ∀ l Q R U δ : ℝ, 3 < l → -((l+1)/4)*Q-δ ≤ R → R ≤ -(l*(l+1)/12)*Q+U → 2*l*Q/6 ≤ 4*l/((l-3)*(l+1))*(U+δ) := by
  intro l Q R U δ hl h1 h2
  have hD : 0 < (l - 3) * (l + 1) := by nlinarith
  have hkey : (l - 3) * (l + 1) * Q ≤ 12 * (U + δ) := by nlinarith
  have hl0 : (0:ℝ) ≤ l := by linarith
  have hmul : l * ((l - 3) * (l + 1) * Q) ≤ l * (12 * (U + δ)) :=
    mul_le_mul_of_nonneg_left hkey hl0
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  nlinarith [hmul]
