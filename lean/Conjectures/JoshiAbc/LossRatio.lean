import Mathlib

theorem Conjectures.JoshiAbc.LossRatio :
    ∀ l : ℝ, 3 < l → (4*l/((l-3)*(l+1))) / (4*l/((l-3)*(l+4))) = 1+3/(l+1) := by
  intro l hl
  have h0 : l ≠ 0 := ne_of_gt (by linarith)
  have h3 : l - 3 ≠ 0 := ne_of_gt (by linarith)
  have h1 : l + 1 ≠ 0 := ne_of_gt (by linarith)
  have h4 : l + 4 ≠ 0 := ne_of_gt (by linarith)
  have hprod : (l - 3) * (l + 1) ≠ 0 := mul_ne_zero h3 h1
  have hprod4 : (l - 3) * (l + 4) ≠ 0 := mul_ne_zero h3 h4
  field_simp
  ring
