import Mathlib

theorem Conjectures.JoshiAbc.MeasurableDensity :
    ∀ (w v ρ : ℝ) (d : ℕ), 0 < w → 0 < ρ → ρ ≤ 1 → 0 < d → ρ*w ≤ v → (Real.log w + Real.log ρ)/d ≤ Real.log v/d := by
  intro w v ρ d hw hρ _ hd hle
  have hpos : (0:ℝ) < w * ρ := mul_pos hw hρ
  have hprod : w * ρ ≤ v := by
    have hcomm : w * ρ = ρ * w := mul_comm w ρ
    linarith [hle, hcomm]
  have hlog : Real.log w + Real.log ρ = Real.log (w * ρ) :=
    (Real.log_mul hw.ne' hρ.ne').symm
  have hmono : Real.log (w * ρ) ≤ Real.log v := Real.log_le_log hpos hprod
  have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [hlog]
  exact div_le_div_of_nonneg_right hmono hdpos.le
