import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem Conjectures.Cuts.Task55422f3cecc6df13924fe708 :
  (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → x1 * ↑x6 ≤ x3 * ↑x6 * Real.log ↑x6) := by
  intro C _hC ε hε
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (C / ε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hLog
  refine ⟨N, ?_⟩
  intro X hX
  have hBound := (div_le_iff₀ hε).mp (hN X hX)
  calc
    C * (X : ℝ) ≤ (Real.log (X : ℝ) * ε) * (X : ℝ) :=
      mul_le_mul_of_nonneg_right hBound (Nat.cast_nonneg X)
    _ = ε * (X : ℝ) * Real.log (X : ℝ) := by
      rw [mul_comm (Real.log (X : ℝ)) ε, mul_assoc,
        mul_comm (Real.log (X : ℝ)) (X : ℝ), ← mul_assoc]
