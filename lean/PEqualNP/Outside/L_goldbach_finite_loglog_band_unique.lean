import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_loglog_band_unique :
    ∀ n : ℕ, 4 ≤ n → (n:ℝ) < Real.exp (Real.exp 50) → ∃! j : ℕ, j < 1000 ∧ (j:ℝ)/20 ≤ Real.log (Real.log n) ∧ Real.log (Real.log n) < ((j:ℝ)+1)/20 := by
  intro n hn hnlt
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hlog : 1 ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).2
    (by linarith [Real.exp_one_lt_three])
  let t := Real.log (Real.log n)
  have ht : 0 ≤ t := Real.log_nonneg hlog
  have ht50 : t < 50 := (Real.log_lt_iff_lt_exp (by linarith : 0 < Real.log n)).2
    ((Real.log_lt_iff_lt_exp hnpos).2 hnlt)
  have hscaled : 0 ≤ 20 * t := by positivity
  refine ⟨⌊20 * t⌋₊, ⟨(Nat.floor_lt hscaled).2 (by push_cast; linarith), ?_, ?_⟩, ?_⟩
  · change (⌊20 * t⌋₊ : ℝ) / 20 ≤ t
    linarith [Nat.floor_le hscaled]
  · change t < ((⌊20 * t⌋₊ : ℝ) + 1) / 20
    linarith [Nat.lt_floor_add_one (20 * t)]
  · intro j hj
    obtain ⟨_, hlo, hhi⟩ := hj
    change (j : ℝ) / 20 ≤ t at hlo
    change t < ((j : ℝ) + 1) / 20 at hhi
    exact ((Nat.floor_eq_iff hscaled).2 ⟨by linarith, by linarith⟩).symm
