import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_scale :
    ∀ (c ε : ℝ), 0<c → 0<ε → ∀ k : ℕ, 4*c*Real.log 2/ε < (2:ℝ)^k → |4*c*Real.log 2/(2:ℝ)^k|<ε := by
  intro c ε hc hε k h
  have hp : 0 < (2 : ℝ)^k := pow_pos (by norm_num) _
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hn : 0 ≤ 4 * c * Real.log 2 := mul_nonneg (mul_nonneg (by norm_num) hc.le) hl
  rw [abs_of_nonneg (div_nonneg hn hp.le)]
  exact (div_lt_iff₀ hp).2 (by simpa only [mul_comm] using (div_lt_iff₀ hε).1 h)
