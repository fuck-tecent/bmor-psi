import Mathlib

theorem PEqualNP.Outside.L_twin_primes_unit_band :
    (let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ x n : ℝ, 1000 ≤ x → x ≤ n → 50*n ≤ 51*x → 1/4 < f x n 1 ∧ f x n 1 < 7/4) := by
  dsimp only
  intro x n hx hxn hw
  have hn : (0 : ℝ) < n := by linarith
  have h1n : (0 : ℝ) < 1 / n := by positivity
  have hlog_lo : 2 * (1 / n) / ((1 / n) + 2) ≤ Real.log (1 + 1 / n) :=
    Real.le_log_one_add_of_nonneg (le_of_lt h1n)
  have hlog_hi : Real.log (1 + 1 / n) < 1 / n := by
    have hpos : (0 : ℝ) < 1 + 1 / n := by positivity
    have hne : (1 + 1 / n : ℝ) ≠ 1 := by intro h; linarith
    have := Real.log_lt_sub_one_of_pos hpos hne
    linarith
  constructor
  · have hx' : 50 * n / 51 ≤ x := by linarith
    have hstep : x * (2 * (1 / n) / ((1 / n) + 2)) ≤ x * Real.log (1 + 1 / n) :=
      mul_le_mul_of_nonneg_left hlog_lo (by linarith)
    have hval : (1 : ℝ) / 4 < (50 * n / 51) * (2 * (1 / n) / ((1 / n) + 2)) := by
      have hn1 : (1 : ℝ) ≤ n := by linarith
      rw [show (50 * n / 51) * (2 * (1 / n) / ((1 / n) + 2)) = 100 * n / (51 * (2 * n + 1)) by
        field_simp
        ring]
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    calc (1 : ℝ) / 4 < (50 * n / 51) * (2 * (1 / n) / ((1 / n) + 2)) := hval
      _ ≤ x * (2 * (1 / n) / ((1 / n) + 2)) := by
          apply mul_le_mul_of_nonneg_right hx'
          positivity
      _ ≤ x * Real.log (1 + 1 / n) := hstep
  · have hstep : x * Real.log (1 + 1 / n) < x * (1 / n) :=
      mul_lt_mul_of_pos_left hlog_hi (by linarith)
    have hle : x * (1 / n) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    linarith
