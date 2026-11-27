import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_power_contamination_budget :
    ∀ (n : ℕ), 4*10^18 < n → Real.log (Real.log n) < (76:ℝ)/20 →
      2*((Nat.sqrt n:ℝ)+(Nat.log 2 n:ℝ)*(n:ℝ)^(1/3:ℝ))*(Real.log n)^2 < (n:ℝ)/10^5 := by
  intro n hn hll
  set N : ℝ := (n:ℝ) with hN
  have hNgt : (4*10^18:ℝ) < N := by
    rw [hN]
    exact_mod_cast hn
  have hNpos : (0:ℝ) < N := by linarith
  have hn0 : n ≠ 0 := by omega
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have hLl : Real.log (Real.log N) < 19/5 := by linarith
  have hexp195_lt : Real.exp (19/5) < 45 := by
    have h45 : Real.exp (4/5) < 2.23 := by
      have h : Real.exp (4/5) ≤
          (∑ m ∈ Finset.range 8, (4/5:ℝ)^m/(m.factorial:ℝ)) +
            (4/5:ℝ)^8*((8:ℝ)+1)/((Nat.factorial 8:ℝ)*8) :=
        Real.exp_bound' (x := (4/5:ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      have hnum : (∑ m ∈ Finset.range 8, (4/5:ℝ)^m/(m.factorial:ℝ)) +
            (4/5:ℝ)^8*((8:ℝ)+1)/((Nat.factorial 8:ℝ)*8) < 2.23 := by
        norm_num [Finset.sum_range_succ]
      linarith
    have he1 : Real.exp 1 ^ 3 < (2.7182818286:ℝ)^3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have hprod : Real.exp 1 ^ 3 * Real.exp (4/5) < (2.7182818286:ℝ)^3 * 2.23 := by
      calc Real.exp 1 ^ 3 * Real.exp (4/5) < (2.7182818286:ℝ)^3 * Real.exp (4/5) :=
            mul_lt_mul_of_pos_right he1 (Real.exp_pos (4/5))
        _ < (2.7182818286:ℝ)^3 * 2.23 :=
            mul_lt_mul_of_pos_left h45 (by norm_num)
    have hexp195 : Real.exp (19/5) = Real.exp 1 ^ 3 * Real.exp (4/5) := by
      have h3 : Real.exp (3:ℝ) = Real.exp 1 ^ 3 := by simp
      have h : (19/5:ℝ) = 3 + 4/5 := by norm_num
      rw [h, Real.exp_add, h3]
    calc Real.exp (19/5) = Real.exp 1 ^ 3 * Real.exp (4/5) := hexp195
      _ < (2.7182818286:ℝ)^3 * 2.23 := hprod
      _ < 45 := by norm_num
  have hlogNlt : Real.log N < 45 := by
    have h1 : Real.log N < Real.exp (19/5) := (Real.log_lt_iff_lt_exp hlogNpos).mp hLl
    linarith
  have hlogNsq : (Real.log N)^2 ≤ 2025 := by nlinarith
  have hk_nonneg : (0:ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : (2:ℝ)^(Nat.log 2 n) ≤ N := by
    have h' : (2:ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by exact_mod_cast hpow
    rwa [← hN] at h'
  have hlogineq : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log N := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^Nat.log 2 n) hpowR
    rwa [Real.log_pow] at h
  have hlog2n90 : (Nat.log 2 n : ℝ) ≤ 90 := by
    have hpos : (0:ℝ) ≤ Real.log 2 - 1/2 := by linarith [Real.log_two_gt_d9]
    have h1 : (Nat.log 2 n : ℝ) ≤ 2 * Real.log N := by
      nlinarith [mul_nonneg hk_nonneg hpos]
    linarith
  have hsqrt_nat : (Nat.sqrt n : ℝ)^2 ≤ N := by
    have h' : (Nat.sqrt n : ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast (Nat.sqrt_le' n)
    rwa [← hN] at h'
  have hsqrt_bd : (Nat.sqrt n : ℝ) ≤ N/10^9 := by
    have h1 : (0:ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ N/10^9 := by positivity
    have hsq : (Nat.sqrt n : ℝ)^2 ≤ (N/10^9)^2 := by
      have h3 : N ≤ (N/10^9)^2 := by nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ h1 h2 (by norm_num : (2:ℕ) ≠ 0)).mp hsq
  have hcube : N^(1/3:ℝ) ≤ N/10^12 := by
    have hleft : (N^(1/3:ℝ))^3 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      norm_num
    have hN18 : (10:ℝ)^18 ≤ N := by nlinarith
    have hN2 : (10:ℝ)^36 ≤ N^2 := by nlinarith
    have hN3 : N ≤ (N/10^12)^3 := by
      have h1 : N * (10:ℝ)^36 ≤ N * N^2 := mul_le_mul_of_nonneg_left hN2 hNpos.le
      rw [div_pow]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hright3 : (N^(1/3:ℝ))^3 ≤ (N/10^12)^3 := by
      rw [hleft]
      exact hN3
    exact (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hNpos _).le (by positivity)
      (by norm_num : (3:ℕ) ≠ 0)).mp hright3
  have hcube_nonneg : (0:ℝ) ≤ N^(1/3:ℝ) := (Real.rpow_pos_of_pos hNpos _).le
  have h2 : (Nat.log 2 n : ℝ) * N^(1/3:ℝ) ≤ 90 * (N/10^12) := by
    calc (Nat.log 2 n : ℝ) * N^(1/3:ℝ) ≤ 90 * N^(1/3:ℝ) :=
          mul_le_mul_of_nonneg_right hlog2n90 hcube_nonneg
      _ ≤ 90 * (N/10^12) := mul_le_mul_of_nonneg_left hcube (by norm_num)
  have hterm : (Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * N^(1/3:ℝ) ≤
      N/10^9 + 90*(N/10^12) := by linarith
  have hSnneg : (0:ℝ) ≤ (Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * N^(1/3:ℝ) := by
    have h1 : (0:ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
    have h2' : (0:ℝ) ≤ (Nat.log 2 n : ℝ) * N^(1/3:ℝ) := mul_nonneg hk_nonneg hcube_nonneg
    linarith
  have hS'nonneg : (0:ℝ) ≤ N/10^9 + 90*(N/10^12) := by positivity
  have hstep1 : 2 * ((Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * N^(1/3:ℝ)) * (Real.log N)^2 ≤
      2 * (N/10^9 + 90*(N/10^12)) * (Real.log N)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hterm (sq_nonneg (Real.log N))]
  have hstep2 : 2 * (N/10^9 + 90*(N/10^12)) * (Real.log N)^2 ≤
      2 * (N/10^9 + 90*(N/10^12)) * 2025 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogNsq
      (by linarith : (0:ℝ) ≤ 2 * (N/10^9 + 90*(N/10^12)))]
  have hnum : 2 * (N/10^9 + 90*(N/10^12)) * 2025 < N/10^5 := by nlinarith
  linarith
