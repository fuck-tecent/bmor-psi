import Mathlib

open Finset
open scoped ArithmeticFunction

theorem PEqualNP.Outside.L_goldbach_proper_power_correction :
    ∃ C : ℝ,
      0 < C ∧
        ∀ n : ℕ,
          2 ≤ n →
            let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
            let D : ℝ :=
              (∑ p ∈ Finset.range (n + 1),
                  ArithmeticFunction.vonMangoldt p *
                    ArithmeticFunction.vonMangoldt (n - p)) -
                ∑ p ∈ Finset.range (n + 1), w p * w (n - p)
            0 ≤ D ∧ D ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
  refine ⟨4 / (Real.log 2) ^ 2, by positivity, ?_⟩
  intro n hn
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  let S : ℝ :=
    ∑ p ∈ Finset.range (n + 1),
      if IsPrimePow p ∧ ¬ Nat.Prime p then ArithmeticFunction.vonMangoldt p else 0
  let D : ℝ :=
    (∑ p ∈ Finset.range (n + 1),
        ArithmeticFunction.vonMangoldt p * ArithmeticFunction.vonMangoldt (n - p)) -
      ∑ p ∈ Finset.range (n + 1), w p * w (n - p)
  change 0 ≤ D ∧ D ≤ (4 / (Real.log 2) ^ 2) * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 3
  have hΛ_nonneg : ∀ k : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt k := fun k =>
    ArithmeticFunction.vonMangoldt_nonneg
  have hw_le : ∀ k : ℕ, w k ≤ ArithmeticFunction.vonMangoldt k := by
    intro k
    by_cases hk : Nat.Prime k
    · simp [w, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
    · simp [w, hk, hΛ_nonneg k]
  have hdiff : ∀ k : ℕ,
      ArithmeticFunction.vonMangoldt k - w k =
        if IsPrimePow k ∧ ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0 := by
    intro k
    by_cases hk : Nat.Prime k
    · simp [w, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
    · by_cases hkpp : IsPrimePow k
      · simp [w, hk, hkpp]
      · have hzero : ArithmeticFunction.vonMangoldt k = 0 :=
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hkpp
        simp [w, hk, hkpp, hzero]
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hΛ_log : ∀ k : ℕ, k ≤ n → ArithmeticFunction.vonMangoldt k ≤ Real.log (n : ℝ) := by
    intro k hk
    trans Real.log (k : ℝ)
    · exact ArithmeticFunction.vonMangoldt_le_log
    · rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hkpos
      · simp [hlog_nonneg]
      · exact Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hk)
  have hw_log : ∀ k : ℕ, k ≤ n → w k ≤ Real.log (n : ℝ) := by
    intro k hk
    by_cases hkprime : Nat.Prime k
    · have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkprime.pos
      have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      simpa [w, hkprime] using Real.log_le_log hkpos hkn
    · simp [w, hkprime, hlog_nonneg]
  have hDsplit : D = ∑ p ∈ Finset.range (n + 1),
      ((ArithmeticFunction.vonMangoldt p - w p) * ArithmeticFunction.vonMangoldt (n - p) +
        w p * (ArithmeticFunction.vonMangoldt (n - p) - w (n - p))) := by
    simp only [D, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have hterm : ∀ p ∈ Finset.range (n + 1),
      ((ArithmeticFunction.vonMangoldt p - w p) *
          ArithmeticFunction.vonMangoldt (n - p) +
        w p * (ArithmeticFunction.vonMangoldt (n - p) - w (n - p))) ≤
      (if IsPrimePow p ∧ ¬ Nat.Prime p then ArithmeticFunction.vonMangoldt p else 0) *
          Real.log (n : ℝ) +
        Real.log (n : ℝ) *
          (if IsPrimePow (n - p) ∧ ¬ Nat.Prime (n - p) then
            ArithmeticFunction.vonMangoldt (n - p) else 0) := by
    intro p hp
    have hpn : p ≤ n := by simpa using (Finset.mem_range.mp hp)
    have hq : n - p ≤ n := Nat.sub_le _ _
    have hd_p := hdiff p
    have hd_q := hdiff (n - p)
    have h1 : 0 ≤ ArithmeticFunction.vonMangoldt (n - p) := hΛ_nonneg _
    have h2 : 0 ≤ ArithmeticFunction.vonMangoldt p - w p := by
      linarith [hw_le p]
    have h3 : 0 ≤ ArithmeticFunction.vonMangoldt (n - p) - w (n - p) := by
      linarith [hw_le (n - p)]
    have h4 := hΛ_log (n - p) hq
    have h5 := hw_log p hpn
    calc
      _ = (ArithmeticFunction.vonMangoldt p - w p) * ArithmeticFunction.vonMangoldt (n - p) +
            w p * (ArithmeticFunction.vonMangoldt (n - p) - w (n - p)) := rfl
      _ ≤ (ArithmeticFunction.vonMangoldt p - w p) * Real.log (n : ℝ) +
            w p * (ArithmeticFunction.vonMangoldt (n - p) - w (n - p)) := by
        gcongr
      _ ≤ (ArithmeticFunction.vonMangoldt p - w p) * Real.log (n : ℝ) +
            Real.log (n : ℝ) * (ArithmeticFunction.vonMangoldt (n - p) - w (n - p)) := by
        gcongr
      _ = (if IsPrimePow p ∧ ¬ Nat.Prime p then ArithmeticFunction.vonMangoldt p else 0) *
            Real.log (n : ℝ) +
          Real.log (n : ℝ) *
            (if IsPrimePow (n - p) ∧ ¬ Nat.Prime (n - p) then
              ArithmeticFunction.vonMangoldt (n - p) else 0) := by
        rw [hd_p, hd_q]
  have hD_le_sum : D ≤ Real.log (n : ℝ) * (S + S) := by
    calc
      D = ∑ p ∈ Finset.range (n + 1), _ := hDsplit
      _ ≤ ∑ p ∈ Finset.range (n + 1),
          ((if IsPrimePow p ∧ ¬ Nat.Prime p then ArithmeticFunction.vonMangoldt p else 0) *
              Real.log (n : ℝ) +
            Real.log (n : ℝ) *
              (if IsPrimePow (n - p) ∧ ¬ Nat.Prime (n - p) then
                ArithmeticFunction.vonMangoldt (n - p) else 0)) := by
        exact Finset.sum_le_sum hterm
      _ = Real.log (n : ℝ) * (S + S) := by
        let f : ℕ → ℝ := fun p =>
          if IsPrimePow p ∧ ¬ Nat.Prime p then ArithmeticFunction.vonMangoldt p else 0
        have hrefl : (∑ p ∈ Finset.range (n + 1), f (n - p)) =
            ∑ p ∈ Finset.range (n + 1), f p := by
          rw [← Finset.sum_range_reflect f (n + 1)]
          simp [Nat.add_sub_cancel]
        have h1 : (∑ p ∈ Finset.range (n + 1), f p * Real.log (n : ℝ)) =
            S * Real.log (n : ℝ) := by
          simp [S, f, Finset.sum_mul]
        have h2 : (∑ p ∈ Finset.range (n + 1), Real.log (n : ℝ) * f (n - p)) =
            Real.log (n : ℝ) * S := by
          calc
            (∑ p ∈ Finset.range (n + 1), Real.log (n : ℝ) * f (n - p)) =
                Real.log (n : ℝ) * ∑ p ∈ Finset.range (n + 1), f (n - p) := by
              rw [Finset.mul_sum]
            _ = Real.log (n : ℝ) * ∑ p ∈ Finset.range (n + 1), f p := by rw [hrefl]
            _ = Real.log (n : ℝ) * S := by simp [S, f]
        rw [Finset.sum_add_distrib, h1, h2]
        ring
  have hS_le_psi_theta : S ≤ Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime (x := (n : ℝ)), Nat.floor_natCast]
    rw [show S = ∑ p ∈ (Finset.range (n + 1)).filter (fun p => IsPrimePow p ∧ ¬ Nat.Prime p),
        ArithmeticFunction.vonMangoldt p by
      simp [S, Finset.sum_filter]]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have hp2 : 2 ≤ p := hp.2.1.two_le
      have hpn : p ≤ n := by omega
      have hmem : p ∈ Finset.Ioc 0 n := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      exact Finset.mem_filter.mpr ⟨hmem, hp.2.2⟩
    · intro p hp hps
      exact hΛ_nonneg p
  have hS_bound : S ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    refine le_trans hS_le_psi_theta ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact Chebyshev.psi_sub_theta_le hn1
  have hD_nonneg : 0 ≤ D := by
    rw [hDsplit]
    apply Finset.sum_nonneg
    intro p hp
    have h1 : 0 ≤ ArithmeticFunction.vonMangoldt p - w p := by linarith [hw_le p]
    have h2 : 0 ≤ ArithmeticFunction.vonMangoldt (n - p) - w (n - p) := by
      linarith [hw_le (n - p)]
    have h3 : 0 ≤ w p := by
      by_cases hp' : Nat.Prime p
      · simp [w, hp']
        positivity
      · simp [w, hp']
    have h4 : 0 ≤ ArithmeticFunction.vonMangoldt (n - p) := hΛ_nonneg _
    exact add_nonneg (mul_nonneg h1 h4) (mul_nonneg h3 h2)
  constructor
  · exact hD_nonneg
  · -- final constants
    have hD_bound : D ≤ 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by
      calc
        D ≤ Real.log (n : ℝ) * (S + S) := hD_le_sum
        _ = 2 * Real.log (n : ℝ) * S := by ring
        _ ≤ 2 * Real.log (n : ℝ) * (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by
          gcongr
        _ = 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n))
    have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlog2pos hlog2le
    have hlog2sq : (Real.log 2) ^ 2 ≤ Real.log (n : ℝ) := by
      have hlog2lt1 : Real.log 2 ≤ 1 := by
        nlinarith [Real.log_two_lt_d9]
      nlinarith [hlog2pos, hlog2le, hlog2lt1, sq_nonneg (Real.log 2)]
    have hlog_sq_bound : Real.log (n : ℝ) ^ 2 ≤
        Real.log (n : ℝ) ^ 3 / (Real.log 2) ^ 2 := by
      have ha2pos : 0 < (Real.log 2) ^ 2 := by positivity
      rw [le_div_iff₀ ha2pos]
      nlinarith [mul_le_mul_of_nonneg_right hlog2sq (sq_nonneg (Real.log (n : ℝ)))]
    calc
      D ≤ 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) := hD_bound
      _ = 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2 := by ring
      _ ≤ 4 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ) ^ 3 / (Real.log 2) ^ 2) := by
        gcongr
      _ = (4 / (Real.log 2) ^ 2) * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 3 := by ring
