import Mathlib

open scoped BigOperators
open Finset

theorem Conjectures.Goldbach.PacketMangoldtUniformSpectralError :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t))
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0
    let high := fun (n k : ℕ) => w k - low n k
    let d := fun (n : ℕ) (t : ℝ) =>
      ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      d n t ≤ 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  intro w E S low high d n hn t
  have hphase : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hcoeff : ∀ k : ℕ,
      ArithmeticFunction.vonMangoldt k - high n k =
        if Nat.Prime k then low n k else ArithmeticFunction.vonMangoldt k := by
    intro k
    by_cases hp : Nat.Prime k
    · by_cases hcube : k ^ 3 ≤ n
      · simp [high, low, w, hp, hcube,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp [high, low, w, hp, hcube,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [high, low, w, hp]
  have hcoeff_nonneg : ∀ k : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt k - high n k := by
    intro k
    rw [hcoeff k]
    split_ifs with hp
    · dsimp only [low]
      split_ifs with hcube
      · dsimp only [w]
        simp only [hp, if_pos]
        exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  have hdiff :
      S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t =
        ∑ k ∈ Finset.range (n + 1),
          ((ArithmeticFunction.vonMangoldt k - high n k : ℝ) : ℂ) *
            E ((k : ℝ) * t) := by
    dsimp only [S]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← sub_mul, ← Complex.ofReal_sub]
  have hnorm :
      ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖ ≤
        ∑ k ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt k - high n k) := by
    rw [hdiff]
    calc
      ‖∑ k ∈ Finset.range (n + 1),
          ((ArithmeticFunction.vonMangoldt k - high n k : ℝ) : ℂ) *
            E ((k : ℝ) * t)‖
          ≤ ∑ k ∈ Finset.range (n + 1),
              ‖((ArithmeticFunction.vonMangoldt k - high n k : ℝ) : ℂ) *
                E ((k : ℝ) * t)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt k - high n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hcoeff_nonneg k), hphase, mul_one]
  have hcoeff_le : ∀ k : ℕ,
      ArithmeticFunction.vonMangoldt k - high n k ≤
        (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0) + low n k := by
    intro k
    rw [hcoeff k]
    by_cases hp : Nat.Prime k
    · simp [hp]
    · simp [hp, low, w]
  have hnonprime :
      (∑ k ∈ Finset.range (n + 1),
        (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0)) =
        Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp only [Nat.floor_natCast]
    rw [Finset.sum_filter]
    rw [Finset.sum_range_eq_add_Ico _ (Nat.zero_lt_succ n)]
    rw [show n.succ = n + 1 by omega]
    rw [Finset.Ico_add_one_right_eq_Icc]
    have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIcc]
    have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
      simp [ArithmeticFunction.vonMangoldt_apply]
    rw [hΛ0]
    simp
  have hnonprime_bound :
      (∑ k ∈ Finset.range (n + 1),
        (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0)) ≤
        2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    rw [hnonprime]
    exact Chebyshev.psi_sub_theta_le (x := (n : ℝ)) (by exact_mod_cast hn)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hw_nonneg : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    dsimp only [w]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · exact le_rfl
  have hlow_nonneg : ∀ k : ℕ, 0 ≤ low n k := by
    intro k
    dsimp only [low]
    split_ifs
    · exact hw_nonneg k
    · exact le_rfl
  have hlow_le_log : ∀ k ∈ Finset.range (n + 1),
      low n k ≤ Real.log (n : ℝ) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [low, w]
    split_ifs with h1 hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
    · exact hlog_nonneg
    · exact hlog_nonneg
  let s : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
  have hsum_low : (∑ k ∈ Finset.range (n + 1), low n k) = ∑ k ∈ s, low n k := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hks => ?_
    have hnot : ¬ (k ^ 3 ≤ n) := by
      intro hle
      exact hks (Finset.mem_filter.mpr ⟨hk, hle⟩)
    simp [low, hnot]
  have hs_sub : s ⊆ Finset.range (Nat.sqrt n + 1) := by
    intro k hk
    have hk3 : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
    have hk2 : k ^ 2 ≤ n := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkpow : k ^ 2 ≤ k ^ 3 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
          exact Nat.le_mul_of_pos_right (k ^ 2) hkpos
        exact hkpow.trans hk3
    have hksqrt : k ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa [pow_two] using hk2)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hksqrt)
  have hcard_nat : s.card ≤ Nat.sqrt n + 1 := by
    simpa [Finset.card_range] using Finset.card_le_card hs_sub
  have hcard : (s.card : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
    exact_mod_cast hcard_nat
  have hlow_sum_bound :
      (∑ k ∈ Finset.range (n + 1), low n k) ≤
        ((Nat.sqrt n : ℝ) + 1) * Real.log (n : ℝ) := by
    rw [hsum_low]
    calc
      (∑ k ∈ s, low n k) ≤ ∑ _k ∈ s, Real.log (n : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact hlow_le_log k (Finset.mem_filter.mp hk).1
      _ = (s.card : ℝ) * Real.log (n : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Nat.sqrt n : ℝ) + 1) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcard hlog_nonneg
  have hsqrt_nat : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    exact_mod_cast Nat.sqrt_le' n
  have hone_sqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    simpa using (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
  have hsqrt_factor : (Nat.sqrt n : ℝ) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by
    linarith
  have hlow_final :
      (∑ k ∈ Finset.range (n + 1), low n k) ≤
        2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    exact hlow_sum_bound.trans
      (mul_le_mul_of_nonneg_right hsqrt_factor hlog_nonneg)
  have hsum_split :
      (∑ k ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt k - high n k)) ≤
        (∑ k ∈ Finset.range (n + 1),
          (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0)) +
          ∑ k ∈ Finset.range (n + 1), low n k := by
    calc
      (∑ k ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt k - high n k)) ≤
          ∑ k ∈ Finset.range (n + 1),
            ((if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0) + low n k) := by
        exact Finset.sum_le_sum fun k hk => hcoeff_le k
      _ = (∑ k ∈ Finset.range (n + 1),
          (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0)) +
          ∑ k ∈ Finset.range (n + 1), low n k := by
        rw [Finset.sum_add_distrib]
  have htotal :
      (∑ k ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt k - high n k)) ≤
        4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    calc
      _ ≤ (∑ k ∈ Finset.range (n + 1),
          (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0)) +
          ∑ k ∈ Finset.range (n + 1), low n k := hsum_split
      _ ≤ (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) +
          (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) :=
        by exact add_le_add hnonprime_bound hlow_final
      _ = 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by ring
  simpa [d] using hnorm.trans htotal
