import Mathlib

open Finset MeasureTheory
open scoped BigOperators

namespace Conjectures.Goldbach.VaughanSignedBudget_aux

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def poly (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k : ℂ) * phase ((k : ℝ) * t)

private theorem continuous_poly (n : ℕ) (a : ℕ → ℝ) : Continuous (poly n a) := by
  unfold poly phase
  fun_prop

private theorem parseval (n : ℕ) (a : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, ‖poly n a t‖ ^ 2) = ∑ k ∈ range (n + 1), a k ^ 2 := by
  have hstar_E : ∀ x : ℝ, star (phase x) = Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
    intro x
    dsimp only [phase]
    change (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hE_mul_star : ∀ (j k : ℕ) (t : ℝ),
      phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t)) =
      Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    intro j k t
    rw [hstar_E]
    dsimp only [phase]
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Int.cast_sub, Int.cast_natCast]
    ring
  have hint_exp : ∀ m : ℤ,
      intervalIntegral (fun t : ℝ => Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
        (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · simp only [hm, ↓reduceIte]
      set c : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      have hc : c ≠ 0 := by
        dsimp only [c]
        have hm0 : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
        have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_ne_zero hm0 (mul_ne_zero (mul_ne_zero two_ne_zero hpi0) Complex.I_ne_zero)
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c) (Complex.exp (c * (t : ℂ))) t := by
        intro t _
        have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
          have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
          simpa using this
        have h2 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ))) (Complex.exp (c * (t : ℂ)) * c) t :=
          h1.cexp
        have h3 := h2.div_const c
        simpa [mul_div_cancel_right₀ _ hc] using h3
      have hcont : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
      have hexp1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
        rw [Complex.ofReal_one, mul_one]
        exact Complex.exp_int_mul_two_pi_mul_I m
      have hexp0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
        rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [hexp1, hexp0, sub_self]
  have hpoint : ∀ t : ℝ,
      ((‖poly n a t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((a j : ℂ) * (a k : ℂ)) *
          Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    intro t
    have hns : ((‖poly n a t‖ ^ 2 : ℝ) : ℂ) = poly n a t * star (poly n a t) := by
      have := Complex.mul_conj (poly n a t)
      rw [Complex.normSq_eq_norm_sq] at this
      exact this.symm
    rw [hns]
    dsimp only [poly]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
    rw [show (a j : ℂ) * phase ((j : ℝ) * t) * ((a k : ℂ) * star (phase ((k : ℝ) * t))) =
      ((a j : ℂ) * (a k : ℂ)) * (phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t))) by ring]
    rw [hE_mul_star j k t]
  have hparseval_complex :
      ((intervalIntegral (fun t => ‖poly n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1), ((a k : ℂ) * (a k : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal]
    calc
      intervalIntegral (fun t => ((‖poly n a t‖ ^ 2 : ℝ) : ℂ)) (0 : ℝ) 1 MeasureTheory.volume
        = intervalIntegral
            (fun t => ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              ((a j : ℂ) * (a k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
            (0 : ℝ) 1 MeasureTheory.volume := intervalIntegral.integral_congr fun t _ => hpoint t
      _ = ∑ j ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ∑ k ∈ Finset.range (n + 1),
                ((a j : ℂ) * (a k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine intervalIntegral.integral_finsetSum fun j _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ((a j : ℂ) * (a k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine Finset.sum_congr rfl fun j _ => ?_
          refine intervalIntegral.integral_finsetSum fun k _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ((a j : ℂ) * (a k : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [intervalIntegral.integral_const_mul, hint_exp ((j : ℤ) - (k : ℤ))]
      _ = ∑ j ∈ Finset.range (n + 1), ((a j : ℂ) * (a j : ℂ)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_eq_single j]
          · simp
          · intro k _ hkj
            have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
            simp [hne]
          · intro hj'
            exact (hj' hj).elim
  have hparseval :
      intervalIntegral (fun t => ‖poly n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
      ∑ k ∈ Finset.range (n + 1), (a k) ^ 2 := by
    have hre := congrArg Complex.re hparseval_complex
    rw [Complex.ofReal_re] at hre
    rw [hre, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
  exact hparseval

private theorem cauchy_on_unit {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, ‖f t‖ * ‖g t‖) ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2) := by
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hmem {v : ℝ → ℂ} (hv : Continuous v) : MemLp v (ENNReal.ofReal 2) μ := by
    have hs : Integrable (fun x => ‖v x‖ ^ 2) μ :=
      ((hv.norm.pow 2).intervalIntegrable 0 1).1
    simpa using (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).2 hs
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (hmem hf) (hmem hg)
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two, μ] using h

noncomputable def pair (A : Set ℝ) (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, A.indicator
    (fun t => poly n a t * poly n b t * phase (-j * t)) t

private theorem continuous_pair_integrand (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    Continuous (fun t => poly n a t * poly n b t * phase (-j * t)) := by
  have hp := (continuous_poly n a).mul (continuous_poly n b)
  have hphase : Continuous (fun t : ℝ => phase (-j * t)) := by
    unfold phase
    fun_prop
  exact hp.mul hphase

private theorem intervalIntegrable_pair (A : Set ℝ) (hA : MeasurableSet A)
    (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    IntervalIntegrable (A.indicator
      (fun t => poly n a t * poly n b t * phase (-j * t))) volume 0 1 := by
  have hi := (continuous_pair_integrand j n a b).intervalIntegrable (μ := volume) 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi ⊢
  exact hi.indicator hA

private theorem poly_add (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    poly n (a + b) t = poly n a t + poly n b t := by
  simp [poly, add_mul, Finset.sum_add_distrib]

private theorem poly_sub (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    poly n (a - b) t = poly n a t - poly n b t := by
  simp [poly, sub_mul, Finset.sum_sub_distrib]

private theorem pair_norm_le (A : Set ℝ) (hA : MeasurableSet A)
    (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    ‖pair A j n a b‖ ≤
      Real.sqrt (∑ k ∈ range (n + 1), a k ^ 2) *
        Real.sqrt (∑ k ∈ range (n + 1), b k ^ 2) := by
  have hnorm :
      ‖pair A j n a b‖ ≤ ∫ t in (0 : ℝ)..1, ‖poly n a t‖ * ‖poly n b t‖ := by
    unfold pair
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_
      (((continuous_poly n a).norm.mul (continuous_poly n b).norm).intervalIntegrable 0 1)
    filter_upwards with t _
    change ‖A.indicator (fun t => poly n a t * poly n b t * phase (-j * t)) t‖ ≤
      ‖poly n a t‖ * ‖poly n b t‖
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht, norm_mul, phase,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      rfl
    · simp [Set.indicator_of_notMem ht, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖poly n a t‖ * ‖poly n b t‖ := hnorm
    _ ≤ Real.sqrt (∫ t in (0 : ℝ)..1, ‖poly n a t‖ ^ 2) *
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖poly n b t‖ ^ 2) :=
      cauchy_on_unit (continuous_poly n a) (continuous_poly n b)
    _ = _ := by rw [parseval, parseval]

private theorem pair_add_left (A : Set ℝ) (hA : MeasurableSet A)
    (j : ℝ) (n : ℕ) (a b c : ℕ → ℝ) :
    pair A j n (a + b) c = pair A j n a c + pair A j n b c := by
  unfold pair
  symm
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_pair A hA j n a c)
    (intervalIntegrable_pair A hA j n b c)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ A
  · simp only [Set.indicator_of_mem ht, poly_add]
    ring
  · simp [Set.indicator_of_notMem ht]

private theorem pair_square_sub (A : Set ℝ) (hA : MeasurableSet A)
    (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    pair A j n a a - pair A j n b b = pair A j n (a - b) (a + b) := by
  unfold pair
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_pair A hA j n a a)
    (intervalIntegrable_pair A hA j n b b)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ A
  · simp only [Set.indicator_of_mem ht, poly_sub, poly_add]
    ring
  · simp [Set.indicator_of_notMem ht]

noncomputable def weight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def cutoff (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

noncomputable def truncatedMangoldt (H : ℕ) (k : ℕ) : ℝ :=
  if k ≤ H then ArithmeticFunction.vonMangoldt k else 0

private theorem weight_nonneg (k : ℕ) : 0 ≤ weight k := by
  unfold weight
  split <;> positivity

private theorem weight_le_mangoldt (k : ℕ) : weight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hp : k.Prime
  · simp [weight, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [weight, hp]

private theorem mangoldt_le_log_of_mem {k n : ℕ} (hk : k ∈ Finset.range (n+1)) :
    ArithmeticFunction.vonMangoldt k ≤ Real.log n := by
  refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
  by_cases hk0 : k = 0
  · simpa [hk0] using Real.log_natCast_nonneg n
  · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0)
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)

private theorem swap_diff_energy (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - weight k)^2)
      ≤ 2 * Real.sqrt n * (Real.log n)^2 := by
  let R (k : ℕ) := ArithmeticFunction.vonMangoldt k - weight k
  have htotal : (∑ k ∈ Finset.range (n+1), R k) = Chebyshev.psi n - Chebyshev.theta n := by
    simp only [R, weight, Finset.sum_sub_distrib, Chebyshev.psi_eq_sum_Icc,
      Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    (∑ k ∈ Finset.range (n+1), (R k)^2) ≤ ∑ k ∈ Finset.range (n+1), R k * Real.log n := by
      apply Finset.sum_le_sum
      intro k hk
      rw [sq]
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (weight_le_mangoldt k))
      exact (sub_le_self _ (weight_nonneg k)).trans (mangoldt_le_log_of_mem hk)
    _ = (Chebyshev.psi n - Chebyshev.theta n) * Real.log n := by rw [← Finset.sum_mul, htotal]
    _ ≤ (2 * Real.sqrt n * Real.log n) * Real.log n :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le hn') (Real.log_natCast_nonneg n)
    _ = _ := by ring

private theorem swap_sum_energy (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k + weight k)^2)
      ≤ 8 * (n : ℝ) * (Real.log n)^2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    _ ≤ ∑ _k ∈ Finset.range (n+1), (2 * Real.log n)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply pow_le_pow_left₀ (add_nonneg ArithmeticFunction.vonMangoldt_nonneg (weight_nonneg k))
      linarith [weight_le_mangoldt k, mangoldt_le_log_of_mem hk]
    _ = ((n:ℝ)+1) * (2 * Real.log n)^2 := by simp
    _ ≤ (2 * (n:ℝ)) * (2 * Real.log n)^2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by ring

private theorem truncated_energy (n H : ℕ) (hH : H ≤ n) (hn : 2 ≤ n) :
    (∑ k ∈ range (n + 1), truncatedMangoldt H k ^ 2) ≤
      (H + 1 : ℕ) * (Real.log n)^2 := by
  have hsubset : range (H + 1) ⊆ range (n + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hsum :
      (∑ k ∈ range (n + 1), truncatedMangoldt H k ^ 2) =
        ∑ k ∈ range (H + 1), truncatedMangoldt H k ^ 2 := by
    symm
    exact Finset.sum_subset hsubset fun k hk hkH => by
      have hnot : ¬ k ≤ H := by
        simpa [Finset.mem_range] using hkH
      simp [truncatedMangoldt, hnot]
  rw [hsum]
  calc
    _ ≤ ∑ _k ∈ range (H + 1), (Real.log n)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ∈ range (n + 1) := hsubset hk
      have hΛ := mangoldt_le_log_of_mem hkn
      by_cases hkH : k ≤ H
      · simp only [truncatedMangoldt, hkH, ↓reduceIte]
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := k), Real.log_natCast_nonneg n]
      · rw [truncatedMangoldt]
        simp only [hkH, ↓reduceIte, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact sq_nonneg _
    _ = _ := by simp

private theorem mangoldt_energy (n : ℕ) :
    (∑ k ∈ range (n + 1), ArithmeticFunction.vonMangoldt k ^ 2) ≤
      (n + 1 : ℕ) * (Real.log n)^2 := by
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (Real.log n)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hΛ := mangoldt_le_log_of_mem hk
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := k), Real.log_natCast_nonneg n]
    _ = _ := by simp

private theorem cutoff_energy (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ range (n + 1), truncatedMangoldt (cutoff n) k ^ 2) ≤
      2 * Real.sqrt n * (Real.log n)^2 := by
  have hcut : cutoff n ≤ n := by
    exact (Nat.sqrt_le_self (Nat.sqrt n)).trans (Nat.sqrt_le_self n)
  have hreal : (cutoff n : ℝ) ≤ Real.sqrt n := by
    calc
      (cutoff n : ℝ) ≤ (Nat.sqrt n : ℝ) := by
        exact_mod_cast Nat.sqrt_le_self (Nat.sqrt n)
      _ ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  calc
    _ ≤ (cutoff n + 1 : ℕ) * (Real.log n)^2 :=
      truncated_energy n (cutoff n) hcut hn
    _ ≤ (2 * Real.sqrt n) * (Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right
      · calc
          ((cutoff n + 1 : ℕ) : ℝ) = (cutoff n : ℝ) + 1 := by norm_num
          _ ≤ 2 * Real.sqrt n := by linarith
      · positivity
    _ = _ := by ring

private theorem full_energy (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ range (n + 1), ArithmeticFunction.vonMangoldt k ^ 2) ≤
      2 * (n : ℝ) * (Real.log n)^2 := by
  calc
    _ ≤ (n + 1 : ℕ) * (Real.log n)^2 := mangoldt_energy n
    _ ≤ (2 * (n : ℝ)) * (Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show n + 1 ≤ 2 * n by omega)
      · positivity
    _ = _ := by ring

private theorem short_pair_bound (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) (hn : 2 ≤ n) :
    ‖pair A (n : ℝ) n (truncatedMangoldt (cutoff n)) ArithmeticFunction.vonMangoldt‖ ≤
      Real.sqrt (2 * Real.sqrt n * (Real.log n)^2) *
        Real.sqrt (2 * (n : ℝ) * (Real.log n)^2) := by
  refine (pair_norm_le A hA (n : ℝ) n
    (truncatedMangoldt (cutoff n)) ArithmeticFunction.vonMangoldt).trans ?_
  exact mul_le_mul
    (Real.sqrt_le_sqrt (cutoff_energy n hn))
    (Real.sqrt_le_sqrt (full_energy n hn))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem transfer_pair_bound (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) (hn : 2 ≤ n) :
    ‖pair A (n : ℝ) n ArithmeticFunction.vonMangoldt ArithmeticFunction.vonMangoldt -
      pair A (n : ℝ) n weight weight‖ ≤
      Real.sqrt (2 * Real.sqrt n * (Real.log n)^2) *
        Real.sqrt (8 * (n : ℝ) * (Real.log n)^2) := by
  rw [pair_square_sub A hA]
  refine (pair_norm_le A hA (n : ℝ) n
    (ArithmeticFunction.vonMangoldt - weight)
    (ArithmeticFunction.vonMangoldt + weight)).trans ?_
  exact mul_le_mul
    (Real.sqrt_le_sqrt (swap_diff_energy n hn))
    (Real.sqrt_le_sqrt (swap_sum_energy n hn))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

open Filter in
private theorem transfer_eventually : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    2 ≤ n ∧ Real.sqrt (2 * Real.sqrt (n : ℝ) * (Real.log n)^2) *
      Real.sqrt (8 * (n : ℝ) * (Real.log n)^2) ≤ e * (n : ℝ) := by
  intro e he
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1/4 by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply eventually_atTop.mp
  filter_upwards [hl.bound (show 0 < e/4 by positivity), eventually_ge_atTop (2 : ℕ)] with n hlog hn
  refine ⟨hn, ?_⟩
  let y := (n : ℝ) ^ (1/4 : ℝ)
  have hy : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 : y^2 = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  have h4 : y^4 = (n : ℝ) := by
    calc
      y^4 = (y^2)^2 := by ring
      _ = (n : ℝ) := by rw [h2, Real.sq_sqrt (Nat.cast_nonneg n)]
  change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ e/4 * ‖y‖ at hlog
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hy] at hlog
  calc
    _ = 4*y^3*(Real.log n)^2 := by
      rw [← Real.sqrt_mul (by positivity), Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
      calc
        _ = (2*y^2*(Real.log n)^2)*(8*y^4*(Real.log n)^2) := by rw [h2,h4]
        _ = _ := by ring
    _ ≤ 4*y^3*(e/4*y) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = e*n := by rw [← h4]; ring

open Filter in
private theorem short_eventually : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    2 ≤ n ∧ Real.sqrt (2 * Real.sqrt (n : ℝ) * (Real.log n)^2) *
      Real.sqrt (2 * (n : ℝ) * (Real.log n)^2) ≤ e * (n : ℝ) := by
  intro e he
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1/4 by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply eventually_atTop.mp
  filter_upwards [hl.bound (show 0 < e/2 by positivity), eventually_ge_atTop (2 : ℕ)] with n hlog hn
  refine ⟨hn, ?_⟩
  let y := (n : ℝ) ^ (1/4 : ℝ)
  have hy : 0 ≤ y := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 : y^2 = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  have h4 : y^4 = (n : ℝ) := by
    calc
      y^4 = (y^2)^2 := by ring
      _ = (n : ℝ) := by rw [h2, Real.sq_sqrt (Nat.cast_nonneg n)]
  change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ e/2 * ‖y‖ at hlog
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hy] at hlog
  calc
    _ = 2*y^3*(Real.log n)^2 := by
      rw [← Real.sqrt_mul (by positivity), Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
      calc
        _ = (2*y^2*(Real.log n)^2)*(2*y^4*(Real.log n)^2) := by rw [h2,h4]
        _ = _ := by ring
    _ ≤ 2*y^3*(e/2*y) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = e*n := by rw [← h4]; ring

end Conjectures.Goldbach.VaughanSignedBudget_aux

theorem Conjectures.Goldbach.VaughanSignedBudget :
    let cut (h : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun k => if k ≤ h then f k else 0, (ite_eq_left (Nat.zero_le h)).trans f.map_zero⟩; let L := ArithmeticFunction.vonMangoldt; let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius; let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta; let h (n : ℕ) := Nat.sqrt (Nat.sqrt n); let a (n : ℕ) := cut (h n) m; let b (n : ℕ) := cut (h n) L; let I (n : ℕ) := a n * ArithmeticFunction.log - a n * b n * z; let J (n : ℕ) := (m-a n) * ((L-b n) * z); let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ)*t); let Q (n : ℕ) := (Nat.log 2 (n+2))^2; let A (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let B (n : ℕ) (u v : ℕ → ℝ) := (intervalIntegral ((A n)ᶜ.indicator (fun t => S n u t * S n v t * E (-(n : ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume).re; let lower (F : ℕ → ℝ) := ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, Even n → -(e*(n:ℝ)) ≤ F n; lower (fun n => B n (I n) L) → lower (fun n => B n (J n) L) → lower (fun n => B n w w) := by
  classical
  intro cut L m z h a b I J w E S Q A B lower hI hJ
  have hA_measurable (n : ℕ) : MeasurableSet (A n) := by
    let piece (q r : ℕ) := {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ r ≤ q ∧ Nat.Coprime r q ∧
      |t - (r : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
    have cover : A n = ⋃ q : ℕ, ⋃ r : ℕ, piece q r := by
      ext t
      simp only [Set.mem_iUnion] <;> rfl
    rw [cover]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro r
    by_cases hc : 1 ≤ q ∧ q ≤ Q n ∧ r ≤ q ∧ Nat.Coprime r q
    · obtain ⟨hq, hQ, hr, hcop⟩ := hc
      have sublevel : piece q r = {t : ℝ |
          |t - (r : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
        ext t
        exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨hq, hQ, hr, hcop, ht⟩⟩
      rw [sublevel]
      have hdist : Continuous (fun t : ℝ => |t - (r : ℝ) / (q : ℝ)|) :=
        (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => (r : ℝ) / (q : ℝ)))).abs
      exact (isClosed_le hdist
        (continuous_const : Continuous
          (fun _ : ℝ => (Q n : ℝ) / ((q : ℝ) * (n : ℝ))))).measurableSet
    · have empty : piece q r = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro t ⟨hq, hQ, hr, hcop, _⟩
        exact hc ⟨hq, hQ, hr, hcop⟩
      rw [empty]
      exact MeasurableSet.empty
  have hA_compl (n : ℕ) : MeasurableSet (A n)ᶜ := (hA_measurable n).compl
  have hB_pair (n : ℕ) (u v : ℕ → ℝ) :
      B n u v =
        (Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n u v).re := by
    rfl
  have hB_add (n : ℕ) (u v c : ℕ → ℝ) :
      B n (u + v) c = B n u c + B n v c := by
    calc
      B n (u + v) c =
          (Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n (u + v) c).re :=
        hB_pair n (u + v) c
      _ = (Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n u c +
          Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n v c).re := by
        congr 1
        exact Conjectures.Goldbach.VaughanSignedBudget_aux.pair_add_left
          (A n)ᶜ (hA_compl n) (n : ℝ) n u v c
      _ = B n u c + B n v c := by
        rw [Complex.add_re, hB_pair, hB_pair]
  have hvaughan (n : ℕ) :
      L = b n + (a n * ArithmeticFunction.log - a n * b n * z) +
        (m - a n) * ((L - b n) * z) := by
    have h1 : m * z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
    have h2 : L * z = ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
    linear_combination (b n - L) * h1 + a n * h2
  have hsplit (n : ℕ) : (L : ℕ → ℝ) = b n + I n + J n := by
    funext k
    have hk := congrArg (fun f : ArithmeticFunction ℝ => f k) (hvaughan n)
    simpa only [I, J, ArithmeticFunction.add_apply, Pi.add_apply] using hk
  have hdecomp (n : ℕ) :
      B n L L = B n (b n) L + B n (I n) L + B n (J n) L := by
    calc
      B n L L = B n (b n + I n + J n) L := by rw [hsplit n]
      _ = B n (b n + I n) L + B n (J n) L := hB_add n (b n + I n) (J n) L
      _ = B n (b n) L + B n (I n) L + B n (J n) L := by rw [hB_add]
  intro e he
  obtain ⟨NI, hNI⟩ := hI (e / 4) (by positivity)
  obtain ⟨NJ, hNJ⟩ := hJ (e / 4) (by positivity)
  obtain ⟨NS, hNS⟩ := Conjectures.Goldbach.VaughanSignedBudget_aux.short_eventually
    (e / 4) (by positivity)
  obtain ⟨NT, hNT⟩ := Conjectures.Goldbach.VaughanSignedBudget_aux.transfer_eventually
    (e / 4) (by positivity)
  refine ⟨max (max NI NJ) (max NS NT), ?_⟩
  intro n hn hEven
  have hnI : NI ≤ n :=
    (le_max_left NI NJ).trans ((le_max_left (max NI NJ) (max NS NT)).trans hn)
  have hnJ : NJ ≤ n :=
    (le_max_right NI NJ).trans ((le_max_left (max NI NJ) (max NS NT)).trans hn)
  have hnS : NS ≤ n :=
    (le_max_left NS NT).trans ((le_max_right (max NI NJ) (max NS NT)).trans hn)
  have hnT : NT ≤ n :=
    (le_max_right NS NT).trans ((le_max_right (max NI NJ) (max NS NT)).trans hn)
  have hIb := hNI n hnI hEven
  have hJb := hNJ n hnJ hEven
  have hS := hNS n hnS
  have hT := hNT n hnT
  have hb (k : ℕ) :
      b n k = Conjectures.Goldbach.VaughanSignedBudget_aux.truncatedMangoldt
        (Conjectures.Goldbach.VaughanSignedBudget_aux.cutoff n) k := by
    rfl
  have hbfun : (b n : ℕ → ℝ) =
      Conjectures.Goldbach.VaughanSignedBudget_aux.truncatedMangoldt
        (Conjectures.Goldbach.VaughanSignedBudget_aux.cutoff n) := by
    funext k
    exact hb k
  have hLfun : (L : ℕ → ℝ) = ArithmeticFunction.vonMangoldt := by
    rfl
  have hshort_complex :
      ‖Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n (b n) L‖ ≤
        (e / 4) * (n : ℝ) := by
    have hbound := Conjectures.Goldbach.VaughanSignedBudget_aux.short_pair_bound
      (A n)ᶜ (hA_compl n) n hS.1
    calc
      _ = ‖Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n
          (Conjectures.Goldbach.VaughanSignedBudget_aux.truncatedMangoldt
            (Conjectures.Goldbach.VaughanSignedBudget_aux.cutoff n))
          ArithmeticFunction.vonMangoldt‖ := by rw [hbfun, hLfun]
      _ ≤ _ := hbound.trans hS.2
  have hshort : -(e / 4) * (n : ℝ) ≤ B n (b n) L := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hshort_complex)).1
    rw [hB_pair]
    simpa only [neg_mul] using hre
  have hw (k : ℕ) :
      w k = Conjectures.Goldbach.VaughanSignedBudget_aux.weight k := by
    rfl
  have hwfun : w = Conjectures.Goldbach.VaughanSignedBudget_aux.weight := by
    funext k
    exact hw k
  have htransfer_complex :
      ‖Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n L L -
        Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n w w‖ ≤
        (e / 4) * (n : ℝ) := by
    have hbound := Conjectures.Goldbach.VaughanSignedBudget_aux.transfer_pair_bound
      (A n)ᶜ (hA_compl n) n hT.1
    calc
      _ = ‖Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n
          ArithmeticFunction.vonMangoldt ArithmeticFunction.vonMangoldt -
          Conjectures.Goldbach.VaughanSignedBudget_aux.pair (A n)ᶜ (n : ℝ) n
            Conjectures.Goldbach.VaughanSignedBudget_aux.weight
            Conjectures.Goldbach.VaughanSignedBudget_aux.weight‖ := by rw [hLfun, hwfun]
      _ ≤ _ := hbound.trans hT.2
  have htransfer : B n L L - B n w w ≤ (e / 4) * (n : ℝ) := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans htransfer_complex)).2
    rw [hB_pair, hB_pair]
    simpa only [Complex.sub_re] using hre
  have hIb' : -(e / 4) * (n : ℝ) ≤ B n (I n) L := by
    simpa only [neg_mul] using hIb
  have hJb' : -(e / 4) * (n : ℝ) ≤ B n (J n) L := by
    simpa only [neg_mul] using hJb
  change -(e * (n : ℝ)) ≤ B n w w
  have hsum : -(3 : ℝ) * ((e / 4) * (n : ℝ)) ≤
      B n (b n) L + B n (I n) L + B n (J n) L := by
    linarith [hshort, hIb', hJb']
  have hLL : -(3 : ℝ) * ((e / 4) * (n : ℝ)) ≤ B n L L := by
    rw [hdecomp n]
    exact hsum
  have hww : -(4 : ℝ) * ((e / 4) * (n : ℝ)) ≤ B n w w := by
    calc
      -(4 : ℝ) * ((e / 4) * (n : ℝ)) =
          (-(3 : ℝ) * ((e / 4) * (n : ℝ))) - ((e / 4) * (n : ℝ)) := by ring
      _ ≤ B n L L - ((e / 4) * (n : ℝ)) := sub_le_sub_right hLL _
      _ ≤ B n w w := by linarith [htransfer]
  calc
    -(e * (n : ℝ)) = -(4 : ℝ) * ((e / 4) * (n : ℝ)) := by ring
    _ ≤ B n w w := hww
