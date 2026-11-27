import Mathlib

open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux

open Finset MeasureTheory

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def poly (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k : ℂ) * phase ((k : ℝ) * t)

private theorem continuous_poly (n : ℕ) (a : ℕ → ℝ) : Continuous (poly n a) := by
  unfold poly phase
  fun_prop

private theorem parseval (n : ℕ) (a : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, ‖poly n a t‖ ^ 2) = ∑ k ∈ range (n + 1), a k ^ 2 := by
  have hstar_E : ∀ x : ℝ, star (phase x) =
      Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
    intro x
    dsimp only [phase]
    change (starRingEnd ℂ)
        (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hE_mul_star : ∀ (j k : ℕ) (t : ℝ),
      phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t)) =
      Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    intro j k t
    rw [hstar_E]
    dsimp only [phase]
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Int.cast_sub, Int.cast_natCast]
    ring
  have hint_exp : ∀ m : ℤ,
      intervalIntegral
          (fun t : ℝ => Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
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
          HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c)
            (Complex.exp (c * (t : ℂ))) t := by
        intro t _
        have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
          have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
          simpa using this
        have h2 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
            (Complex.exp (c * (t : ℂ)) * c) t := h1.cexp
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
          Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
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
    rw [show (a j : ℂ) * phase ((j : ℝ) * t) *
          ((a k : ℂ) * star (phase ((k : ℝ) * t))) =
        ((a j : ℂ) * (a k : ℂ)) *
          (phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t))) by ring]
    rw [hE_mul_star j k t]
  have hparseval_complex :
      ((intervalIntegral (fun t => ‖poly n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1), ((a k : ℂ) * (a k : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal]
    calc
      intervalIntegral (fun t => ((‖poly n a t‖ ^ 2 : ℝ) : ℂ))
          (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral
            (fun t => ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              ((a j : ℂ) * (a k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) *
                  (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
            (0 : ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_congr fun t _ => hpoint t
      _ = ∑ j ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ∑ k ∈ Finset.range (n + 1),
                ((a j : ℂ) * (a k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) *
                    (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine intervalIntegral.integral_finsetSum fun j _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ((a j : ℂ) * (a k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) *
                  (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine Finset.sum_congr rfl fun j _ => ?_
          refine intervalIntegral.integral_finsetSum fun k _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ((a j : ℂ) * (a k : ℂ)) *
              (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
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

noncomputable def masked (A : Set ℝ) (j : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, A.indicator (fun u => (poly n a u)^2 * phase (-j * u)) t

private theorem swap_masked (A : Set ℝ) (hA : MeasurableSet A) (j : ℝ) (n : ℕ)
    (a b : ℕ → ℝ) :
    ‖masked A j n a - masked A j n b‖ ≤
      Real.sqrt (∑ k ∈ Finset.range (n + 1), (a k - b k)^2) *
        Real.sqrt (∑ k ∈ Finset.range (n + 1), (a k + b k)^2) := by
  classical
  let d := fun k => a k - b k
  let s := fun k => a k + b k
  have hd (t : ℝ) : poly n d t = poly n a t - poly n b t := by
    simp [poly, d, sub_mul, sum_sub_distrib]
  have hs (t : ℝ) : poly n s t = poly n a t + poly n b t := by
    simp [poly, s, add_mul, sum_add_distrib]
  have cont (c : ℕ → ℝ) :
      Continuous (fun t => (poly n c t)^2 * phase (-j * t)) := by
    have hp := continuous_poly n c
    unfold phase
    fun_prop
  have integ (c : ℕ → ℝ) :
      IntervalIntegrable (A.indicator (fun t => (poly n c t)^2 * phase (-j * t)))
        volume 0 1 := by
    have hi := (cont c).intervalIntegrable (μ := volume) 0 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi ⊢
    exact hi.indicator hA
  have norm_bound :
      ‖masked A j n a - masked A j n b‖ ≤
        ∫ t in (0 : ℝ)..1, ‖poly n d t‖ * ‖poly n s t‖ := by
    unfold masked
    rw [← intervalIntegral.integral_sub (integ a) (integ b)]
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_
      (((continuous_poly n d).norm.mul (continuous_poly n s).norm).intervalIntegrable 0 1)
    filter_upwards with t _
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht]
      rw [show (poly n a t)^2 * phase (-j * t) - (poly n b t)^2 * phase (-j * t) =
          (poly n d t * poly n s t) * phase (-j * t) by rw [hd, hs]; ring]
      simp only [norm_mul, phase, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
    · simp [Set.indicator_of_notMem ht, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  have bound := norm_bound.trans (cauchy_on_unit (continuous_poly n d) (continuous_poly n s))
  simpa only [parseval, d, s] using bound

noncomputable def weight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def high (m k : ℕ) : ℝ := if k ≤ m then 0 else weight k

private theorem weight_nonneg (k : ℕ) : 0 ≤ weight k := by
  unfold weight
  split <;> positivity

private theorem high_nonneg (m k : ℕ) : 0 ≤ high m k := by
  unfold high
  by_cases h : k ≤ m
  · simp [h]
  · simp [h, weight_nonneg]

private theorem high_le_weight (m k : ℕ) : high m k ≤ weight k := by
  unfold high
  split <;> simp [weight_nonneg]

private theorem theta_eq_weight_sum (r : ℕ) :
    Chebyshev.theta r = ∑ k ∈ Finset.range (r + 1), weight k := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rfl

private theorem weight_sum_le (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), weight k) ≤ Real.log 4 * (r : ℝ) := by
  rw [← theta_eq_weight_sum]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg r)

private theorem weight_le_log_of_mem {k n : ℕ} (hn : 2 ≤ n)
    (hk : k ∈ Finset.range (n + 1)) : weight k ≤ Real.log (n : ℝ) := by
  unfold weight
  split_ifs with hp
  · apply Real.log_le_log (by exact_mod_cast hp.pos)
    have : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    exact_mod_cast this
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

private theorem diff_term (m k : ℕ) :
    weight k - high m k = if k ≤ m then weight k else 0 := by
  unfold high
  by_cases h : k ≤ m
  · simp [h]
  · simp [h]

private theorem diff_mass_le_theta (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (weight k - high m k)) ≤ Chebyshev.theta m := by
  classical
  have hsplit :
      (∑ k ∈ Finset.range (n + 1), (weight k - high m k)) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ m), weight k := by
    simp_rw [diff_term m]
    rw [Finset.sum_filter]
  have hsubset :
      (Finset.range (n + 1)).filter (fun k => k ≤ m) ⊆ Finset.range (m + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  calc
    (∑ k ∈ Finset.range (n + 1), (weight k - high m k)) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k ≤ m), weight k := hsplit
    _ ≤ ∑ k ∈ Finset.range (m + 1), weight k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => weight_nonneg _)
    _ = Chebyshev.theta m := (theta_eq_weight_sum m).symm

private theorem diff_energy_le (n m : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (weight k - high m k)^2) ≤
      Real.log 4 * Real.log (n : ℝ) * (m : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (weight k - high m k)^2 ≤ Real.log (n : ℝ) * (weight k - high m k) := by
    intro k hk
    have hlow : 0 ≤ weight k - high m k := sub_nonneg.mpr (high_le_weight m k)
    have hle : weight k - high m k ≤ weight k := by
      exact sub_le_self _ (high_nonneg m k)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hle.trans (weight_le_log_of_mem hn hk)) hlow
  calc
    (∑ k ∈ Finset.range (n + 1), (weight k - high m k)^2) ≤
        ∑ k ∈ Finset.range (n + 1), Real.log (n : ℝ) * (weight k - high m k) :=
      Finset.sum_le_sum hterm
    _ = Real.log (n : ℝ) * (∑ k ∈ Finset.range (n + 1), (weight k - high m k)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log (n : ℝ) * (Real.log 4 * (m : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ hlog
      exact (diff_mass_le_theta n m).trans
        (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg m))
    _ = Real.log 4 * Real.log (n : ℝ) * (m : ℝ) := by ring

private theorem weight_energy_le (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (weight k)^2) ≤
      Real.log 4 * Real.log (n : ℝ) * (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  calc
    (∑ k ∈ Finset.range (n + 1), (weight k)^2) ≤
        ∑ k ∈ Finset.range (n + 1), Real.log (n : ℝ) * weight k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [sq]
      exact mul_le_mul_of_nonneg_right (weight_le_log_of_mem hn hk) (weight_nonneg k)
    _ = Real.log (n : ℝ) * (∑ k ∈ Finset.range (n + 1), weight k) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log (n : ℝ) * (Real.log 4 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (weight_sum_le n) hlog
    _ = Real.log 4 * Real.log (n : ℝ) * (n : ℝ) := by ring

private theorem sum_energy_le (n m : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (weight k + high m k)^2) ≤
      4 * (Real.log 4 * Real.log (n : ℝ) * (n : ℝ)) := by
  calc
    (∑ k ∈ Finset.range (n + 1), (weight k + high m k)^2) ≤
        ∑ k ∈ Finset.range (n + 1), 4 * (weight k)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hwh : weight k + high m k ≤ 2 * weight k := by
        linarith [high_le_weight m k]
      have hnonneg : 0 ≤ weight k + high m k := by
        linarith [weight_nonneg k, high_nonneg m k]
      calc
        (weight k + high m k)^2 ≤ (2 * weight k)^2 := pow_le_pow_left₀ hnonneg hwh 2
        _ = 4 * (weight k)^2 := by ring
    _ = 4 * (∑ k ∈ Finset.range (n + 1), (weight k)^2) := by rw [Finset.mul_sum]
    _ ≤ 4 * (Real.log 4 * Real.log (n : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (weight_energy_le n hn) (by norm_num)

private theorem sqrt_energy_product (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b * c) * Real.sqrt (4 * (a * b * d)) =
      2 * a * b * Real.sqrt (c * d) := by
  have hleft : Real.sqrt (a * b * c) = Real.sqrt a * Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul ha]
  have hright : Real.sqrt (4 * (a * b * d)) =
      2 * (Real.sqrt a * Real.sqrt b * Real.sqrt d) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul ha]
    norm_num
  have habsq : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
    rw [← Real.sqrt_mul ha]
    exact Real.sq_sqrt (mul_nonneg ha hb)
  rw [hleft, hright]
  calc
    (Real.sqrt a * Real.sqrt b * Real.sqrt c) *
          (2 * (Real.sqrt a * Real.sqrt b * Real.sqrt d)) =
        2 * (Real.sqrt a * Real.sqrt b) ^ 2 * (Real.sqrt c * Real.sqrt d) := by ring
    _ = 2 * a * b * Real.sqrt (c * d) := by rw [habsq, Real.sqrt_mul hc]; ring

theorem main_bound (n m : ℕ) (hn : 2 ≤ n) (_hmn : m ≤ n) (A : Set ℝ) (hA : MeasurableSet A)
    (j : ℝ) :
    ‖masked A j n weight - masked A j n (high m)‖ ≤
      2 * Real.log 4 * Real.log (n : ℝ) * Real.sqrt ((m : ℝ) * n) := by
  classical
  have hdiff := diff_energy_le n m hn
  have hsum := sum_energy_le n m hn
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmain := swap_masked A hA j n weight (high m)
  refine hmain.trans ?_
  refine le_trans (mul_le_mul (Real.sqrt_le_sqrt hdiff) (Real.sqrt_le_sqrt hsum)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
  rw [sqrt_energy_product (Real.log 4) (Real.log (n : ℝ)) (m : ℝ) (n : ℝ)
    hlog4 hlog hm hnR]

end Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux

theorem Conjectures.Goldbach.MaskedPrimeCutoffLoss : let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let high := fun m k : ℕ => if k ≤ m then 0 else w k; let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S := fun (n : ℕ) (a : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (a k : ℂ) * E ((k : ℝ) * t)); let I := fun (A : Set ℝ) (j : ℝ) (n : ℕ) (a : ℕ → ℝ) => intervalIntegral (A.indicator (fun t => (S n a t)^2 * E (-j * t))) (0 : ℝ) 1 MeasureTheory.volume; ∀ n m : ℕ, 2 ≤ n → m ≤ n → ∀ A : Set ℝ, MeasurableSet A → ∀ j : ℝ, ‖I A j n w - I A j n (high m)‖ ≤ 2 * Real.log 4 * Real.log (n : ℝ) * Real.sqrt ((m : ℝ) * n) := by
  intro w high E S I n m hn hmn A hA j
  change ‖Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux.masked A j n
      Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux.weight -
    Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux.masked A j n
      (Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux.high m)‖ ≤ _
  exact Conjectures.Goldbach.MaskedPrimeCutoffLoss_aux.main_bound n m hn hmn A hA j
