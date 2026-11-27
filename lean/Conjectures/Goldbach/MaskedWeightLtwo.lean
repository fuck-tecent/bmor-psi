import Mathlib

namespace Conjectures.Goldbach.MaskedWeightLtwo_aux

open Finset MeasureTheory
open scoped BigOperators

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def poly (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k : ℂ) * phase ((k : ℝ) * t)

noncomputable def masked (A : Set ℝ) (j : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℂ :=
  intervalIntegral (A.indicator (fun t => (poly n a t) ^ 2 * phase (-j * t))) (0 : ℝ) 1
    MeasureTheory.volume

theorem continuous_poly (n : ℕ) (a : ℕ → ℝ) : Continuous (poly n a) := by
  unfold poly phase
  fun_prop

theorem parseval (n : ℕ) (a : ℕ → ℝ) :
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
          have hthis := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
          simpa using hthis
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
      have hthis := Complex.mul_conj (poly n a t)
      rw [Complex.normSq_eq_norm_sq] at hthis
      exact hthis.symm
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

theorem cauchy_on_unit {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
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

theorem swap_masked (A : Set ℝ) (hA : MeasurableSet A) (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    ‖masked A j n a - masked A j n b‖ ≤
      Real.sqrt (∑ k ∈ Finset.range (n + 1), (a k - b k) ^ 2) *
        Real.sqrt (∑ k ∈ Finset.range (n + 1), (a k + b k) ^ 2) := by
  classical
  let d := fun k => a k - b k
  let s := fun k => a k + b k
  have hd (t : ℝ) : poly n d t = poly n a t - poly n b t := by
    simp [poly, d, sub_mul, sum_sub_distrib]
  have hs (t : ℝ) : poly n s t = poly n a t + poly n b t := by
    simp [poly, s, add_mul, sum_add_distrib]
  have cont (w : ℕ → ℝ) : Continuous (fun t => (poly n w t) ^ 2 * phase (-j * t)) := by
    have hp := continuous_poly n w
    unfold phase
    fun_prop
  have integ (w : ℕ → ℝ) :
      IntervalIntegrable (A.indicator (fun t => (poly n w t) ^ 2 * phase (-j * t))) volume 0 1 := by
    have hi := (cont w).intervalIntegrable (μ := volume) 0 1
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
      rw [show (poly n a t) ^ 2 * phase (-j * t) - (poly n b t) ^ 2 * phase (-j * t) =
          (poly n d t * poly n s t) * phase (-j * t) by rw [hd, hs]; ring]
      simp only [norm_mul, phase, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
    · simp [Set.indicator_of_notMem ht, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  have bound := norm_bound.trans (cauchy_on_unit (continuous_poly n d) (continuous_poly n s))
  simpa only [parseval, d, s] using bound

end Conjectures.Goldbach.MaskedWeightLtwo_aux

open Conjectures.Goldbach.MaskedWeightLtwo_aux

theorem Conjectures.Goldbach.MaskedWeightLtwo :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ)*t); let C (A : Set ℝ) (n : ℕ) (u : ℕ → ℝ) := intervalIntegral (A.indicator (fun t => (S n u t)^2 * E (-(n : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume; ∀ (A : Set ℝ) (n : ℕ) (u v : ℕ → ℝ), MeasurableSet A → ‖C A n u - C A n v‖ ≤ Real.sqrt (∑ k ∈ Finset.range (n+1), (u k-v k)^2) * Real.sqrt (∑ k ∈ Finset.range (n+1), (u k+v k)^2) := by
  dsimp only
  intro A n u v hA
  exact swap_masked A hA (n : ℝ) n u v
