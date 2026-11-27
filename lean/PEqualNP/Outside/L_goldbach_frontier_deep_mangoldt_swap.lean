import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeSwap

open Finset MeasureTheory
open scoped BigOperators

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def poly (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (a k : ℂ) * phase ((k : ℝ) * t)

private theorem continuous_poly (n : ℕ) (a : ℕ → ℝ) : Continuous (poly n a) := by
  unfold poly phase
  fun_prop

/-- Parseval on the unit interval. The finite character orthogonality argument is
adapted from the Goldbach project, PR #495, `L_goldbach_small_bulk_saving`. -/
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

noncomputable def masked (A : Set ℝ) (j : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, A.indicator (fun u => (poly n a u)^2 * phase (-j * u)) t

private theorem swap_masked (A : Set ℝ) (hA : MeasurableSet A) (j : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    ‖masked A j n a - masked A j n b‖ ≤
      Real.sqrt (∑ k ∈ Finset.range (n+1), (a k - b k)^2) *
        Real.sqrt (∑ k ∈ Finset.range (n+1), (a k + b k)^2) := by
  classical
  let d := fun k => a k - b k
  let s := fun k => a k + b k
  have hd (t : ℝ) : poly n d t = poly n a t - poly n b t := by
    simp [poly, d, sub_mul, sum_sub_distrib]
  have hs (t : ℝ) : poly n s t = poly n a t + poly n b t := by
    simp [poly, s, add_mul, sum_add_distrib]
  have cont (a : ℕ → ℝ) : Continuous (fun t => (poly n a t)^2 * phase (-j * t)) := by
    have hp := continuous_poly n a
    unfold phase
    fun_prop
  have integ (a : ℕ → ℝ) :
      IntervalIntegrable (A.indicator (fun t => (poly n a t)^2 * phase (-j * t))) volume 0 1 := by
    have hi := (cont a).intervalIntegrable (μ := volume) 0 1
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
      rw [show (poly n a t)^2 * phase (-j*t) - (poly n b t)^2 * phase (-j*t) =
          (poly n d t * poly n s t) * phase (-j*t) by rw [hd, hs]; ring]
      simp only [norm_mul, phase, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
    · simp [Set.indicator_of_notMem ht, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  have bound := norm_bound.trans (cauchy_on_unit (continuous_poly n d) (continuous_poly n s))
  simpa only [parseval, d, s] using bound

end PrimeSwap

namespace PrimeSwap

private noncomputable def weight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

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

end PrimeSwap

open Filter in
private theorem swap_eventually : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
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

theorem PEqualNP.Outside.L_goldbach_frontier_deep_mangoldt_swap :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Λ := ArithmeticFunction.vonMangoldt; let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Jdeep n Λ Λ - deepMinor n‖ ≤ e * (n : ℝ) := by
  intro w E S Q f Q₁ H wideArcs deepMinor Λ Jdeep ε hε
  obtain ⟨N, hN⟩ := swap_eventually ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hn₂, hsmall⟩ := hN n hn
  classical
  have hmeas : MeasurableSet (wideArcs n) := by
    have heq : wideArcs n =
        ⋃ q ∈ Finset.range (Q₁ n + 1), ⋃ a ∈ Finset.range (Q₁ n + 1),
          if 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q then
            {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}
          else ∅ := by
      ext t
      simp only [wideArcs, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨q, a, hq, hqQ, haq, hcop, hdist⟩
        refine ⟨q, Nat.lt_succ_of_le hqQ, a, Nat.lt_succ_of_le (haq.trans hqQ), ?_⟩
        split_ifs with hcond
        · exact hdist
        · exact False.elim (hcond ⟨hq, haq, hcop⟩)
      · rintro ⟨q, hq, a, _, ht⟩
        split_ifs at ht with hcond
        · exact ⟨q, a, hcond.1, Nat.lt_succ_iff.mp hq, hcond.2.1, hcond.2.2, ht⟩
        · exact False.elim ht
    rw [heq]
    refine Finset.measurableSet_biUnion _ fun q _ => Finset.measurableSet_biUnion _ fun a _ => ?_
    split_ifs
    · exact (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
    · exact MeasurableSet.empty
  let A := (wideArcs n)ᶜ
  have hJ : Jdeep n Λ Λ = PrimeSwap.masked A n n Λ := by
    simp only [Jdeep, PrimeSwap.masked, pow_two]
    rfl
  have hw : deepMinor n = PrimeSwap.masked A n n PrimeSwap.weight := rfl
  rw [hJ, hw]
  refine (PrimeSwap.swap_masked A hmeas.compl n n Λ PrimeSwap.weight).trans ?_
  refine le_trans ?_ hsmall
  exact mul_le_mul (Real.sqrt_le_sqrt (PrimeSwap.swap_diff_energy n hn₂))
    (Real.sqrt_le_sqrt (PrimeSwap.swap_sum_energy n hn₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
