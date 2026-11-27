import Mathlib

/- The block variance is partitioned by reduced additive frequency.
The low conductors are controlled by the uniform Siegel–Walfisz estimate, and
the high conductors by the sharp separated additive large sieve. -/

section

/-!
# Major-arc estimates for the prime logarithmic sum

The general finite estimates below are from DFQDZZ, goldbach-proofs PR #316,
revision e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).

The analytic material in the namespaces OAI.LargePrimeGaps is selected and adapted
from OpenAI's openai/math, lean/OAI/NumberTheory/PrimeGaps, at revision
f5702854040e97fa7675c21ba37a9608f5f92dd3, licensed under Apache 2.0 (see LICENSE).
It is specialized to the declarations required for the small-modulus estimate and
ported from toolchain 4.34.1 to the version locked by this repository.
-/

section

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

end LargePrimeGaps
end OAI

-- Source module: ConductorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

end LargePrimeGaps
end OAI

-- Source module: LogParameters
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

end LargePrimeGaps
end OAI

-- Source module: DirichletGrowth
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset
lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  have hint : (∫ t in Ioi (1:ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun {t} ht => he t ht)
  rw [hint,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps
end OAI

-- Source module: TaylorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
set_option maxHeartbeats 800000 in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory
noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps
end OAI

-- Source module: SiegelBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end
section
open Complex Finset ArithmeticFunction
noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps
end OAI

-- Source module: ZeroFreeBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end
lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset
lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps
end OAI

-- Source module: PrincipalGrowth
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps
end OAI

-- Source module: RieszBounds
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps
end OAI

-- Source module: MellinSmoothing
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology
lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory
open scoped FourierTransform
lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology
lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology
noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

set_option maxHeartbeats 3000000 in
lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  have hbase : Integrable (fun t : ℝ => ‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖) :=
    (rieszDenominator_verticalIntegrable hσ.le).norm
  change Integrable (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))
  apply (hbase.const_mul (1/(σ-1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI

-- Source module: RieszDecay
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology
noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

set_option maxHeartbeats 800000 in
lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology
noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology
lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps
end OAI

-- Source module: Main
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) := by
      exact add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

end LargePrimeGaps
end OAI


-- Source module: OrthantIntegrals
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps
end OAI

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

end LargePrimeGaps
end OAI

end

open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open OAI.LargePrimeGaps

noncomputable section

/-- The character form of Siegel–Walfisz gives a uniform bound for a reduced class.
The second term pays for replacing the character by its primitive character. -/
theorem progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q b : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        b < q → b.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q b - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, x₀, hx₀, hχ⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q b hq hqlog hb hcop
  let : NeZero q := ⟨hq.ne'⟩
  have hchar (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ‖ ≤
        M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
    have hcond : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    exact (primeCharacterError_le_primitive x hq χ).trans (add_le_add
      (hχ x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) (hcond.trans hqlog) χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive) (le_refl _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (endpointClassError_le_character_sum x hq hb hcop).trans
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        (M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q) :=
      sum_le_sum fun χ _ => hchar χ
    _ = _ := by rw [sum_const, card_univ, hcard, nsmul_eq_mul, mul_comm]

private theorem primeWeight_le_mangoldt (k : ℕ) :
    primeWeight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [primeWeight, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [primeWeight, hk]

private theorem classMass_succ (N q b : ℕ) :
    classMass (N + 1) q b =
      ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), primeWeight k := by
  rw [classMass, Nat.range_succ_eq_Icc_zero, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc]
  · simp [primeWeight]
  · exact Nat.zero_le _

/-- Restriction to one class can discard no more prime-power mass than ψ(N) − θ(N). -/
theorem prime_power_correction (N q b : ℕ) :
    |classMass (N + 1) q b - residuePrefix ArithmeticFunction.vonMangoldt N q b| ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [classMass_succ, residuePrefix, residueSlice, abs_sub_comm, ← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun k _ => sub_nonneg.mpr (primeWeight_le_mangoldt k))]
  have htotal : (∑ k ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt k - primeWeight k)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    simp only [sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, sum_filter,
      primeWeight]
  rw [← htotal]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  exact fun k _ _ => sub_nonneg.mpr (primeWeight_le_mangoldt k)

/-- Siegel–Walfisz for the actual logarithmic prime weights, uniformly in reduced residue
classes. The additive terms account for nonprimitive characters and proper prime powers. -/
theorem prime_progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B →
        b < q → b.Coprime q →
        |classMass (N + 1) q b - (N : ℝ) / q.totient| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb hcop
  have he := h (N : ℝ) hN q b hq hlog hb hcop
  simp only [Nat.floor_natCast] at he
  have hpow := (prime_power_correction N q b).trans (Chebyshev.psi_sub_theta_le (hx₀.le.trans hN))
  exact (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt N q b) _).trans
    ((add_le_add hpow he).trans_eq (add_comm _ _))

private theorem classMass_nonunit (N q b : ℕ) (hq : 0 < q) (hb : ¬ b.Coprime q) :
    classMass (N + 1) q b ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  rw [classMass_succ]
  have hs : (Ioc 0 N).filter (fun k => k % q = b) ⊆
      (Ioc 0 N).filter (fun k => ¬ k.Coprime q) := by
    intro k hk
    obtain ⟨hkN, hkb⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hkN, fun h => hb ?_⟩
    rw [← hkb, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact h.gcd_eq_one
  calc
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum fun k _ => primeWeight_le_mangoldt k
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => ¬ k.Coprime q), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le N hq

/-- A single error budget for every residue, with the initial segment length and the q-dependent
constant exactly as in the expansion of the prime exponential sum. -/
theorem all_class_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B → b < q →
        |classError (N + 1) q b| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N + 1 := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := prime_progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb
  have hN' : (1 : ℝ) ≤ N := hx₀.le.trans hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN'
  by_cases hcop : b.Coprime q
  · rw [classError, ite_eq_left hcop]
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hlast : |(N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient| ≤ 1 := by
      rw [show (N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient = -(1 / (q.totient : ℝ)) by
        push_cast; ring, abs_neg, abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).mpr hφ
    exact (abs_sub_le _ ((N : ℝ) / q.totient) _).trans (add_le_add (h N q b hN hq hlog hb hcop) hlast)
  · rw [classError, ite_eq_right hcop, sub_zero, abs_of_nonneg (by
      unfold classMass
      apply sum_nonneg
      intro k _
      unfold primeWeight
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_le)
      · exact le_rfl)]
    have hmain : 0 ≤ M * N * (Real.log N) ^ (-A) := by positivity
    have hpower : 0 ≤ 2 * Real.sqrt N * Real.log N := by positivity
    linarith [classMass_nonunit N q b hq hcop]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped ComplexConjugate

noncomputable section

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

end
end GoldbachMajorArc

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachMajorArc.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)


end
end GoldbachMajorArc

end

section

/- These finite estimates use the Ramanujan CRT, prime-power formula and reduced
mean identity from DFQDZZ, goldbach-proofs PR #316 (Apache License 2.0). -/

namespace GoldbachMajorArc
open Finset
open scoped ComplexConjugate

/-- For frequency one the prime-power factors are zero or minus one. -/
theorem norm_ram_one_le (q : ℕ) : ‖ram q 1‖ ≤ 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    have hnd (k : ℕ) : ¬ p^(k+1) ∣ 1 :=
      fun h => hp.not_dvd_one ((dvd_pow_self _ (Nat.succ_ne_zero k)).trans h)
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      rw [ram_primePower p k 1 hp, ite_eq_right (hnd k)]
      cases k with
      | zero => simp
      | succ k => simp [hnd k]
  | coprime q r hq hr hc iq ir =>
    rw [ram_mul (by omega) (by omega) hc, norm_mul]
    exact (mul_le_mul iq ir (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Absolute-value bound for an arbitrary frequency by the number of unit residues. -/
theorem norm_ram_le_totient (q m : ℕ) : ‖ram q m‖ ≤ q.totient := by
  rw [ram]
  refine (norm_sum_le _ _).trans ?_
  have hc : ((range q).filter (fun a => a.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]; simp only [Nat.coprime_comm]
  simp only [phase,Complex.norm_exp_ofReal_mul_I,sum_const,nsmul_eq_mul,mul_one,hc,le_refl]

theorem norm_unitMean_le_inv_totient {q a : ℕ} (ha : a.Coprime q) :
    ‖unitMean q a‖ ≤ 1 / (q.totient : ℝ) := by
  rw [unitMean_eq_ram ha, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_ram_one_le q) (Nat.cast_nonneg _)

end GoldbachMajorArc

end

section

namespace GoldbachEstermann
open Finset

/-- Each divisor has totient at most that of the ambient integer. Summing over
divisors and using Gauss's identity gives a divisor-count majorant. -/
private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹) := by
  have hφ := Nat.totient_pos.mpr hq
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum (fun d hd =>
        Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  calc
    _ ≤ (q.divisors.card : ℝ) / q := (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)).mpr
      (by rw [one_mul]; exact_mod_cast hcount)
    _ = ∑ _ ∈ q.divisorsAntidiagonal, (q:ℝ)⁻¹ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (q:ℝ)⁻¹)]; simp [div_eq_mul_inv]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_inv]

/-- A finite reciprocal-totient bound with constant one. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ)) ≤ (1 + Real.log Q)^2 := by
  let S := Icc 1 Q
  let w := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hf := Nat.fst_mem_divisors_of_mem_antidiagonal hab
      have hs := Nat.snd_mem_divisors_of_mem_antidiagonal hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ hf,hm _ hs⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hab
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hab).2,by omega⟩
  have hsum : (∑ i ∈ S, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab :=
      sum_le_sum (fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1)
    _ = ∑ q ∈ S, ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w ab :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w ab :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ab ∈ S ×ˢ S, w ab := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ S, (i:ℝ)⁻¹)^2 := by rw [sq,sum_product,sum_mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hsum 2

end GoldbachEstermann

end

section

/- The sharp separated additive large sieve and its auxiliary proofs are adapted from
OpenAI, openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/Ostmann/Preliminaries (Apache License 2.0). -/
namespace GoldbachBDHSharp

-- Upstream module CosecantKernel
namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

noncomputable def cosecantKernel (x y : ℝ) : ℝ := (Real.sin (Real.pi * (x - y)))⁻¹
noncomputable def cotangentKernel (x y : ℝ) : ℝ :=
  Real.cos (Real.pi * (x - y)) / Real.sin (Real.pi * (x - y))

@[simp] theorem cosecantKernel_self (x : ℝ) : cosecantKernel x x = 0 := by
  simp [cosecantKernel]

@[simp] theorem cotangentKernel_self (x : ℝ) : cotangentKernel x x = 0 := by
  simp [cotangentKernel]

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI

-- Upstream module SieveGeometricKernel
namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

noncomputable def sieveHalfPhase (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem sieveHalfPhase_zero : sieveHalfPhase 0 = 1 := by simp [sieveHalfPhase]

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem sieveHalfPhase_norm (t : ℝ) : ‖sieveHalfPhase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI

-- Upstream module SeparatedInverseSquares
namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI

-- Upstream module SeparatedSetSquares
namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI

-- Upstream module CosecantDistanceBound
namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

noncomputable def cosecantRowWeight (t : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * t) ^ 2 +
    2 * |Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ^ 2|

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI

-- Upstream module CircleSeparatedPoints
namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredCircleRemainder (t : ℝ) : ℝ := t - (⌊t + 1 / 2⌋ : ℤ)

def CircleSeparated {ι : Type*} (x : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ s t, s ≠ t → ∀ m : ℤ, δ ≤ |x s - x t - m|

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1; congr 1; dsimp [centeredCircleRemainder]; ring

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI

-- Upstream module CosecantRowSum
namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI

-- Upstream module SkewKernelSquare
namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI

-- Upstream module HermitianEigenvector
namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h := hA.star_dotProduct_mulVec_comm u v
  rw [heig, dotProduct_smul] at h
  apply star_injective
  rw [h]
  simp [dotProduct, mul_comm]

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI

-- Upstream module CosecantMatrix
namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def imaginaryKernelMatrix (h : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of (fun s t => Complex.I * (h s t : ℂ))

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI

-- Upstream module SymmetricQuadraticBound
namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI

-- Upstream module KernelEigenvalueBound
namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

end Ostmann

end OAI

-- Upstream module HermitianNormBound
namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI

-- Upstream module CosecantHilbertBound
namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cosecantMatrix (x : ι → ℝ) : Matrix ι ι ℂ :=
  imaginaryKernelMatrix (fun s t => cosecantKernel (x s) (x t))

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI

-- Upstream module SievePhaseGram
namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI

-- Upstream module SieveDualEnergy
namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def twistedCosecantSum (x : ι → ℝ) (b : ι → ℂ) (L : ℝ) : ℂ :=
  ∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
    (cosecantKernel (x s) (x t) : ℂ)

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI

-- Upstream module FiniteMatrixDuality
namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI

-- Upstream module SeparatedAdditiveSieve
namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

noncomputable def sievePhaseMatrix {ι : Type*} (x : ι → ℝ) (M : ℕ) (J : ℝ) :
    Matrix ι (Fin M) ℂ :=
  Matrix.of (fun s n => sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s))

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI


end GoldbachBDHSharp

end

section

theorem GoldbachBDH.farey_sep :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ, 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq hqQ hr hrQ ha hb hdistinct m
  let d : ℤ := a * (r : ℤ) - b * (q : ℤ) - m * q * r
  have hd : d ≠ 0 := by
    intro heq
    change (a : ℤ) * r - b * q - m * q * r = 0 at heq
    have hqr : q ∣ a * r := by
      have : (q : ℤ) ∣ (a : ℤ) * r := ⟨b + m * r, by linarith only [heq]⟩
      exact_mod_cast this
    have hrq : r ∣ b * q := by
      have : (r : ℤ) ∣ (b : ℤ) * q := ⟨a - m * q, by linarith only [heq]⟩
      exact_mod_cast this
    have hsame := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqr) (hb.symm.dvd_of_dvd_mul_left hrq)
    subst r
    have hqi : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have he : ((a : ℤ) - b - m * q) * q = 0 := by linarith only [heq]
    have hab := (mul_eq_zero.mp he).resolve_right hqi
    have hmod : (a : ℤ) ≡ b [ZMOD (q : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-m, by linarith only [hab]⟩
    exact hdistinct.elim (fun h => h rfl) (fun h => h (Int.natCast_modEq_iff.mp hmod))
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hD : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |d| by have := abs_pos.mpr hd; omega)
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by rw [sq]; exact_mod_cast Nat.mul_le_mul hqQ hrQ
  calc 1 / (Q : ℝ)^2 ≤ 1 / ((q : ℝ) * r) := one_div_le_one_div_of_le (mul_pos hq' hr') hden
    _ ≤ |(d : ℝ)| / ((q : ℝ) * r) := div_le_div_of_nonneg_right hD (mul_pos hq' hr').le
    _ = _ := by
      rw [← abs_of_pos (mul_pos hq' hr'), ← abs_div]
      congr 1
      dsimp [d]; push_cast; field_simp

end

section

/- The discrete Parseval calculation is adapted from houmy555809, goldbach-proofs
PR #208, commit dcfadb86851309af7a32ea86bafabb81491bb206 (Apache-2.0). -/
namespace GoldbachBDH

open scoped BigOperators

private lemma phase_add (s t : ℝ) :
    Complex.exp (((2*Real.pi*(s+t):ℝ):ℂ)*Complex.I)
      = Complex.exp (((2*Real.pi*s:ℝ):ℂ)*Complex.I) * Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_norm (x : ℝ) :
    ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (((2*Real.pi*x:ℝ):ℂ)*Complex.I).re = 0 := by simp
  rw [h, Real.exp_zero]

private lemma phase_star (x : ℝ) :
    star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))
      = Complex.exp (((2*Real.pi*(-x):ℝ):ℂ)*Complex.I) := by
  have h1 : (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))⁻¹
      = star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) := Complex.inv_eq_conj (phase_norm x)
  rw [← h1, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- E(a) * conj(E(b)) = conj(E(b-a))。 -/
private lemma phase_star_mul (a b : ℝ) :
    Complex.exp (((2*Real.pi*a:ℝ):ℂ)*Complex.I)
      * star (Complex.exp (((2*Real.pi*b:ℝ):ℂ)*Complex.I))
      = star (Complex.exp (((2*Real.pi*(b-a):ℝ):ℂ)*Complex.I)) := by
  rw [phase_star, ← phase_add, phase_star]
  congr 1
  push_cast
  ring

private lemma phase_pow (x : ℝ) (j : ℕ) :
    Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)^j
      = Complex.exp (((2*Real.pi*((j:ℝ)*x):ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- 单位根正交性（ℕ 版）：Σ_{j<M} E(jk/M) = if M ∣ k then M else 0。 -/
private lemma char_orth (M k : ℕ) (hM : 0 < M) :
    Finset.sum (Finset.range M) (fun j : ℕ =>
      Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
      = if M ∣ k then (M:ℂ) else 0 := by
  have hMne : M ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * ((Real.pi:ℝ):ℂ) * Complex.I / (M:ℂ)) with hζ
  have hprim : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hMne
  have hterm : ∀ j : ℕ, Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I) = ζ^(j*k) := by
    intro j
    have harg : (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
        = (j*k:ℕ) * (2 * ((Real.pi:ℝ):ℂ) * Complex.I / (M:ℂ)) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hdvd : M ∣ k
  · obtain ⟨t, rfl⟩ := hdvd
    have hone : ∀ j : ℕ, ζ^(j*(M*t)) = 1 := by
      intro j
      rw [show j*(M*t) = M*(j*t) by ring, pow_mul, hprim.pow_eq_one, one_pow]
    rw [Finset.sum_congr rfl (fun j _ => hone j)]
    simp
  · have hζk_ne : ζ^k ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd k).mp h)
    have hpow : (ζ^k)^M = 1 := by
      rw [← pow_mul, Nat.mul_comm k M, pow_mul, hprim.pow_eq_one, one_pow]
    have hsum : Finset.sum (Finset.range M) (fun j : ℕ => ζ^(j*k)) = 0 := by
      have hstep : ∀ j : ℕ, ζ^(j*k) = (ζ^k)^j := by
        intro j
        rw [show (ζ^k)^j = ζ^(k*j) by rw [pow_mul], Nat.mul_comm]
      rw [Finset.sum_congr rfl (fun j _ => hstep j), geom_sum_eq hζk_ne M, hpow]
      simp
    rw [hsum, if_neg hdvd]

/-- 两指标正交性：Σ_{j<M} E(jl/M)·conj(E(jk/M)) = if l=k then M else 0。 -/
private lemma pair_orth (M l k : ℕ) (hM : 0 < M) (hl : l < M) (hk : k < M) :
    Finset.sum (Finset.range M) (fun j : ℕ =>
      Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
        * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
      = if l = k then (M:ℂ) else 0 := by
  rcases le_total k l with hle | hle
  · -- l ≥ k：项 = E(j(l-k)/M)
    have hstep : ∀ j : ℕ,
        Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
          * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
        = Complex.exp (((2*Real.pi*((j:ℝ)*((l-k:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I) := by
      intro j
      rw [phase_star_mul, phase_star]
      congr 1
      have hsub : ((l-k:ℕ):ℝ) = (l:ℝ) - (k:ℝ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [hsub]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), char_orth M (l-k) hM]
    by_cases hlk : l = k
    · subst hlk; simp
    · have hne : ¬ M ∣ l - k := by
        intro h
        have hpos : 0 < l - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hle (Ne.symm hlk))
        have := Nat.le_of_dvd hpos h
        omega
      rw [if_neg hne, if_neg hlk]
  · -- l ≤ k：项 = conj(E(j(k-l)/M))
    have hstep : ∀ j : ℕ,
        Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
          * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
        = star (Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) := by
      intro j
      rw [phase_star_mul]
      congr 1
      have hsub : ((k-l:ℕ):ℝ) = (k:ℝ) - (l:ℝ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [hsub]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    have hsum_eq : Finset.sum (Finset.range M) (fun j : ℕ =>
        star (Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = star (Finset.sum (Finset.range M) (fun j : ℕ =>
          Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))) := by simp
    rw [hsum_eq, char_orth M (k-l) hM]
    by_cases hlk : l = k
    · subst hlk; simp
    · have hne : ¬ M ∣ k - l := by
        intro h
        have hpos : 0 < k - l := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hlk)
        have := Nat.le_of_dvd hpos h
        omega
      simp [hne, hlk]


theorem parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ)); let F := fun (M : ℕ) (f : ℕ → ℂ) (j : ℕ) => Finset.sum (Finset.range M) (fun k => f k*c M j k); ∀ M f, Finset.sum (Finset.range M) (fun j => ‖F M f j‖^2) = (M:ℝ)*Finset.sum (Finset.range M) (fun k => ‖f k‖^2) := by
  intro E c F M f
  simp only [E, c, F]
  by_cases hM0 : M = 0
  · subst hM0
    simp
  have hM : 0 < M := Nat.pos_of_ne_zero hM0
  -- 缩写：A j k = exp(2πi·j·k/M)
  have hcompl : Finset.sum (Finset.range M) (fun j : ℕ =>
      (Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        * star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
      = (M:ℂ) * Finset.sum (Finset.range M) (fun k : ℕ => f k * star (f k)) := by
    -- star 推进内层和
    have hstar_sum : ∀ j : ℕ,
        star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = Finset.sum (Finset.range M) (fun v : ℕ =>
          star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)) := by
      intro j
      have hs : star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          = Finset.sum (Finset.range M) (fun v : ℕ =>
            star (f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))) := by
        have hmap := map_sum (starRingEnd ℂ)
          (fun v : ℕ => f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
          (Finset.range M)
        simpa using hmap
      rw [hs]
      apply Finset.sum_congr rfl
      intro v _
      rw [star_mul]
    have hstep1 : Finset.sum (Finset.range M) (fun j : ℕ =>
        (Finset.sum (Finset.range M) (fun u : ℕ =>
          f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          * star (Finset.sum (Finset.range M) (fun v : ℕ =>
            f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
        = Finset.sum (Finset.range M) (fun j : ℕ =>
          (Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
            * (Finset.sum (Finset.range M) (fun v : ℕ =>
              star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hstar_sum j]
    rw [hstep1]
    -- 展开成三重和
    have hexp : Finset.sum (Finset.range M) (fun j : ℕ =>
        (Finset.sum (Finset.range M) (fun u : ℕ =>
          f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          * (Finset.sum (Finset.range M) (fun v : ℕ =>
            star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v))))
        = Finset.sum (Finset.range M) (fun u : ℕ =>
          Finset.sum (Finset.range M) (fun v : ℕ =>
            f u * star (f v) * Finset.sum (Finset.range M) (fun j : ℕ =>
              Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
                * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))) := by
      have h1 : ∀ j : ℕ,
          (Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
            * (Finset.sum (Finset.range M) (fun v : ℕ =>
              star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)))
          = Finset.sum (Finset.range M) (fun u : ℕ =>
            Finset.sum (Finset.range M) (fun v : ℕ =>
              f u * star (f v) *
                (Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
                  * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))) := by
        intro j
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [Finset.sum_congr rfl (fun j _ => h1 j)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
    rw [hexp]
    -- 内层正交和 = if u = v then M else 0
    have hinner : ∀ u ∈ Finset.range M, ∀ v ∈ Finset.range M,
        Finset.sum (Finset.range M) (fun j : ℕ =>
          Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
            * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = if u = v then (M:ℂ) else 0 := by
      intro u hu v hv
      exact pair_orth M u v hM (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
    rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => by
      rw [hinner u hu v hv]))]
    -- 对角化
    have hdiag : Finset.sum (Finset.range M) (fun u : ℕ =>
        Finset.sum (Finset.range M) (fun v : ℕ =>
          f u * star (f v) * (if u = v then (M:ℂ) else 0)))
        = Finset.sum (Finset.range M) (fun u : ℕ => f u * star (f u) * (M:ℂ)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_eq_single u]
      · rw [if_pos rfl]
      · intro v _ hvu
        rw [if_neg (Ne.symm hvu), mul_zero]
      · intro hnot
        exact absurd hu hnot
    rw [hdiag]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  -- 把两侧都写成实数的提升
  have hleft : Finset.sum (Finset.range M) (fun j : ℕ =>
      (Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        * star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
      = ((Finset.sum (Finset.range M) (fun j : ℕ =>
          ‖Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))‖^2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← starRingEnd_apply]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hright : (M:ℂ) * Finset.sum (Finset.range M) (fun k : ℕ => f k * star (f k))
      = (((M:ℝ) * Finset.sum (Finset.range M) (fun k : ℕ => ‖f k‖^2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← starRingEnd_apply]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : ((Finset.sum (Finset.range M) (fun j : ℕ =>
      ‖Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))‖^2) : ℝ) : ℂ)
      = (((M:ℝ) * Finset.sum (Finset.range M) (fun k : ℕ => ‖f k‖^2) : ℝ) : ℂ) := by
    rw [← hleft, ← hright]
    exact hcompl
  exact Complex.ofReal_inj.mp hcast

end GoldbachBDH

end

section

namespace GoldbachBDH
open Finset
noncomputable section

def num (q : ℕ) := (range q).filter (fun a => a.Coprime q)

lemma num_card (d : ℕ) : (num d).card=d.totient := by
  rw [Nat.totient_eq_card_coprime]
  simp [num,Nat.coprime_comm]

/-- Every a/q with 0 ≤ a < q occurs once, in its reduced denominator. -/
theorem all_frequencies (q : ℕ) (hq : 0<q) (f : ℕ → ℝ) :
    (∑ a ∈ range q, f a) = ∑ d ∈ q.divisors, ∑ b ∈ num d, f (b*(q/d)) := by
  classical
  rw [sum_sigma']
  symm
  apply sum_bij (fun p _ => p.2*(q/p.1))
  · rintro ⟨d,b⟩ h
    obtain ⟨hd,hb⟩ := mem_sigma.mp h
    obtain ⟨hb',hcop⟩ := mem_filter.mp hb
    have hdm := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    have hpos : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
    exact mem_range.mpr ((Nat.mul_lt_mul_of_pos_right (mem_range.mp hb') hpos).trans_eq (by simpa [mul_comm] using hdm))
  · rintro ⟨d,b⟩ h ⟨e,c⟩ h' he
    obtain ⟨hd,hb⟩ := mem_sigma.mp h
    obtain ⟨he',hc⟩ := mem_sigma.mp h'
    have hg {d b : ℕ} (hd : d∈q.divisors) (hb : b∈num d) :
        (b*(q/d)).gcd q = q/d := by
      have hm := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      conv_lhs => rhs; rw [←hm,Nat.mul_comm (q/d) d]
      rw [Nat.gcd_mul_right]
      simp [(mem_filter.mp hb).2.gcd_eq_one]
    change b*(q/d)=c*(q/e) at he
    have heq : q/d=q/e := (hg hd hb).symm.trans ((congrArg (fun a : ℕ => a.gcd q) he).trans (hg he' hc))
    have hden : d=e := by
      have hpd := Nat.pos_of_mem_divisors hd
      have hm := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      have hm' := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he')
      rw [←heq] at hm'
      exact Nat.eq_of_mul_eq_mul_left (Nat.div_pos (Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd))
        (hm.trans hm'.symm)
    subst e
    have hpos : 0<q/d := Nat.div_pos (Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
    have hbc := Nat.eq_of_mul_eq_mul_right hpos he
    subst c; rfl
  · intro a ha
    let g := a.gcd q
    have hg : 0<g := Nat.gcd_pos_of_pos_right a hq
    have hdq : g∣q := Nat.gcd_dvd_right a q
    have hda : g∣a := Nat.gcd_dvd_left a q
    have hcop : (a/g).Coprime (q/g) := Nat.coprime_div_gcd_div_gcd hg
    have hden : q/(q/g)=g := Nat.div_div_self hdq hq.ne'
    have hprod := Nat.div_mul_cancel hdq
    have haprod := Nat.div_mul_cancel hda
    have hb : a/g<q/g := by
      by_contra! hb
      have hle := Nat.mul_le_mul_right g hb
      rw [hprod,haprod] at hle
      exact (mem_range.mp ha).not_ge hle
    refine ⟨⟨q/g,a/g⟩,mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdq,hq.ne'⟩,
      mem_filter.mpr ⟨mem_range.mpr hb,hcop⟩⟩,?_⟩
    simpa only [hden] using haprod
  · intros; rfl

/-- A reduced denominator d occurs at most 2Q/d times in Q < q ≤ 2Q. -/
theorem divisibility_weight (Q d : ℕ) (hQ : 0<Q) (hd : 0<d) :
    (∑ q ∈ (Ioc Q (2*Q)).filter (fun q => d∣q), 1/(q:ℝ)) ≤ 2/(d:ℝ) := by
  let s := (Ioc Q (2*Q)).filter (fun q => d∣q)
  have hc : s.card ≤ 2*Q/d := by
    calc
      s.card ≤ (Icc 1 (2*Q/d)).card := by
        apply card_le_card_of_injOn (fun q : ℕ => q/d)
        · intro q hq
          obtain ⟨hI,hdiv⟩ := mem_filter.mp hq
          obtain ⟨hq0,hqU⟩ := mem_Ioc.mp hI
          exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hd, Nat.div_le_div_right hqU⟩
        · intro q hq p hp he
          exact (Nat.div_mul_cancel (mem_filter.mp hq).2).symm.trans
            ((congrArg (·*d) he).trans (Nat.div_mul_cancel (mem_filter.mp hp).2))
      _ = _ := by simp
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hdr : (0:ℝ)<d := by exact_mod_cast hd
  have hprod : (s.card:ℝ)*d ≤ (2:ℝ)*Q := by
    exact_mod_cast (Nat.mul_le_mul_right d hc).trans (Nat.div_mul_le_self (2*Q) d)
  calc
    _ ≤ ∑ _q ∈ s, 1/(Q:ℝ) := sum_le_sum fun q hq =>
      one_div_le_one_div_of_le hQr (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hq).1).1.le)
    _ = (s.card:ℝ)/Q := by simp [div_eq_mul_inv]
    _ ≤ _ := (div_le_div_iff₀ hQr hdr).mpr hprod

theorem aggregate (Q : ℕ) (hQ : 0<Q) (f : ℕ → ℝ) (hf : ∀ d,0≤f d) :
    (∑ q ∈ Ioc Q (2*Q), (∑ d ∈ q.divisors, f d)/(q:ℝ)) ≤
      ∑ d ∈ Icc 1 (2*Q), 2/(d:ℝ)*f d := by
  let S := Ioc Q (2*Q); let T := Icc 1 (2*Q)
  have he (q : ℕ) (hq : q∈S) : q.divisors=T.filter (fun d=>d∣q) := by
    ext d
    have hqp := (mem_Ioc.mp hq).1
    have hqU := (mem_Ioc.mp hq).2
    simp only [Nat.mem_divisors,mem_filter,mem_Icc,T]
    exact ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega), (Nat.le_of_dvd (by omega) h.1).trans hqU⟩,h.1⟩,
      fun h => ⟨h.2,by omega⟩⟩
  change (∑ q ∈ S, _) ≤ ∑ d ∈ T, _
  calc
    _ = ∑ q ∈ S, ∑ d ∈ T, if d∣q then (1/(q:ℝ))*f d else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [he q hq, sum_div,sum_filter]
      apply sum_congr rfl
      intro d _; split_ifs <;> ring
    _ = ∑ d ∈ T, (∑ q ∈ S.filter (fun q=>d∣q), 1/(q:ℝ))*f d := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_mul,sum_filter]
    _ ≤ _ := sum_le_sum fun d hd => mul_le_mul_of_nonneg_right (divisibility_weight Q d hQ (mem_Icc.mp hd).1) (hf d)
end
end GoldbachBDH

end

section

namespace GoldbachBDH
open Finset GoldbachMajorArc
noncomputable section

lemma average_surj {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G →* H) (hs : Function.Surjective f) (w : H → ℂ) :
    (∑ x, w (f x)) / Fintype.card G = (∑ y, w y)/Fintype.card H := by
  classical
  let m := Fintype.card f.ker
  have hcard (y : H) : (univ.filter (fun x:G=>f x=y)).card=m := by
    rw [←Fintype.card_coe]
    apply Fintype.card_congr
    exact (Equiv.subtypeEquivRight (fun x => by
      change x∈univ.filter (fun x:G => f x=y) ↔ f x∈({y}:Set H)
      simp)).trans (MonoidHom.fiberEquivKerOfSurjective hs y)
  have hsum (u : H → ℂ) : (∑ x, u (f x)) = (m:ℂ)*(∑ y, u y) := by
    rw [←sum_fiberwise_of_maps_to' (fun (x:G) (_ : x∈univ) => mem_univ (f x)) u, mul_sum]
    simp_rw [sum_const,hcard,nsmul_eq_mul]
  have hG : (Fintype.card G:ℂ) = (m:ℂ)*(Fintype.card H:ℂ) := by simpa using hsum (fun _ => 1)
  rw [hsum,hG]
  have hm : (m:ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1:f.ker)⟩).ne'
  field_simp

lemma phase_residue (q a r : ℕ) [NeZero q] :
    phase ((r:ℝ)*((a:ℝ)/q)) = ZMod.stdAddChar ((a:ZMod q)*(r:ZMod q)) := by
  have h := ZMod.stdAddChar_coe (N:=q) ((a*r:ℕ):ℤ)
  push_cast at h
  rw [h]; unfold phase
  push_cast; congr 1; ring

lemma sum_units_val (q : ℕ) [NeZero q] (f : ℕ → ℂ) :
    (∑ r ∈ (range q).filter (fun k => k.Coprime q), f r) = ∑ u : (ZMod q)ˣ, f u.val.val := by
  apply sum_bij (fun a h => ZMod.unitOfCoprime a (mem_filter.mp h).2)
  · intros; exact mem_univ _
  · intro a ha b hb e
    have h := congrArg (fun u : (ZMod q)ˣ => u.val.val) e
    simpa [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),
      ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using h
  · intro u _
    exact ⟨u.val.val, mem_filter.mpr ⟨mem_range.mpr u.val.val_lt,ZMod.val_coe_unit_coprime u⟩,
      Units.ext (ZMod.natCast_zmod_val _)⟩
  · intro a ha
    simp [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1)]

lemma unitMean_lift (d k b : ℕ) (hd : 0<d) (hk : 0<k) :
    unitMean (d*k) (b*k) = unitMean d b := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero (d*k) := ⟨(Nat.mul_pos hd hk).ne'⟩
  have dv : d∣d*k := dvd_mul_right _ _
  let f := ZMod.unitsMap dv
  let W : (ZMod d)ˣ → ℂ := fun u => ZMod.stdAddChar ((b:ZMod d)*u.val)
  have hG := average_surj f (ZMod.unitsMap_surjective dv) W
  unfold unitMean
  rw [sum_units_val, sum_units_val]
  have rhs (u : (ZMod d)ˣ) : phase ((u.val.val:ℝ)*((b:ℝ)/d))= W u := by
    rw [phase_residue,ZMod.natCast_zmod_val]
  have lhs (u : (ZMod (d*k))ˣ) : phase ((u.val.val:ℝ)*(((b*k:ℕ):ℝ)/((d*k:ℕ):ℝ)))= W (f u) := by
    have rat : (((b*k:ℕ):ℝ)/((d*k:ℕ):ℝ))=(b:ℝ)/d := by push_cast; field_simp
    rw [rat,phase_residue]
    dsimp [W,f]
    congr 2
    simp [ZMod.unitsMap_def]
  simp_rw [lhs,rhs]
  simpa only [ZMod.card_units_eq_totient] using hG
end
end GoldbachBDH

end

section

namespace GoldbachBDHSW
open Filter GoldbachMajorArc
open scoped Topology

private theorem logarithmicGrowth (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, (Real.log n)^k ≤ (n : ℝ)^s := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^k / (n : ℝ)^s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hp : (0 : ℝ) < n := by exact_mod_cast hn1
  simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mp hn.le

private theorem uniformAll (h b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ q r : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log n)^h → r < q →
      |classError (n+1) q r| ≤ C*(n:ℝ)/(Real.log n)^b := by
  obtain ⟨M,hM,x,hx,hs⟩ := all_class_error (b+1 : ℕ) (h+1 : ℕ) (by positivity) (by positivity)
  refine ⟨M+5, by linarith, ?_⟩
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop x,
    logarithmicGrowth (h+1+b) (s := 1) (by norm_num),
    logarithmicGrowth b (s := 1) (by norm_num),
    logarithmicGrowth (b+1) (s := 1/2) (by norm_num)] with n hL hnx hnb hnb1 hnroot q r hq hqh hr
  change 1 ≤ Real.log n at hL
  change x ≤ (n : ℝ) at hnx
  have hn : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : 0 < Real.log n := by linarith
  have hQ : (q : ℝ) ≤ (Real.log n)^(h+1) := hqh.trans (by
    rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hL)
  have he := hs n q r hnx hq (by simpa only [Real.rpow_natCast] using hQ) hr
  rw [Real.rpow_neg hlog.le, Real.rpow_natCast, ← div_eq_mul_inv] at he
  apply he.trans
  have main : M * n / (Real.log n)^(b+1) ≤ M*n/(Real.log n)^b := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hL
  have hnat := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat,Real.logb] at hnat
  have h2 := Real.log_two_gt_d9
  have hnlog : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := hnat.trans ((div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [mul_nonneg hlog.le (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]))
  have hqlog := (Real.log_le_self (Nat.cast_nonneg q)).trans hqh
  have hq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have corr := mul_le_mul hnlog hqlog hq0 (by positivity)
  rw [Real.rpow_one] at hnb
  rw [← Real.sqrt_eq_rpow] at hnroot
  have ec : (Nat.log 2 n : ℝ)*Real.log q ≤ 2*n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (2 * Real.log n * (Real.log n)^h) * (Real.log n)^b := mul_le_mul_of_nonneg_right corr (by positivity)
      _ = 2 * (Real.log n)^(h+1+b) := by simp only [pow_add,pow_one]; ring
      _ ≤ _ := by linarith
  have er : 2 * Real.sqrt n * Real.log n ≤ 2*n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = 2 * Real.sqrt n * (Real.log n)^(b+1) := by rw [pow_succ]; ring
      _ ≤ 2 * Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hnroot (by positivity)
      _ = _ := by nlinarith only [Real.sq_sqrt hn.le]
  have e1 : (1:ℝ) ≤ n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa using hnb1
  calc
    _ ≤ M*n/(Real.log n)^b + 2*n/(Real.log n)^b + 2*n/(Real.log n)^b + n/(Real.log n)^b :=
      by linarith only [main, ec, er, e1]
    _ = _ := by ring

noncomputable def density (q r : ℕ) : ℝ := if r.Coprime q then 1/(q.totient:ℝ) else 0

private lemma density_range (q r : ℕ) (hq : 0<q) : 0 ≤ density q r ∧ density q r ≤ 1 := by
  have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold density
  split_ifs <;> constructor <;> first | positivity | exact (div_le_one (by linarith)).mpr hφ

theorem normalizedAP (h b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ q r : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log n)^h → r < q →
      |classMass (n+1) q r/(n:ℝ) - density q r| ≤ C/(Real.log n)^b := by
  obtain ⟨M,hM,he⟩ := uniformAll h b
  refine ⟨M+1,by linarith, ?_⟩
  filter_upwards [he,eventually_ge_atTop (2:ℕ), logarithmicGrowth b (s:=1) (by norm_num)] with n hn hn2 hg q r hq hqh hr
  have hb := hn q r hq hqh hr
  have hnR : (1:ℝ) < n := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos hnR
  have hrange := density_range q r hq
  have hid : classMass (n+1) q r/(n:ℝ) - density q r =
      (classError (n+1) q r + density q r)/n := by
    unfold density classError; split_ifs <;> push_cast <;> field_simp <;> ring
  rw [hid, abs_div, abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  have h1 : (1:ℝ) ≤ n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr; simpa using hg
  calc
    _ ≤ |classError (n+1) q r| + |density q r| := abs_add_le _ _
    _ ≤ M*n/(Real.log n)^b + n/(Real.log n)^b := add_le_add hb ((abs_of_nonneg hrange.1).le.trans (hrange.2.trans h1))
    _ = _ := by ring

end GoldbachBDHSW

end

section

namespace GoldbachBDH
open Finset GoldbachMajorArc GoldbachBDHSharp.OAI.Ostmann
noncomputable section

def spectrum (n d : ℕ) : ℝ := ∑ a ∈ num d, ‖primeSum n ((a:ℝ)/d)‖^2

lemma spectrum_nonneg (n d : ℕ) : 0 ≤ spectrum n d := sum_nonneg fun _ _ => sq_nonneg _

def weightEnergy (n : ℕ) : ℝ := ∑ k ∈ range (n+1), (primeWeight k)^2

lemma energy_bound (n : ℕ) (hn : 1≤n) : weightEnergy n ≤ Real.log 4 * n * Real.log n := by
  have hL := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
  have hpt (k : ℕ) (hk : k∈range (n+1)) : (primeWeight k)^2 ≤ primeWeight k*Real.log n := by
    unfold primeWeight
    split_ifs with hp
    · rw [sq]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show k≤n by simpa using hk)))
        (Real.log_nonneg (by exact_mod_cast hp.one_le))
    · simp
  have hs : (∑ k ∈ range (n+1), primeWeight k)=Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range,sum_filter]; rfl
  calc
    _ ≤ ∑ k ∈ range (n+1), primeWeight k*Real.log n := sum_le_sum hpt
    _ = Chebyshev.theta n*Real.log n := by rw [←sum_mul,hs]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) hL

lemma bounded_spectrum (n Y : ℕ) (hY : 0<Y) :
    (∑ d ∈ Icc 1 Y, spectrum n d) ≤ ((n:ℝ)+1+(Y:ℝ)^2)*weightEnergy n := by
  classical
  let pairs := (Icc 1 Y).sigma num
  let x : pairs → ℝ := fun p => (p.val.2:ℝ)/p.val.1
  let δ := 1/(Y:ℝ)^2
  have hd : 0<δ := by dsimp [δ]; positivity
  have hsep : CircleSeparated x δ := by
    rintro ⟨⟨d,a⟩,ha⟩ ⟨⟨e,b⟩,hb⟩ hne t
    obtain ⟨hd1,ha'⟩ := mem_sigma.mp ha
    obtain ⟨he1,hb'⟩ := mem_sigma.mp hb
    apply farey_sep Y a b d e (mem_Icc.mp hd1).1 (mem_Icc.mp hd1).2
      (mem_Icc.mp he1).1 (mem_Icc.mp he1).2 (mem_filter.mp ha').2 (mem_filter.mp hb').2 _ t
    by_contra! hh
    obtain ⟨de,numEq⟩ := hh
    rw [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha').1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hb').1)] at numEq
    subst e; change a=b at numEq; subst b; exact hne rfl
  have hs := separated_additive_sieve x δ hd hsep (n+1) 0 (fun k => (primeWeight k.val:ℂ))
  have hphase (k : Fin (n+1)) (p : pairs) :
      sieveHalfPhase (2*(0+(k.val:ℝ))*x p) = phase ((k.val:ℝ)*x p) := by
    unfold sieveHalfPhase phase; congr 2; ring
  simp_rw [hphase] at hs
  have hs1 (p : pairs) :
      (∑ k : Fin (n+1), (primeWeight k.val:ℂ)*phase ((k.val:ℝ)*x p))=primeSum n (x p) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => (primeWeight k:ℂ)*phase ((k:ℝ)*x p)) (n+1)
  simp_rw [hs1] at hs
  have he : (∑ k:Fin (n+1), ‖(primeWeight k.val:ℂ)‖^2) = weightEnergy n := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖(primeWeight k:ℂ)‖^2)]
    simp [weightEnergy,Real.norm_eq_abs]
  rw [he] at hs
  have hconst : (((n+1:ℕ):ℝ)+1/δ) = (n:ℝ)+1+(Y:ℝ)^2 := by dsimp [δ]; push_cast; field_simp
  rw [hconst] at hs
  calc
    _ = ∑ p ∈ pairs, ‖primeSum n ((p.2:ℝ)/p.1)‖^2 := by
      dsimp [spectrum,pairs]; rw [sum_sigma']
    _ = ∑ p : pairs, ‖primeSum n (x p)‖^2 := (sum_attach pairs _).symm
    _ ≤ _ := hs
end
end GoldbachBDH

end

section

namespace GoldbachBDH
open Finset
noncomputable section

/-- A cumulative large-sieve bound (x+y²)E implies the reciprocal-denominator
bound (x/T+2Y)E on T < d ≤ Y. Track the unused cumulative bound at each step. -/
theorem abel_bound (T Y : ℕ) (hT : 0<T) (hY : T≤Y) (x E : ℝ) (hE : 0≤E)
    (S : ℕ → ℝ) (hS : ∀ d,0≤S d)
    (hb : ∀ d, T≤d → (∑ i ∈ Icc 1 d, S i) ≤ (x+(d:ℝ)^2)*E) :
    (∑ d ∈ Ioc T Y, S d/(d:ℝ)) ≤ (x/T+2*(Y:ℝ))*E := by
  let slack := fun d : ℕ => (x+(d:ℝ)^2)*E - ∑ i ∈ Icc 1 d, S i
  have hs (d : ℕ) (hd : T≤d) : 0 ≤ slack d := sub_nonneg.mpr (hb d hd)
  have hinv : ∀ d : ℕ, T ≤ d →
      (∑ i ∈ Ioc T d,S i/(i:ℝ)) + slack d/d ≤ (x/T+2*(d:ℝ))*E := by
    intro d hd
    induction d,hd using Nat.le_induction with
    | base =>
      rw [Ioc_self,sum_empty,zero_add]
      have hTr : (0:ℝ)<T := by exact_mod_cast hT
      apply (div_le_iff₀ hTr).mpr
      dsimp [slack]
      have hn := sum_nonneg (s:=Icc 1 T) (fun i _ => hS i)
      have hsq : 0 ≤ (T:ℝ)^2 * E := mul_nonneg (sq_nonneg _) hE
      rw [add_mul,add_mul]
      field_simp
      nlinarith only [hn,hsq,mul_nonneg hTr.le (add_nonneg hn hsq)]
    | succ d hd ih =>
      have hdr : (0:ℝ)<d := by exact_mod_cast hT.trans_le hd
      have had : (∑ i ∈ Ioc T (d+1),S i/(i:ℝ)) =
          (∑ i ∈ Ioc T d,S i/(i:ℝ)) + S (d+1)/(d+1:ℕ) := by rw [show Ioc T (d+1) = insert (d+1) (Ioc T d) by ext k; simp; omega,sum_insert (by simp)]; ring
      have hcum : (∑ i ∈ Icc 1 (d+1),S i)=(∑ i ∈ Icc 1 d,S i)+S (d+1) := by
        rw [show Icc 1 (d+1) = insert (d+1) (Icc 1 d) by ext k; simp; omega,sum_insert (by simp)]; ring
      have hstep : S (d+1)+slack (d+1)=slack d+(2*(d:ℝ)+1)*E := by
        dsimp [slack]; rw [hcum]; push_cast; ring
      have h1 : slack d/((d:ℝ)+1) ≤ slack d/d := div_le_div_of_nonneg_left (hs d hd) hdr (by linarith)
      have h2 : ((2*(d:ℝ)+1)*E)/((d:ℝ)+1) ≤ 2*E := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hE])
      rw [had]
      push_cast
      calc
        _ = (∑ i ∈ Ioc T d,S i/(i:ℝ)) + (S (d+1)+slack (d+1))/((d:ℝ)+1) := by ring
        _ = (∑ i ∈ Ioc T d,S i/(i:ℝ)) + (slack d/((d:ℝ)+1) + ((2*(d:ℝ)+1)*E)/((d:ℝ)+1)) := by rw [hstep,add_div]
        _ ≤ (∑ i ∈ Ioc T d,S i/(i:ℝ)) + slack d/d + 2*E := by linarith only [h1,h2]
        _ ≤ _ := by linarith only [ih]
  exact (le_add_of_nonneg_right (div_nonneg (hs Y hY) (Nat.cast_nonneg Y))).trans (hinv Y hY)
end
end GoldbachBDH

end

section

namespace GoldbachBDH
open Finset GoldbachMajorArc
noncomputable section

def dev (n q r : ℕ) : ℝ := classMass (n+1) q r - if r.Coprime q then (n:ℝ)/q.totient else 0

def variance (n q : ℕ) : ℝ := ∑ r ∈ range q, (dev n q r)^2

def diff (n q a : ℕ) : ℂ := primeSum n ((a:ℝ)/q) - (n:ℂ)*unitMean q a

def freqEnergy (n d : ℕ) : ℝ := ∑ b ∈ num d, ‖diff n d b‖^2

lemma transform (n q a : ℕ) (hq : 0<q) : diff n q a =
    ∑ r ∈ range q, (dev n q r:ℂ)*phase ((r:ℝ)*((a:ℝ)/q)) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hmass : primeSum n ((a:ℝ)/q) =
      ∑ r ∈ range q, (classMass (n+1) q r:ℂ)*phase ((r:ℝ)*((a:ℝ)/q)) := by
    unfold primeSum
    rw [←sum_fiberwise_of_maps_to (t:=range q) (fun i (_ : i∈range (n+1)) => mem_range.mpr (Nat.mod_lt i hq))]
    apply sum_congr rfl
    intro r _
    unfold classMass
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    have hm := (mem_filter.mp hk).2
    rw [phase_residue,phase_residue,←hm,ZMod.natCast_mod]
  have hmean : (n:ℂ)*unitMean q a =
      ∑ r ∈ range q, (((if r.Coprime q then (n:ℝ)/q.totient else 0):ℝ):ℂ)*phase ((r:ℝ)*((a:ℝ)/q)) := by
    unfold unitMean
    rw [show (n:ℂ)*((∑ r ∈ (range q).filter (fun k => k.Coprime q), phase ((r:ℝ)*((a:ℝ)/q)))/(q.totient:ℂ))
      = ((n:ℂ)/q.totient)*(∑ r ∈ (range q).filter (fun k=>k.Coprime q),phase ((r:ℝ)*((a:ℝ)/q))) by ring]
    rw [mul_sum,sum_filter]
    apply sum_congr rfl
    intro r _
    split_ifs <;> push_cast <;> ring
  unfold diff
  rw [hmass,hmean,←sum_sub_distrib]
  apply sum_congr rfl
  intro r _; unfold dev; push_cast; ring

lemma parseval_dev (n q : ℕ) (hq : 0<q) :
    variance n q = (∑ a ∈ range q, ‖diff n q a‖^2)/(q:ℝ) := by
  let Z := fun a : ℕ => ∑ r ∈ range q, (dev n q r:ℂ)*phase ((a:ℝ)*r/q)
  have he : (∑ a ∈ range q, ‖Z a‖^2) = (q:ℝ)*∑ r ∈ range q, ‖(dev n q r:ℂ)‖^2 :=
    GoldbachBDH.parseval q (fun r => (dev n q r:ℂ))
  have hZ (a : ℕ) : Z a = diff n q a := by
    rw [transform n q a hq]
    apply sum_congr rfl
    intro r _
    exact congrArg ((dev n q r:ℂ)*·) (congrArg phase (by ring))
  simp_rw [hZ] at he
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs] at he
  apply (eq_div_iff (by exact_mod_cast hq.ne')).mpr
  rw [mul_comm]
  exact he.symm

lemma freq_reduce (n d b k : ℕ) (hd : 0<d) (hk : 0<k) :
    diff n (d*k) (b*k) = diff n d b := by
  unfold diff
  rw [unitMean_lift d k b hd hk]
  congr 2
  push_cast
  field_simp

lemma variance_reduced (n q : ℕ) (hq : 0<q) :
    variance n q = (∑ d ∈ q.divisors, freqEnergy n d)/(q:ℝ) := by
  rw [parseval_dev n q hq,all_frequencies q hq]
  apply congrArg (· / (q:ℝ))
  apply sum_congr rfl
  intro d hd
  unfold freqEnergy
  apply sum_congr rfl
  intro b _
  have hdq := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hk := Nat.div_pos (Nat.le_of_dvd hq hdq) hdpos
  have h := freq_reduce n d b (q/d) hdpos hk
  rw [Nat.mul_div_cancel' hdq] at h
  rw [h]

lemma var_total (n Q : ℕ) (hQ : 0<Q) :
    (∑ q ∈ Ioc Q (2*Q), variance n q) ≤ ∑ d ∈ Icc 1 (2*Q), 2/(d:ℝ)*freqEnergy n d := by
  calc
    _ = ∑ q ∈ Ioc Q (2*Q), (∑ d ∈ q.divisors,freqEnergy n d)/(q:ℝ) := by
      apply sum_congr rfl
      exact fun q hq => variance_reduced n q (hQ.trans (mem_Ioc.mp hq).1)
    _ ≤ _ := aggregate Q hQ _ (fun d => sum_nonneg fun b _ => sq_nonneg _)
end
end GoldbachBDH

end

section

namespace GoldbachBDH
open Finset Filter GoldbachMajorArc
open scoped Topology
noncomputable section

lemma logrange_deviation (h b : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0<q → (q:ℝ) ≤ (Real.log n)^h →
      ∀ r<q, |dev n q r| ≤ C*n/(Real.log n)^b := by
  obtain ⟨C,hC,he⟩ := GoldbachBDHSW.normalizedAP h b
  refine ⟨C,hC,?_⟩
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with n hn hn1 q hq hqh r hr
  have h := hn q r hq hqh hr
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn1
  have hid : classMass (n+1) q r/n-GoldbachBDHSW.density q r=dev n q r/n := by
    unfold GoldbachBDHSW.density dev
    split_ifs <;> field_simp <;> ring
  rw [hid,abs_div,abs_of_pos hn0] at h
  exact ((div_le_iff₀ hn0).mp h).trans_eq (by ring)

lemma low_frequency (n d : ℕ) (hd : 0<d) (B : ℝ) (hB : 0≤B)
    (hm : ∀ r<d, |dev n d r|≤B) : freqEnergy n d ≤ (d:ℝ)^3 * B^2 := by
  have hf (a : ℕ) : ‖diff n d a‖ ≤ d*B := by
    rw [transform n d a hd]
    calc
      _ ≤ ∑ r ∈ range d, ‖(dev n d r:ℂ)*phase ((r:ℝ)*(a/d))‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ range d, B := by
        apply sum_le_sum
        intro r hr
        rw [norm_mul, show ‖phase ((r:ℝ)*((a:ℝ)/d))‖ = 1 by exact Complex.norm_exp_ofReal_mul_I _, mul_one, Complex.norm_real,Real.norm_eq_abs]
        exact hm r (mem_range.mp hr)
      _ = _ := by simp
  calc
    _ ≤ ∑ _ ∈ num d, ((d:ℝ)*B)^2 :=
      sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hf a) 2
    _ = (d.totient:ℝ)*((d:ℝ)*B)^2 := by simp [num_card]
    _ ≤ (d:ℝ)*((d:ℝ)*B)^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast d.totient_le) (sq_nonneg _)
    _ = _ := by ring

lemma high_frequency (n d : ℕ) (hd : 0<d) :
    freqEnergy n d ≤ 2*spectrum n d + 2*(n:ℝ)^2/d.totient := by
  have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  calc
    _ ≤ ∑ a ∈ num d, (2*‖primeSum n ((a:ℝ)/d)‖^2 + 2*((n:ℝ)/d.totient)^2) := by
      apply sum_le_sum
      intro a ha
      have h := norm_sub_le (primeSum n ((a:ℝ)/d)) ((n:ℂ)*unitMean d a)
      have hc := norm_unitMean_le_inv_totient (mem_filter.mp ha).2
      rw [norm_mul,Complex.norm_natCast] at h
      have h' : ‖diff n d a‖ ≤ ‖primeSum n ((a:ℝ)/d)‖+n/d.totient := by
        apply h.trans; apply add_le_add_right
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α:=ℝ) n)
      have hz := pow_le_pow_left₀ (norm_nonneg _) h' 2
      nlinarith only [hz,sq_nonneg (‖primeSum n ((a:ℝ)/d)‖-n/d.totient)]
    _ = _ := by rw [sum_add_distrib,←mul_sum,sum_const,num_card,nsmul_eq_mul]; unfold spectrum; field_simp

set_option maxHeartbeats 1200000 in
theorem block_bound (n Q T : ℕ) (hQ : 0<Q) (hT : 0<T) (htY : T≤2*Q)
    (B : ℝ) (hB : 0≤B) (hsmall : ∀ d∈Icc 1 T, ∀ r<d, |dev n d r|≤B) :
    (∑ q ∈ Ioc Q (2*Q), variance n q) ≤
      2*(T:ℝ)^4*B^2 + 4*(((n:ℝ)+1)/T+2*(2*Q:ℕ))*weightEnergy n +
      4*(n:ℝ)^2/T*(1+Real.log (2*Q:ℕ))^2 := by
  let L := Icc 1 T; let H := Ioc T (2*Q)
  have hTr : 0<(T:ℝ) := by exact_mod_cast hT
  have hE : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
  have hlow : (∑ d ∈ L, 2/(d:ℝ)*freqEnergy n d) ≤ 2*(T:ℝ)^4*B^2 := by
    calc
      _ ≤ ∑ _d ∈ L, 2*((T:ℝ)^3*B^2) := by
        apply sum_le_sum
        intro d hd
        have hdR : (1:ℝ)≤d := by exact_mod_cast (mem_Icc.mp hd).1
        have h2 : (2:ℝ)/d≤2 := div_le_self (by norm_num) hdR
        have hs := low_frequency n d (mem_Icc.mp hd).1 B hB (hsmall d hd)
        apply mul_le_mul h2 (hs.trans _) (sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (mem_Icc.mp hd).2) 3) (sq_nonneg _)
      _ = _ := by simp [L,Nat.card_Icc]; ring
  have hhigh : (∑ d ∈ H, 2/(d:ℝ)*freqEnergy n d) ≤
      4*(((n:ℝ)+1)/T+2*(2*Q:ℕ))*weightEnergy n + 4*(n:ℝ)^2/T*(1+Real.log (2*Q:ℕ))^2 := by
    have hS := abel_bound T (2*Q) hT htY ((n:ℝ)+1) (weightEnergy n) hE (spectrum n) (spectrum_nonneg n)
      (fun d hd => bounded_spectrum n d (hT.trans_le hd))
    have hsub : H ⊆ Icc 1 (2*Q) := by
      intro d hd
      exact mem_Icc.mpr ⟨hT.trans_le (mem_Ioc.mp hd).1.le,(mem_Ioc.mp hd).2⟩
    have hφ : (∑ d ∈ H, 1/(d.totient:ℝ)) ≤ (1+Real.log (2*Q:ℕ))^2 := by
      apply le_trans _ (GoldbachEstermann.sum_inv_totient_le (2*Q))
      exact sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    calc
      _ ≤ ∑ d ∈ H, (4*(spectrum n d/d) + (4*(n:ℝ)^2/T)*(1/(d.totient:ℝ))) := by
        apply sum_le_sum
        intro d hd
        have hdR : (T:ℝ)≤d := by exact_mod_cast (mem_Ioc.mp hd).1.le
        have he := high_frequency n d (hT.trans (mem_Ioc.mp hd).1)
        have hweight := one_div_le_one_div_of_le hTr hdR
        calc
          _ ≤ 2/(d:ℝ)*(2*spectrum n d + 2*(n:ℝ)^2/d.totient) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = 4*(spectrum n d/d)+(4*(n:ℝ)^2*(1/(d.totient:ℝ)))*(1/d) := by ring
          _ ≤ 4*(spectrum n d/d)+(4*(n:ℝ)^2*(1/(d.totient:ℝ)))*(1/T) :=
            by gcongr
          _ = _ := by ring
      _ = 4*(∑ d∈H, spectrum n d/d)+(4*(n:ℝ)^2/T)*(∑ d∈H,1/(d.totient:ℝ)) := by rw [sum_add_distrib,←mul_sum,←mul_sum]
      _ ≤ _ := by nlinarith only [hS,hφ,mul_le_mul_of_nonneg_left hφ (show 0 ≤ 4*(n:ℝ)^2/T by positivity)]
  have hunion : (Icc 1 (2*Q)) = L∪H := by ext d; simp [L,H]; omega
  have hdis : Disjoint L H := disjoint_left.mpr fun d hd h => (mem_Ioc.mp h).1.not_ge (mem_Icc.mp hd).2
  apply (var_total n Q hQ).trans
  rw [hunion,sum_union hdis]
  linarith only [hlow,hhigh]
end
end GoldbachBDH

end

section

namespace GoldbachBDH
open Filter Finset GoldbachMajorArc
open scoped Topology
noncomputable section

lemma logs32 :
    ∀ᶠ n : ℕ in atTop, 512*(Real.log n)^32 ≤ (n:ℝ) := by
  have hh : Tendsto (fun n : ℕ => (Real.log n)^32/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop ((32:ℕ):ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [(tendsto_order.mp hh).2 (1/512) (by norm_num),eventually_ge_atTop (1:ℕ)] with n hn hn1
  have h := (div_lt_iff₀ (show 0<(n:ℝ) by exact_mod_cast hn1)).mp hn
  linarith

private lemma natlog2_bd (n : ℕ) (hn : 1≤n) :
    (Nat.log 2 n:ℝ) ≤ 2*Real.log n := by
  have hL := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
  have h2 := Real.log_two_gt_d9
  have h := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat,Real.logb] at h
  exact h.trans ((div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]))

theorem calibrated :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ n : ℕ in atTop,
      let Q := n/(Nat.log 2 n)^8
      (∑ q ∈ Ioc Q (2*Q), variance n q) ≤ K*n*Q*Real.log n := by
  obtain ⟨C,hC,hdev⟩ := logrange_deviation 24 80
  let K := 1024*C^2 + (4*2052)*Real.log 4 + 36864
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  have hlt := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hdev,logs32,hlt.eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with n hdevn h32 hlog hn
  intro Q
  let l := Real.log n
  let D := (Nat.log 2 n)^8
  let T := ⌊l^24⌋₊
  change 2 ≤ l at hlog
  change 512*l^32 ≤ (n:ℝ) at h32
  have h1 : 1≤l := by linarith
  have hl : 0<l := by linarith
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have h8 : (D:ℝ)≤256*l^8 := by
    dsimp [D]; push_cast
    calc
      _ ≤ (2*l)^8 := pow_le_pow_left₀ (Nat.cast_nonneg _) (natlog2_bd n (by omega)) _
      _ = _ := by ring
  have h8le : l^8 ≤ l^32 := pow_le_pow_right₀ h1 (by norm_num)
  have hdpos : 0<D := Nat.pow_pos (Nat.log_pos (by norm_num) hn)
  have hD : D≤n := by exact_mod_cast (show (D:ℝ)≤n by linarith only [h8,h8le,h32,pow_nonneg hl.le 8])
  have hQ : 0<Q := Nat.div_pos hD hdpos
  have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hnQ : (n:ℝ) ≤ 512*(Q:ℝ)*l^8 := by
    have hnlt : n < (Q+1)*D := (Nat.div_lt_iff_lt_mul hdpos).mp (Nat.lt_succ_self Q)
    have hh : (n:ℝ) ≤ ((Q:ℝ)+1)*D := by exact_mod_cast hnlt.le
    apply hh.trans
    calc _ ≤ (2*(Q:ℝ))*(256*l^8) := mul_le_mul (by linarith) h8 (Nat.cast_nonneg _) (by positivity)
         _ = _ := by ring
  have hTup : (T:ℝ) ≤ l^24 := Nat.floor_le (by positivity)
  have hTlo : l^24 ≤ 2*(T:ℝ) := by
    have h := Nat.lt_floor_add_one (l^24)
    have h2 : 2≤l^24 := hlog.trans (by simpa using (pow_le_pow_right₀ h1 (show 1≤24 by norm_num)))
    change l^24 < (T:ℝ)+1 at h
    linarith
  have hT : 0<T := by
    have hp : 0<(T:ℝ) := by linarith only [hTlo,pow_pos hl 24]
    exact_mod_cast hp
  have hTQ : T≤2*Q := by
    have hcmp : l^24 ≤ (Q:ℝ) := by
      have h := h32.trans hnQ
      rw [show l^32=l^24*l^8 by ring] at h
      exact (le_of_mul_le_mul_right (by nlinarith only [h] : l^24*l^8 ≤ (Q:ℝ)*l^8) (pow_pos hl 8))
    exact_mod_cast (show (T:ℝ)≤2*Q by linarith [hTup,hcmp])
  have hTr : 0<(T:ℝ) := by exact_mod_cast hT
  let B := C*n/l^80
  have hfin := block_bound n Q T hQ hT hTQ B (by dsimp [B];positivity) (fun d hd r hr =>
    hdevn d (mem_Icc.mp hd).1 ((show (d:ℝ)≤T by exact_mod_cast (mem_Icc.mp hd).2).trans hTup) r hr)
  have hlepow (a b : ℕ) (hab : a≤b) : l^a≤l^b := pow_le_pow_right₀ h1 hab
  have hscaled (k : ℕ) (hk : 8≤k) : (n:ℝ) ≤ 512*(Q:ℝ)*l^k :=
    hnQ.trans (mul_le_mul_of_nonneg_left (hlepow 8 k hk) (by positivity))
  have hsmall : 2*(T:ℝ)^4*B^2 ≤ 1024*C^2*n*Q*l := by
    calc
      _ ≤ 2*(l^24)^4*B^2 := by gcongr
      _ = (2*C^2*n)*(n/l^64) := by dsimp [B]; field_simp
      _ ≤ (2*C^2*n)*(512*Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_iff₀ (pow_pos hl _)).mpr (hscaled 64 (by norm_num))
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0≤1024*C^2*n*Q by positivity) (sub_nonneg.mpr h1)]
  have hmid : ((n:ℝ)+1)/T ≤ 2048*Q := by
    apply (div_le_iff₀ hTr).mpr
    have h24 := hscaled 24 (by norm_num)
    have hTall := mul_le_mul_of_nonneg_left hTlo (show 0≤512*(Q:ℝ) by positivity)
    nlinarith only [hn1,h24,hTall]
  have hmiddle : 4*(((n:ℝ)+1)/T+2*(2*Q:ℕ))*weightEnergy n ≤ (4*2052)*Real.log 4*n*Q*l := by
    have hE := energy_bound n (by omega)
    have hEn : 0≤weightEnergy n := sum_nonneg fun _ _ => sq_nonneg _
    have hu : ((n:ℝ)+1)/T+2*(2*Q:ℕ) ≤ 2052*Q := by push_cast; linarith only [hmid]
    calc
      _ ≤ (4*(2052*Q))*(Real.log 4*n*l) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hE hEn (by positivity)
      _ = _ := by ring
  have hQn : Q≤n := Nat.div_le_self _ _
  have hYlog : 1+Real.log (2*Q:ℕ) ≤ 3*l := by
    have hy : (0:ℝ)<((2*Q:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0<2) hQ
    have hlarg : ((2*Q:ℕ):ℝ) ≤ (n:ℝ)^2 := by
      have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
      have hqn : (Q:ℝ)≤n := by exact_mod_cast hQn
      push_cast; nlinarith only [hqn,mul_nonneg hn0.le (sub_nonneg.mpr hn2)]
    have h := Real.log_le_log hy hlarg
    rw [Real.log_pow] at h
    change 1+Real.log (2*Q:ℕ) ≤ 3*Real.log n
    dsimp [l] at hlog; norm_num1 at h; linarith only [h,hlog]
  have hYpos : 0≤1+Real.log (2*Q:ℕ) := by
    have hp : (1:ℝ)≤((2*Q:ℕ):ℝ) := by exact_mod_cast (show 1≤2*Q by omega)
    linarith [Real.log_nonneg hp]
  have hlast : 4*(n:ℝ)^2/T*(1+Real.log (2*Q:ℕ))^2 ≤ 36864*n*Q*l := by
    have h2 : 1/(T:ℝ) ≤ 2/l^24 := (div_le_div_iff₀ hTr (pow_pos hl _)).mpr (by linarith only [hTlo])
    calc
      _ ≤ (4*(n:ℝ)^2*(2/l^24))*(3*l)^2 := by
        rw [div_eq_mul_one_div (4*(n:ℝ)^2)]
        gcongr
      _ = (72*n)*(n/l^22) := by field_simp; ring
      _ ≤ (72*n)*(512*Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_iff₀ (pow_pos hl _)).mpr (hscaled 22 (by norm_num))
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0≤36864*(n:ℝ)*Q by positivity) (sub_nonneg.mpr h1)]
  apply hfin.trans
  dsimp [K]
  nlinarith only [hsmall,hmiddle,hlast]
end
end GoldbachBDH

end

section

namespace GoldbachProjectionBDH
open Finset Filter GoldbachMajorArc GoldbachBDH
open scoped Topology
noncomputable section
open Finset

private def fiber (N q r : ℕ) := (range N).filter (fun k => k % q = r)

private lemma fiber_card_exact (N q r : ℕ) (hq : 0<q) (hr : r<q) :
    (fiber N q r).card = N/q + if r < N % q then 1 else 0 := by
  have he := Nat.count_modEq_card_eq_ceil N hq r
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hr] at he
  have hf : (range N).filter (fun k => k ≡ r [MOD q]) = fiber N q r := by
    ext k; simp [fiber, Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [hf] at he
  have hrQ : (r:ℚ)<q := by exact_mod_cast hr
  have hqQ : 0<(q:ℚ) := by exact_mod_cast hq
  have hm : ((N % q : ℕ):ℚ)<q := by exact_mod_cast Nat.mod_lt N hq
  have hde : (N:ℚ) = (q:ℚ)*((N/q : ℕ):ℚ) + ((N % q:ℕ):ℚ) := by
    exact_mod_cast (Nat.div_add_mod N q).symm
  have hval : ((N:ℚ)-r)/q = (((N % q:ℕ):ℚ)-r)/q + ((N/q:ℕ):ℚ) := by rw [hde]; field_simp; ring
  rw [hval, Int.ceil_add_natCast] at he
  split_ifs with h
  · have h0 : (0:ℚ)<(((N % q:ℕ):ℚ)-r)/q := div_pos (sub_pos.mpr (by exact_mod_cast h)) hqQ
    have h1 : (((N % q:ℕ):ℚ)-r)/q ≤ 1 := (div_le_one hqQ).mpr (by linarith [Nat.cast_nonneg (α:=ℚ) r])
    have hc : ⌈(((N % q:ℕ):ℚ)-r)/q⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by norm_num; exact h0,h1⟩
    rw [hc] at he
    omega
  · have h1 : (((N % q:ℕ):ℚ)-r)/q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast le_of_not_gt h)) hqQ.le
    have h0 : -1 < (((N % q:ℕ):ℚ)-r)/q := (lt_div_iff₀ hqQ).mpr (by linarith [Nat.cast_nonneg (α:=ℚ) (N % q)])
    have hc : ⌈(((N % q:ℕ):ℚ)-r)/q⌉ = 0 := Int.ceil_eq_zero_iff.mpr ⟨h0,h1⟩
    rw [hc] at he
    omega

private lemma fiber_error (N q r : ℕ) (hq : 0<q) (hr : r<q) :
    |((fiber N q r).card : ℝ)*q - N| ≤ q := by
  have he : (N:ℝ) = (q:ℝ)*((N/q : ℕ):ℝ) + ((N % q:ℕ):ℝ) := by exact_mod_cast (Nat.div_add_mod N q).symm
  have hm : ((N % q:ℕ):ℝ) < q := by exact_mod_cast Nat.mod_lt N hq
  have hz := Nat.cast_nonneg (α:=ℝ) (N % q)
  rw [fiber_card_exact N q r hq hr]
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> nlinarith only [he,hm.le,hz]

private lemma fiber_large (n q r : ℕ) (hq : 0<q) (hr : r<q) (hsize : 2*q≤n) :
    (n:ℝ) ≤ 2*((fiber (n+1) q r).card:ℝ)*q := by
  have hN : q ≤ n+1 := by omega
  have h1 : 1 ≤ (n+1)/q := (Nat.le_div_iff_mul_le hq).2 (by simpa)
  have hd : (n+1)/q ≤ (fiber (n+1) q r).card := by rw [fiber_card_exact _ _ _ hq hr]; omega
  have hc : (1:ℝ) ≤ (fiber (n+1) q r).card := by exact_mod_cast h1.trans hd
  have he := (abs_le.mp (fiber_error (n+1) q r hq hr)).1
  push_cast at he
  nlinarith only [he, mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg (α:=ℝ) q)]

def unitModel (q r : ℕ) : ℝ := if r.Coprime q then (q:ℝ)/q.totient else 0
def residual (n q r : ℕ) : ℝ := classMass (n+1) q r - ((fiber (n+1) q r).card:ℝ)*unitModel q r
def energy (n q : ℕ) : ℝ := ∑ r ∈ range q, (residual n q r)^2/((fiber (n+1) q r).card:ℝ)

lemma ratio_bound (q : ℕ) (hq : 0<q) :
    (q:ℝ)/q.totient ≤ (1+Real.log q)^2 := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hgauss : (q:ℝ) = ∑ d ∈ q.divisors, (d.totient:ℝ) := by exact_mod_cast (Nat.sum_totient q).symm
  calc
    _ = ∑ d ∈ q.divisors, (d.totient:ℝ)/q.totient := by rw [←sum_div, ←hgauss]
    _ ≤ ∑ d ∈ q.divisors, 1/((q/d).totient:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hdq := Nat.dvd_of_mem_divisors hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hk := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
      have hφk : (0:ℝ)<(q/d).totient := by exact_mod_cast Nat.totient_pos.mpr hk
      have hh := Nat.totient_super_multiplicative d (q/d)
      rw [Nat.mul_div_cancel' hdq] at hh
      apply (div_le_div_iff₀ hφ hφk).mpr; simpa using (show (d.totient:ℝ)*((q/d).totient:ℝ)≤q.totient by exact_mod_cast hh)
    _ = ∑ d ∈ q.divisors, 1/(d.totient:ℝ) := Nat.sum_div_divisors q (fun d => 1/(d.totient:ℝ))
    _ ≤ ∑ d ∈ Icc 1 q, 1/(d.totient:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun d hd => mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
      · intros; positivity
    _ ≤ _ := GoldbachEstermann.sum_inv_totient_le q

lemma energy_one (n q : ℕ) (hq : 0<q) (hs : 2*q≤n) :
    energy n q ≤ (2*(q:ℝ)/n)*(2*variance n q+8*(q:ℝ)*((q:ℝ)/q.totient)^2) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hsq (r : ℕ) (hr : r∈range q) :
      (residual n q r)^2 ≤ 2*(dev n q r)^2 + 8*((q:ℝ)/q.totient)^2 := by
    have hab := abs_le.mp (fiber_error (n+1) q r hq (mem_range.mp hr))
    push_cast at hab
    let a := classMass (n+1) q r
    let c := ((fiber (n+1) q r).card:ℝ)
    have hraw : |(n:ℝ)-c*q| ≤ 2*q := abs_le.mpr ⟨by dsimp [c]; linarith only [hab.2,hq1],
      by dsimp [c]; linarith only [hab.1,hq1]⟩
    by_cases hc : r.Coprime q
    · have h : |(n:ℝ)/q.totient - c*((q:ℝ)/q.totient)| ≤ 2*((q:ℝ)/q.totient) := by
        rw [←mul_div_assoc,←sub_div, abs_div,abs_of_pos hφ, ←mul_div_assoc]
        exact div_le_div_of_nonneg_right hraw hφ.le
      have hs' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
      rw [sq_abs] at hs'
      change (a - c * unitModel q r)^2 ≤ 2*(a - (if r.Coprime q then (n:ℝ)/q.totient else 0))^2 + _
      simp only [unitModel,ite_eq_left hc]
      nlinarith only [hs', sq_nonneg ((a - (n:ℝ)/q.totient) - ((n:ℝ)/q.totient-c*((q:ℝ)/q.totient)))]
    · simp only [residual,unitModel,dev,ite_eq_right hc,mul_zero,sub_zero]
      nlinarith only [sq_nonneg (classMass (n+1) q r),sq_nonneg ((q:ℝ)/q.totient)]
  have hfull (r : ℕ) (hr : r∈range q) : (residual n q r)^2/((fiber (n+1) q r).card:ℝ) ≤
      (2*(q:ℝ)/n)*(residual n q r)^2 := by
    have hlarge := fiber_large n q r hq (mem_range.mp hr) hs
    have hc : (0:ℝ)<(fiber (n+1) q r).card := by
      by_contra! hb
      nlinarith only [hlarge,hn0,mul_nonpos_of_nonpos_of_nonneg hb (Nat.cast_nonneg (α:=ℝ) q)]
    calc
      _ = (1/((fiber (n+1) q r).card:ℝ))*(residual n q r)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_div_iff₀ hc hn0).mpr (by linarith only [hlarge])) (sq_nonneg _)
  calc
    _ ≤ ∑ r ∈ range q, (2*(q:ℝ)/n)*(residual n q r)^2 := sum_le_sum hfull
    _ ≤ (2*(q:ℝ)/n)*(∑ r ∈ range q, (2*(dev n q r)^2+8*((q:ℝ)/q.totient)^2)) := by
      rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (sum_le_sum hsq) (by positivity)
    _ = _ := by rw [sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]; unfold variance; ring

lemma binary_scale (n : ℕ) (hn : 2 ≤ n) :
    let Q := n/(Nat.log 2 n)^8
    (Q:ℝ)*(Real.log n)^8 ≤ 256*n := by
  intro Q
  have hNat := Nat.lt_pow_succ_log_self (by norm_num : 1<2) n
  have hReal : (n:ℝ)<(2:ℝ)^((Nat.log 2 n)+1) := by exact_mod_cast hNat
  have hlog := Real.log_le_log (show 0<(n:ℝ) by exact_mod_cast (show 0<n by omega)) hReal.le
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have h1 : (1:ℝ) ≤ Nat.log 2 n := by exact_mod_cast Nat.log_pos (by norm_num : 1<2) hn
  have hL : Real.log n ≤ 2*(Nat.log 2 n:ℝ) := by
    nlinarith only [h1,hlog,Real.log_two_lt_d9,mul_nonneg (show 0≤(Nat.log 2 n:ℝ)+1 by positivity) (show 0≤1-Real.log 2 by linarith [Real.log_two_lt_d9])]
  have hpow := pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))) hL 8
  have hp : (Q:ℝ)*(Nat.log 2 n:ℝ)^8 ≤ n := by exact_mod_cast Nat.div_mul_le_self n ((Nat.log 2 n)^8)
  calc
    _ ≤ (Q:ℝ)*(2*(Nat.log 2 n:ℝ))^8 := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = 256*((Q:ℝ)*(Nat.log 2 n:ℝ)^8) := by ring
    _ ≤ _ := by linarith
end
end GoldbachProjectionBDH

end

section

namespace GoldbachProjectionBDH
open Finset Filter GoldbachBDH
open scoped Topology
noncomputable section

theorem energy_rate : ∃ K : ℝ, 0<K ∧ ∀ᶠ n : ℕ in atTop,
    let Q := n/(Nat.log 2 n)^8
    (∑ q ∈ Ioc Q (2*Q), energy n q) ≤ K*n*Q/(Real.log n)^5 := by
  obtain ⟨C,hC,hb⟩ := calibrated
  let K := 2048*C+64*(256:ℝ)^2*81
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hb,hlog.eventually_ge_atTop 4,eventually_ge_atTop (2:ℕ)] with n hbd hL hn
  intro Q
  let l := Real.log n
  change 4 ≤ l at hL
  have hpos : 0 < l := by linarith
  have h1 : 1≤l := by linarith
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change (∑ q ∈ Ioc Q (2*Q), variance n q) ≤ C*n*Q*l at hbd
  have hscale := binary_scale n hn
  change (Q:ℝ)*l^8 ≤ 256*n at hscale
  have hlim : 4*Q ≤ n := by
    have h8 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) hL 8
    norm_num1 at h8
    have hz := mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg (α:=ℝ) Q)
    exact_mod_cast (show (4:ℝ)*Q≤n by nlinarith only [hz,hscale,Nat.cast_nonneg (α:=ℝ) Q])
  have hQn : Q≤n := Nat.div_le_self _ _
  have hpoint (q : ℕ) (hq : q∈Ioc Q (2*Q)) :
      energy n q ≤ (8*(Q:ℝ)/n)*variance n q + 64*(Q:ℝ)^2/n*(3*l)^4 := by
    obtain ⟨hql,hqu⟩ := mem_Ioc.mp hq
    have hqp := (Nat.zero_le Q).trans_lt hql
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hqp
    have hquR : (q:ℝ)≤2*Q := by exact_mod_cast hqu
    have hr := ratio_bound q hqp
    have hql' := Real.log_nonneg hq1
    have hlogq : 1+Real.log q ≤ 3*l := by
      have hnn : (2:ℝ)≤n := by exact_mod_cast hn
      have hQnR : (Q:ℝ)≤n := by exact_mod_cast hQn
      have hq2 : (q:ℝ) ≤ (n:ℝ)^2 := by nlinarith only [hquR,hQnR,mul_nonneg hn0.le (sub_nonneg.mpr hnn)]
      have hh := Real.log_le_log (by linarith : (0:ℝ)<q) hq2
      rw [Real.log_pow] at hh; norm_num1 at hh; change 1+_≤3*Real.log n; dsimp [l] at hL; linarith
    have hR : ((q:ℝ)/q.totient)^2 ≤ (3*l)^4 := by
      calc
        _ ≤ ((1+Real.log q)^2)^2 := pow_le_pow_left₀ (by positivity) hr _
        _ ≤ ((3*l)^2)^2 := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (by positivity) hlogq 2) 2
        _ = _ := by ring
    have hv : 0≤variance n q := sum_nonneg fun _ _ => sq_nonneg _
    have he := energy_one n q hqp (by omega)
    apply he.trans
    calc
      _ ≤ (2*(2*Q:ℝ)/n)*(2*variance n q+8*(2*Q:ℝ)*(3*l)^4) := by gcongr
      _ = _ := by ring
  have hsum : (∑ q ∈ Ioc Q (2*Q), energy n q) ≤
      (8*(Q:ℝ)/n)*(C*n*Q*l) + 64*(Q:ℝ)^3/n*(3*l)^4 := by
    apply (sum_le_sum hpoint).trans
    rw [sum_add_distrib,←mul_sum,sum_const,Nat.card_Ioc,show 2*Q-Q=Q by omega,nsmul_eq_mul]
    calc
      _ ≤ (8*(Q:ℝ)/n)*(C*n*Q*l)+(Q:ℝ)*(64*(Q:ℝ)^2/n*(3*l)^4) :=
        by gcongr
      _ = _ := by ring
  have hpow (a b : ℕ) (hab : a≤b) : l^a≤l^b := pow_le_pow_right₀ h1 hab
  have hsmall : (Q:ℝ)*l^6 ≤ 256*n := (mul_le_mul_of_nonneg_left (hpow 6 8 (by norm_num)) (Nat.cast_nonneg _)).trans hscale
  have hs2 : (Q:ℝ)^2*l^9 ≤ 256^2*(n:ℝ)^2 := by
    calc
      _ ≤ (Q:ℝ)^2*l^16 := mul_le_mul_of_nonneg_left (hpow 9 16 (by norm_num)) (sq_nonneg _)
      _ = ((Q:ℝ)*l^8)^2 := by ring
      _ ≤ (256*(n:ℝ))^2 := pow_le_pow_left₀ (by positivity) hscale _
      _ = _ := by ring
  apply hsum.trans
  apply (le_div_iff₀ (pow_pos hpos _)).mpr
  have hh1 := mul_le_mul_of_nonneg_left hsmall (show 0≤8*C*(Q:ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hs2 (show 0≤64*81*(Q:ℝ) by positivity)
  dsimp [K]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_left hh1 hn0.le,hh2]
end
end GoldbachProjectionBDH

end

section

namespace GoldbachProjectionBDH.L2

open Finset

private def fiber (n q r : ℕ) := (range (n+1)).filter (fun k => k % q=r)
private def j (n q r : ℕ) := (n+q-r) % q

private lemma refl_mod {n q k : ℕ} (hq : 0<q) (hk : k≤n) :
    (n-k) % q = j n q (k % q) := by
  unfold j
  change n-k ≡ n+q-k % q [MOD q]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_sub hk, Nat.cast_sub (show k % q≤n+q by have := Nat.mod_lt k hq; omega)]
  push_cast; simp

private lemma refl_twice {n q r : ℕ} (hq : 0<q) (hr : r<q) : j n q (j n q r) = r := by
  unfold j
  apply Eq.trans _ (Nat.mod_eq_of_lt hr)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_sub (show (n+q-r) % q≤n+q by have := Nat.mod_lt (n+q-r) hq; omega)]
  simp only [ZMod.natCast_mod]
  rw [Nat.cast_sub (by omega : r≤n+q)]
  push_cast; ring

private lemma refl_member {n q r k : ℕ} (hq : 0<q) (hk : k∈fiber n q r) :
    n-k∈fiber n q (j n q r) := by
  obtain ⟨hkN,hkr⟩ := mem_filter.mp hk
  have hn : k≤n := by simpa using hkN
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (refl_mod hq hn).trans (by rw [hkr])⟩

private lemma refl_card (n q r : ℕ) (hq : 0<q) (hr : r<q) :
    (fiber n q r).card = (fiber n q (j n q r)).card := by
  apply card_nbij' (fun k => n-k) (fun k => n-k)
  · exact fun _ hk => refl_member hq hk
  · intro k hk
    change n-k ∈ fiber n q r
    simpa only [refl_twice hq hr] using refl_member hq hk
  · intro k hk
    apply Nat.sub_sub_self
    simpa using (mem_filter.mp hk).1
  · intro k hk
    apply Nat.sub_sub_self
    simpa using (mem_filter.mp hk).1

private lemma abs_dot (s : Finset ℕ) (x y : ℕ → ℝ) :
    |∑ i ∈ s, x i*y i| ≤ Real.sqrt ((∑ i ∈ s, (x i)^2)*(∑ i ∈ s, (y i)^2)) := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact sum_mul_sq_le_sq_mul_sq s x y

theorem transfer :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r) % q; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; let G := fun n q => ∑ r ∈ Finset.range q, A n q r*A n q (j n q r)/((F n q r).card:ℝ); let U := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*(μ q r)^2; let E := fun n q => ∑ r ∈ Finset.range q, (v n q r)^2/((F n q r).card:ℝ); let K := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*μ q r*μ q (j n q r); ∀ n q : ℕ, 0<q → |G n q-K n q| ≤ 2*Real.sqrt (U n q*E n q)+E n q := by
  intro F w A J μ v G U E K n q hq
  let c := fun r => ((F n q r).card:ℝ)
  let a := fun r => Real.sqrt (c r)*μ q r
  let b := fun r => v n q r/Real.sqrt (c r)
  let R := J n q
  let I := range q
  have hc (r : ℕ) : 0≤c r := Nat.cast_nonneg _
  have href (r : ℕ) (hr : r∈I) : c (R r) = c r := by
    change ((fiber n q (j n q r)).card:ℝ) = ((fiber n q r).card:ℝ)
    exact_mod_cast (refl_card n q r hq (mem_range.mp hr)).symm
  have perm (f : ℕ → ℝ) : (∑ r ∈ I,f (R r))=∑ r ∈ I,f r := by
    apply sum_nbij' R R
    · intro r _; exact mem_range.mpr (Nat.mod_lt _ hq)
    · intro r _; exact mem_range.mpr (Nat.mod_lt _ hq)
    · intro r hr; exact refl_twice hq (mem_range.mp hr)
    · intro r hr; exact refl_twice hq (mem_range.mp hr)
    · intros; rfl
  have ha : (∑ r ∈ I,(a r)^2)=U n q := by
    apply sum_congr rfl
    intro r _
    simp [a,mul_pow,Real.sq_sqrt (hc r),c]
  have hb : (∑ r ∈ I,(b r)^2)=E n q := by
    apply sum_congr rfl
    intro r _
    simp [b,div_pow,Real.sq_sqrt (hc r),c]
  have hu := abs_dot I a (fun r => b (R r))
  have hv := abs_dot I b (fun r => a (R r))
  have he := abs_dot I b (fun r => b (R r))
  rw [perm (fun r => (b r)^2),hb,ha] at hu
  rw [perm (fun r => (a r)^2),ha,hb,mul_comm (E n q) (U n q)] at hv
  rw [perm (fun r => (b r)^2),hb,←sq,Real.sqrt_sq (sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hc r))] at he
  have hform : G n q-K n q =
      (∑ r ∈ I,a r*b (R r)) + (∑ r ∈ I,b r*a (R r)) + ∑ r ∈ I,b r*b (R r) := by
    dsimp only [G,K]
    rw [←sum_sub_distrib,←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    change A n q r*A n q (R r)/c r - c r*μ q r*μ q (R r) =
      a r*b (R r)+b r*a (R r)+b r*b (R r)
    dsimp only [a,b]
    change _ = _ * ((A n q (R r) - c (R r)*μ q (R r))/Real.sqrt (c (R r))) +
      ((A n q r-c r*μ q r)/Real.sqrt (c r))*(Real.sqrt (c (R r))*μ q (R r)) +
      ((A n q r-c r*μ q r)/Real.sqrt (c r))*((A n q (R r)-c (R r)*μ q (R r))/Real.sqrt (c (R r)))
    rw [href r hr]
    by_cases h : c r=0
    · simp [h]
    · have hs : (Real.sqrt (c r))^2 = c r := Real.sq_sqrt (hc r)
      have hn := (Real.sqrt_pos.mpr (lt_of_le_of_ne (hc r) (Ne.symm h))).ne'
      have algebra (t x y u v : ℝ) (ht : t≠0) :
          x*y/t^2-t^2*u*v=t*u*((y-t^2*v)/t)+((x-t^2*u)/t)*(t*v)+((x-t^2*u)/t)*((y-t^2*v)/t) := by
        field_simp; ring
      simpa only [hs] using algebra (Real.sqrt (c r)) (A n q r) (A n q (R r)) (μ q r) (μ q (R r)) hn
  change |∑ i ∈ I,b i*b (R i)| ≤ E n q at he
  rw [hform]
  refine (abs_add_le _ _).trans ?_
  linarith only [abs_add_le (∑ r ∈ I,a r*b (R r)) (∑ r ∈ I,b r*a (R r)),hu,hv,he]

end GoldbachProjectionBDH.L2

namespace GoldbachProjectionBDH.Rounding

open Finset

private def fiber (N q r : ℕ) := (range N).filter (fun k => k % q = r)

private lemma fiber_card_exact (N q r : ℕ) (hq : 0<q) (hr : r<q) :
    (fiber N q r).card = N/q + if r < N % q then 1 else 0 := by
  have he := Nat.count_modEq_card_eq_ceil N hq r
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hr] at he
  have hf : (range N).filter (fun k => k ≡ r [MOD q]) = fiber N q r := by
    ext k; simp [fiber, Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [hf] at he
  have hrQ : (r:ℚ)<q := by exact_mod_cast hr
  have hqQ : 0<(q:ℚ) := by exact_mod_cast hq
  have hm : ((N % q : ℕ):ℚ)<q := by exact_mod_cast Nat.mod_lt N hq
  have hde : (N:ℚ) = (q:ℚ)*((N/q : ℕ):ℚ) + ((N % q:ℕ):ℚ) := by
    exact_mod_cast (Nat.div_add_mod N q).symm
  have hval : ((N:ℚ)-r)/q = (((N % q:ℕ):ℚ)-r)/q + ((N/q:ℕ):ℚ) := by rw [hde]; field_simp <;> ring
  rw [hval, Int.ceil_add_natCast] at he
  split_ifs with h
  · have h0 : (0:ℚ)<(((N % q:ℕ):ℚ)-r)/q := div_pos (sub_pos.mpr (by exact_mod_cast h)) hqQ
    have h1 : (((N % q:ℕ):ℚ)-r)/q ≤ 1 := (div_le_one hqQ).mpr (by linarith [Nat.cast_nonneg (α:=ℚ) r])
    have hc : ⌈(((N % q:ℕ):ℚ)-r)/q⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by norm_num; exact h0,h1⟩
    rw [hc] at he
    omega
  · have h1 : (((N % q:ℕ):ℚ)-r)/q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast le_of_not_gt h)) hqQ.le
    have h0 : -1 < (((N % q:ℕ):ℚ)-r)/q := (lt_div_iff₀ hqQ).mpr (by linarith [Nat.cast_nonneg (α:=ℚ) (N % q)])
    have hc : ⌈(((N % q:ℕ):ℚ)-r)/q⌉ = 0 := Int.ceil_eq_zero_iff.mpr ⟨h0,h1⟩
    rw [hc] at he
    omega

private lemma fiber_error (N q r : ℕ) (hq : 0<q) (hr : r<q) :
    |((fiber N q r).card : ℝ)*q - N| ≤ q := by
  have he : (N:ℝ) = (q:ℝ)*((N/q : ℕ):ℝ) + ((N % q:ℕ):ℝ) := by exact_mod_cast (Nat.div_add_mod N q).symm
  have hm : ((N % q:ℕ):ℝ) < q := by exact_mod_cast Nat.mod_lt N hq
  have hz := Nat.cast_nonneg (α:=ℝ) (N % q)
  rw [fiber_card_exact N q r hq hr]
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> nlinarith only [he,hm.le,hz]

private lemma fiber_large (n q r : ℕ) (hq : 0<q) (hr : r<q) (hsize : 2*q≤n) :
    (n:ℝ) ≤ 2*((fiber (n+1) q r).card:ℝ)*q := by
  have hN : q ≤ n+1 := by omega
  have h1 : 1 ≤ (n+1)/q := (Nat.le_div_iff_mul_le hq).2 (by simpa)
  have hd : (n+1)/q ≤ (fiber (n+1) q r).card := by rw [fiber_card_exact _ _ _ hq hr]; omega
  have hc : (1:ℝ) ≤ (fiber (n+1) q r).card := by exact_mod_cast h1.trans hd
  have he := (abs_le.mp (fiber_error (n+1) q r hq hr)).1
  push_cast at he
  nlinarith only [he, mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg (α:=ℝ) q)]

theorem singular :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let j := fun n q r : ℕ => (n+q-r) % q; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let K := fun n q => ∑ r ∈ Finset.range q, ((F n q r).card:ℝ)*μ q r*μ q (j n q r); let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n q : ℕ, 0<q → |K n q - ((n+1:ℕ):ℝ)*(q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2| ≤ ((q:ℝ)/(q.totient:ℝ))^2*(R n q:ℝ) := by
  intro F j μ K R n q hq
  let U := (range q).filter (fun r => r.Coprime q ∧ (j n q r).Coprime q)
  let z := (q:ℝ)/q.totient
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq
  have lhs : K n q = ∑ r ∈ U, ((F n q r).card:ℝ)*z^2 := by
    dsimp only [K,U]
    rw [sum_filter]
    apply sum_congr rfl
    intro r _
    unfold μ z
    split_ifs <;> simp_all <;> ring
  have rhs : ((n+1:ℕ):ℝ)*q*(R n q:ℝ)/(q.totient:ℝ)^2 = ∑ _r ∈ U, (((n+1:ℕ):ℝ)/q)*z^2 := by
    rw [sum_const,nsmul_eq_mul]
    change _ = (R n q:ℝ)*((((n+1:ℕ):ℝ)/q)*z^2)
    dsimp [z]
    field_simp <;> ring
  rw [lhs,rhs,←sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ U, |((F n q r).card:ℝ)*z^2-(((n+1:ℕ):ℝ)/q)*z^2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ U, z^2 := by
      apply sum_le_sum
      intro r hr
      have h := fiber_error (n+1) q r hq (mem_range.mp (mem_filter.mp hr).1)
      change |((F n q r).card:ℝ)*q-((n+1:ℕ):ℝ)| ≤ q at h
      have hd : |((F n q r).card:ℝ)-((n+1:ℕ):ℝ)/q| ≤ 1 := by
        rw [sub_div' hq0.ne', abs_div, abs_of_pos hq0,div_le_one hq0]
        simpa [mul_comm] using h
      rw [←sub_mul,abs_mul,abs_of_nonneg (sq_nonneg z)]
      simpa using mul_le_mul_of_nonneg_right hd (sq_nonneg z)
    _ = _ := by rw [sum_const,nsmul_eq_mul]; change (R n q:ℝ)*z^2 = z^2*(R n q:ℝ); ring

end GoldbachProjectionBDH.Rounding

end

section

namespace GoldbachProjectionBDH
open Filter Finset GoldbachBDH GoldbachMajorArc
open scoped Topology
noncomputable section

def F (n q r : ℕ) := (range (n+1)).filter (fun k => k % q = r)
def refl (n q r : ℕ) := (n+q-r) % q
def G (n q : ℕ) : ℝ := ∑ r ∈ range q, classMass (n+1) q r*classMass (n+1) q (refl n q r)/((F n q r).card:ℝ)
def U (n q : ℕ) : ℝ := ∑ r ∈ range q, ((F n q r).card:ℝ)*(unitModel q r)^2
def K (n q : ℕ) : ℝ := ∑ r ∈ range q, ((F n q r).card:ℝ)*unitModel q r*unitModel q (refl n q r)
def good (n q : ℕ) := (range q).filter (fun r => r.Coprime q ∧ (refl n q r).Coprime q)
def mainTerm (n q : ℕ) : ℝ := (q:ℝ)*(good n q).card/(q.totient:ℝ)^2

lemma energy_pos (n q : ℕ) : 0≤energy n q :=
  sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
lemma U_pos (n q : ℕ) : 0≤U n q :=
  sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

lemma U_upper (n q : ℕ) (hq : 0<q) : U n q ≤ ((n+1:ℕ):ℝ)*((q:ℝ)/q.totient)^2 := by
  have hsum : (∑ r ∈ range q, (F n q r).card) = n+1 := by
    simpa [F] using card_eq_sum_card_fiberwise (fun i (_ : i∈range (n+1)) => mem_range.mpr (Nat.mod_lt i hq)) |>.symm
  calc
    _ ≤ ∑ r ∈ range q, ((F n q r).card:ℝ)*((q:ℝ)/q.totient)^2 := by
      apply sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      unfold unitModel
      split_ifs
      · exact le_rfl
      · simp only [zero_pow (by decide : 2≠0)]; exact sq_nonneg _
    _ = _ := by rw [←sum_mul]; congr 1; exact_mod_cast hsum

lemma target_upper (n q : ℕ) (hq : 0<q) : mainTerm n q ≤ ((q:ℝ)/q.totient)^2 := by
  have hr : (good n q).card ≤ q := (card_le_card (filter_subset _ _)).trans_eq (card_range _)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold mainTerm
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq] using mul_le_mul_of_nonneg_left (show ((good n q).card:ℝ)≤q by exact_mod_cast hr) (Nat.cast_nonneg (α:=ℝ) q)

private lemma young {u e t : ℝ} (hu : 0≤u) (he : 0≤e) (ht : 0<t) :
    2*Real.sqrt (u*e) ≤ t*u+e/t := by
  have hprod : (t*u)*(e/t) = u*e := by field_simp
  have h1 := Real.sq_sqrt (mul_nonneg ht.le hu)
  have h2 := Real.sq_sqrt (div_nonneg he ht.le)
  have h3 : Real.sqrt (u*e) = Real.sqrt (t*u)*Real.sqrt (e/t) := by rw [←Real.sqrt_mul (mul_nonneg ht.le hu),hprod]
  rw [h3]
  nlinarith only [h1,h2,sq_nonneg (Real.sqrt (t*u)-Real.sqrt (e/t))]

lemma abs_gram_one (n q : ℕ) (hq : 0<q) (hn : 0<n) (t : ℝ) (ht : 0<t) :
    |G n q/n - mainTerm n q| ≤
      (t*U n q+(1+1/t)*energy n q+((q:ℝ)/q.totient)^2*(q+1))/n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hG : |G n q-K n q| ≤ 2*Real.sqrt (U n q*energy n q)+energy n q := L2.transfer n q hq
  have hK : |K n q-((n+1:ℕ):ℝ)*mainTerm n q| ≤ ((q:ℝ)/q.totient)^2*(good n q).card := by
    have h := Rounding.singular n q hq
    change |K n q-((n+1:ℕ):ℝ)*q*(good n q).card/(q.totient:ℝ)^2| ≤ _ at h
    change |K n q-((n+1:ℕ):ℝ)*q*(good n q).card/(q.totient:ℝ)^2| ≤ ((q:ℝ)/q.totient)^2*(good n q).card at h
    rw [show ((n+1:ℕ):ℝ)*mainTerm n q=((n+1:ℕ):ℝ)*q*(good n q).card/(q.totient:ℝ)^2 by unfold mainTerm; ring]
    exact h
  have hmain0 : 0 ≤ mainTerm n q := by unfold mainTerm; positivity
  have he := young (U_pos n q) (energy_pos n q) ht
  have hr : ((good n q).card:ℝ)≤q := by
    exact_mod_cast (card_le_card (s:=good n q) (t:=range q) (filter_subset _ _)).trans_eq (card_range _)
  rw [div_sub' hn0.ne',abs_div,abs_of_pos hn0]
  apply div_le_div_of_nonneg_right _ hn0.le
  rw [show G n q-(n:ℝ)*mainTerm n q=(G n q-K n q)+(K n q-((n+1:ℕ):ℝ)*mainTerm n q)+mainTerm n q by push_cast;ring]
  have htri := abs_add_le (G n q-K n q) (K n q-((n+1:ℕ):ℝ)*mainTerm n q)
  have htri' := abs_add_le ((G n q-K n q)+(K n q-((n+1:ℕ):ℝ)*mainTerm n q)) (mainTerm n q)
  rw [abs_of_nonneg hmain0] at htri'
  rw [show (1+1/t)*energy n q = energy n q + energy n q/t by ring]
  nlinarith only [hG,hK,he,htri,htri',target_upper n q hq,mul_le_mul_of_nonneg_left hr (sq_nonneg ((q:ℝ)/q.totient))]

end
end GoldbachProjectionBDH

end

section

namespace GoldbachProjectionBDH
open Filter Finset GoldbachBDH
open scoped Topology
noncomputable section

theorem meanL1 (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let Q := n/(Nat.log 2 n)^8
    (∑ q ∈ Ioc Q (2*Q), |G n q/n - mainTerm n q|) ≤ ε*Q := by
  obtain ⟨C,hC,hE⟩ := energy_rate
  let τ := ε/1000
  have hτ : 0<τ := by dsimp [τ]; positivity
  let M := C + C/τ + 62208
  have hM : 0<M := by dsimp [M]; positivity
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hE,hl.eventually_ge_atTop 1,hl.eventually_ge_atTop (2*M/ε),eventually_ge_atTop (2:ℕ)] with n hsum hlog hlimit hn
  intro Q
  let l := Real.log n
  let t := τ/l^4
  let s := Ioc Q (2*Q)
  change 1 ≤ l at hlog
  change 2*M/ε ≤ l at hlimit
  have hl0 : 0<l := by linarith
  have ht : 0<t := by dsimp [t]; positivity
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  change (∑ q ∈ s, energy n q)≤ C*n*Q/l^5 at hsum
  change (∑ q ∈ s, |G n q/n-mainTerm n q|)≤ε*Q
  have hpoint (q : ℕ) (hq : q∈s) :
      |G n q/n-mainTerm n q| ≤ 162*τ + ((1+1/t)/n)*energy n q +
        (243*(Q:ℝ)*l^4)/n := by
    obtain ⟨hql,hqu⟩ := mem_Ioc.mp hq
    have hqp := (Nat.zero_le Q).trans_lt hql
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hqp
    have hQp : 0<Q := by omega
    have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQp
    have hquR : (q:ℝ)≤2*Q := by exact_mod_cast hqu
    have hQnR : (Q:ℝ)≤n := by exact_mod_cast (show Q≤n from Nat.div_le_self _ _)
    have hlogq : 1+Real.log q ≤ 3*l := by
      have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
      have hq2 : (q:ℝ)≤(n:ℝ)^2 := by nlinarith only [hquR,hQnR,mul_nonneg hn0.le (sub_nonneg.mpr hn2)]
      have hh := Real.log_le_log (by linarith : 0<(q:ℝ)) hq2
      rw [Real.log_pow] at hh; norm_num1 at hh
      change 1+_≤3*Real.log n; dsimp [l] at hlog; linarith only [hh,hlog]
    have hz : ((q:ℝ)/q.totient)^2 ≤ 81*l^4 := by
      calc
        _ ≤ ((1+Real.log q)^2)^2 := pow_le_pow_left₀ (by positivity) (ratio_bound q hqp) _
        _ ≤ ((3*l)^2)^2 := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (by linarith [Real.log_nonneg hq1]) hlogq 2) 2
        _ = _ := by ring
    have hu : U n q ≤ 162*n*l^4 := by
      apply (U_upper n q hqp).trans
      calc
        _ ≤ (2*(n:ℝ))*(81*l^4) := mul_le_mul (by push_cast; linarith) hz (sq_nonneg _) (by positivity)
        _ = _ := by ring
    have he := abs_gram_one n q hqp (by omega) t ht
    apply he.trans
    apply (div_le_iff₀ hn0).mpr
    have hu' : t*U n q ≤ 162*τ*n := by
      apply (mul_le_mul_of_nonneg_left hu ht.le).trans_eq
      dsimp [t]; field_simp
    have hr : ((q:ℝ)/q.totient)^2*(q+1) ≤ 243*Q*l^4 := by
      calc
        _ ≤ (81*l^4)*(3*(Q:ℝ)) := mul_le_mul hz (by linarith only [hquR,hQ1]) (by positivity) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ 162*τ*n + (1+1/t)*energy n q + 243*Q*l^4 := by linarith only [hu',hr]
      _ = _ := by field_simp
  have hcard : s.card=Q := by dsimp [s]; rw [Nat.card_Ioc]; omega
  have hrough : (∑ q ∈ s, |G n q/n-mainTerm n q|) ≤
      162*τ*Q + ((1+1/t)/n)*(C*n*Q/l^5)+(Q:ℝ)*(243*Q*l^4/n) := by
    apply (sum_le_sum hpoint).trans
    rw [sum_add_distrib,sum_add_distrib,←mul_sum s (fun q => energy n q) ((1+1/t)/n),sum_const,sum_const,hcard,nsmul_eq_mul,nsmul_eq_mul]
    calc
      _ ≤ (Q:ℝ)*(162*τ) + (1+1/t)/n*(C*n*Q/l^5) + Q*(243*Q*l^4/n) := by gcongr
      _ = _ := by ring
  have hqscale := binary_scale n hn
  change (Q:ℝ)*l^8 ≤ 256*n at hqscale
  have hbig : ((Q:ℝ)*l^4/n) ≤ 256/l := by
    apply (div_le_div_iff₀ hn0 hl0).mpr
    calc
      _ = (Q:ℝ)*l^5 := by ring
      _ ≤ (Q:ℝ)*l^8 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by norm_num)) (Nat.cast_nonneg _)
      _ ≤ _ := hqscale
  have hC1 : C/l^5 ≤ C/l := div_le_div_of_nonneg_left hC.le hl0 (by simpa using (pow_le_pow_right₀ hlog (show 1≤5 by norm_num)))
  have hcoeff : (1+1/t)*(C/l^5) ≤ (C+C/τ)/l := by
    calc
      _ = C/l^5+(C/τ)/l := by dsimp [t]; field_simp
      _ ≤ C/l+(C/τ)/l := by linarith only [hC1]
      _ = _ := by ring
  have hlast : (243*(Q:ℝ)*l^4/n) ≤ 62208/l := by
    calc
      _ = 243*((Q:ℝ)*l^4/n) := by ring
      _ ≤ 243*(256/l) := by linarith only [hbig]
      _ = _ := by ring
  have herr : M/l ≤ ε/2 := (div_le_iff₀ hl0).mpr (by linarith only [(div_le_iff₀ hε).mp hlimit])
  apply hrough.trans
  calc
    _ = (Q:ℝ)*(162*τ+(1+1/t)*(C/l^5)+243*(Q:ℝ)*l^4/n) := by field_simp
    _ ≤ (Q:ℝ)*(162*τ+(C+C/τ)/l+62208/l) := by gcongr
    _ = (Q:ℝ)*(162*τ+M/l) := by dsimp [M]; ring
    _ ≤ _ := by
      rw [mul_comm ε]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      dsimp [τ]; linarith only [herr,hε]
end
end GoldbachProjectionBDH

end

section

namespace GoldbachProjectionBDH
open Filter Finset
open scoped Topology
noncomputable section

theorem positive_from_local (floor : ∀ n q : ℕ, Even n → 0<q → (1:ℝ)/2 ≤ mainTerm n q)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Even n → let Q := n/(Nat.log 2 n)^8
      (((Ioc Q (2*Q)).filter (fun q => G n q ≤ (n:ℝ)/4)).card:ℝ) ≤ ε*Q := by
  filter_upwards [meanL1 (ε/4) (by positivity),eventually_ge_atTop (1:ℕ)] with n hn hpos heven
  intro Q
  let s := Ioc Q (2*Q)
  let bad := s.filter (fun q => G n q ≤ (n:ℝ)/4)
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hpos
  have hlower (q : ℕ) (hq : q∈bad) : (1:ℝ)/4 ≤ |G n q/n - mainTerm n q| := by
    obtain ⟨hI,hG⟩ := mem_filter.mp hq
    have hm := floor n q heven ((Nat.zero_le _).trans_lt (mem_Ioc.mp hI).1)
    have hu : G n q/n ≤ (1:ℝ)/4 := (div_le_iff₀ hn0).mpr (by linarith only [hG])
    rw [abs_sub_comm]
    exact (show (1:ℝ)/4 ≤ mainTerm n q-G n q/n by linarith only [hm,hu]).trans (le_abs_self _)
  have h : (bad.card:ℝ)*(1/4) ≤ (ε/4)*Q := by
    calc
      _ = ∑ _q ∈ bad, (1:ℝ)/4 := by simp
      _ ≤ ∑ q ∈ bad, |G n q/n-mainTerm n q| := sum_le_sum hlower
      _ ≤ ∑ q ∈ s, |G n q/n-mainTerm n q| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ _ := hn
  change (bad.card:ℝ)≤_
  linarith only [h]

end
end GoldbachProjectionBDH

end

section

namespace GoldbachBDHLocalFloor

open scoped Classical

private def countGood (n q : ℕ) := ((Finset.range q).filter
  (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card
private abbrev Good (n : ℕ) (R : Type*) [Ring R] :=
  {z : R // IsUnit z ∧ IsUnit ((n:R)-z)}
private theorem asCard (n q : ℕ) [NeZero q] :
    countGood n q = Fintype.card (Good n (ZMod q)) := by
  let A := (Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)
  have compat (r : ℕ) (hr : r<q) : (((n+q-r) % q:ℕ):ZMod q) = (n:ZMod q)-r := by
    rw [ZMod.natCast_mod,Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_self,add_zero]
  have cond (r : ℕ) (hr : r<q) : (r.Coprime q ∧ ((n+q-r) % q).Coprime q) ↔
      IsUnit (r:ZMod q) ∧ IsUnit ((n:ZMod q)-r) := by
    rw [←ZMod.isUnit_iff_coprime,←ZMod.isUnit_iff_coprime,compat r hr]
  let e : A ≃ Good n (ZMod q) := {
    toFun := fun r => ⟨(r.val:ZMod q), (cond r.val (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1)).mp
      (Finset.mem_filter.mp r.property).2⟩
    invFun := fun z => ⟨z.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      (cond _ (ZMod.val_lt _)).mpr (by simpa using z.property)⟩⟩
    left_inv := fun r => Subtype.ext (ZMod.val_natCast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1))
    right_inv := fun z => Subtype.ext (ZMod.natCast_zmod_val _) }
  simpa [countGood,A] using Fintype.card_congr e
private theorem goodMap {R S : Type*} [Ring R] [Ring S] (n : ℕ) (e : R →+* S) (z : Good n R) :
    IsUnit (e z.val) ∧ IsUnit ((n:S)-e z.val) := by
  refine ⟨z.property.1.map e, ?_⟩
  rw [← map_natCast e n, ← map_sub]
  exact z.property.2.map e
private def mapGood {R S : Type*} [Ring R] [Ring S] (n : ℕ) (e : R ≃+* S) :
    Good n R ≃ Good n S where
  toFun z := ⟨e z,goodMap n e.toRingHom z⟩
  invFun z := ⟨e.symm z,goodMap n e.symm.toRingHom z⟩
  left_inv z := Subtype.ext (e.symm_apply_apply _)
  right_inv z := Subtype.ext (e.apply_symm_apply _)
private def prodGood (n : ℕ) (R S : Type*) [Ring R] [Ring S] :
    Good n (R × S) ≃ Good n R × Good n S where
  toFun z := ⟨⟨z.val.1,(Prod.isUnit_iff.mp z.property.1).1,(Prod.isUnit_iff.mp z.property.2).1⟩,
    ⟨z.val.2,(Prod.isUnit_iff.mp z.property.1).2,(Prod.isUnit_iff.mp z.property.2).2⟩⟩
  invFun z := ⟨(z.1.val,z.2.val),Prod.isUnit_iff.mpr ⟨z.1.property.1,z.2.property.1⟩,
    Prod.isUnit_iff.mpr ⟨z.1.property.2,z.2.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem unitCRT :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  intro R n a b ha hb hab
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨hb.ne'⟩
  let : NeZero (a*b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  let e := (mapGood n (ZMod.chineseRemainder hab)).trans (prodGood n (ZMod a) (ZMod b))
  exact (asCard n (a*b)).trans ((Fintype.card_congr e).trans ((Fintype.card_prod _ _).trans
    (congrArg₂ Nat.mul (asCard n a).symm (asCard n b).symm)))


private theorem liftAtPower :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n p a : ℕ, p.Prime → 0<a → R n (p^a)=p^(a-1)*(if p∣n then p-1 else p-2) := by
  intro R n p a hp ha
  let q := p^a
  have hpq : p ∣ q := dvd_pow_self _ ha.ne'
  let P := fun k : ℕ => (k:ZMod p) ≠ 0 ∧ (k:ZMod p) ≠ n
  let M := fun z : ℕ => ((Finset.range z).filter P).card
  have hcop (s : ℕ) : s.Coprime q ↔ (s:ZMod p) ≠ 0 := by
    rw [show q=p^a from rfl,Nat.coprime_pow_right_iff ha,Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
    exact not_congr (ZMod.natCast_eq_zero_iff s p).symm
  have cond (r : ℕ) (hr : r<q) :
      (r.Coprime q ∧ ((n+q-r) % q).Coprime q) ↔ P r := by
    have hmod := (Nat.mod_modEq (n+q-r) q).of_dvd hpq
    have hc := (ZMod.natCast_eq_natCast_iff ..).mpr hmod
    have he : (((n+q-r) % q:ℕ):ZMod p) = (n:ZMod p)-r := by
      rw [hc,Nat.cast_sub (by omega),Nat.cast_add,(ZMod.natCast_eq_zero_iff ..).mpr hpq,add_zero]
    rw [hcop,hcop, he]
    dsimp only [P]; rw [sub_ne_zero]; exact and_congr_right' ne_comm
  have hR : R n q = M q := by
    change ((Finset.range q).filter _).card = ((Finset.range q).filter P).card
    congr 1; ext k
    simp only [Finset.mem_filter,Finset.mem_range]
    by_cases hk : k<q
    · rw [cond k hk]
    · simp [hk]
  have add (t : ℕ) : M (p*t+p) = M (p*t)+M p := by
    have cm (z : ℕ) : M z = ∑ k ∈ Finset.range z, if P k then 1 else 0 := by simp [M,Finset.sum_boole]
    simp only [cm,Finset.sum_range_add]
    congr 1; apply Finset.sum_congr rfl
    intro k _
    simp [P,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self]
  have block (t : ℕ) : M (p*t) = t*M p := by
    induction t with
    | zero => simp [M]
    | succ t ih => rw [Nat.mul_succ,add,ih,Nat.succ_mul]
  have hset : (Finset.range p).filter P = ((Finset.range p).erase 0).erase (n % p) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_erase,P]
    by_cases hk : k<p
    · have hm : ((k:ZMod p) = n) ↔ k = n % p := by
        rw [ZMod.natCast_eq_natCast_iff]; change k % p = n % p ↔ _; rw [Nat.mod_eq_of_lt hk]
      have h0 : (k:ZMod p) = 0 ↔ k=0 := by rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,Nat.mod_eq_of_lt hk]
      tauto
    · tauto
  have mp : M p = if p ∣ n then p-1 else p-2 := by
    dsimp only [M]; rw [hset]
    have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
    split_ifs with h
    · simp [Nat.mod_eq_zero_of_dvd h,Finset.card_erase_of_mem hzero]
    · have h' : n % p ∈ (Finset.range p).erase 0 :=
        Finset.mem_erase.mpr ⟨mt Nat.dvd_of_mod_eq_zero h,Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)⟩
      rw [Finset.card_erase_of_mem h',Finset.card_erase_of_mem hzero,Finset.card_range]; omega
  change R n q = _
  rw [hR, show q=p*p^(a-1) by dsimp [q]; rw [mul_comm,pow_sub_one_mul ha.ne'],block,mp]


private theorem normalized :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n q : ℕ, 0<q → (q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2 = ∏ p ∈ q.primeFactors, (p:ℝ)*(if p∣n then (p:ℝ)-1 else (p:ℝ)-2)/((p:ℝ)-1)^2 := by
  intro R n q
  let f := fun p : ℕ => (p:ℝ)*(if p∣n then (p:ℝ)-1 else (p:ℝ)-2)/((p:ℝ)-1)^2
  change 0<q → (q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2 = ∏ p ∈ q.primeFactors, f p
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => intro _; simp [R,Nat.totient_one,Finset.range_one]
  | prime_pow p a hp ha =>
    intro _
    have h1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (p:ℝ) ≠ 0 := by positivity
    have hr : R n (p^a) = p^(a-1)*(if p∣n then p-1 else p-2) := liftAtPower n p a hp ha
    rw [Nat.primeFactors_prime_pow ha.ne' hp,Finset.prod_singleton,hr,Nat.totient_prime_pow hp ha]
    dsimp only [f]
    have he : (p:ℝ)^a=(p:ℝ)^(a-1)*p := (pow_sub_one_mul ha.ne' _).symm
    split_ifs <;> push_cast [Nat.cast_sub hp.two_le,Nat.cast_sub hp.one_lt.le] <;>
      rw [he] <;> field_simp <;> ring
  | coprime a b ha hb hab ia ib =>
    intro _
    have ha' : 0<a := by omega
    have hb' : 0<b := by omega
    have he : R n (a*b) = R n a * R n b := unitCRT n a b ha' hb' hab
    rw [hab.primeFactors_mul,Finset.prod_union hab.disjoint_primeFactors, ← ia ha',← ib hb',he,Nat.totient_mul hab]
    push_cast
    ring


private noncomputable def minorFactor (p : ℕ) : ℝ :=
  if 3≤p then 1-1/((p:ℝ)-1)^2 else 1

private theorem positiveMinor (p : ℕ) : 0 ≤ minorFactor p ∧ minorFactor p ≤ 1 := by
  dsimp only [minorFactor]
  split_ifs with h
  · have hp : 3 ≤ (p:ℝ) := by exact_mod_cast h
    have h2 : 1 ≤ ((p:ℝ)-1)^2 := by nlinarith
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr h2)
    · linarith [show 0 ≤ 1/((p:ℝ)-1)^2 by positivity]
  · norm_num

private theorem telescope (m : ℕ) :
    ∏ p ∈ Finset.range (m+3), minorFactor p = ((m:ℝ)+2)/(2*((m:ℝ)+1)) := by
  induction m with
  | zero => norm_num [Finset.prod_range_succ,minorFactor]
  | succ m ih =>
    rw [show (m+1)+3=(m+3)+1 by omega,Finset.prod_range_succ, ih]
    simp only [minorFactor,if_pos (show 3 ≤ m+3 by omega)]
    push_cast
    have hm : 0 ≤ (m:ℝ) := by positivity
    have h1 : (m:ℝ)+1 ≠ 0 := by linarith
    have h2 : (m:ℝ)+3-1 ≠ 0 := by linarith
    have h3 : (m:ℝ)+1+1 ≠ 0 := by linarith
    field_simp
    ring

theorem lower :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n q : ℕ, Even n → 0<q → (1:ℝ)/2 ≤ (q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2 := by
  intro R n q hn hq
  have hw := normalized n q hq
  change (q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2 = _ at hw
  rw [hw]
  let s := q.primeFactors
  have sub : s ⊆ Finset.range (q+3) := by
    intro p hp; apply Finset.mem_range.mpr
    have h := Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hp); omega
  calc
    (1:ℝ)/2 ≤ ∏ p ∈ Finset.range (q+3), minorFactor p := by
      rw [telescope,le_div_iff₀ (by positivity)]; linarith
    _ ≤ ∏ p ∈ s, minorFactor p := Finset.prod_le_prod_of_subset_of_le_one₀ sub
      (fun p _ => (positiveMinor p).1) (fun p _ _ => (positiveMinor p).2)
    _ ≤ _ := by
      refine Finset.prod_le_prod₀ (fun p _ => (positiveMinor p).1) (fun p hp => ?_)
      have pp := Nat.prime_of_mem_primeFactors hp
      have p2 : 2 ≤ (p:ℝ) := by exact_mod_cast pp.two_le
      by_cases he : p=2
      · subst p; norm_num [minorFactor,hn.two_dvd]
      · have p3 : 3 ≤ p := by have := pp.two_le; omega
        rw [minorFactor,if_pos p3]
        have hden : 0 < ((p:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
        apply (le_div_iff₀ hden).mpr
        rw [sub_mul,div_mul_cancel₀ 1 hden.ne']
        split_ifs <;> nlinarith

end GoldbachBDHLocalFloor

end

section

theorem PEqualNP.Outside.L_goldbach_coset_block_most_positive :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r) % q; let G := fun n q => ∑ r ∈ Finset.range q, A n q r*A n q (j n q r)/((F n q r).card:ℝ); let Q := fun n : ℕ => n/(Nat.log 2 n)^8; ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, Even n → (((Finset.Ioc (Q n) (2*Q n)).filter (fun q => G n q ≤ (n:ℝ)/4)).card : ℝ) ≤ ε*(Q n:ℝ) := by
  intro F w A j G Q ε hε
  exact Filter.eventually_atTop.mp (GoldbachProjectionBDH.positive_from_local
    (fun n q he hq => GoldbachBDHLocalFloor.lower n q he hq) ε hε)

end
