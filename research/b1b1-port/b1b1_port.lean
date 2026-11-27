import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion

set_option maxHeartbeats 4000000

open Finset MeasureTheory
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand

noncomputable section

namespace B1B1Port


/-- The `Λ`-weighted progression sum attached to one atom. -/
def atomWave (a U R : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.Icc (U+1) R, (ArithmeticFunction.vonMangoldt r : ℂ) * phase ((a*r : ℕ) * t)

/-- The balanced-frontier coefficient `τ₁` as `lowBandCoefficient`, expanded into
atoms indexed by the small divisor `a ∈ (U, B₁]`. -/
theorem plainPolynomial_tau1 (n : ℕ) (t : ℝ) :
    plainPolynomial n (fun m => (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)) t
      = ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) * atomWave a (cutoffU n) (n / a) t := by
  have h := Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion
  simp only [plainPolynomial, atomWave, lowBandCoefficient, lowMoebiusWeight,
    cutoffU, lowCut, phase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Finset.mul_sum] at h ⊢
  exact h n t




/-! ### Weighted progression sums

`split_shifted_wave` is stated for the unweighted geometric progression
`wave g l r`.  For the balanced-frontier cell the progression is weighted by
`Λ`, so we redo the two structural lemmas with an arbitrary coefficient
sequence `c : ℕ → ℂ`.  The proofs are the ones from the verified `b1-b4`
module with the weight `c h` carried along; the only arithmetic input is
`q ∣ g → e(g h a/q) = 1`, which is weight-independent.
-/

/-- A weighted geometric progression. -/
def wwave (c : ℕ → ℂ) (u l r : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Ioc l r, c h * phase ((u*h : ℕ) * t)

/-- The weighted progression with the grid neighbourhoods removed. -/
def woffWave (c : ℕ → ℂ) (b : ℝ) (u l r : ℕ) : ℝ → ℂ :=
  (gridNear b u)ᶜ.indicator (wwave c u l r)

theorem continuous_wwave (c : ℕ → ℂ) (u l r : ℕ) : Continuous (wwave c u l r) := by
  unfold wwave
  exact continuous_finsetSum _ fun h _ =>
    continuous_const.mul (by unfold phase; fun_prop)

theorem wwave_at_cell_center {q g : ℕ} (qPositive : 0 < q) (divides : q ∣ g)
    (l r : ℕ) (c : ℕ → ℂ) (a : ℕ) (t : ℝ) :
    wwave c g l r (t + (a : ℝ) / q) = wwave c g l r t := by
  unfold wwave
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨v, identity⟩ := divides
  have centerTerm : ((g * j : ℕ) : ℝ) * ((a : ℝ) / q) = ((v * j * a : ℕ) : ℝ) := by
    rw [identity]
    push_cast
    field_simp
  rw [mul_add, phase_add, centerTerm, phase_nat, mul_one]

/-- Cell-integral reduction, weighted form. -/
theorem integral_cell_wwave {n M B H q a g : ℕ} (qLower : 1 < q) (qBound : q ≤ M)
    (aMember : a ∈ numSet q) (divides : q ∣ g) (l r : ℕ) (c : ℕ → ℂ) (k : ℤ) :
    (∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator (fun x =>
      phase ((k : ℝ) * x) * wwave c g l r x) t) = phase ((k : ℝ) * ((a : ℝ) / q)) *
      ∫ t in window n M B H q, phase ((k : ℝ) * t) * wwave c g l r t := by
  rw [integral_cell_translate qLower qBound aMember, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change phase ((k : ℝ) * (t + (a : ℝ) / q)) * wwave c g l r (t + (a : ℝ) / q) = _
  rw [wwave_at_cell_center (by omega : 0 < q) divides, mul_add, phase_add]
  ring

/-- The weighted analogue of `centered_deep_wave_integral`. -/
theorem centered_deep_wwave_integral (n M B H R g l r : ℕ) (c : ℕ → ℂ) (k : ℤ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator
        (fun x => phase ((k : ℝ) * x) * wwave c g l r x) t) =
      ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q k *
        ∫ t in window n M B H q, phase ((k : ℝ) * t) * wwave c g l r t := by
  classical
  let f (x : ℝ) := phase ((k : ℝ) * x) * wwave c g l r x
  have fContinuous : Continuous f := by
    unfold f
    exact (by unfold phase; fun_prop : Continuous fun x : ℝ => phase ((k : ℝ) * x)).mul
      (continuous_wwave c g l r)
  have cellIntegrable (q a : ℕ) : IntervalIntegrable ((cell n M B H q a).indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (fContinuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (cell_measurable n M B H q a)
  have split : (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) =
      ∑ q ∈ g.divisors, ∑ a ∈ numSet q, ∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ g.divisors, ∑ a ∈ numSet q,
            (cell n M B H q a).indicator f t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact deep_cell_indicator f n M g B H nPositive gPositive gBound Bbound width t
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun q _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          exact fun a _ => cellIntegrable q a
        · intro q _
          have integrated := IntervalIntegrable.sum (numSet q) (fun a _ => cellIntegrable q a)
          convert integrated using 1
          funext t
          simp only [Finset.sum_apply]
  change (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) = _
  rw [split, Finset.sum_filter]
  refine sum_congr rfl fun q qMember => ?_
  have qPositive := Nat.pos_of_mem_divisors qMember
  by_cases large : R < q
  · have qLower : 1 < q := Rpositive.trans_lt large
    have divides := (Nat.mem_divisors.mp qMember).1
    have qBound : q ≤ M := (Nat.le_of_dvd gPositive divides).trans gBound
    rw [if_pos large, ramanujan, sum_mul]
    exact sum_congr rfl fun a aMember => integral_cell_wwave qLower qBound aMember divides l r c k
  · rw [if_neg large]
    apply sum_eq_zero
    intro a _
    have emptyWindow := window_empty_of_small_modulus nPositive qPositive (le_of_not_gt large) Rbound cover
    have emptyCell : cell n M B H q a = ∅ := by simp [cell, emptyWindow]
    simp [emptyCell]

/-- The weighted analogue of `split_shifted_wave`: the deep-minor integral of
`shiftedPolynomial × weighted progression` splits into a far (off-grid) part and
an exact near part given by Ramanujan sums. -/
theorem split_shifted_wwave (n M B H R g l r : ℕ) (c : ℕ → ℂ) (a : ℕ → ℂ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator
        (fun x => shiftedPolynomial n a x * wwave c g l r x) t) =
      (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator
        (fun x => shiftedPolynomial n a x * woffWave c (radius M) g l r x) t) +
      ∑ q ∈ g.divisors.filter (fun q => R < q), ∑ m ∈ range (n + 1), a m *
        ramanujan q ((m : ℤ) - n) *
        ∫ t in window n M B H q, phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wwave c g l r t := by
  classical
  let near := gridNear (radius M) g
  let outside := (wide n B H)ᶜ
  let f (t : ℝ) := shiftedPolynomial n a t * wwave c g l r t
  let off (t : ℝ) := shiftedPolynomial n a t * woffWave c (radius M) g l r t
  let v (m : ℕ) (t : ℝ) := phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wwave c g l r t
  have waveContinuous : Continuous (wwave c g l r) := continuous_wwave c g l r
  have fContinuous : Continuous f := (shiftedPolynomial_continuous n a).mul waveContinuous
  have nearMeasurable : MeasurableSet near := gridNear_measurable (radius M) g
  have outsideMeasurable : MeasurableSet outside := (wide_measurable n B H).compl
  have offEqual : outside.indicator off = (outside ∩ nearᶜ).indicator f := by
    funext t
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;>
      simp_all only [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff,
        Set.mem_compl_iff, not_true_eq_false, not_false_eq_true, and_true, and_false,
        false_and, true_and, mul_zero, off, near, woffWave, f]
  have offInt : IntervalIntegrable (outside.indicator off) volume 0 1 := by
    rw [offEqual]
    exact indicator_intervalIntegrable fContinuous (outsideMeasurable.inter nearMeasurable.compl)
  have nearInt : IntervalIntegrable ((near ∩ outside).indicator f) volume 0 1 :=
    indicator_intervalIntegrable fContinuous (nearMeasurable.inter outsideMeasurable)
  have split (t : ℝ) : outside.indicator f t = outside.indicator off t + (near ∩ outside).indicator f t := by
    rw [offEqual]
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;> simp [nearMem, outsideMem]
  have expandNear (t : ℝ) : (near ∩ outside).indicator f t =
      ∑ m ∈ range (n + 1), a m * (near ∩ outside).indicator (v m) t := by
    by_cases membership : t ∈ near ∩ outside
    · simp only [Set.indicator_of_mem membership, f, shiftedPolynomial, sum_mul, v, mul_assoc]
    · simp [membership]
  have termInt (m : ℕ) : IntervalIntegrable (fun t => a m * (near ∩ outside).indicator (v m) t) volume 0 1 := by
    have continuousMode : Continuous (fun t : ℝ => phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) := by
      unfold phase
      fun_prop
    exact (indicator_intervalIntegrable (continuousMode.mul waveContinuous)
      (nearMeasurable.inter outsideMeasurable)).const_mul (a m)
  change (∫ t in (0 : ℝ)..1, outside.indicator f t) = (∫ t in (0 : ℝ)..1, outside.indicator off t) + _
  calc
    _ = ∫ t in (0 : ℝ)..1, outside.indicator off t + (near ∩ outside).indicator f t :=
      intervalIntegral.integral_congr fun t _ => split t
    _ = (∫ t in (0 : ℝ)..1, outside.indicator off t) +
          ∫ t in (0 : ℝ)..1, (near ∩ outside).indicator f t :=
      intervalIntegral.integral_add offInt nearInt
    _ = _ := by
      congr 1
      simp_rw [expandNear]
      rw [intervalIntegral.integral_finsetSum (fun m _ => termInt m)]
      simp_rw [intervalIntegral.integral_const_mul]
      have identify (m : ℕ) : (∫ t in (0 : ℝ)..1, (near ∩ outside).indicator (v m) t) =
          ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q ((m : ℤ) - n) *
            ∫ t in window n M B H q, v m t :=
        centered_deep_wwave_integral n M B H R g l r c ((m : ℤ) - n)
          nPositive gPositive gBound Bbound width Rpositive Rbound cover
      simp_rw [identify, mul_sum]
      rw [sum_comm]
      simp only [v, mul_assoc]



/-! ### The `τ₁ × τ₁` deep-minor integral -/

/-- `atomWave` is the weighted progression `wwave` with weight `Λ`. -/
theorem atomWave_eq_wwave (a U R : ℕ) (t : ℝ) :
    atomWave a U R t = wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a U R t := by
  unfold atomWave wwave
  congr 1
  ext h
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- The balanced-frontier coefficient as a complex sequence. -/
def tauCoeff (n : ℕ) : ℕ → ℂ :=
  fun m => (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)

/-- The task's wide arcs in the `wide`-normal form of the verified module. -/
def wideSet (n : ℕ) : Set ℝ := wide n (cutoffB n) (cutoffH n)

/-- The deep-minor integral `Jdeep` in the port's normal form. -/
def deepIntegral (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator
    (fun x => plainPolynomial n (tauCoeff n) x * shiftedPolynomial n (tauCoeff n) x) t

/-- The port's `deepIntegral` is the task's `Jdeep` integrand. -/
theorem deepIntegral_eq_task (n : ℕ) :
    deepIntegral n = ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator
      (fun x => plainPolynomial n (tauCoeff n) x * plainPolynomial n (tauCoeff n) x *
        phase (-(n:ℝ)*x)) t := by
  unfold deepIntegral
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ (wideSet n)ᶜ
  · simp only [Set.indicator_of_mem ht, shiftedPolynomial_eq]
    ring
  · simp only [Set.indicator_of_notMem ht]

theorem lowCut_le_maximumStep (n : ℕ) (nPositive : 0 < n) : lowCut n ≤ maximumStep n := by
  have nReal : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast nPositive
  have h₁ : lowCut n ≤ cutoffB n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nReal (by norm_num : (1/4:ℝ) ≤ 1/3))
  exact h₁.trans (cutoffs_ordered n nPositive).2.2.1

/-- The far (off-grid) part for one atom. -/
def farPart (n a : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator (fun x =>
    shiftedPolynomial n (tauCoeff n) x *
      woffWave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) (radius (maximumStep n))
        a (cutoffU n) (n / a) x) t

/-- The near (annulus) part for one atom, exact Ramanujan expansion. -/
def nearPart (n a : ℕ) : ℂ :=
  ∑ q ∈ a.divisors.filter (fun q => cutoffR n < q), ∑ m ∈ Finset.range (n + 1),
    tauCoeff n m * ramanujan q ((m : ℤ) - n) *
      ∫ t in window n (maximumStep n) (cutoffB n) (cutoffH n) q,
        phase (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) * t) *
          wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a) t

/-- **The exact decomposition of the b1-b1 deep-minor integral** into a far
(off-grid) and a near (annulus, Ramanujan) part, atom by atom.

This is the `τ₁ × τ₁` analogue of the verified `deepPairIntegral_split`, using
the weighted split because the progression carries the `Λ` weight. -/
theorem deepIntegral_split (n : ℕ) (nPositive : 0 < n)
    (width : 4 * cutoffH n * maximumStep n ≤ n) :
    deepIntegral n =
      ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        (lowMoebiusWeight (cutoffU n) a : ℂ) * (farPart n a + nearPart n a) := by
  classical
  have hfactor : ∀ t : ℝ, plainPolynomial n (tauCoeff n) t =
      ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        (lowMoebiusWeight (cutoffU n) a : ℂ) *
          wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a) t := by
    intro t
    unfold tauCoeff
    rw [plainPolynomial_tau1 n t]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [atomWave_eq_wwave]
  have hpoint : ∀ t : ℝ,
      (wideSet n)ᶜ.indicator
        (fun x => plainPolynomial n (tauCoeff n) x * shiftedPolynomial n (tauCoeff n) x) t =
      ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        (lowMoebiusWeight (cutoffU n) a : ℂ) *
          (wideSet n)ᶜ.indicator
            (fun x => shiftedPolynomial n (tauCoeff n) x *
              wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a) x) t := by
    intro t
    by_cases ht : t ∈ (wideSet n)ᶜ
    · simp only [Set.indicator_of_mem ht]
      rw [hfactor t, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    · simp only [Set.indicator_of_notMem ht, mul_zero, Finset.sum_const_zero]
  unfold deepIntegral
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨haLower, haUpper⟩ := Finset.mem_Icc.mp ha
    have haPos : 0 < a := by omega
    have haBound : a ≤ maximumStep n := haUpper.trans (lowCut_le_maximumStep n nPositive)
    obtain ⟨rPos, rB, bM, _⟩ := cutoffs_ordered n nPositive
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact split_shifted_wwave n (maximumStep n) (cutoffB n) (cutoffH n) (cutoffR n) a
      (cutoffU n) (n / a) (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) (tauCoeff n)
      nPositive haPos haBound bM width rPos rB (cutoffR_covered n nPositive)
  · intro a _
    exact (indicator_intervalIntegrable
      ((shiftedPolynomial_continuous n (tauCoeff n)).mul
        (continuous_wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a)))
      ((wide_measurable n (cutoffB n) (cutoffH n)).compl)).const_mul _


/-! ### The two ingredients of a weighted `waveBound`

`waveBound` in the verified module controls `wave u l r` by
`(2/u) * smoothKernel (1/(n+1)) (i/u)` and is built from two inputs:
`‖wave u l r t‖ ≤ n/u` (length) and `‖wave u l r t‖ · |t - i/u| ≤ 1/u`
(oscillation, via `wave_sin`).  Below is the weighted length bound.  The weighted
oscillation bound

  `‖wwave (Λ) u l r t‖ · |t - i/u| ≤ (something) / u`

is the remaining analytic input; it requires a weighted exponential-sum estimate
for `∑_{h} Λ(h) e(u h t)`.
-/

/-- Weighted length bound: a weighted progression is bounded by its total weight. -/
theorem wwave_cap (c : ℕ → ℂ) (u l r : ℕ) (t : ℝ) :
    ‖wwave c u l r t‖ ≤ ∑ h ∈ Finset.Ioc l r, ‖c h‖ := by
  unfold wwave
  calc ‖∑ h ∈ Finset.Ioc l r, c h * phase ((u*h : ℕ) * t)‖
      ≤ ∑ h ∈ Finset.Ioc l r, ‖c h * phase ((u*h : ℕ) * t)‖ := norm_sum_le _ _
    _ = ∑ h ∈ Finset.Ioc l r, ‖c h‖ := by simp

/-- The `Λ`-weighted length bound: at most the Chebyshev sum over the range. -/
theorem wwave_mangoldt_cap (u l r : ℕ) (t : ℝ) :
    ‖wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) u l r t‖
      ≤ ∑ h ∈ Finset.Ioc l r, ArithmeticFunction.vonMangoldt h := by
  refine (wwave_cap _ u l r t).trans_eq ?_
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]


/-! ### Bridge to the verified Vinogradov minor-arc saving

`Conjectures.Goldbach.VinogradovPolylogMinorSaving` (a verified catalogue module)
states: for every `A > 0` and all large `n`, every `t ∈ [0,1]` outside the
polylog-denominator arcs

  `arcsPoly B n = ⋃_{q ≤ (log₂(n+2))^B} ⋃_{a ≤ q, (a,q)=1} [a/q ± (log₂(n+2))^B/(q n)]`

satisfies `‖∑_{k ≤ n} Λ k · e(k t)‖ ≤ n · (log n)^(-A)`.

Those arcs are *contained* in the wide arcs, so `t ∉ wideArcs n` implies
`t ∉ arcsPoly B n` and the Vinogradov saving is available on the deep-minor set.
-/

/-- The polylog-denominator arcs of the verified Vinogradov saving are contained
in the wide arcs, provided the polylog cutoff and radius fit under the wide ones. -/
theorem arcsPoly_subset_wideSet {B n : ℕ}
    (hQ : (Nat.log 2 (n + 2)) ^ B ≤ cutoffB n)
    (hH : (((Nat.log 2 (n + 2)) ^ B : ℕ) : ℝ) ≤ (cutoffH n : ℝ)) :
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (n + 2)) ^ B ∧ a ≤ q ∧
        Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n + 2)) ^ B : ℕ) : ℝ)/((q:ℝ)*(n:ℝ))}
      ⊆ wideSet n := by
  rintro t ⟨q, a, hq1, hqP, haq, hcop, hle⟩
  exact ⟨q, a, hq1, hqP.trans hQ, haq, hcop,
    hle.trans (div_le_div_of_nonneg_right hH (by positivity))⟩


/-! ### The structural identity behind `τ₁`: the Möbius weight is a *small-divisor* sum

`∑_{d | a} μ(d) = [a = 1]`, so for `a > 1`

```text
lowMoebiusWeight U a = ∑_{U < d | a} μ(d) = - ∑_{d | a, d ≤ U} μ(d) .
```

Thus `τ₁` is a Möbius sum over the **small** divisors `d ≤ U = n^(1/16)`, not over the
large ones.  (Numerically this is what makes `∑_a c(a)/a` of size `log log n` rather
than `o(1)`; see the README.)
-/

/-- Pointwise Möbius inversion over the divisors of `n`, real-valued form. -/
theorem sum_moebius_divisors_real (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.mul_apply] at h
  have hreindex : (∑ x ∈ n.divisorsAntidiagonal,
        ((μ x.1 : ℝ) * (ArithmeticFunction.zeta x.2 : ℝ)))
      = ∑ d ∈ n.divisors, (μ d : ℝ) := by
    refine Finset.sum_nbij' (fun x : ℕ × ℕ => x.1) (fun d : ℕ => (d, n / d)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      exact Nat.mem_divisors.mpr ⟨⟨x.2, hx'.1.symm⟩, hx'.2⟩
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hd'.1, hd'.2⟩
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hxpos : 0 < x.1 := by
        rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
        · rw [h0, zero_mul] at hx'; omega
        · exact hpos
      have hdiv : n / x.1 = x.2 := by
        rw [← hx'.1, Nat.mul_comm x.1 x.2, Nat.mul_div_left x.2 hxpos]
      exact Prod.ext rfl hdiv
    · intro d _
      rfl
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hx2 : x.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hx'
        exact hx'.2 hx'.1.symm
      rw [ArithmeticFunction.zeta_apply, if_neg (by omega : ¬ x.2 = 0)]
      push_cast
      ring
  have h' : (∑ x ∈ n.divisorsAntidiagonal,
      ((μ x.1 : ℝ) * (ArithmeticFunction.zeta x.2 : ℝ)))
      = (1 : ArithmeticFunction ℝ) n := h
  rw [hreindex] at h'
  rw [ArithmeticFunction.one_apply] at h'
  exact h'

/-- For `a > 1` the low Möbius weight is minus the sum over the *small* divisors. -/
theorem lowMoebiusWeight_eq_neg_small (U a : ℕ) (ha : 1 < a) :
    lowMoebiusWeight U a
      = - ∑ d ∈ a.divisors.filter (fun d => d ≤ U), (μ d : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not a.divisors
    (fun d : ℕ => d ≤ U) (fun d => (μ d : ℝ))
  have hnot : a.divisors.filter (fun d => ¬ d ≤ U) = a.divisors.filter (fun d => U < d) := by
    refine Finset.filter_congr fun d _ => ?_
    omega
  rw [hnot] at hsplit
  have hzero : (∑ d ∈ a.divisors, (μ d : ℝ)) = 0 := by
    rw [sum_moebius_divisors_real, if_neg (by omega)]
  unfold lowMoebiusWeight
  linarith [hsplit, hzero]



/-! ### Fourier orthogonality on the unit interval

These are the two facts on which the weighted `L²` (`Parseval`) identity

```text
∫ |wwave c u l r|² = ∑_{h ∈ (l,r]} ‖c h‖²
```

rests; the identity itself is the next target.  It is the exact replacement for
the module's unweighted `∫ |wave u l r|² = r - l`.
-/

/-- Orthogonality of the Fourier modes `phase (k t)` on the unit interval. -/
theorem integral_phase_int (k : ℤ) :
    (∫ t in (0:ℝ)..1, phase ((k:ℝ)*t)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [phase]
  · have hc : ((2*Real.pi*Complex.I) * (k:ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · exact_mod_cast hk
    rw [if_neg hk]
    have hcongr : ∀ t : ℝ,
        phase ((k:ℝ)*t) = Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (t:ℂ)) := by
      intro t
      unfold phase
      congr 1
      push_cast
      ring
    simp_rw [hcongr]
    rw [integral_exp_mul_complex hc]
    have htop : Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * ((1:ℝ):ℂ)) = 1 := by
      rw [show ((2*Real.pi*Complex.I) * (k:ℂ)) * ((1:ℝ):ℂ)
          = (k:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    have hbot : Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * ((0:ℝ):ℂ)) = 1 := by simp
    rw [htop, hbot, sub_self, zero_div]

/-- Distinct modes are orthogonal on the unit interval. -/
theorem integral_phase_sub (a b : ℕ) :
    (∫ t in (0:ℝ)..1, phase ((a:ℝ)*t) * (starRingEnd ℂ) (phase ((b:ℝ)*t)))
      = if a = b then 1 else 0 := by
  have hconj : ∀ t : ℝ, (starRingEnd ℂ) (phase ((b:ℝ)*t)) = phase (-((b:ℝ)*t)) := by
    intro t
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, map_ofNat]
  simp_rw [hconj]
  have hcomb : ∀ t : ℝ, phase ((a:ℝ)*t) * phase (-((b:ℝ)*t))
      = phase ((((a:ℤ) - (b:ℤ) : ℤ) : ℝ) * t) := by
    intro t
    rw [← phase_add]
    congr 1
    push_cast
    ring
  simp_rw [hcomb]
  rw [integral_phase_int]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab]
    have hne : ((a:ℤ) - (b:ℤ) : ℤ) ≠ 0 := by
      intro h
      exact hab (by exact_mod_cast (sub_eq_zero.mp h))
    rw [if_neg hne]

/-- **Weighted Parseval.**  For a `Λ`-weighted progression the `L²` mass is the
sum of the squared weights, the exact replacement of `∫ |wave u l r|² = r - l`. -/
theorem integral_wwave_norm_sq (c : ℕ → ℂ) {u : ℕ} (hu : 0 < u) (l r : ℕ) :
    (∫ t in (0:ℝ)..1, ‖wwave c u l r t‖ ^ 2) = ∑ h ∈ Finset.Ioc l r, ‖c h‖ ^ 2 := by
  classical
  set N : ℕ := r * u with hN
  set b : ℕ → ℂ := fun m => ∑ h ∈ (Finset.Ioc l r).filter (fun h => h * u = m), c h with hb
  have hmaps : ∀ h ∈ Finset.Ioc l r, h * u ∈ Finset.range (N + 1) := by
    intro h hh
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    calc h * u ≤ r * u := Nat.mul_le_mul_right u (Finset.mem_Ioc.mp hh).2
      _ = N := hN
  have hfun : ∀ t : ℝ, wwave c u l r t =
      ∑ m ∈ Finset.range (N + 1), b m * phase ((m:ℝ) * t) := by
    intro t
    have hrewrite : wwave c u l r t =
        ∑ h ∈ Finset.Ioc l r, c h * phase (((h * u : ℕ) : ℝ) * t) := by
      unfold wwave
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Nat.mul_comm u h]
    rw [hrewrite, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun h => c h * phase (((h * u : ℕ) : ℝ) * t))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [(Finset.mem_filter.mp hh).2]
  have hemode : ∀ (m : ℕ) (t : ℝ), phase ((m:ℝ)*t) = DyadicMixedB4Fourier.mode (m:ℤ) t := by
    intro m t
    rw [DyadicMixedB4Fourier.mode, DyadicMixedB4Fourier.frequency]
    unfold phase
    congr 1
    push_cast
    ring
  have hstep : (∫ t in (0:ℝ)..1, ‖wwave c u l r t‖ ^ 2)
      = ∫ t in (0:ℝ)..1, ‖∑ m ∈ Finset.range (N + 1), b m * phase ((m:ℝ)*t)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun z => ‖z‖ ^ 2) (hfun t)
  rw [hstep]
  have hparse : (∫ t in (0:ℝ)..1, ‖∑ m ∈ Finset.range (N + 1), b m * phase ((m:ℝ)*t)‖ ^ 2)
      = ∑ m ∈ Finset.range (N + 1), ‖b m‖ ^ 2 := by
    simp only [hemode]
    exact DyadicMixedB4Fourier.parseval_real (N + 1) b
  rw [hparse]
  have hinj : ∀ h h' : ℕ, h * u = h' * u → h = h' := fun h h' he =>
    Nat.eq_of_mul_eq_mul_right hu he
  have hsingle : ∀ m : ℕ, ‖b m‖ ^ 2 =
      ∑ h ∈ (Finset.Ioc l r).filter (fun h => h * u = m), ‖c h‖ ^ 2 := by
    intro m
    rw [hb]
    simp only
    have hcard : ((Finset.Ioc l r).filter (fun h => h * u = m)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b' hbb
      exact hinj a b' (by rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hbb).2])
    rcases Nat.eq_zero_or_pos ((Finset.Ioc l r).filter (fun h => h * u = m)).card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      simp
    · obtain ⟨h₀, hset⟩ := Finset.card_eq_one.mp (le_antisymm hcard hpos)
      rw [hset]
      simp
  simp_rw [hsingle]
  exact Finset.sum_fiberwise_of_maps_to hmaps (fun h => ‖c h‖ ^ 2)

/-! ### How close is a weighted progression to its total mass?

On the archimedean core `|t| ≲ 1/(u N)` the weighted progression is essentially
its total mass.  Off that core it is **not**: the correct error term carries a
factor `h`, not just `Λ h`:

```text
‖wwave Λ u l r t - ∑_{h} Λ h‖ ≤ 2π |t| ∑_{h} u h · Λ h ,
```

and `∑_{h ≤ N} h Λ h ≈ N²/2` against `∑_{h ≤ N} Λ h ≈ N`, so the relative error is
`≈ π u N |t|`.  Hence a constant approximation is only available on `|t| ≤ 1/(u N)`;
the rest of the annulus needs the oscillation/window-kernel analysis.
-/

/-- The weighted progression minus its total mass, with the honest error term. -/
theorem wwave_mangoldt_sub_total_norm_le (u l r : ℕ) (t : ℝ) :
    ‖wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) u l r t
        - ∑ h ∈ Finset.Ioc l r, (ArithmeticFunction.vonMangoldt h : ℂ)‖
      ≤ 2 * Real.pi * |t| *
          ∑ h ∈ Finset.Ioc l r, ((u:ℝ) * (h:ℝ)) * ArithmeticFunction.vonMangoldt h := by
  have hsplit : wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) u l r t
        - ∑ h ∈ Finset.Ioc l r, (ArithmeticFunction.vonMangoldt h : ℂ)
      = ∑ h ∈ Finset.Ioc l r,
          ((ArithmeticFunction.vonMangoldt h : ℂ) * (phase ((u*h:ℕ)*t) - 1)) := by
    unfold wwave
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ h ∈ Finset.Ioc l r,
      ‖(ArithmeticFunction.vonMangoldt h : ℂ) * (phase ((u*h:ℕ)*t) - 1)‖
        ≤ ((u:ℝ)*(h:ℝ)) * ArithmeticFunction.vonMangoldt h * (2 * Real.pi * |t|) := by
    intro h _
    have hcast : |(((u*h:ℕ):ℝ) * t)| = (u:ℝ) * (h:ℝ) * |t| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (u*h))]
      push_cast
      ring
    have hnorm : ‖phase ((u*h:ℕ)*t : ℝ) - 1‖ ≤ 2 * Real.pi * ((u:ℝ) * (h:ℝ) * |t|) := by
      have := DyadicMixedB4ProgressionApprox.norm_phase_sub_one_le (((u*h:ℕ):ℝ) * t)
      rwa [hcast] at this
    calc ‖(ArithmeticFunction.vonMangoldt h : ℂ) * (phase ((u*h:ℕ)*t) - 1)‖
        = ArithmeticFunction.vonMangoldt h * ‖phase ((u*h:ℕ)*t) - 1‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ArithmeticFunction.vonMangoldt h * (2 * Real.pi * ((u:ℝ) * (h:ℝ) * |t|)) :=
          mul_le_mul_of_nonneg_left hnorm ArithmeticFunction.vonMangoldt_nonneg
      _ = ((u:ℝ)*(h:ℝ)) * ArithmeticFunction.vonMangoldt h * (2 * Real.pi * |t|) := by ring
  calc ∑ h ∈ Finset.Ioc l r,
        ‖(ArithmeticFunction.vonMangoldt h : ℂ) * (phase ((u*h:ℕ)*t) - 1)‖
      ≤ ∑ h ∈ Finset.Ioc l r,
          ((u:ℝ)*(h:ℝ)) * ArithmeticFunction.vonMangoldt h * (2 * Real.pi * |t|) :=
        Finset.sum_le_sum hterm
    _ = 2 * Real.pi * |t| *
          ∑ h ∈ Finset.Ioc l r, ((u:ℝ) * (h:ℝ)) * ArithmeticFunction.vonMangoldt h := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        ring

/-! ### Archimedean decay: the window transform of a single mode

The near-side annulus integral is `∫_{window q} phase (k t) · wwave`, and its
basic input is the decay of the transform of one mode,

```text
‖∫_{|x| ≤ ρ} e(k t) dt‖ ≤ 1/(π |k|) ,        (k ≠ 0)
```

so that an annulus (a difference of two balls) costs `2/(π|k|)`.
-/

/-- Oscillation bound for the Fourier integral over an interval. -/
theorem norm_integral_phase_osc (k : ℤ) (hk : k ≠ 0) {A B : ℝ} :
    ‖∫ t in A..B, phase ((k:ℝ)*t)‖ ≤ 1/(Real.pi * |(k:ℝ)|) := by
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : ((2*Real.pi*Complex.I) * (k:ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
    · exact_mod_cast hk
  have hcongr : ∀ t : ℝ,
      phase ((k:ℝ)*t) = Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (t:ℂ)) := by
    intro t
    unfold phase
    congr 1
    push_cast
    ring
  simp_rw [hcongr]
  rw [integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (B:ℂ)) -
      Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (A:ℂ))‖ ≤ 2 := by
    have hnorm : ∀ x : ℝ, ‖Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (x:ℂ))‖ = 1 := by
      intro x
      rw [Complex.norm_exp]
      have : (((2*Real.pi*Complex.I) * (k:ℂ)) * (x:ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [this, Real.exp_zero]
    calc ‖Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (B:ℂ)) -
          Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (A:ℂ))‖
        ≤ ‖Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (B:ℂ))‖ +
          ‖Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (A:ℂ))‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hnorm B, hnorm A]
      _ = 2 := by norm_num
  have hden : ‖((2*Real.pi*Complex.I) * (k:ℂ))‖ = 2*Real.pi*|(k:ℝ)| := by
    rw [norm_mul, norm_mul]
    have h1 : ‖(2 * (Real.pi:ℂ))‖ = 2*Real.pi := by
      rw [show (2 * (Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖(k:ℂ)‖ = |(k:ℝ)| := by
      rw [show (k:ℂ) = ((k:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2, Complex.norm_I, mul_one]
  rw [hden]
  have hdenpos : (0:ℝ) < 2*Real.pi*|(k:ℝ)| := by positivity
  rw [div_le_iff₀ hdenpos]
  have hval : (1/(Real.pi * |(k:ℝ)|)) * (2*Real.pi*|(k:ℝ)|) = 2 := by
    field_simp
  rw [hval]
  exact hnum

/-- The closed ball `{|x| ≤ ρ}` is an interval. -/
theorem integral_ball_eq {ρ : ℝ} (hρ : 0 ≤ ρ) (f : ℝ → ℂ) :
    (∫ t in {x : ℝ | |x| ≤ ρ}, f t) = ∫ t in (-ρ)..ρ, f t := by
  have hset : {x : ℝ | |x| ≤ ρ} = Set.Icc (-ρ) ρ := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  rw [hset, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (a := -ρ) (b := ρ) (by linarith)]

/-- Archimedean decay of the ball transform. -/
theorem norm_integral_ball_phase_le (k : ℤ) (hk : k ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖∫ t in {x : ℝ | |x| ≤ ρ}, phase ((k:ℝ)*t)‖ ≤ 1/(Real.pi * |(k:ℝ)|) := by
  rw [integral_ball_eq hρ]
  exact norm_integral_phase_osc k hk

/-- An annulus (difference of two concentric balls) costs twice the ball decay. -/
theorem norm_integral_annulus_phase_le (k : ℤ) (hk : k ≠ 0) {ρ inner : ℝ}
    (h0 : 0 ≤ inner) (hρ : inner ≤ ρ) :
    ‖∫ t in ({x : ℝ | |x| ≤ ρ} \ {x : ℝ | |x| ≤ inner}), phase ((k:ℝ)*t)‖
      ≤ 2/(Real.pi * |(k:ℝ)|) := by
  have hsub : {x : ℝ | |x| ≤ inner} ⊆ {x : ℝ | |x| ≤ ρ} := by
    intro x hx
    exact le_trans hx hρ
  have hmeas : MeasurableSet {x : ℝ | |x| ≤ inner} := by
    exact measurableSet_le continuous_abs.measurable measurable_const
  have hsubIcc : {x : ℝ | |x| ≤ ρ} ⊆ Set.Icc (-ρ) ρ := by
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le x, hx], by linarith [le_abs_self x, hx]⟩
  have hint : IntegrableOn (fun t : ℝ => phase ((k:ℝ)*t)) {x : ℝ | |x| ≤ ρ} := by
    have hc : Continuous fun t : ℝ => phase ((k:ℝ)*t) := by unfold phase; fun_prop
    exact (hc.integrableOn_Icc (a := -ρ) (b := ρ)).mono_set hsubIcc
  rw [MeasureTheory.setIntegral_sdiff hmeas hint hsub]
  refine (norm_sub_le _ _).trans ?_
  have h2 := norm_integral_ball_phase_le k hk h0
  have hρ0 : (0:ℝ) ≤ ρ := le_trans h0 hρ
  have h1' := norm_integral_ball_phase_le k hk hρ0
  have hden : (0:ℝ) < Real.pi * |(k:ℝ)| := by positivity
  have hval : 1/(Real.pi * |(k:ℝ)|) + 1/(Real.pi * |(k:ℝ)|) = 2/(Real.pi * |(k:ℝ)|) := by ring
  linarith [h1', h2]

/-! ### The exact reduction `Jdeep = D - W`

`Jdeep` is the deep-minor integral of `S_{τ₁}² e(-n·)`.  Splitting the circle at the
wide arcs gives

```text
Jdeep = D  -  W ,
D = ∑_{m + m' = n} τ₁(m) τ₁(m') ,        W = ∫_{wideArcs} S_{τ₁}² e(-n·) .
```

`D` is the *diagonal* (the full-circle Fourier coefficient) and `W` is the wide-arc
part.  Numerically `D = Θ(n log log² n)` (see `theta_numerics.py`), so `Jdeep = o(n)`
is a main-term *matching* statement, and this identity is its exact framework.
-/

/-- The diagonal sum `D = ∑_{m + m' = n} τ₁(m) τ₁(m')`. -/
def diagonalSum (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), ∑ m' ∈ Finset.range (n + 1),
    if m + m' = n then tauCoeff n m * tauCoeff n m' else 0

/-- The square of the polynomial, expanded on frequencies. -/
theorem plainPolynomial_sq_expand (n : ℕ) (t : ℝ) :
    plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t)
      = ∑ m ∈ Finset.range (n + 1), ∑ m' ∈ Finset.range (n + 1),
          tauCoeff n m * tauCoeff n m' *
            phase (((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) : ℝ) * t) := by
  unfold plainPolynomial
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  have hph : phase ((m:ℝ)*t) * phase ((m':ℝ)*t) * phase (-(n:ℝ)*t)
      = phase (((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) : ℝ) * t) := by
    rw [← phase_add, ← phase_add]
    congr 1
    push_cast
    ring
  calc (tauCoeff n m * phase ((m:ℝ)*t)) * (tauCoeff n m' * phase ((m':ℝ)*t)) * phase (-(n:ℝ)*t)
      = tauCoeff n m * tauCoeff n m' *
          (phase ((m:ℝ)*t) * phase ((m':ℝ)*t) * phase (-(n:ℝ)*t)) := by ring
    _ = _ := by rw [hph]

/-- The full-circle Fourier coefficient is the diagonal sum. -/
theorem integral_sq_phase_eq_diagonal (n : ℕ) :
    (∫ t in (0:ℝ)..1, plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t))
      = diagonalSum n := by
  classical
  have hpt : ∀ t : ℝ, plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t)
      = ∑ m ∈ Finset.range (n + 1), ∑ m' ∈ Finset.range (n + 1),
          tauCoeff n m * tauCoeff n m' *
            phase (((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) : ℝ) * t) :=
    fun t => plainPolynomial_sq_expand n t
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro m _
    exact (by unfold phase; fun_prop : Continuous fun t : ℝ =>
      ∑ m' ∈ Finset.range (n + 1), tauCoeff n m * tauCoeff n m' *
        phase (((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) : ℝ) * t)).intervalIntegrable _ _
  unfold diagonalSum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro m' _
    exact (by unfold phase; fun_prop : Continuous fun t : ℝ =>
      tauCoeff n m * tauCoeff n m' *
        phase (((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) : ℝ) * t)).intervalIntegrable _ _
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_phase_int]
  by_cases hmn : m + m' = n
  · have hk : ((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) = 0) := by
      have : (m:ℤ) + (m':ℤ) = (n:ℤ) := by exact_mod_cast hmn
      omega
    rw [if_pos hmn, if_pos hk, mul_one]
  · have hk : ((((m:ℤ) + (m':ℤ) - (n:ℤ) : ℤ)) ≠ 0) := by
      intro h0
      apply hmn
      have : (m:ℤ) + (m':ℤ) - (n:ℤ) = 0 := h0
      have h2 : (m:ℤ) + (m':ℤ) = (n:ℤ) := by omega
      exact_mod_cast h2
    rw [if_neg hmn, if_neg hk, mul_zero]

/-- **The exact reduction**: the deep-minor integral is `D` minus the wide-arc part. -/
theorem deepIntegral_eq_diagonal_sub_wide (n : ℕ) :
    deepIntegral n = diagonalSum n
      - ∫ t in (0:ℝ)..1, (wideSet n).indicator
          (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t := by
  have hcont : Continuous fun x : ℝ =>
      plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x) := by
    unfold plainPolynomial phase
    fun_prop
  have hmeas : MeasurableSet (wideSet n) := wide_measurable n (cutoffB n) (cutoffH n)
  have hAc : IntervalIntegrable ((wideSet n)ᶜ.indicator
      (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x))) MeasureTheory.volume 0 1 :=
    indicator_intervalIntegrable hcont hmeas.compl
  have hA : IntervalIntegrable ((wideSet n).indicator
      (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x))) MeasureTheory.volume 0 1 :=
    indicator_intervalIntegrable hcont hmeas
  have hpt : ∀ t : ℝ, plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t)
      = (wideSet n).indicator (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t
        + (wideSet n)ᶜ.indicator (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t := by
    intro t
    by_cases ht : t ∈ wideSet n
    · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem (by simpa using ht)]
      simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_mem (by simpa using ht)]
      simp
  have hsplit : (∫ t in (0:ℝ)..1, plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t))
      = (∫ t in (0:ℝ)..1, (wideSet n).indicator
            (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t)
        + ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator
            (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t := by
    rw [← intervalIntegral.integral_add hA hAc]
    exact intervalIntegral.integral_congr fun t _ => hpt t
  have hdeep : deepIntegral n = ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator
      (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t := by
    unfold deepIntegral
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ (wideSet n)ᶜ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, shiftedPolynomial_eq]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  rw [hdeep, ← integral_sq_phase_eq_diagonal n, hsplit]
  ring

/-- The `Λ` case of weighted Parseval. -/
theorem integral_wwave_mangoldt_norm_sq (u l r : ℕ) (hu : 0 < u) :
    (∫ t in (0:ℝ)..1,
        ‖wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) u l r t‖ ^ 2)
      = ∑ h ∈ Finset.Ioc l r, (ArithmeticFunction.vonMangoldt h) ^ 2 := by
  rw [integral_wwave_norm_sq _ hu]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Parseval for the task coefficient `τ₁`: its `L²` mass is the sum of the
squares of its values. -/
theorem integral_tauCoeff_norm_sq (n : ℕ) :
    (∫ t in (0:ℝ)..1, ‖plainPolynomial n (tauCoeff n) t‖ ^ 2)
      = ∑ m ∈ Finset.range (n + 1), ‖tauCoeff n m‖ ^ 2 := by
  simp_rw [← norm_shiftedPolynomial_eq n (tauCoeff n)]
  exact shiftedPolynomial_parseval n (tauCoeff n)

/-! ### The `L²` size of `S_{τ₁}`

The far side consumes `‖S_{τ₁}‖₂² = ∫ |S_{τ₁}|² = ∑_m |τ₁(m)|²`.  Here is the
elementary bound needed for it: with `T` a bound for `|c(a)|`,

```text
|τ₁(m)| ≤ T · ∑_{a | m, U < a ≤ B₁} Λ(m/a) ≤ T · ∑_{a | m} Λ(m/a) = T · log m ,
```

hence `∑_{m ≤ n} |τ₁(m)|² ≤ T² n (log n)²`.
-/

/-- Reindexing: `∑_{a | m} Λ(m/a) = log m`. -/
theorem sum_vonMangoldt_div_divisors (m : ℕ) :
    (∑ a ∈ m.divisors, ArithmeticFunction.vonMangoldt (m / a)) = Real.log m := by
  rw [← ArithmeticFunction.vonMangoldt_sum (n := m)]
  refine Finset.sum_nbij' (fun a : ℕ => m / a) (fun d : ℕ => m / d) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    refine Nat.mem_divisors.mpr ⟨⟨a, ?_⟩, (Nat.mem_divisors.mp ha).2⟩
    rw [Nat.mul_comm]
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)).symm
  · intro d hd
    refine Nat.mem_divisors.mpr ⟨⟨d, ?_⟩, (Nat.mem_divisors.mp hd).2⟩
    rw [Nat.mul_comm]
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
  · intro a ha
    obtain ⟨⟨k, hk⟩, hm0⟩ := Nat.mem_divisors.mp ha
    have hapos : 0 < a := Nat.pos_of_mem_divisors ha
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · rw [h0, mul_zero] at hk; omega
      · exact h
    have hm_eq : m = a * k := hk
    have h1 : m / a = k := by rw [hm_eq, Nat.mul_comm a k, Nat.mul_div_cancel k hapos]
    have h2 : m / k = a := by rw [hm_eq, Nat.mul_div_cancel a hkpos]
    rw [h1, h2]
  · intro d hd
    obtain ⟨⟨k, hk⟩, hm0⟩ := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · rw [h0, mul_zero] at hk; omega
      · exact h
    have hm_eq : m = d * k := hk
    have h1 : m / d = k := by rw [hm_eq, Nat.mul_comm d k, Nat.mul_div_cancel k hdpos]
    have h2 : m / k = d := by rw [hm_eq, Nat.mul_div_cancel d hkpos]
    rw [h1, h2]
  · intro a _
    rfl

/-- Pointwise size of the task coefficient. -/
theorem tauCoeff_abs_le (n m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ a, cutoffU n < a → a ≤ lowCut n → |lowMoebiusWeight (cutoffU n) a| ≤ T) :
    ‖tauCoeff n m‖ ≤ T * Real.log m := by
  classical
  unfold tauCoeff lowBandCoefficient
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hstep : ∀ a ∈ (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a),
      |lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)|
        ≤ T * ArithmeticFunction.vonMangoldt (m / a) := by
    intro a ha
    obtain ⟨_, hUa, haB, _⟩ := Finset.mem_filter.mp ha
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_right (hc a hUa haB) ArithmeticFunction.vonMangoldt_nonneg
  calc |∑ a ∈ (Nat.divisors m).filter
          (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a),
          lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)|
      ≤ ∑ a ∈ (Nat.divisors m).filter
          (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a),
          |lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Nat.divisors m).filter
          (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a),
          T * ArithmeticFunction.vonMangoldt (m / a) := Finset.sum_le_sum hstep
    _ ≤ ∑ a ∈ Nat.divisors m, T * ArithmeticFunction.vonMangoldt (m / a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro a _ _
        exact mul_nonneg hT ArithmeticFunction.vonMangoldt_nonneg
    _ = T * ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt (m / a) := by
        rw [Finset.mul_sum]
    _ = T * Real.log m := by rw [sum_vonMangoldt_div_divisors]

/-- `L²` bound for `S_{τ₁}`. -/
theorem integral_tauCoeff_norm_sq_le (n : ℕ) (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ a, cutoffU n < a → a ≤ lowCut n → |lowMoebiusWeight (cutoffU n) a| ≤ T) :
    (∫ t in (0:ℝ)..1, ‖plainPolynomial n (tauCoeff n) t‖ ^ 2)
      ≤ T ^ 2 * ((n : ℝ) + 1) * (Real.log n) ^ 2 := by
  rw [integral_tauCoeff_norm_sq]
  have hlog : ∀ m ∈ Finset.range (n + 1), (Real.log (m:ℝ)) ^ 2 ≤ (Real.log (n:ℝ)) ^ 2 := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simpa using sq_nonneg (Real.log (n:ℝ))
    · have h1 : Real.log (m:ℝ) ≤ Real.log (n:ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hmn)
      have h2 : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
      nlinarith [h1, h2]
  have hsum : (∑ m ∈ Finset.range (n + 1), ‖tauCoeff n m‖ ^ 2)
      ≤ ∑ m ∈ Finset.range (n + 1), T ^ 2 * (Real.log (n:ℝ)) ^ 2 := by
    refine Finset.sum_le_sum fun m hm => ?_
    have h1 : ‖tauCoeff n m‖ ≤ T * Real.log (m:ℝ) := tauCoeff_abs_le n m hT hc
    have h2 : (Real.log (m:ℝ)) ^ 2 ≤ (Real.log (n:ℝ)) ^ 2 := hlog m hm
    have h3 : 0 ≤ Real.log (m:ℝ) := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; simp
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    calc ‖tauCoeff n m‖ ^ 2 ≤ (T * Real.log (m:ℝ)) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = T ^ 2 * (Real.log (m:ℝ)) ^ 2 := by ring
      _ ≤ T ^ 2 * (Real.log (n:ℝ)) ^ 2 := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine hsum.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl


/-! ### The bridge to the prime-indicator major-arc model

`Λ` and the prime indicator `w k = if k is prime then log k else 0` agree on
primes and differ exactly on the prime powers `p^j` with `j ≥ 2`.  Splitting each
atom into its prime part and this correction is what lets the verified
major-arc model (`L_goldbach_frontier_medcore_bv_band`, stated for `S n w`)
be applied to `S_{τ₁}`.
-/

/-- The prime part of one atom. -/
def primeWave (a U N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (U+1) N,
    (if Nat.Prime k then (Real.log (k:ℝ) : ℂ) else 0) * phase ((a*k:ℕ)*t)

/-- The prime-power correction `Λ - w` of one atom. -/
def primePowerCorrection (a U N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (U+1) N,
    ((ArithmeticFunction.vonMangoldt k : ℂ) -
      (if Nat.Prime k then (Real.log (k:ℝ) : ℂ) else 0)) * phase ((a*k:ℕ)*t)

/-- An atom is its prime part plus the prime-power correction. -/
theorem atomWave_eq_primeWave_add_correction (a U N : ℕ) (t : ℝ) :
    atomWave a U N t = primeWave a U N t + primePowerCorrection a U N t := by
  unfold atomWave primeWave primePowerCorrection
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The prime-power correction is bounded by the total `Λ`-mass of the composite
prime powers in the range. -/
theorem primePowerCorrection_norm_le (a U N : ℕ) (t : ℝ) :
    ‖primePowerCorrection a U N t‖
      ≤ ∑ k ∈ Finset.Icc (U+1) N,
          if Nat.Prime k then 0 else ArithmeticFunction.vonMangoldt k := by
  unfold primePowerCorrection
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, show ‖phase ((a*k:ℕ)*t)‖ = 1 from by simp, mul_one]
  by_cases hp : Nat.Prime k
  · rw [if_pos hp]
    have hlam : ArithmeticFunction.vonMangoldt k = Real.log (k:ℝ) :=
      ArithmeticFunction.vonMangoldt_apply_prime hp
    rw [if_pos hp, hlam]
    simp
  · rw [if_neg hp, if_neg hp, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- **Prime/major-arc split of `S_{τ₁}`.** -/
theorem plainPolynomial_tauCoeff_prime_split (n : ℕ) (t : ℝ) :
    plainPolynomial n (tauCoeff n) t
      = (∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) * primeWave a (cutoffU n) (n / a) t)
        + ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) *
            primePowerCorrection a (cutoffU n) (n / a) t := by
  unfold tauCoeff
  rw [plainPolynomial_tau1]
  simp_rw [atomWave_eq_primeWave_add_correction, mul_add]
  rw [Finset.sum_add_distrib]

/-- The prime-indicator exponential sum up to `N`, evaluated at `θ`. -/
def primeSum (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N+1), (if Nat.Prime k then (Real.log (k:ℝ) : ℂ) else 0) * phase ((k:ℝ)*θ)

/-- **Dilation**: the prime part of an atom is the prime sum up to `n/a` evaluated
at the dilated point `a·t`, minus the short `k ≤ U` truncation. -/
theorem primeWave_eq_dilated (a U N : ℕ) (t : ℝ) (hU : U ≤ N) :
    primeWave a U N t = primeSum N ((a:ℝ)*t) - primeSum U ((a:ℝ)*t) := by
  classical
  set W : ℕ → ℂ := fun k => (if Nat.Prime k then (Real.log (k:ℝ) : ℂ) else 0) *
    phase ((k:ℝ) * ((a:ℝ)*t)) with hW
  have hprimeWave : primeWave a U N t
      = ∑ k ∈ (Finset.range (N+1)).filter (fun k => U < k), W k := by
    unfold primeWave
    refine Finset.sum_congr ?_ (fun k _ => ?_)
    · ext k
      simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_filter]
      omega
    · simp only [hW]
      congr 2
      push_cast
      ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (N+1)) (fun k => U < k) W
  have hnot : (Finset.range (N+1)).filter (fun k => ¬ U < k) = Finset.range (U+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hnot] at hsplit
  rw [hprimeWave]
  unfold primeSum
  rw [← hsplit]
  ring

/-- **The full dilation bridge for `S_{τ₁}`.** -/
theorem plainPolynomial_tauCoeff_dilated (n : ℕ) (t : ℝ)
    (hUa : ∀ a, cutoffU n + 1 ≤ a → a ≤ lowCut n → cutoffU n ≤ n / a) :
    plainPolynomial n (tauCoeff n) t
      = (∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) * primeSum (n / a) ((a:ℝ)*t))
        - (∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) * primeSum (cutoffU n) ((a:ℝ)*t))
        + ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) *
            primePowerCorrection a (cutoffU n) (n / a) t := by
  rw [plainPolynomial_tauCoeff_prime_split]
  have h1 : ∀ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
      (lowMoebiusWeight (cutoffU n) a : ℂ) * primeWave a (cutoffU n) (n / a) t
        = (lowMoebiusWeight (cutoffU n) a : ℂ) * primeSum (n / a) ((a:ℝ)*t)
          - (lowMoebiusWeight (cutoffU n) a : ℂ) * primeSum (cutoffU n) ((a:ℝ)*t) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    rw [primeWave_eq_dilated a (cutoffU n) (n / a) t (hUa a h1 h2)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]

/-- `primeSum` is literally the module's `S n w`, i.e. the prime indicator
times `log`, with the same exponential kernel.  This is the interface on which
the verified major-arc modules are stated. -/
theorem primeSum_eq_module (N : ℕ) (θ : ℝ) :
    primeSum N θ
      = ∑ k ∈ Finset.range (N+1),
          (((if Nat.Prime k then Real.log (k:ℝ) else 0) : ℝ) : ℂ) * phase ((k:ℝ)*θ) := by
  unfold primeSum
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : Nat.Prime k <;> simp [hk]

/-! ### Weighted phase-quadruple expansion

The weighted analogue of the verified `phase-quadruple-expansion`: the square of
`S_{τ₁}` times `e(-n·)` written as an explicit sum over the four atom indices and
the frequency `a j + a' k - n`.  This is the first step of the `exact_split`
port: after this, integrating over the arc complement collects the `sinc` kernel.
-/

/-- Pair expansion for two weighted progressions. -/
theorem wwave_pair_expand (c c' : ℕ → ℂ) (a a' U U' N N' n : ℕ) (t : ℝ) :
    wwave c a U N t * wwave c' a' U' N' t * phase (-(n:ℝ)*t)
      = ∑ j ∈ Finset.Ioc U N, ∑ k ∈ Finset.Ioc U' N',
          (c j * c' k) *
            phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * t) := by
  unfold wwave
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (c j * phase ((a*j:ℕ)*t)) * (c' k * phase ((a'*k:ℕ)*t)) * phase (-(n:ℝ)*t)
      = (c j * c' k) * (phase ((a*j:ℕ)*t) * phase ((a'*k:ℕ)*t) * phase (-(n:ℝ)*t)) from by ring]
  rw [← phase_add, ← phase_add]
  congr 2
  push_cast
  ring

/-- **The weighted phase-quadruple expansion** for `S_{τ₁}`. -/
theorem plainPolynomial_sq_dilated_expand (n : ℕ) (t : ℝ) :
    plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t)
      = ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
            ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
              ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
                ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                  ((ArithmeticFunction.vonMangoldt j : ℂ) *
                    (ArithmeticFunction.vonMangoldt k : ℂ)) *
                    phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * t) := by
  unfold tauCoeff
  rw [plainPolynomial_tau1]
  simp_rw [atomWave_eq_wwave]
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [show ((lowMoebiusWeight (cutoffU n) a : ℂ) *
        wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a) t) *
      ((lowMoebiusWeight (cutoffU n) a' : ℂ) *
        wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a' (cutoffU n) (n / a') t) *
      phase (-(n:ℝ)*t)
      = ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
        (wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a (cutoffU n) (n / a) t *
          wwave (fun h => (ArithmeticFunction.vonMangoldt h : ℂ)) a' (cutoffU n) (n / a') t *
          phase (-(n:ℝ)*t)) from by ring]
  rw [wwave_pair_expand]

/-! ### The archimedean sinc factor

The `spatial_exact_split` port collects, for each frequency `m`, the ball
transform

```text
∫_{|β| ≤ ρ} e(m β) dβ  =  sin (2π m ρ) / (π m) .
```

First in exponential form, then converted to `sin`.
-/

/-- Ball transform of one mode, exponential form. -/
theorem integral_phase_symmetric_exp (m : ℤ) (hm : m ≠ 0) (ρ : ℝ) :
    (∫ β in (-ρ)..ρ, phase ((m:ℝ)*β))
      = (Complex.exp (Complex.I * ((2*Real.pi*(m:ℝ)*ρ : ℝ):ℂ)) -
          Complex.exp (-(Complex.I * ((2*Real.pi*(m:ℝ)*ρ : ℝ):ℂ)))) /
          (2*Real.pi*((m:ℝ):ℂ)*Complex.I) := by
  have hc : ((2*Real.pi*Complex.I) * (m:ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
    · exact_mod_cast hm
  have hcongr : ∀ β : ℝ,
      phase ((m:ℝ)*β) = Complex.exp (((2*Real.pi*Complex.I) * (m:ℂ)) * (β:ℂ)) := by
    intro β
    unfold phase
    congr 1
    push_cast
    ring
  simp_rw [hcongr]
  rw [integral_exp_mul_complex hc]
  have hb : ((2*Real.pi*Complex.I) * (m:ℂ)) * ((ρ:ℝ):ℂ)
      = Complex.I * ((2*Real.pi*(m:ℝ)*ρ : ℝ):ℂ) := by push_cast; ring
  have ha : ((2*Real.pi*Complex.I) * (m:ℂ)) * (((-ρ):ℝ):ℂ)
      = -(Complex.I * ((2*Real.pi*(m:ℝ)*ρ : ℝ):ℂ)) := by push_cast; ring
  have hcval : ((2*Real.pi*Complex.I) * (m:ℂ)) = 2*Real.pi*((m:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [hb, ha, hcval]

/-- Ball transform of one mode, `sinc` form. -/
theorem integral_phase_symmetric (m : ℤ) (hm : m ≠ 0) (ρ : ℝ) :
    (∫ β in (-ρ)..ρ, phase ((m:ℝ)*β))
      = ((Real.sin (2*Real.pi*(m:ℝ)*ρ) : ℝ) : ℂ) / ((Real.pi*(m:ℝ) : ℝ) : ℂ) := by
  rw [integral_phase_symmetric_exp m hm ρ]
  set y : ℝ := 2*Real.pi*(m:ℝ)*ρ with hy
  have hsin : Complex.exp (Complex.I * (y:ℂ)) - Complex.exp (-(Complex.I * (y:ℂ)))
      = 2 * Complex.I * ((Real.sin y : ℝ) : ℂ) := by
    have e2 : -(Complex.I * (y:ℂ)) = ((-y:ℝ):ℂ) * Complex.I := by push_cast; ring
    have e1 : Complex.I * (y:ℂ) = (y:ℂ) * Complex.I := mul_comm _ _
    rw [e2, e1, Complex.exp_ofReal_mul_I y, Complex.exp_ofReal_mul_I (-y),
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hsin]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  have hpi : ((Real.pi*(m:ℝ) : ℝ) : ℂ) ≠ 0 := by
    have h : Real.pi*(m:ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hden : 2*Real.pi*((m:ℝ):ℂ)*Complex.I ≠ 0 := by
    have h2pi : (2*Real.pi : ℂ) ≠ 0 := by
      have h : (2*Real.pi : ℝ) ≠ 0 := by positivity
      exact_mod_cast h
    have hmC : ((m:ℝ):ℂ) ≠ 0 := by exact_mod_cast hmR
    exact mul_ne_zero (mul_ne_zero h2pi hmC) hI
  rw [div_eq_div_iff hden hpi]
  push_cast
  ring

/-- Ball transform of one mode in `sinc` form, as a set integral. -/
theorem integral_ball_phase_eq_sinc (m : ℤ) (hm : m ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫ t in {x : ℝ | |x| ≤ ρ}, phase ((m:ℝ)*t))
      = ((Real.sin (2*Real.pi*(m:ℝ)*ρ) : ℝ) : ℂ) / ((Real.pi*(m:ℝ) : ℝ) : ℂ) := by
  rw [integral_ball_eq hρ, integral_phase_symmetric m hm ρ]


/-! ### The wide-arc integral split (ported from `arcsplit.lean`) -/

def logSq (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

/-- The individual arc of denominator `q` and numerator `a`. -/
def arcSet (n q a : ℕ) : Set ℝ :=
  {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))}

lemma arcSet_measurable (n q a : ℕ) : MeasurableSet (arcSet n q a) := by
  unfold arcSet
  exact measurableSet_le (by fun_prop) measurable_const

lemma intervalIntegrable_indicator {f : ℝ → ℂ} {s : Set ℝ} (hf : Continuous f)
    (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hs

/-- Membership in the wide arcs, in the arc-family form used by the integral
expansion. -/
lemma mem_wideSet_iff (n : ℕ) (t : ℝ) :
    t ∈ wideSet n ↔
      ∃ q ∈ Finset.Icc 1 (cutoffB n),
        ∃ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          t ∈ arcSet n q a := by
  simp only [wideSet, wide, Set.mem_setOf_eq, arcSet, Finset.mem_Icc, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨q, a, hq1, hqQ, haq, hcop, hle⟩
    exact ⟨q, ⟨hq1, hqQ⟩, a, ⟨by omega, hcop⟩, hle⟩
  · rintro ⟨q, ⟨hq1, hqQ⟩, a, ⟨haq, hcop⟩, hle⟩
    exact ⟨q, a, hq1, hqQ, by omega, hcop, hle⟩

/-- Reduced fractions are equal only if numerator and denominator agree. -/
lemma fraction_inj {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (h : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ)) : a = a' ∧ q = q' := by
  have hcross : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by
    have h' : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h
      exact h
    exact_mod_cast h'
  have hqq' : q = q' := by
    have hdvd : (q:ℤ) ∣ (q':ℤ) := by
      have hq_dvd : (q:ℤ) ∣ (a:ℤ) * (q':ℤ) :=
        ⟨(a':ℤ), by rw [mul_comm (q:ℤ) (a':ℤ)]; exact hcross⟩
      have hcopZ : IsCoprime (q:ℤ) (a:ℤ) := hcop.symm.isCoprime
      have hq_dvd' : (q:ℤ) ∣ (q':ℤ) * (a:ℤ) := by rw [mul_comm]; exact hq_dvd
      exact hcopZ.dvd_of_dvd_mul_right hq_dvd'
    have hdvd' : q ∣ q' := by exact_mod_cast hdvd
    have hdvd2 : (q':ℤ) ∣ (q:ℤ) := by
      have hq'_dvd : (q':ℤ) ∣ (a':ℤ) * (q:ℤ) :=
        ⟨(a:ℤ), by rw [mul_comm (q':ℤ) (a:ℤ)]; exact hcross.symm⟩
      have hcopZ' : IsCoprime (q':ℤ) (a':ℤ) := hcop'.symm.isCoprime
      have hq'_dvd' : (q':ℤ) ∣ (q:ℤ) * (a':ℤ) := by rw [mul_comm]; exact hq'_dvd
      exact hcopZ'.dvd_of_dvd_mul_right hq'_dvd'
    have hdvd2' : q' ∣ q := by exact_mod_cast hdvd2
    exact Nat.le_antisymm (Nat.le_of_dvd hq' hdvd') (Nat.le_of_dvd hq hdvd2')
  have haa' : a = a' := by
    have hZ : (a:ℤ) * (q:ℤ) = (a':ℤ) * (q:ℤ) := by
      rw [hqq']
      have hc := hcross
      rw [hqq'] at hc
      exact hc
    have hqZ : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (a:ℤ) = (a':ℤ) := mul_right_cancel₀ hqZ hZ
    exact_mod_cast h
  exact ⟨haa', hqq'⟩

/-- Radius-sum inequality: for `q, q' ≤ Q₁` the two semi-widths sum to less
than the Farey spacing, provided `512 Q₁² Q < n`. -/
lemma radius_sum_lt (n q q' : ℕ) (hn : 512 * (cutoffB n)^2 * logSq n < n)
    (hqQ : q ≤ cutoffB n) (hq'Q : q' ≤ cutoffB n) :
    (cutoffH n : ℝ) * ((q:ℝ) + (q':ℝ)) < (n:ℝ) := by
  have hH : (cutoffH n : ℝ) = 256 * (cutoffB n : ℝ) * (logSq n : ℝ) := by
    unfold cutoffH logSq
    push_cast
    ring
  have hsum : (q:ℝ) + (q':ℝ) ≤ 2 * (cutoffB n : ℝ) := by
    have h1 : (q:ℝ) ≤ (cutoffB n : ℝ) := by exact_mod_cast hqQ
    have h2 : (q':ℝ) ≤ (cutoffB n : ℝ) := by exact_mod_cast hq'Q
    linarith
  have hbound : (cutoffH n : ℝ) * ((q:ℝ) + (q':ℝ)) ≤
      256 * (cutoffB n : ℝ) * (logSq n : ℝ) * (2 * (cutoffB n : ℝ)) := by
    rw [hH]
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have hcast : (512 * (cutoffB n)^2 * logSq n : ℕ) < n := hn
  have hcastR : (256 * (cutoffB n : ℝ) * (logSq n : ℝ) * (2 * (cutoffB n : ℝ))) < (n:ℝ) := by
    have : (256 * (cutoffB n : ℝ) * (logSq n : ℝ) * (2 * (cutoffB n : ℝ))) =
        ((512 * (cutoffB n)^2 * logSq n : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast hcast
  linarith

/-- The individual wide arcs are pairwise disjoint for large `n`. -/
lemma arcs_disjoint (n : ℕ) (hn : 512 * (cutoffB n)^2 * logSq n < n)
    {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ cutoffB n) (hq'Q : q' ≤ cutoffB n)
    (hne : (a:ℝ)/(q:ℝ) ≠ (a':ℝ)/(q':ℝ)) :
    Disjoint (arcSet n q a) (arcSet n q' a') := by
  rw [Set.disjoint_left]
  intro t h1 h2
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'pos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hspacing : (1:ℝ)/((q:ℝ)*(q':ℝ)) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| := by
    set z : ℤ := (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) with hz
    have hzne : z ≠ 0 := by
      intro h0
      apply hne
      have hcross : (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) = 0 := by rwa [← hz]
      have h1 : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by omega
      have h2 : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by exact_mod_cast h1
      rw [div_eq_div_iff (ne_of_gt hqpos) (ne_of_gt hq'pos)]
      exact h2
    have habs : (1:ℤ) ≤ |z| := Int.one_le_abs hzne
    have hkey : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| = ((|z| : ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
      have hnum : (a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ) = ((z:ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
        rw [hz]; push_cast; field_simp
      rw [hnum, abs_div, ← Int.cast_abs, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ)*(q':ℝ))]
    rw [hkey]
    exact div_le_div_of_nonneg_right (by exact_mod_cast habs) (by positivity)
  have htri : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| ≤
      (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) + (cutoffH n:ℝ)/((q':ℝ)*(n:ℝ)) := by
    calc |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)|
        = |((a:ℝ)/(q:ℝ) - t) + (t - (a':ℝ)/(q':ℝ))| := by ring_nf
      _ ≤ |(a:ℝ)/(q:ℝ) - t| + |t - (a':ℝ)/(q':ℝ)| := abs_add_le _ _
      _ = |t - (a:ℝ)/(q:ℝ)| + |t - (a':ℝ)/(q':ℝ)| := by rw [abs_sub_comm]
      _ ≤ _ := add_le_add h1 h2
  have hlt : (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) + (cutoffH n:ℝ)/((q':ℝ)*(n:ℝ)) <
      (1:ℝ)/((q:ℝ)*(q':ℝ)) := by
    have hsum := radius_sum_lt n q q' hn hqQ hq'Q
    have hden : (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) + (cutoffH n:ℝ)/((q':ℝ)*(n:ℝ)) =
        (cutoffH n:ℝ) * ((q:ℝ) + (q':ℝ)) / ((q:ℝ)*(q':ℝ)*(n:ℝ)) := by
      field_simp
      ring
    rw [hden]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have hsum' := mul_lt_mul_of_pos_right hsum hpos
    nlinarith [hsum']
  exact absurd (lt_of_le_of_lt hspacing (lt_of_le_of_lt htri hlt)) (lt_irrefl _)

/-- Arc indices are unique: a point of the circle lies in at most one wide arc. -/
lemma arcSet_unique (n : ℕ) (hn : 512 * (cutoffB n)^2 * logSq n < n)
    {q q' a a' : ℕ}
    (hq : q ∈ Finset.Icc 1 (cutoffB n)) (hq' : q' ∈ Finset.Icc 1 (cutoffB n))
    (ha : a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q))
    (ha' : a' ∈ (Finset.range (q'+1)).filter (fun a => Nat.Coprime a q'))
    {t : ℝ} (ht : t ∈ arcSet n q a) (ht' : t ∈ arcSet n q' a') :
    q = q' ∧ a = a' := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq'1 : 1 ≤ q' := (Finset.mem_Icc.mp hq').1
  have hqpos : 0 < q := by omega
  have hq'pos : 0 < q' := by omega
  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have hcop' : Nat.Coprime a' q' := (Finset.mem_filter.mp ha').2
  by_cases hfrac : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ)
  · obtain ⟨haa, hqq⟩ := fraction_inj hqpos hq'pos hcop hcop' hfrac
    exact ⟨hqq, haa⟩
  · exfalso
    exact Set.disjoint_left.mp
      (arcs_disjoint n hn hqpos hq'pos (Finset.mem_Icc.mp hq).2
        (Finset.mem_Icc.mp hq').2 hfrac) ht ht'

/-- Pointwise: the indicator of the wide arcs is the sum of the indicators of
the individual arcs. -/
lemma wideSet_indicator_eq_sum (n : ℕ) (hn : 512 * (cutoffB n)^2 * logSq n < n)
    (f : ℝ → ℂ) (t : ℝ) :
    (wideSet n).indicator f t =
      ∑ q ∈ Finset.Icc 1 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t := by
  classical
  by_cases ht : t ∈ wideSet n
  · obtain ⟨q0, hq0, a0, ha0, ht0⟩ := (mem_wideSet_iff n t).mp ht
    have collapse : (∑ q ∈ Finset.Icc 1 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t) = f t := by
      rw [Finset.sum_eq_single q0]
      · rw [Finset.sum_eq_single a0]
        · exact Set.indicator_of_mem ht0 f
        · intro a ha hane
          exact Set.indicator_of_notMem
            (fun hta => hane (arcSet_unique n hn hq0 hq0 ha0 ha ht0 hta).2.symm) f
        · intro ha0notin
          exact absurd ha0 ha0notin
      · intro q hq hqne
        apply Finset.sum_eq_zero
        intro a ha
        exact Set.indicator_of_notMem
          (fun hta => hqne (arcSet_unique n hn hq hq0 ha ha0 hta ht0).1) f
      · intro hq0notin
        exact absurd hq0 hq0notin
    rw [Set.indicator_of_mem ht f, collapse]
  · have : ∀ q ∈ Finset.Icc 1 (cutoffB n),
        (∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t) = 0 := by
      intro q hq
      apply Finset.sum_eq_zero
      intro a ha
      exact Set.indicator_of_notMem
        (fun hta => ht ((mem_wideSet_iff n t).mpr ⟨q, hq, a, ha, hta⟩)) f
    rw [Set.indicator_of_notMem ht f]
    rw [Finset.sum_congr rfl this]
    simp

/-- The integral over the wide arcs is the sum of the integrals over the
individual arcs. -/
lemma integral_wideSet_eq_sum (n : ℕ) (hn : 512 * (cutoffB n)^2 * logSq n < n)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, (wideSet n).indicator f t)
      = ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
            ∫ t in (0:ℝ)..1, (arcSet n q a).indicator f t := by
  have hpt : ∀ t : ℝ, (wideSet n).indicator f t =
      ∑ q ∈ Finset.Icc 1 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t := fun t => wideSet_indicator_eq_sum n hn f t
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum]
    intro a ha
    exact indicator_intervalIntegrable hf (arcSet_measurable n q a)
  · intro q hq
    convert IntervalIntegrable.sum ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q))
      (fun a ha => indicator_intervalIntegrable hf (arcSet_measurable n q a)) using 1
    ext t
    rw [Finset.sum_apply]


/-- The arc is the closed interval centred at `a/q`. -/
theorem arcSet_eq_Icc (n q a : ℕ) :
    arcSet n q a = Set.Icc ((a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))
      ((a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))) := by
  ext t
  simp only [arcSet, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **The sinc factor of one arc**: the full arc integral of one mode. -/
theorem integral_arcSet_phase (n q a : ℕ) (m : ℤ) (hm : m ≠ 0) :
    (∫ t in arcSet n q a, phase ((m:ℝ)*t))
      = phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
          (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
            ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  set c : ℝ := (a:ℝ)/(q:ℝ) with hc
  set ρ : ℝ := (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) with hρ
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  rw [show arcSet n q a = Set.Icc (c - ρ) (c + ρ) from by
    rw [hc, hρ]; exact arcSet_eq_Icc n q a]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := c - ρ) (b := c + ρ) (by linarith)]
  rw [show c - ρ = c + (-ρ) from by ring]
  rw [← intervalIntegral.integral_comp_add_left (f := fun t : ℝ => phase ((m:ℝ)*t))
    (a := -ρ) (b := ρ) (d := c)]
  have hfact : ∀ β : ℝ, phase ((m:ℝ)*(c+β)) = phase ((m:ℝ)*c) * phase ((m:ℝ)*β) := by
    intro β
    rw [show (m:ℝ)*(c+β) = (m:ℝ)*c + (m:ℝ)*β by ring, ← phase_add]
  simp_rw [hfact]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact integral_phase_symmetric m hm ρ

/-- For an arc strictly inside `(0,1)`, the clipped indicator integral is the full
arc integral. -/
theorem integral_arcSet_indicator_phase_of_inside (n q a : ℕ) (m : ℤ)
    (hleft : 0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))
    (hright : (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n q a).indicator (fun y => phase ((m:ℝ)*y)) t)
      = ∫ t in arcSet n q a, phase ((m:ℝ)*t) := by
  have hsub : arcSet n q a ⊆ Set.Ioc (0:ℝ) 1 := by
    intro t ht
    rw [arcSet_eq_Icc] at ht
    obtain ⟨h1, h2⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hmeas : MeasurableSet (arcSet n q a) := arcSet_measurable n q a
  have hsupp : ∀ x ∉ Set.Ioc (0:ℝ) 1,
      (arcSet n q a).indicator (fun y => phase ((m:ℝ)*y)) x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx (hsub hc)) (fun y => phase ((m:ℝ)*y))
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    MeasureTheory.integral_indicator hmeas]

/-- The sinc sum over the arc family (the `sincKernel` sum). -/
theorem sum_arcSet_phase (n : ℕ) (m : ℤ) (hm : m ≠ 0) :
    (∑ q ∈ Finset.Icc 1 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          ∫ t in arcSet n q a, phase ((m:ℝ)*t))
      = ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
            phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
              (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
                ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  exact integral_arcSet_phase n q a m hm

/-- The phase at an integer is `1`. -/
theorem phase_int (k : ℤ) : phase ((k:ℝ)) = 1 := by
  unfold phase
  rw [show (((2 * Real.pi * (k:ℝ) : ℝ) : ℂ) * Complex.I)
      = (k:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- **Boundary arcs**: by `1`-periodicity of `e(m·)`, the two clipped boundary
pieces at `0` and `1` combine to the full ball at `0`. -/
theorem integral_boundary_arcs (m : ℤ) (ρ : ℝ) :
    (∫ t in (0:ℝ)..ρ, phase ((m:ℝ)*t)) + (∫ t in (1-ρ)..1, phase ((m:ℝ)*t))
      = ∫ t in (-ρ)..ρ, phase ((m:ℝ)*t) := by
  have hcont : Continuous fun t : ℝ => phase ((m:ℝ)*t) := by unfold phase; fun_prop
  have hone : ∀ u : ℝ, phase ((m:ℝ)*(u+1)) = phase ((m:ℝ)*u) := by
    intro u
    rw [show (m:ℝ)*(u+1) = (m:ℝ)*u + (m:ℝ) by ring, phase_add, phase_int, mul_one]
  have hshift : (∫ t in (1-ρ)..1, phase ((m:ℝ)*t))
      = ∫ u in (-ρ)..0, phase ((m:ℝ)*u) := by
    have h := intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => phase ((m:ℝ)*t)) (a := -ρ) (b := 0) (1:ℝ)
    simp only [neg_add_cancel, zero_add] at h
    rw [show (-ρ + 1 : ℝ) = 1 - ρ by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun u _ => hone u
  rw [hshift, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]

/-- Splitting the circle at the wide arcs: `∫_{Aᶜ} = ∫₀¹ - ∫_A`. -/
theorem integral_compl_indicator_phase (n : ℕ) (m : ℤ) :
    (∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator (fun y => phase ((m:ℝ)*y)) t)
      = (∫ t in (0:ℝ)..1, phase ((m:ℝ)*t))
        - ∫ t in (0:ℝ)..1, (wideSet n).indicator (fun y => phase ((m:ℝ)*y)) t := by
  have hcont : Continuous fun t : ℝ => phase ((m:ℝ)*t) := by unfold phase; fun_prop
  have hmeas : MeasurableSet (wideSet n) := wide_measurable n (cutoffB n) (cutoffH n)
  have hA : IntervalIntegrable ((wideSet n).indicator (fun y => phase ((m:ℝ)*y)))
      MeasureTheory.volume 0 1 := indicator_intervalIntegrable hcont hmeas
  have hAc : IntervalIntegrable ((wideSet n)ᶜ.indicator (fun y => phase ((m:ℝ)*y)))
      MeasureTheory.volume 0 1 := indicator_intervalIntegrable hcont hmeas.compl
  have hpt : ∀ t : ℝ, phase ((m:ℝ)*t)
      = (wideSet n).indicator (fun y => phase ((m:ℝ)*y)) t
        + (wideSet n)ᶜ.indicator (fun y => phase ((m:ℝ)*y)) t := by
    intro t
    by_cases ht : t ∈ wideSet n
    · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem (by simpa using ht)]
      simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_mem (by simpa using ht)]
      simp
  have hsplit : (∫ t in (0:ℝ)..1, phase ((m:ℝ)*t))
      = (∫ t in (0:ℝ)..1, (wideSet n).indicator (fun y => phase ((m:ℝ)*y)) t)
        + ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator (fun y => phase ((m:ℝ)*y)) t := by
    rw [← intervalIntegral.integral_add hA hAc]
    exact intervalIntegral.integral_congr fun t _ => hpt t
  rw [hsplit]
  ring

/-- For nonzero frequency the full circle contributes nothing, so the complement
integral is minus the wide-arc integral. -/
theorem integral_compl_indicator_phase_eq (n : ℕ) (m : ℤ) (hm : m ≠ 0) :
    (∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator (fun y => phase ((m:ℝ)*y)) t)
      = - ∫ t in (0:ℝ)..1, (wideSet n).indicator (fun y => phase ((m:ℝ)*y)) t := by
  rw [integral_compl_indicator_phase, integral_phase_int, if_neg hm, zero_sub]

/-! ### The two boundary arcs at `q = 1` -/

/-- The arc at `0/1` clipped to `[0,1]` is `[0, ρ]`. -/
theorem integral_arcSet_one_zero (n : ℕ) (m : ℤ)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n 1 0).indicator (fun y => phase ((m:ℝ)*y)) t)
      = ∫ t in (0:ℝ)..((cutoffH n : ℝ)/(n:ℝ)), phase ((m:ℝ)*t) := by
  have hset : arcSet n 1 0 = Set.Icc (-((cutoffH n : ℝ)/(n:ℝ))) ((cutoffH n : ℝ)/(n:ℝ)) := by
    rw [arcSet_eq_Icc]
    simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_div, zero_sub, zero_add]
  have hI : Set.Ioc (0:ℝ) 1 ∩ Set.Icc (-((cutoffH n : ℝ)/(n:ℝ))) ((cutoffH n : ℝ)/(n:ℝ))
      = Set.Ioc 0 ((cutoffH n : ℝ)/(n:ℝ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h0, _⟩, _, hle⟩
      exact ⟨h0, hle⟩
    · rintro ⟨h0, hle⟩
      exact ⟨⟨h0, le_trans hle (le_of_lt hρ1)⟩, by linarith, hle⟩
  rw [hset, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_indicator measurableSet_Icc, hI,
    ← intervalIntegral.integral_of_le hρ0]

/-- The arc at `1/1` clipped to `[0,1]` is `[1-ρ, 1]`. -/
theorem integral_arcSet_one_one (n : ℕ) (m : ℤ)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n 1 1).indicator (fun y => phase ((m:ℝ)*y)) t)
      = ∫ t in (1 - (cutoffH n : ℝ)/(n:ℝ))..1, phase ((m:ℝ)*t) := by
  have hset : arcSet n 1 1 = Set.Icc (1 - (cutoffH n : ℝ)/(n:ℝ)) (1 + (cutoffH n : ℝ)/(n:ℝ)) := by
    rw [arcSet_eq_Icc]
    simp only [Nat.cast_one, one_mul, Nat.cast_zero, div_one]
  have hI : Set.Ioc (0:ℝ) 1 ∩ Set.Icc (1 - (cutoffH n : ℝ)/(n:ℝ)) (1 + (cutoffH n : ℝ)/(n:ℝ))
      = Set.Icc (1 - (cutoffH n : ℝ)/(n:ℝ)) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h1⟩, hlo, _⟩
      exact ⟨hlo, h1⟩
    · rintro ⟨hlo, h1⟩
      exact ⟨⟨by linarith, h1⟩, hlo, by linarith⟩
  rw [hset, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_indicator measurableSet_Icc, hI,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (1:ℝ) - (cutoffH n : ℝ)/(n:ℝ) ≤ 1)]

/-- **The `q = 1` contribution** is the full sinc term. -/
theorem sum_arcSet_one (n : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∑ a ∈ (Finset.range 2).filter (fun a => Nat.Coprime a 1),
        ∫ t in (0:ℝ)..1, (arcSet n 1 a).indicator (fun y => phase ((m:ℝ)*y)) t)
      = (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n : ℝ)/(n:ℝ))) : ℝ) : ℂ) /
          ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  have hmem : (0:ℕ) ∈ (Finset.range 2).filter (fun a => Nat.Coprime a 1) := by
    simp
  have hmem1 : (1:ℕ) ∈ (Finset.range 2).filter (fun a => Nat.Coprime a 1) := by
    simp
  have hfilter : (Finset.range 2).filter (fun a => Nat.Coprime a 1) = {0, 1} := by
    decide
  rw [hfilter, Finset.sum_insert (by simp), Finset.sum_singleton,
    integral_arcSet_one_zero n m hρ0 hρ1, integral_arcSet_one_one n m hρ0 hρ1]
  have hsin := integral_boundary_arcs m ((cutoffH n : ℝ)/(n:ℝ))
  rw [hsin]
  exact integral_phase_symmetric m hm ((cutoffH n : ℝ)/(n:ℝ))

/-- **Interior arcs contribute their sinc term.** -/
theorem integral_arcSet_clipped_eq_sinc (n q a : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hleft : 0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))
    (hright : (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n q a).indicator (fun y => phase ((m:ℝ)*y)) t)
      = phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
          (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
            ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  rw [integral_arcSet_indicator_phase_of_inside n q a m hleft hright,
    integral_arcSet_phase n q a m hm]

/-- The sinc sum over the *interior* arcs (`q ≥ 2`). -/
theorem sum_arcSet_phase_interior (n : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    (∑ q ∈ Finset.Icc 2 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          ∫ t in (0:ℝ)..1, (arcSet n q a).indicator (fun y => phase ((m:ℝ)*y)) t)
      = ∑ q ∈ Finset.Icc 2 (cutoffB n),
          ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
            phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
              (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
                ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun a ha => ?_
  exact integral_arcSet_clipped_eq_sinc n q a m hm (hint q hq a ha).1 (hint q hq a ha).2

/-- The deep-minor arc kernel in frequency form: `∫_{wideArcsᶜ} e(m t) dt`. -/
def arcKernel (n : ℕ) (m : ℤ) : ℂ :=
  ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator (fun x => phase ((m:ℝ)*x)) t

end B1B1Port
