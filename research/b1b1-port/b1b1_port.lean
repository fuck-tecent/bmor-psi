import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion
import PEqualNP.Outside.L_goldbach_bulk_density_one

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

/-- **The weighted quadruple expansion with the arc indicator distributed.**
Pointwise form of the `τ₁` `exact_split` expansion: the deep-minor integrand is a
nested sum over the four atom indices with the arc indicator applied to each
frequency separately. -/
theorem deepIntegrand_eq_quadruple_sum (n : ℕ) (t : ℝ) :
    (wideSet n)ᶜ.indicator
      (fun x => plainPolynomial n (tauCoeff n) x * plainPolynomial n (tauCoeff n) x *
        phase (-(n:ℝ)*x)) t
    = ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
            ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
              ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                ((ArithmeticFunction.vonMangoldt j : ℂ) *
                  (ArithmeticFunction.vonMangoldt k : ℂ)) *
                  (wideSet n)ᶜ.indicator (fun x =>
                    phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * x)) t := by
  classical
  by_cases ht : t ∈ (wideSet n)ᶜ
  · rw [Set.indicator_of_mem ht]
    rw [show plainPolynomial n (tauCoeff n) t * plainPolynomial n (tauCoeff n) t *
          phase (-(n:ℝ)*t)
        = plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t) from by ring]
    rw [plainPolynomial_sq_dilated_expand n t]
    simp only [Set.indicator_of_mem ht]
  · have hz : ∀ a a' j k, (wideSet n)ᶜ.indicator (fun x =>
        phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * x)) t = 0 := by
      intro a a' j k
      exact Set.indicator_of_notMem ht _
    rw [Set.indicator_of_notMem ht]
    simp only [hz, mul_zero, Finset.sum_const_zero]

/-- `Jdeep` is the integral of the expanded quadruple sum (the pointwise expansion
integrated; the finite-sum interchange is the remaining formal step). -/
theorem deepIntegral_eq_integral_quadruple (n : ℕ) :
    deepIntegral n =
      ∫ t in (0:ℝ)..1,
        ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
            ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
              ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
                ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                  ((ArithmeticFunction.vonMangoldt j : ℂ) *
                    (ArithmeticFunction.vonMangoldt k : ℂ)) *
                    (wideSet n)ᶜ.indicator (fun x =>
                      phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * x)) t := by
  have hstep : deepIntegral n =
      ∫ t in (0:ℝ)..1, (wideSet n)ᶜ.indicator
        (fun x => plainPolynomial n (tauCoeff n) x * plainPolynomial n (tauCoeff n) x *
          phase (-(n:ℝ)*x)) t := by
    unfold deepIntegral
    apply intervalIntegral.integral_congr
    intro t _
    congr 1
    funext x
    rw [shiftedPolynomial_eq]
    ring
  rw [hstep]
  apply intervalIntegral.integral_congr
  intro t _
  exact deepIntegrand_eq_quadruple_sum n t

/-- Interval integrability of a finite sum, in the `fun t => ∑ i, f i t` form. -/
theorem intervalIntegrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) MeasureTheory.volume 0 1 := by
  have := IntervalIntegrable.sum s h
  convert this using 1
  ext x
  simp only [Finset.sum_apply]

/-- **The quadruple-sum form of `Jdeep`.** -/
theorem deepIntegral_eq_quadruple_sum (n : ℕ) :
    deepIntegral n =
      ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
            ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
              ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                ((ArithmeticFunction.vonMangoldt j : ℂ) *
                  (ArithmeticFunction.vonMangoldt k : ℂ)) *
                  arcKernel n (((a*j : ℕ) : ℤ) + ((a'*k : ℕ) : ℤ) - (n : ℤ)) := by
  classical
  have hmeas : MeasurableSet (wideSet n) := wide_measurable n (cutoffB n) (cutoffH n)
  rw [deepIntegral_eq_integral_quadruple]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro a _
    exact intervalIntegrable_finset_sum' _ (fun a' _ =>
      IntervalIntegrable.const_mul (intervalIntegrable_finset_sum' _ (fun j _ =>
        intervalIntegrable_finset_sum' _ (fun k _ =>
          IntervalIntegrable.const_mul
            (indicator_intervalIntegrable (by unfold phase; fun_prop) hmeas.compl) _))) _)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro a' _
    exact IntervalIntegrable.const_mul (intervalIntegrable_finset_sum' _ (fun j _ =>
      intervalIntegrable_finset_sum' _ (fun k _ =>
        IntervalIntegrable.const_mul
          (indicator_intervalIntegrable (by unfold phase; fun_prop) hmeas.compl) _))) _
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro j _
    exact intervalIntegrable_finset_sum' _ (fun k _ =>
      IntervalIntegrable.const_mul
        (indicator_intervalIntegrable (by unfold phase; fun_prop) hmeas.compl) _)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro k _
    exact IntervalIntegrable.const_mul
      (indicator_intervalIntegrable (by unfold phase; fun_prop) hmeas.compl) _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  unfold arcKernel
  congr 1
  ext x
  congr 2
  push_cast
  ring

/-- The `q = 1` term of the sinc sum with the `range 1` index set. -/
theorem sum_range_one_rhs (n : ℕ) (m : ℤ) :
    (∑ a ∈ (Finset.range 1).filter (fun a => Nat.Coprime a 1),
        phase ((m:ℝ)*((a:ℝ)/(((1:ℕ):ℝ)))) *
          (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((((1:ℕ):ℝ))*((n:ℕ):ℝ)))) : ℝ) : ℂ) /
            ((Real.pi*(m:ℝ) : ℝ) : ℂ)))
      = (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n : ℝ)/(n:ℝ))) : ℝ) : ℂ) /
          ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  have hfil : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  rw [hfil, Finset.sum_singleton]
  norm_num
  simp [phase]

/-- **The sinc collection with the `range q` index set.** -/
theorem integral_wideSet_phase_eq_sinc_range (n : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : (0:ℝ) ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    (∫ t in (0:ℝ)..1, (wideSet n).indicator (fun y => phase ((m:ℝ)*y)) t)
      = ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
              (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
                ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  classical
  have hcont : Continuous fun t : ℝ => phase ((m:ℝ)*t) := by unfold phase; fun_prop
  have hsplit : Finset.Icc 1 (cutoffB n) = insert 1 (Finset.Icc 2 (cutoffB n)) := by
    clear hn hρ0 hρ1
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl h.symm
    · rintro (rfl | ⟨h2, h3⟩)
      · exact ⟨le_rfl, hQ⟩
      · exact ⟨Nat.le_trans (by norm_num) h2, h3⟩
  have hnot1 : (1:ℕ) ∉ Finset.Icc 2 (cutoffB n) := by
    intro h
    exact absurd (Finset.mem_Icc.mp h).1 (Nat.not_succ_le_self 1)
  have hfilter : ∀ q : ℕ, 2 ≤ q →
      (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)
        = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    intro q hq
    clear hn hρ0 hρ1
    have hins : Finset.range (q+1) = insert q (Finset.range q) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    rw [hins, Finset.filter_insert, if_neg]
    intro hcop
    have := (Nat.coprime_self q).mp hcop
    omega
  rw [integral_wideSet_eq_sum n hn _ hcont, hsplit, Finset.sum_insert hnot1]
  rw [Finset.sum_insert hnot1]
  rw [sum_arcSet_one n m hm hρ0 hρ1, sum_range_one_rhs n m]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
  rw [hfilter q hq2]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsub : a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      omega), (Finset.mem_filter.mp ha).2⟩
  exact integral_arcSet_clipped_eq_sinc n q a m hm
    (hint q hq a hsub).1 (hint q hq a hsub).2

/-- **The arc kernel in closed form.** -/
theorem arcKernel_eq_sinc (n : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : (0:ℝ) ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    arcKernel n m
      = - ∑ q ∈ Finset.Icc 1 (cutoffB n),
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
                (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
                  ((Real.pi*(m:ℝ) : ℝ) : ℂ)) := by
  unfold arcKernel
  rw [integral_compl_indicator_phase_eq n m hm,
    integral_wideSet_phase_eq_sinc_range n m hm hn hQ hρ0 hρ1 hint]

/-- The kernel at zero frequency is the complement measure. -/
theorem arcKernel_zero (n : ℕ) :
    arcKernel n 0
      = ((MeasureTheory.volume.real ((wideSet n)ᶜ ∩ Set.Ioc (0:ℝ) 1) : ℝ) : ℂ) := by
  have hmeas : MeasurableSet (wideSet n) := wide_measurable n (cutoffB n) (cutoffH n)
  have hpt : ∀ t : ℝ, (wideSet n)ᶜ.indicator (fun y => phase (((0:ℤ):ℝ)*y)) t
      = (wideSet n)ᶜ.indicator (fun _ => (1:ℂ)) t := by
    intro t
    congr 1
    funext y
    simp [phase]
  unfold arcKernel
  simp_rw [hpt]
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_indicator hmeas.compl]
  rw [Set.inter_comm, MeasureTheory.setIntegral_const]
  simp

/-- One term of the sinc sum. -/
def sineFactor (n : ℕ) (m : ℤ) (q a : ℕ) : ℂ :=
  phase ((m:ℝ)*((a:ℝ)/(q:ℝ))) *
    (((Real.sin (2*Real.pi*(m:ℝ)*((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))) : ℝ) : ℂ) /
      ((Real.pi*(m:ℝ) : ℝ) : ℂ))

/-- The sinc sum over the arc family (the closed form of `-arcKernel`). -/
def sincSum (n : ℕ) (m : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (cutoffB n),
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), sineFactor n m q a

/-- The arc kernel is minus the sinc sum at nonzero frequency. -/
theorem arcKernel_eq_neg_sincSum (n : ℕ) (m : ℤ) (hm : m ≠ 0)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : (0:ℝ) ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    arcKernel n m = - sincSum n m := by
  rw [arcKernel_eq_sinc n m hm hn hQ hρ0 hρ1 hint]
  simp only [sincSum, sineFactor]

/-- **The full `τ₁` `exact_split`**: `Jdeep` as a quadruple sum with the kernel in
closed form (diagonal at `m = 0`, sinc sum otherwise). -/
theorem deepIntegral_eq_diagonal_sub_sinc (n : ℕ)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : (0:ℝ) ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    deepIntegral n =
      ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
            ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
              ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                ((ArithmeticFunction.vonMangoldt j : ℂ) *
                  (ArithmeticFunction.vonMangoldt k : ℂ)) *
                  (if (((a*j : ℕ) : ℤ) + ((a'*k : ℕ) : ℤ) - (n : ℤ)) = 0
                   then arcKernel n 0
                   else - sincSum n (((a*j : ℕ) : ℤ) + ((a'*k : ℕ) : ℤ) - (n : ℤ))) := by
  rw [deepIntegral_eq_quadruple_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hm : (((a*j : ℕ) : ℤ) + ((a'*k : ℕ) : ℤ) - (n : ℤ)) = 0
  · rw [if_pos hm, hm]
  · rw [if_neg hm, arcKernel_eq_neg_sincSum n _ hm hn hQ hρ0 hρ1 hint]

/-- **The quadruple expansion summed over a finite set of sample points.** -/
theorem sum_plainPolynomial_sq_phase_eq_quad (n : ℕ) (T : Finset ℝ) :
    (∑ x ∈ T, plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x))
      = ∑ x ∈ T,
          ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
            ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
              ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
                ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
                  ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                    ((ArithmeticFunction.vonMangoldt j : ℂ) *
                      (ArithmeticFunction.vonMangoldt k : ℂ)) *
                      phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  exact plainPolynomial_sq_dilated_expand n x

/-! ### Stage 2, step 1: the sinc factor as an arc integral

The amplitude `sin(2π m ρ)/(π m)` depends on `m`, so it **cannot** be pulled out of
the quadruple sum as a constant.  The correct reading is `sineFactor = ∫_{arc} e(m·)`,
which lets the whole `m`-dependence stay inside the integral. -/

/-- The sinc factor of one arc is the arc integral of its mode. -/
theorem sineFactor_eq_arcIntegral (n q a : ℕ) (m : ℤ) (hm : m ≠ 0) :
    sineFactor n m q a = ∫ t in arcSet n q a, phase ((m:ℝ)*t) := by
  unfold sineFactor
  exact (integral_arcSet_phase n q a m hm).symm

/-- **The sinc sum is a sum of arc integrals.** -/
theorem sincSum_eq_sum_arcIntegral (n : ℕ) (m : ℤ) (hm : m ≠ 0) :
    sincSum n m
      = ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ t in arcSet n q a, phase ((m:ℝ)*t) := by
  unfold sincSum
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  exact sineFactor_eq_arcIntegral n q a m hm

/-- **`Jdeep` as `D` minus the sum of arc integrals.** -/
theorem deepIntegral_eq_diagonal_sub_arc_sum (n : ℕ)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) :
    deepIntegral n = diagonalSum n
      - ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
            ∫ t in (0:ℝ)..1, (arcSet n q a).indicator
              (fun x => plainPolynomial n (tauCoeff n) x ^ 2 * phase (-(n:ℝ)*x)) t := by
  rw [deepIntegral_eq_diagonal_sub_wide]
  congr 1
  exact integral_wideSet_eq_sum n hn _
    (by unfold plainPolynomial phase; fun_prop)

/-! ### Stage 2, step 2: unclipping the arcs at `q = 1`

The `q = 1` arcs `0/1` and `1/1` stick out of `(0,1]`; for a `1`-periodic
integrand the two clipped pieces recombine into the single full ball at `0/1`,
which is exactly `arcSet n 1 0`.  This turns the clipped sum over
`range (q+1)` into the unclipped sum over `range q` used by `sincSum`. -/

/-- The plain polynomial is `1`-periodic. -/
theorem plainPolynomial_add_one (n : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    plainPolynomial n c (t + 1) = plainPolynomial n c t := by
  unfold plainPolynomial
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : phase ((m:ℝ)) = 1 := by
    simpa using phase_int (m : ℤ)
  rw [show (m:ℝ)*(t+1) = (m:ℝ)*t + (m:ℝ) by ring, phase_add, h1, mul_one]

/-- The deep integrand `S²·e(-n·)` is `1`-periodic. -/
theorem periodic_deepIntegrand (n : ℕ) (t : ℝ) :
    plainPolynomial n (tauCoeff n) (t + 1) ^ 2 * phase (-(n:ℝ)*(t+1))
      = plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t) := by
  rw [plainPolynomial_add_one]
  have h1 : phase (-(n:ℝ)) = 1 := by
    simpa using phase_int (-(n : ℤ))
  rw [show -(n:ℝ)*(t+1) = -(n:ℝ)*t + (-(n:ℝ)) by ring, phase_add, h1, mul_one]

/-- **Boundary arcs for a `1`-periodic integrand** (generalises
`integral_boundary_arcs` beyond single modes). -/
theorem integral_boundary_arcs_periodic {f : ℝ → ℂ} (hf : Continuous f)
    (hper : ∀ u : ℝ, f (u+1) = f u) (ρ : ℝ) :
    (∫ t in (0:ℝ)..ρ, f t) + (∫ t in (1-ρ)..1, f t) = ∫ t in (-ρ)..ρ, f t := by
  have hshift : (∫ t in (1-ρ)..1, f t) = ∫ u in (-ρ)..0, f u := by
    have h := intervalIntegral.integral_comp_add_right (f := f) (a := -ρ) (b := 0) (1:ℝ)
    simp only [neg_add_cancel, zero_add] at h
    rw [show (-ρ + 1 : ℝ) = 1 - ρ by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun u _ => hper u
  rw [hshift, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]

/-- `arcSet n 1 0` is the full ball at `0/1`. -/
theorem arcSet_one_zero_eq_Icc (n : ℕ) :
    arcSet n 1 0 = Set.Icc (-((cutoffH n : ℝ)/(n:ℝ))) ((cutoffH n : ℝ)/(n:ℝ)) := by
  rw [arcSet_eq_Icc]
  simp only [Nat.cast_one, one_mul, Nat.cast_zero, zero_div, zero_sub, zero_add]

/-- The arc at `0/1` clipped to `[0,1]` is `[0,ρ]` (any integrand). -/
theorem integral_arcSet_one_zero_gen (n : ℕ) (f : ℝ → ℂ)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n 1 0).indicator f t)
      = ∫ t in (0:ℝ)..((cutoffH n : ℝ)/(n:ℝ)), f t := by
  have hset := arcSet_one_zero_eq_Icc n
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

/-- The arc at `1/1` clipped to `[0,1]` is `[1-ρ,1]` (any integrand). -/
theorem integral_arcSet_one_one_gen (n : ℕ) (f : ℝ → ℂ)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n 1 1).indicator f t)
      = ∫ t in (1 - (cutoffH n : ℝ)/(n:ℝ))..1, f t := by
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

/-- The `q = 1` pair of clipped arcs is the full ball at `0/1`. -/
theorem sum_arcSet_one_gen (n : ℕ) (f : ℝ → ℂ) (hf : Continuous f)
    (hper : ∀ u : ℝ, f (u+1) = f u)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∑ a ∈ (Finset.range (1+1)).filter (fun a => Nat.Coprime a 1),
        ∫ t in (0:ℝ)..1, (arcSet n 1 a).indicator f t)
      = ∫ t in (-((cutoffH n : ℝ)/(n:ℝ)))..((cutoffH n : ℝ)/(n:ℝ)), f t := by
  have hfilter : (Finset.range (1+1)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
  rw [hfilter, Finset.sum_insert (by simp), Finset.sum_singleton,
    integral_arcSet_one_zero_gen n f hρ0 hρ1, integral_arcSet_one_one_gen n f hρ0 hρ1]
  exact integral_boundary_arcs_periodic hf hper ((cutoffH n : ℝ)/(n:ℝ))

/-- For an arc strictly inside `(0,1)`, the clipped indicator integral is the full
arc integral (any integrand). -/
theorem integral_arcSet_indicator_of_inside_gen (n q a : ℕ) (f : ℝ → ℂ)
    (hleft : 0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)))
    (hright : (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    (∫ t in (0:ℝ)..1, (arcSet n q a).indicator f t) = ∫ t in arcSet n q a, f t := by
  have hsub : arcSet n q a ⊆ Set.Ioc (0:ℝ) 1 := by
    intro t ht
    rw [arcSet_eq_Icc] at ht
    obtain ⟨h1, h2⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hmeas : MeasurableSet (arcSet n q a) := arcSet_measurable n q a
  have hsupp : ∀ x ∉ Set.Ioc (0:ℝ) 1, (arcSet n q a).indicator f x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx (hsub hc)) f
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    MeasureTheory.integral_indicator hmeas]

/-- For `q ≥ 2` the coprime numerators in `range (q+1)` are exactly those in `range q`. -/
theorem filter_range_succ_coprime {q : ℕ} (hq : 2 ≤ q) :
    (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  have hq' : ¬ Nat.Coprime q q := by
    intro h
    have h1 : q = 1 := by simpa [Nat.Coprime] using h
    omega
  rw [if_neg hq']

/-- **The clipped arc sum is the unclipped arc sum.**  This is the precise sense in
which the `sincSum` index family `(range q) ∩ coprime` is the right one: the
missing numerators at `q = 1` (`a = 1`) are absorbed by the periodicity of the
integrand, and for `q ≥ 2` they are not coprime anyway. -/
theorem sum_arcSet_clipped_eq_sum_arcSet (n : ℕ) (hQ : 1 ≤ cutoffB n)
    {f : ℝ → ℂ} (hf : Continuous f) (hper : ∀ u : ℝ, f (u+1) = f u)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ)) (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1) :
    (∑ q ∈ Finset.Icc 1 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          ∫ t in (0:ℝ)..1, (arcSet n q a).indicator f t)
      = ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ t in arcSet n q a, f t := by
  classical
  have hsplit : Finset.Icc 1 (cutoffB n) = insert 1 (Finset.Icc 2 (cutoffB n)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot1 : (1:ℕ) ∉ Finset.Icc 2 (cutoffB n) := by simp
  have h1 : (∑ a ∈ (Finset.range (1+1)).filter (fun a => Nat.Coprime a 1),
      ∫ t in (0:ℝ)..1, (arcSet n 1 a).indicator f t)
      = ∑ a ∈ (Finset.range 1).filter (fun a => Nat.Coprime a 1),
          ∫ t in arcSet n 1 a, f t := by
    rw [sum_arcSet_one_gen n f hf hper hρ0 hρ1]
    rw [show (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} from by decide,
      Finset.sum_singleton, arcSet_one_zero_eq_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (by linarith : -((cutoffH n : ℝ)/(n:ℝ)) ≤ (cutoffH n : ℝ)/(n:ℝ))]
  have h2 : (∑ q ∈ Finset.Icc 2 (cutoffB n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          ∫ t in (0:ℝ)..1, (arcSet n q a).indicator f t)
      = ∑ q ∈ Finset.Icc 2 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ t in arcSet n q a, f t := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    rw [filter_range_succ_coprime hq2]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q) := by
      rw [filter_range_succ_coprime hq2]
      exact ha
    exact integral_arcSet_indicator_of_inside_gen n q a f (hint q hq a ha').1 (hint q hq a ha').2
  rw [hsplit, Finset.sum_insert hnot1, Finset.sum_insert hnot1, h1, h2]

/-- **The arc decomposition of `Jdeep` in the `sincSum` index family.**

`Jdeep = D - ∑_{q ≤ Q₁} ∑_{a<q, (a,q)=1} ∫_{arc(a/q)} S(t)² e(-n t) dt`,
i.e. `Jdeep = D - W` with `W` the integral over the wide arcs.  This is the
`τ₁`-analogue of `spatial_exact_split`, and the form in which the major-arc
approximation of `S` applies arc by arc. -/
theorem deepIntegral_eq_diagonal_sub_periodic_arc_sum (n : ℕ)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    deepIntegral n = diagonalSum n
      - ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ t in arcSet n q a,
              plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t) := by
  rw [deepIntegral_eq_diagonal_sub_arc_sum n hn]
  congr 1
  exact sum_arcSet_clipped_eq_sum_arcSet n hQ
    (by unfold plainPolynomial phase; fun_prop)
    (fun u => periodic_deepIntegrand n u) hint hρ0 hρ1

/-! ### Stage 2, step 3: shifting to local coordinates on one arc

On the arc of `a/q` write `t = a/q + β`.  The arithmetic information (`S` sampled
at the rational point) separates from the archimedean integral over
`|β| ≤ ρ_q = H/(q n)`.  This is the form in which the major-arc model of `S` is
inserted. -/

/-- **Arc-shift identity.**  On `arcSet n q a`, with `ρ = H/(q n)`,
`∫_{arc} S²e(-n t) dt = e(-n a/q) · ∫_{-ρ}^{ρ} S(a/q+β)² e(-n β) dβ`. -/
theorem integral_arcSet_shift (n q a : ℕ) :
    (∫ t in arcSet n q a,
        plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t))
      = phase (-(n:ℝ)*((a:ℝ)/(q:ℝ))) *
          ∫ β in (-((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))))..((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))),
            plainPolynomial n (tauCoeff n) ((a:ℝ)/(q:ℝ) + β) ^ 2 * phase (-(n:ℝ)*β) := by
  set c : ℝ := (a:ℝ)/(q:ℝ) with hc
  set ρ : ℝ := (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) with hρ
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  rw [show arcSet n q a = Set.Icc (c - ρ) (c + ρ) from by
    rw [hc, hρ]; exact arcSet_eq_Icc n q a]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := c - ρ) (b := c + ρ) (by linarith)]
  rw [show c - ρ = c + (-ρ) from by ring]
  rw [← intervalIntegral.integral_comp_add_left
    (f := fun t : ℝ => plainPolynomial n (tauCoeff n) t ^ 2 * phase (-(n:ℝ)*t))
    (a := -ρ) (b := ρ) (d := c)]
  have hpt : ∀ β : ℝ,
      plainPolynomial n (tauCoeff n) (c+β) ^ 2 * phase (-(n:ℝ)*(c+β))
        = phase (-(n:ℝ)*c) *
            (plainPolynomial n (tauCoeff n) (c+β) ^ 2 * phase (-(n:ℝ)*β)) := by
    intro β
    rw [show -(n:ℝ)*(c+β) = -(n:ℝ)*c + (-(n:ℝ)*β) by ring, phase_add]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]

/-- **The shifted arc decomposition.**  `Jdeep = D - W` with

`W = ∑_{q ≤ Q₁} ∑_{a<q, (a,q)=1} e(-n a/q) ∫_{-ρ_q}^{ρ_q} S(a/q+β)² e(-nβ) dβ`

— the correct form of the requested `W = ∑_q ∑_{a₀} e(-n a₀/q) S(a₀/q)² sinc`.
The `sinc` is the archimedean integral, so `S` must be evaluated at `a/q + β`
inside it, not at `a/q`. -/
theorem deepIntegral_eq_diagonal_sub_shifted_arc_sum (n : ℕ)
    (hn : 512 * (cutoffB n)^2 * logSq n < n) (hQ : 1 ≤ cutoffB n)
    (hρ0 : 0 ≤ (cutoffH n : ℝ)/(n:ℝ))
    (hρ1 : (cutoffH n : ℝ)/(n:ℝ) < 1)
    (hint : ∀ q ∈ Finset.Icc 2 (cutoffB n),
      ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        0 < (a:ℝ)/(q:ℝ) - (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) ∧
          (a:ℝ)/(q:ℝ) + (cutoffH n:ℝ)/((q:ℝ)*(n:ℝ)) < 1) :
    deepIntegral n = diagonalSum n
      - ∑ q ∈ Finset.Icc 1 (cutoffB n),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            phase (-(n:ℝ)*((a:ℝ)/(q:ℝ))) *
              ∫ β in (-((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))))..((cutoffH n:ℝ)/((q:ℝ)*(n:ℝ))),
                plainPolynomial n (tauCoeff n) ((a:ℝ)/(q:ℝ) + β) ^ 2 *
                  phase (-(n:ℝ)*β) := by
  rw [deepIntegral_eq_diagonal_sub_periodic_arc_sum n hn hQ hρ0 hρ1 hint]
  congr 1
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  exact integral_arcSet_shift n q a

/-! ### The local-count identity: `q = ∞` versus finite modulus `q` -/

/-- The Ramanujan sum at a real frequency: `c_q(m) = ∑_{(a₀,q)=1} e(m a₀/q)`.
Stated with a **real** frequency so that it matches the phase argument produced by
`plainPolynomial_sq_dilated_expand` without cast rewriting. -/
def ramanujanPhase (q : ℕ) (m : ℝ) : ℂ :=
  ∑ a₀ ∈ (Finset.range q).filter (fun a₀ => Nat.Coprime a₀ q),
    phase (m * ((a₀:ℝ)/(q:ℝ)))

/-- The outer sum of a five-fold nested sum commutes all the way in.  The fourth and
fifth index sets may depend on the second and third variables respectively. -/
theorem sum_comm_outer5 {α : Type*} [AddCommMonoid α]
    {β γ δ ε ζ : Type*}
    (s : Finset β) (t : Finset γ) (t' : Finset δ)
    (u : γ → Finset ε) (v : δ → Finset ζ)
    (f : β → γ → δ → ε → ζ → α) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ y' ∈ t', ∑ z ∈ u y, ∑ w ∈ v y', f x y y' z w)
      = ∑ y ∈ t, ∑ y' ∈ t', ∑ z ∈ u y, ∑ w ∈ v y', ∑ x ∈ s, f x y y' z w := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]

/-- **The local-count identity.**  The `q`-local weighted count of the diagonal
condition equals the sum of `S(a₀/q)² e(-n a₀/q)` over the reduced numerators:

```text
∑_{quads} c(a)c(a')Λ(j)Λ(k) · c_q(a j + a' k - n)
  = ∑_{a₀ ∈ (range q), (a₀,q)=1} S_{τ₁}(a₀/q)² · e(-n a₀/q)
```

This is the precise statement that `D` is the `q = ∞` count and that the `q`-th term
of `W` is the finite-modulus count. -/
theorem quad_sum_ramanujan (n q : ℕ) :
    (∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
      ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
        ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
          ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
            ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
              ((ArithmeticFunction.vonMangoldt j : ℂ) *
                (ArithmeticFunction.vonMangoldt k : ℂ)) *
                ramanujanPhase q ((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))))
      = ∑ a₀ ∈ (Finset.range q).filter (fun a₀ => Nat.Coprime a₀ q),
          plainPolynomial n (tauCoeff n) ((a₀:ℝ)/(q:ℝ)) ^ 2 *
            phase (-(n:ℝ)*((a₀:ℝ)/(q:ℝ))) := by
  have h1 : ∀ a₀ ∈ (Finset.range q).filter (fun a₀ => Nat.Coprime a₀ q),
      plainPolynomial n (tauCoeff n) ((a₀:ℝ)/(q:ℝ)) ^ 2 * phase (-(n:ℝ)*((a₀:ℝ)/(q:ℝ)))
        = ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
            ∑ a' ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
              ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
                ∑ j ∈ Finset.Ioc (cutoffU n) (n / a),
                  ∑ k ∈ Finset.Ioc (cutoffU n) (n / a'),
                    ((ArithmeticFunction.vonMangoldt j : ℂ) *
                      (ArithmeticFunction.vonMangoldt k : ℂ)) *
                      phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * ((a₀:ℝ)/(q:ℝ))) :=
    fun a₀ _ => plainPolynomial_sq_dilated_expand n _
  rw [Finset.sum_congr rfl h1]
  simp only [ramanujanPhase, Finset.mul_sum]
  exact (sum_comm_outer5
    (s := (Finset.range q).filter (fun a₀ => Nat.Coprime a₀ q))
    (t := Finset.Icc (cutoffU n + 1) (lowCut n))
    (t' := Finset.Icc (cutoffU n + 1) (lowCut n))
    (u := fun a => Finset.Ioc (cutoffU n) (n / a))
    (v := fun a' => Finset.Ioc (cutoffU n) (n / a'))
    (f := fun a₀ a a' j k =>
      ((lowMoebiusWeight (cutoffU n) a : ℂ) * (lowMoebiusWeight (cutoffU n) a' : ℂ)) *
        (((ArithmeticFunction.vonMangoldt j : ℂ) *
          (ArithmeticFunction.vonMangoldt k : ℂ)) *
          phase (((((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))) * ((a₀:ℝ)/(q:ℝ)))))).symm

/-! ### Milestone 39 (step 1): the cutoff budget for a general divisor cutoff

The verified engine converts a block bound carrying `(X/q + X/U + X/V + q)` into
`X/√q + X/√U + X/√V + √(Xq)`.  In `optimizedCutoff_squared_budget` the two cutoffs are
tied to `⌊X^(2/5)⌋`, which is exactly the exponent that matches `X/U` against the
envelope's middle term `X^(4/5)`:  `X · (X/U) ≤ (X^(4/5))²` ⟺ `U ≥ X^(2/5)`.

Below we keep the two cutoffs free.  For `U = X^(1/16)` the resulting scale is
`X/√U = X^(31/32)`, hence `X^(31/32) log⁴ = o(X)` — the budget still closes, the loss
against the `2/5` form being `X^(27/80)`. -/

/-- **General cutoff budget.**  No relation between `U`, `V` and `X^(2/5)` is assumed. -/
theorem cutoff_squared_budget_general (X q C U V R : ℝ)
    (hX : 1 ≤ X) (hq : 0 < q) (hC : 0 ≤ C) (hU : 0 < U) (hV : 0 < V)
    (hbound : R ^ 2 ≤ C * X * (1 + Real.log (2 * X)) ^ 6 *
      (X / q + X / U + X / V + q)) :
    R ≤ Real.sqrt C * (1 + Real.log (2 * X)) ^ 3 *
      (X / Real.sqrt q + X / Real.sqrt U + X / Real.sqrt V + Real.sqrt (X * q)) := by
  have hL : 0 ≤ 1 + Real.log (2 * X) := by
    have h2X : (1 : ℝ) ≤ 2 * X := by linarith
    have := Real.log_nonneg h2X
    linarith
  set S : ℝ := X / Real.sqrt q + X / Real.sqrt U + X / Real.sqrt V + Real.sqrt (X * q) with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hsq : X * (X / q + X / U + X / V + q) ≤ S ^ 2 := by
    have hq' : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
    have hU' : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt (le_of_lt hU)
    have hV' : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt (le_of_lt hV)
    have hXq' : (Real.sqrt (X * q)) ^ 2 = X * q := Real.sq_sqrt (by positivity)
    have hsqsum : X * (X / q + X / U + X / V + q)
        = (X / Real.sqrt q) ^ 2 + (X / Real.sqrt U) ^ 2 + (X / Real.sqrt V) ^ 2
          + (Real.sqrt (X * q)) ^ 2 := by
      rw [div_pow, div_pow, div_pow, hq', hU', hV', hXq']
      field_simp
    have e : S ^ 2 = (X / Real.sqrt q) ^ 2 + (X / Real.sqrt U) ^ 2 + (X / Real.sqrt V) ^ 2
        + (Real.sqrt (X * q)) ^ 2
        + 2 * ((X / Real.sqrt q) * (X / Real.sqrt U) + (X / Real.sqrt q) * (X / Real.sqrt V)
            + (X / Real.sqrt q) * Real.sqrt (X * q) + (X / Real.sqrt U) * (X / Real.sqrt V)
            + (X / Real.sqrt U) * Real.sqrt (X * q)
            + (X / Real.sqrt V) * Real.sqrt (X * q)) := by
      rw [hS]; ring
    have hcross : 0 ≤ 2 * ((X / Real.sqrt q) * (X / Real.sqrt U)
        + (X / Real.sqrt q) * (X / Real.sqrt V)
        + (X / Real.sqrt q) * Real.sqrt (X * q) + (X / Real.sqrt U) * (X / Real.sqrt V)
        + (X / Real.sqrt U) * Real.sqrt (X * q)
        + (X / Real.sqrt V) * Real.sqrt (X * q)) := by positivity
    rw [hsqsum, e]
    linarith
  have h3 : 0 ≤ C * (1 + Real.log (2 * X)) ^ 6 := by positivity
  have hmain : R ^ 2 ≤ (C * (1 + Real.log (2 * X)) ^ 6) * S ^ 2 := by
    calc R ^ 2 ≤ C * X * (1 + Real.log (2 * X)) ^ 6 * (X / q + X / U + X / V + q) := hbound
      _ = (C * (1 + Real.log (2 * X)) ^ 6) * (X * (X / q + X / U + X / V + q)) := by ring
      _ ≤ (C * (1 + Real.log (2 * X)) ^ 6) * S ^ 2 :=
          mul_le_mul_of_nonneg_left hsq h3
  have hK : Real.sqrt (C * (1 + Real.log (2 * X)) ^ 6)
      = Real.sqrt C * (1 + Real.log (2 * X)) ^ 3 := by
    rw [Real.sqrt_mul hC]
    congr 1
    rw [show (1 + Real.log (2 * X)) ^ 6 = ((1 + Real.log (2 * X)) ^ 3) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  calc R ≤ |R| := le_abs_self R
    _ = Real.sqrt (R ^ 2) := (Real.sqrt_sq_eq_abs R).symm
    _ ≤ Real.sqrt ((C * (1 + Real.log (2 * X)) ^ 6) * S ^ 2) := Real.sqrt_le_sqrt hmain
    _ = Real.sqrt (C * (1 + Real.log (2 * X)) ^ 6) * S := by
        rw [Real.sqrt_mul h3, Real.sqrt_sq hS0]
    _ = Real.sqrt C * (1 + Real.log (2 * X)) ^ 3
          * (X / Real.sqrt q + X / Real.sqrt U + X / Real.sqrt V + Real.sqrt (X * q)) := by
        rw [hK, hS]

/-! ### Milestone 39 (step 2): the divisor window

`τ₃` restricts the divisor `a` to a **window** `(B₂, B₃]`, while the verified Type-II
coefficient `typeIICoefficient U` has no upper bound on `a` at all (its Möbius cutoff
and its divisor lower bound are the same number).  Below we split the window off as a
difference of two half-lines, which is the only way the existing interface can see it. -/

/-- The third band cut `B₃ = ⌊n^(2/3)⌋` (the second, `B₂ = ⌊n^(1/3)⌋`, is `cutoffB`). -/
def cutoffB3 (n : ℕ) : ℕ := ⌊(n:ℝ)^(2/3:ℝ)⌋₊

/-- The Type-II half-line coefficient: Möbius cutoff `U`, cofactor cutoff `V`, and the
divisor `a` restricted only by `a > L`.  This is `typeIICoefficient U * longPart V`
restricted to `a > L`. -/
def halfLineTypeII (U V L : ℕ) : ℕ → ℝ :=
  fun m => ∑ a ∈ (Nat.divisors m).filter (fun a => L < a ∧ V < m / a),
    (lowMoebiusWeight U a) * (ArithmeticFunction.vonMangoldt (m / a) : ℝ)

/-- The windowed Type-II coefficient: additionally `a ≤ H`. -/
def windowTypeII (U V L H : ℕ) : ℕ → ℝ :=
  fun m => ∑ a ∈ (Nat.divisors m).filter (fun a => L < a ∧ a ≤ H ∧ V < m / a),
    (lowMoebiusWeight U a) * (ArithmeticFunction.vonMangoldt (m / a) : ℝ)

/-- **The window is the difference of the two half-lines.** -/
theorem windowTypeII_eq_sub (U V L H m : ℕ) (hLH : L ≤ H) :
    windowTypeII U V L H m = halfLineTypeII U V L m - halfLineTypeII U V H m := by
  classical
  unfold windowTypeII halfLineTypeII
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : L < a
  · by_cases h2 : V < m / a
    · by_cases h3 : a ≤ H
      · rw [if_pos (show L < a ∧ a ≤ H ∧ V < m / a from ⟨h1, h3, h2⟩),
          if_pos (show L < a ∧ V < m / a from ⟨h1, h2⟩),
          if_neg (by omega : ¬ (H < a ∧ V < m / a))]
        ring
      · rw [if_neg (by omega : ¬ (L < a ∧ a ≤ H ∧ V < m / a)),
          if_pos (show L < a ∧ V < m / a from ⟨h1, h2⟩),
          if_pos (show H < a ∧ V < m / a from ⟨by omega, h2⟩)]
        ring
    · rw [if_neg (by omega : ¬ (L < a ∧ a ≤ H ∧ V < m / a)),
        if_neg (by omega : ¬ (L < a ∧ V < m / a)),
        if_neg (by omega : ¬ (H < a ∧ V < m / a))]
      ring
  · rw [if_neg (by omega : ¬ (L < a ∧ a ≤ H ∧ V < m / a)),
      if_neg (by omega : ¬ (L < a ∧ V < m / a)),
      if_neg (by omega : ¬ (H < a ∧ V < m / a))]
    ring

/-- The catalogue's `τ₃`, in the window form. -/
def tauThree (n : ℕ) : ℕ → ℝ := windowTypeII (cutoffU n) (cutoffU n) (cutoffB n) (cutoffB3 n)

/-- The window form displayed exactly as the catalogue's `τ₃`. -/
theorem tauThree_apply (n m : ℕ) :
    tauThree n m = ∑ a ∈ (Nat.divisors m).filter
        (fun a => cutoffB n < a ∧ a ≤ cutoffB3 n ∧ cutoffU n < m / a),
      (lowMoebiusWeight (cutoffU n) a) * (ArithmeticFunction.vonMangoldt (m / a) : ℝ) := rfl

/-- **`τ₃` as a difference of two half-line coefficients.** -/
theorem tauThree_eq_sub (n m : ℕ) (h : cutoffB n ≤ cutoffB3 n) :
    tauThree n m = halfLineTypeII (cutoffU n) (cutoffU n) (cutoffB n) m
      - halfLineTypeII (cutoffU n) (cutoffU n) (cutoffB3 n) m :=
  windowTypeII_eq_sub _ _ _ _ _ h

/-- **Support of the small-cofactor region.**  If the cofactor is at most `V₀` then the
argument is at most `H · V₀`.  With `H = n^(2/3)` and `V₀ = n^(2/5)` this puts the
small-cofactor part of `τ₃` on `m ≤ n^(13/15)`. -/
theorem le_mul_of_cofactor_le (m a H V₀ : ℕ) (ha : a ∣ m) (haH : a ≤ H)
    (hcof : m / a ≤ V₀) : m ≤ H * V₀ := by
  have hm : m = a * (m / a) := (Nat.mul_div_cancel' ha).symm
  rw [hm]
  exact Nat.mul_le_mul haH hcof

/-- **The general-cutoff Type-II block bound.**  `typeIIBlock_sq_le_uniform` fed
through `cutoff_squared_budget_general`: no relation between `U`, `V` and `N^(2/5)`.

With `U = N^(1/16)` this gives `N/√U = N^(31/32)`, so the block scale is
`N^(31/32) log³` and the summed scale `N^(31/32) log⁴ = o(N)` — the budget still
closes, the loss against the `2/5` form being `N^(27/80)`. -/
theorem typeIIBlock_norm_le_general (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ)) (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hU : 0 < U) (hV : 0 < V) (hN : 1 ≤ N) :
    ‖OAI.Problem337.Vaughan.typeIIBlock N U V j
        (fun k => OAI.Problem337.VaughanBilinear.phase (θ * (k : ℝ)))‖
      ≤ Real.sqrt 32 * (1 + Real.log (2 * (N : ℝ))) ^ 3 *
        ((N : ℝ) / Real.sqrt q + (N : ℝ) / Real.sqrt U
          + (N : ℝ) / Real.sqrt V + Real.sqrt ((N : ℝ) * q)) := by
  have hb := OAI.Problem337.Vaughan.typeIIBlock_sq_le_uniform θ a q hq hcop happrox
    N U V j hqN hU hV
  have hlog : OAI.Problem337.Vaughan.typeIILogScale N = 1 + Real.log (2 * (N : ℝ)) := rfl
  rw [hlog] at hb
  exact cutoff_squared_budget_general (X := (N : ℝ)) (q := (q : ℝ)) (C := 32)
    (U := (U : ℝ)) (V := (V : ℝ))
    (R := ‖OAI.Problem337.Vaughan.typeIIBlock N U V j
        (fun k => OAI.Problem337.VaughanBilinear.phase (θ * (k : ℝ)))‖)
    (by exact_mod_cast hN) (by exact_mod_cast hq) (by norm_num)
    (by exact_mod_cast hU) (by exact_mod_cast hV) hb

/-! ### Milestone 40: Cauchy–Schwarz for the deep-minor pair integral

Both residual estimates of the `τ₃` reduction need the same inequality: the deep-minor
*bilinear* integral is bounded by the product of the two `L²` masses,

```text
|Jdeep(u,v)| ≤ ‖S_u‖₂ · ‖S_v‖₂ ,      |Jdeep(u,u)| ≤ ‖S_u‖₂² .
```

This is what lets a residual coefficient supported on a short range `m ≤ n^(13/15)`
be discarded: its `L²` mass is `o(n)`. -/

/-- The complex exponential of a real has norm one. -/
theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- **Cauchy–Schwarz for the integral of a product**, on a set inside `(0,1]` and with
globally bounded factors. -/
theorem norm_setIntegral_mul_le_sqrt {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Ioc (0:ℝ) 1)
    {f g : ℝ → ℂ} (Cf Cg : ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ t, ‖f t‖ ≤ Cf) (hgb : ∀ t, ‖g t‖ ≤ Cg) :
    ‖∫ t in E, f t * g t‖
      ≤ Real.sqrt (∫ t in E, ‖f t‖ ^ 2) * Real.sqrt (∫ t in E, ‖g t‖ ^ 2) := by
  have hIoc : volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]
    simp
  have hfin : volume E < ⊤ := (measure_mono hEsub).trans_lt hIoc
  have hfin' : (volume.restrict E) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hfin
  haveI : IsFiniteMeasure (volume.restrict E) := ⟨hfin'⟩
  have hfM : MemLp f (ENNReal.ofReal 2) (volume.restrict E) := by
    simpa using MemLp.of_bound hf.aestronglyMeasurable Cf
      (Filter.Eventually.of_forall hfb)
  have hgM : MemLp g (ENNReal.ofReal 2) (volume.restrict E) := by
    simpa using MemLp.of_bound hg.aestronglyMeasurable Cg
      (Filter.Eventually.of_forall hgb)
  have hpq : (2:ℝ).HolderConjugate 2 :=
    { inv_add_inv_eq_inv := by norm_num, left_pos := by norm_num, right_pos := by norm_num }
  have h := integral_mul_norm_le_Lp_mul_Lq (f := f) (g := g) (p := 2) (q := 2) hpq hfM hgM
  calc ‖∫ t in E, f t * g t‖
      ≤ ∫ t in E, ‖f t * g t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in E, ‖f t‖ * ‖g t‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∫ t in E, ‖f t‖ ^ 2) * Real.sqrt (∫ t in E, ‖g t‖ ^ 2) := by
        refine h.trans (le_of_eq ?_)
        simp only [Real.rpow_two]
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Cross term.**  `|Jdeep(u,v)| ≤ ‖S_u‖₂ ‖S_v‖₂`. -/
theorem norm_deepCross_le_sqrt {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Ioc (0:ℝ) 1) (n : ℕ) (u v : ℕ → ℂ) (Cu Cv : ℝ)
    (hu : ∀ t, ‖plainPolynomial n u t‖ ≤ Cu)
    (hv : ∀ t, ‖plainPolynomial n v t‖ ≤ Cv) :
    ‖∫ t in E, plainPolynomial n u t * plainPolynomial n v t * phase (-(n:ℝ)*t)‖
      ≤ Real.sqrt (∫ t in E, ‖plainPolynomial n u t‖ ^ 2)
        * Real.sqrt (∫ t in E, ‖plainPolynomial n v t‖ ^ 2) := by
  have hnorm : ∀ t : ℝ,
      ‖plainPolynomial n v t * phase (-(n:ℝ)*t)‖ = ‖plainPolynomial n v t‖ := by
    intro t
    rw [norm_mul, norm_phase (x := -(n:ℝ)*t), mul_one]
  have hgb : ∀ t : ℝ, ‖plainPolynomial n v t * phase (-(n:ℝ)*t)‖ ≤ Cv := by
    intro t
    rw [hnorm t]
    exact hv t
  have h := norm_setIntegral_mul_le_sqrt (E := E)
    (f := plainPolynomial n u)
    (g := fun t : ℝ => plainPolynomial n v t * phase (-(n:ℝ)*t)) hE hEsub Cu Cv
    (by unfold plainPolynomial phase; fun_prop)
    ((by unfold plainPolynomial phase; fun_prop : Continuous (plainPolynomial n v)).mul
      (by unfold phase; fun_prop))
    hu hgb
  have hint : (∫ t in E, ‖plainPolynomial n v t * phase (-(n:ℝ)*t)‖ ^ 2)
      = ∫ t in E, ‖plainPolynomial n v t‖ ^ 2 :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun t => by simp only [hnorm t]))
  rw [hint] at h
  have hassoc : (∫ t in E, plainPolynomial n u t
        * (plainPolynomial n v t * phase (-(n:ℝ)*t)))
      = ∫ t in E, plainPolynomial n u t * plainPolynomial n v t * phase (-(n:ℝ)*t) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun t => by simp only [mul_assoc]))
  rw [hassoc] at h
  exact h

/-- **Self term.**  `|Jdeep(u,u)| ≤ ‖S_u‖₂²`. -/
theorem norm_deepSelf_le {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Ioc (0:ℝ) 1) (n : ℕ) (u : ℕ → ℂ) (Cu : ℝ)
    (hu : ∀ t, ‖plainPolynomial n u t‖ ≤ Cu) :
    ‖∫ t in E, plainPolynomial n u t * plainPolynomial n u t * phase (-(n:ℝ)*t)‖
      ≤ ∫ t in E, ‖plainPolynomial n u t‖ ^ 2 := by
  have hA : 0 ≤ ∫ t in E, ‖plainPolynomial n u t‖ ^ 2 := by positivity
  have h := norm_deepCross_le_sqrt hE hEsub n u u Cu Cu hu hu
  calc ‖∫ t in E, plainPolynomial n u t * plainPolynomial n u t * phase (-(n:ℝ)*t)‖
      ≤ Real.sqrt (∫ t in E, ‖plainPolynomial n u t‖ ^ 2)
          * Real.sqrt (∫ t in E, ‖plainPolynomial n u t‖ ^ 2) := h
    _ = Real.sqrt ((∫ t in E, ‖plainPolynomial n u t‖ ^ 2) ^ 2) := by
        rw [← Real.sqrt_mul hA]; ring_nf
    _ = ∫ t in E, ‖plainPolynomial n u t‖ ^ 2 := Real.sqrt_sq hA

/-! ### Milestone 41: the cofactor peeling for `τ₁`, with correct exponents

**Correction.**  `B₃ · n^(2/5) = n^(2/3 + 2/5) = n^(16/15)`, *not* `n^(13/15)`.
Since `16/15 > 1`, the support bound used in M36.5 / M40 for `τ₃` is **vacuous**, and
the conclusions drawn there (`‖S_res‖₂² = o(n)`, `Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)`)
are **not established**.

The support trick does work for `τ₁` and `τ₂`, because their divisor upper bounds are
small:

| cell | `H_i` | support `H_i · V` with `V = n^(2/5)` | short? |
|---|---|---|---|
| τ₁ | `n^(1/4)` | `n^(13/20)` | yes |
| τ₂ | `n^(1/3)` | `n^(11/15)` | yes |
| τ₃ | `n^(2/3)` | `n^(16/15)` | no |
| τ₄ | `n^(15/16)` | `n^(107/80)` | no |

Below is the peeling for `τ₁`: split the cofactor at an arbitrary threshold `V`, show the
low part is supported on `m ≤ B₁ · V`, and bound its `L²` mass by an explicit quantity. -/

/-- `τ₁` with the cofactor restricted to `m / a ≤ V`. -/
def lowBandCoefficientBot (n V : ℕ) : ℕ → ℝ :=
  fun m => ∑ a ∈ (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ m / a ≤ V),
    lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)

/-- `τ₁` with the cofactor restricted to `V < m / a`. -/
def lowBandCoefficientTop (n V : ℕ) : ℕ → ℝ :=
  fun m => ∑ a ∈ (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ V < m / a),
    lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)

/-- **Exact cofactor split.** -/
theorem lowBandCoefficient_eq_bot_add_top (n V m : ℕ) :
    lowBandCoefficient (cutoffU n) (lowCut n) m
      = lowBandCoefficientBot n V m + lowBandCoefficientTop n V m := by
  classical
  have hbot : (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ m / a ≤ V)
      = ((Nat.divisors m).filter
          (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a)).filter
          (fun a => m / a ≤ V) := by
    ext a
    simp only [Finset.mem_filter]
    tauto
  have htop : (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ V < m / a)
      = ((Nat.divisors m).filter
          (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a)).filter
          (fun a => ¬ m / a ≤ V) := by
    ext a
    simp only [Finset.mem_filter, not_le]
    tauto
  unfold lowBandCoefficient lowBandCoefficientBot lowBandCoefficientTop
  rw [hbot, htop]
  exact (Finset.sum_filter_add_sum_filter_not _ (fun a => m / a ≤ V) _).symm

/-- **Support of the low part**: it vanishes above `B₁ · V`. -/
theorem lowBandCoefficientBot_eq_zero (n V m : ℕ) (hm : lowCut n * V < m) :
    lowBandCoefficientBot n V m = 0 := by
  classical
  unfold lowBandCoefficientBot
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨had, hUa, haB, hcofU, hcofV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hadvd, _⟩ := Nat.mem_divisors.mp had
  exact absurd (le_mul_of_cofactor_le m a (lowCut n) V hadvd haB hcofV) (by omega)

/-- Pointwise size of the low part (same bound as `tauCoeff_abs_le`). -/
theorem lowBandCoefficientBot_abs_le (n V m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ a, cutoffU n < a → a ≤ lowCut n → |lowMoebiusWeight (cutoffU n) a| ≤ T) :
    ‖(lowBandCoefficientBot n V m : ℂ)‖ ≤ T * Real.log m := by
  classical
  unfold lowBandCoefficientBot
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc |∑ a ∈ (Nat.divisors m).filter
        (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ m / a ≤ V),
        lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)|
      ≤ ∑ a ∈ (Nat.divisors m).filter
        (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ m / a ≤ V),
        |lowMoebiusWeight (cutoffU n) a * ArithmeticFunction.vonMangoldt (m / a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Nat.divisors m).filter
        (fun a => cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a ∧ m / a ≤ V),
        T * ArithmeticFunction.vonMangoldt (m / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        obtain ⟨_, hUa, haB, _, _⟩ := Finset.mem_filter.mp ha
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_right (hc a hUa haB) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ a ∈ Nat.divisors m, T * ArithmeticFunction.vonMangoldt (m / a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro a _ _
        exact mul_nonneg hT ArithmeticFunction.vonMangoldt_nonneg
    _ = T * Real.log m := by rw [← Finset.mul_sum, sum_vonMangoldt_div_divisors]

/-- Parseval for an arbitrary coefficient sequence. -/
theorem integral_plainPolynomial_norm_sq (n : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖plainPolynomial n a t‖ ^ 2)
      = ∑ m ∈ Finset.range (n + 1), ‖a m‖ ^ 2 := by
  simp_rw [← norm_shiftedPolynomial_eq n a]
  exact shiftedPolynomial_parseval n a

/-- **Localisation of the low part's `L²` mass**: only `m ≤ B₁ · V` contributes. -/
theorem sum_bot_norm_sq_localize (n V : ℕ) (hV : lowCut n * V ≤ n) :
    (∑ m ∈ Finset.range (n + 1), ‖(lowBandCoefficientBot n V m : ℂ)‖ ^ 2)
      = ∑ m ∈ Finset.range (lowCut n * V + 1), ‖(lowBandCoefficientBot n V m : ℂ)‖ ^ 2 := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  · intro m hm hmn
    simp only [Finset.mem_range] at hm hmn
    have hlt : lowCut n * V < m := by omega
    rw [lowBandCoefficientBot_eq_zero n V m hlt]
    simp

/-- **The peeling bound.**  The low-cofactor part of `τ₁` has `L²` mass at most
`T² · (B₁ · V + 1) · log²n`.  With the crude `T ≤ B₁` this is `o(n)` as soon as
`B₁³ · V = o(n)`, i.e. `V = n^(1/4 − δ)`; with the divisor bound `T = n^o(1)` it is `o(n)`
as soon as `B₁ · V = o(n)`, i.e. `V = n^(3/4 − δ)`. -/
theorem integral_bot_norm_sq_le (n V : ℕ) (hV : lowCut n * V ≤ n)
    {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ a, cutoffU n < a → a ≤ lowCut n → |lowMoebiusWeight (cutoffU n) a| ≤ T) :
    (∫ t in (0:ℝ)..1,
        ‖plainPolynomial n (fun m => (lowBandCoefficientBot n V m : ℂ)) t‖ ^ 2)
      ≤ T ^ 2 * ((lowCut n * V : ℕ) + 1 : ℝ) * (Real.log n) ^ 2 := by
  rw [integral_plainPolynomial_norm_sq, sum_bot_norm_sq_localize n V hV]
  have hlog : ∀ m ∈ Finset.range (lowCut n * V + 1),
      (Real.log (m:ℝ)) ^ 2 ≤ (Real.log (n:ℝ)) ^ 2 := by
    intro m hm
    have hmn : m ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)).trans hV
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simpa using sq_nonneg (Real.log (n:ℝ))
    · have h1 : Real.log (m:ℝ) ≤ Real.log (n:ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hmn)
      have h2 : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
      nlinarith [h1, h2]
  have hsum : (∑ m ∈ Finset.range (lowCut n * V + 1),
        ‖(lowBandCoefficientBot n V m : ℂ)‖ ^ 2)
      ≤ ∑ m ∈ Finset.range (lowCut n * V + 1), T ^ 2 * (Real.log (n:ℝ)) ^ 2 := by
    refine Finset.sum_le_sum fun m hm => ?_
    have h1 : ‖(lowBandCoefficientBot n V m : ℂ)‖ ≤ T * Real.log (m:ℝ) :=
      lowBandCoefficientBot_abs_le n V m hT hc
    have h3 : 0 ≤ Real.log (m:ℝ) := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; simp
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    calc ‖(lowBandCoefficientBot n V m : ℂ)‖ ^ 2 ≤ (T * Real.log (m:ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = T ^ 2 * (Real.log (m:ℝ)) ^ 2 := by ring
      _ ≤ T ^ 2 * (Real.log (n:ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (hlog m hm) (by positivity)
  refine hsum.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

/-! ### Milestone 42 (step 1): the crude coefficient bound `T = B₁`, instantiated -/

/-- `|c_U(a)| ≤ a.divisors.card ≤ a ≤ B₁`. -/
theorem lowMoebiusWeight_abs_le_lowCut (n a : ℕ) (ha : a ≤ lowCut n) :
    |lowMoebiusWeight (cutoffU n) a| ≤ (lowCut n : ℝ) := by
  calc |lowMoebiusWeight (cutoffU n) a|
      ≤ (a.divisors.card : ℝ) := abs_lowMoebiusWeight_le (cutoffU n) a
    _ ≤ (a : ℝ) := by exact_mod_cast Nat.card_divisors_le_self a
    _ ≤ (lowCut n : ℝ) := by exact_mod_cast ha

/-- **The peeling bound with the crude coefficient bound `T = B₁`.**
No prime-distribution input: `|c(a)| ≤ a.divisors.card ≤ a ≤ B₁`. -/
theorem integral_bot_norm_sq_le_lowCut (n V : ℕ) (hV : lowCut n * V ≤ n) :
    (∫ t in (0:ℝ)..1,
        ‖plainPolynomial n (fun m => (lowBandCoefficientBot n V m : ℂ)) t‖ ^ 2)
      ≤ (lowCut n : ℝ) ^ 2 * (((lowCut n * V : ℕ) : ℝ) + 1) * (Real.log n) ^ 2 :=
  integral_bot_norm_sq_le n V hV (by positivity)
    (fun a _ ha => lowMoebiusWeight_abs_le_lowCut n a ha)

/-! ### Milestone 42 (step 2): the free coefficient bound `T = U` from Möbius cancellation

`T` in `integral_bot_norm_sq_le` bounds the **coefficient** `c_U(a) = ∑_{U<d|a} μ(d)`,
not a divisor count of `m`.  Since `∑_{d|a} μ(d) = 0` for `a > 1`, the weight equals the
negative of the sum over the *small* divisors `d ≤ U`, so

```text
|c_U(a)|  =  |∑_{d | a, d ≤ U} μ(d)|  ≤  #{d | a : d ≤ U}  ≤  U .
```

This needs no divisor bound at all.  -/

/-- **Trivial Möbius-cancellation bound**: `|c_U(a)| ≤ U` for `a > 1`. -/
theorem lowMoebiusWeight_abs_le_cutoffU (U a : ℕ) (ha : 1 < a) :
    |lowMoebiusWeight U a| ≤ (U : ℝ) := by
  classical
  have hcard : (a.divisors.filter (fun d => d ≤ U)).card ≤ U := by
    have hsub : a.divisors.filter (fun d => d ≤ U) ⊆ Finset.Icc 1 U := by
      intro d hd
      obtain ⟨hda, hdU⟩ := Finset.mem_filter.mp hd
      have hpos : 0 < d := Nat.pos_of_mem_divisors hda
      exact Finset.mem_Icc.mpr ⟨hpos, hdU⟩
    calc (a.divisors.filter (fun d => d ≤ U)).card
        ≤ (Finset.Icc 1 U).card := Finset.card_le_card hsub
      _ = U := by simp
  rw [lowMoebiusWeight_eq_neg_small U a ha, abs_neg]
  calc |∑ d ∈ a.divisors.filter (fun d => d ≤ U), (μ d : ℝ)|
      ≤ ∑ d ∈ a.divisors.filter (fun d => d ≤ U), |(μ d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ a.divisors.filter (fun d => d ≤ U), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
          ArithmeticFunction.abs_moebius_le_one
        have h' : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast h
        simpa using h'
    _ = ((a.divisors.filter (fun d => d ≤ U)).card : ℝ) := by simp
    _ ≤ (U : ℝ) := by exact_mod_cast hcard

/-- **The peeling bound with the free coefficient bound `T = U`.**
With `V = n^(5/8 − δ)` this is `o(n)`: `U² · B₁ · V = n^(1/8) · n^(1/4) · n^(5/8−δ) = n^(1−δ)`. -/
theorem integral_bot_norm_sq_le_cutoffU (n V : ℕ) (hV : lowCut n * V ≤ n)
    (hU : 1 ≤ cutoffU n) :
    (∫ t in (0:ℝ)..1,
        ‖plainPolynomial n (fun m => (lowBandCoefficientBot n V m : ℂ)) t‖ ^ 2)
      ≤ (cutoffU n : ℝ) ^ 2 * (((lowCut n * V : ℕ) : ℝ) + 1) * (Real.log n) ^ 2 :=
  integral_bot_norm_sq_le n V hV (by positivity)
    (fun a hUa _ => lowMoebiusWeight_abs_le_cutoffU (cutoffU n) a (by omega))

end B1B1Port
