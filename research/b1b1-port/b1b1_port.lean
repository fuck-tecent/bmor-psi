import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion

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

end B1B1Port
