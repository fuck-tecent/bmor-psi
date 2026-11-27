import Mathlib

/-!
Absolute real zero gap for quadratic Dirichlet characters.
The arithmetic and determinant argument adapts OpenAI's openai/math,
revision 3344da59991ed94f9ba711217b29c1d760badfa6, under the Apache License 2.0.
The interpolation proof and bridge are by Joseph M. Reilly, copyright 2026,
from jmreilly1113/siegel-zeros-audit, revision 24bcdd89ad7bc09b228cf8437831520632686de9,
under the Apache License 2.0. The Mertens estimates adapt PrimeNumberTheoremAnd,
IEANTN/Mertens.lean, revision c39a751132c88b6e8080b74c74023fd95b3d8be0, under the same license.
This version adapts the selected declarations to the project's library, proves the
analytic estimate using a local disk expansion, and transfers the primitive gap
to arbitrary quadratic characters. The local analytic sources are credited below.
-/

section

/-! Local Landau expansion and Dirichlet growth estimates adapted from Goldbach PRs 43 and 2486.
Source revision f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f, Apache-2.0.
The disk expansion credits the Borel–Carathéodory method of Anthropic, PBC. -/

open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace GoldbachGrhGrowth

variable {q : ℕ} [NeZero q]

/-- The average value of a Dirichlet character over a full period. -/
def charMean (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, χ a

open scoped Classical in
theorem charMean_eq (χ : DirichletCharacter ℂ q) :
    charMean χ = if χ = 1 then (q.totient : ℂ) / (q : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [charMean, MulChar.sum_one_eq_card_units,
      ZMod.card_units_eq_totient, div_eq_inv_mul]
  · simp only [charMean, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem level_mul_charMean (χ : DirichletCharacter ℂ q) :
    (q : ℂ) * charMean χ = ∑ a : ZMod q, χ a := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [charMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem norm_charMean_le_one (χ : DirichletCharacter ℂ q) : ‖charMean χ‖ ≤ 1 := by
  classical
  by_cases hχ : χ = 1
  · simp only [charMean_eq, ite_eq_left hχ, norm_div, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast q.pos_of_neZero)).2
    exact_mod_cast q.totient_le
  · simp [charMean_eq, hχ]

/-- The character sum over the positive integers at most `n`. -/
def charPartialSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)

omit [NeZero q] in
theorem norm_charPartialSum_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖charPartialSum χ n‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range n, ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = n := by simp

private theorem sum_character_block (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun k => (k.val : ZMod q)
      invFun := fun a => ⟨a.val, a.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt])
      right_inv := ZMod.natCast_zmod_val }
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => χ ((m + k : ℕ) : ZMod q)) q]
  refine Fintype.sum_equiv (e.trans (Equiv.addRight (m : ZMod q))) _ _ fun k => ?_
  change χ ((m + k.val : ℕ) : ZMod q) = χ ((k.val : ZMod q) + (m : ZMod q))
  rw [Nat.cast_add, add_comm]

/-- The centered character sum at a natural-number endpoint. -/
def integerRemainder (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  charPartialSum χ n - (n : ℂ) * charMean χ

theorem integerRemainder_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (integerRemainder χ) q := by
  intro n
  have hBlock : (∑ k ∈ range q, χ ((n + k + 1 : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using sum_character_block χ (n + 1)
  simp only [integerRemainder, charPartialSum, Finset.sum_range_add]
  rw [hBlock]
  simp only [Nat.cast_add, add_mul, level_mul_charMean]
  abel

theorem norm_integerRemainder_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖integerRemainder χ n‖ ≤ 2 * (q : ℝ) := by
  rw [← (integerRemainder_periodic χ).map_mod_nat n]
  let r := n % q
  have hr : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n q.pos_of_neZero).le
  calc
    _ ≤ ‖charPartialSum χ r‖ + ‖(r : ℂ) * charMean χ‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := by
      refine add_le_add (norm_charPartialSum_le χ r) ?_
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_charMean_le_one χ) r.cast_nonneg
    _ ≤ _ := by linarith

/-- The centered character sum for real endpoints, extended by zero at `x ≤ 1`. -/
def periodicRemainder (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ

theorem norm_periodicRemainder_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖periodicRemainder χ x‖ ≤ 3 * (q : ℝ) := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
    have hd : ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx0))]
      linarith [Nat.lt_floor_add_one x]
    have hsplit : charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ =
        integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ := by
      unfold integerRemainder
      ring
    rw [periodicRemainder, indicator_of_mem hx, hsplit]
    calc
      _ ≤ ‖integerRemainder χ ⌊x⌋₊‖ + ‖((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ‖ :=
        norm_add_le _ _
      _ ≤ 2 * (q : ℝ) + 1 := by
        refine add_le_add (norm_integerRemainder_le χ _) ?_
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hd (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
        linarith
  · rw [periodicRemainder, indicator_of_notMem hx, norm_zero]
    positivity

omit [NeZero q] in
private theorem measurable_partialSum_floor (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊) :=
  (measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor

private theorem measurable_centeredCharSum (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) :=
  (measurable_partialSum_floor χ).sub (continuous_ofReal.measurable.mul_const _)

theorem measurable_periodicRemainder (χ : DirichletCharacter ℂ q) :
    Measurable (periodicRemainder χ) :=
  (measurable_centeredCharSum χ).indicator measurableSet_Ioi

/-- The Mellin transform of the centered sum, with exponent `-s-1` in the integral. -/
def remainderMellin (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  mellin (periodicRemainder χ) (-s)

theorem remainderMellin_eq_integral (χ : DirichletCharacter ℂ q) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) := by
  have hIntegrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • periodicRemainder χ x) =
      (Ioi (1 : ℝ)).indicator (fun x => (x : ℂ) ^ (-s - 1) *
        (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) := by
    ext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [periodicRemainder, indicator_of_mem hx, smul_eq_mul]
    · simp only [periodicRemainder, indicator_of_notMem hx, smul_zero]
  rw [remainderMellin, mellin, hIntegrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)]

private theorem norm_weightedRemainder_le (χ : DirichletCharacter ℂ q) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)‖ ≤
      (3 * (q : ℝ)) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hBound := norm_periodicRemainder_le χ x
  rw [periodicRemainder, indicator_of_mem hx] at hBound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg hx0.le _)).trans_eq (mul_comm _ _)

private theorem weightedRemainder_integrableOn (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) := by
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine Integrable.mono' hBound ?_ ?_
  · have hKernel : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      intro x hx
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt
    exact (hKernel.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_centeredCharSum χ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx

theorem norm_remainderMellin_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    ‖remainderMellin χ s‖ ≤ (3 * (q : ℝ)) / s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine (norm_integral_le_of_norm_le hBound ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
    rw [show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
    simp only [div_neg, neg_div, neg_neg, mul_one_div]

theorem differentiableAt_remainderMellin (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (remainderMellin χ) s := by
  have hLoc : LocallyIntegrableOn (periodicRemainder χ) (Ioi (0 : ℝ)) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_periodicRemainder χ).aestronglyMeasurable
      (Eventually.of_forall (norm_periodicRemainder_le χ))
  have hTop : periodicRemainder χ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (3 * (q : ℝ)) (Eventually.of_forall fun x => ?_)
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_periodicRemainder_le χ x
  have hBot : periodicRemainder χ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    have hNear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hNear] with x hx
    have hOutside : x ∉ Ioi (1 : ℝ) := fun h => (mem_Iio.mp hx).not_gt (mem_Ioi.mp h)
    simp only [periodicRemainder, indicator_of_notMem hOutside, norm_zero, zero_mul, le_refl]
  have hNeg : (-s).re < 0 := by simpa only [neg_re, neg_lt_zero] using hs
  have hAbove : -s.re - 1 < (-s).re := by rw [neg_re]; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hNeg hBot hAbove).comp s
    differentiableAt_id.neg

omit [NeZero q] in
private def seriesCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

omit [NeZero q] in
private theorem sum_seriesCoefficient_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [seriesCoefficient, charPartialSum]

private theorem integral_centeringTerm (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) ∧
      (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) =
        charMean χ / (s - 1) := by
  have hPower : (-s).re < -1 := by rw [neg_re]; linarith
  have hIntegrand (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) = charMean χ * (x : ℂ) ^ (-s) := by
    have hx0 : 0 < x := zero_lt_one.trans (Set.mem_Ioi.mp hx)
    have hProd : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
      simpa only [sub_add_cancel, cpow_one] using
        (cpow_add (-s - 1) 1 (ofReal_ne_zero.mpr hx0.ne')).symm
    rw [← mul_assoc, hProd, mul_comm]
  constructor
  · have hInt : IntegrableOn (fun x : ℝ => charMean χ * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt hPower zero_lt_one).const_mul (charMean χ)
    exact hInt.congr_fun (fun x hx => (hIntegrand x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand, integral_const_mul,
      integral_Ioi_cpow_of_lt hPower zero_lt_one]
    rw [show -s + 1 = -(s - 1) by ring]
    simp only [ofReal_one, one_cpow, div_neg, neg_div, neg_neg, mul_one_div]

/-- Abel summation on the half-plane of absolute convergence. -/
theorem LFunction_eq_centeredMellin_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s =
      s * (remainderMellin χ s + charMean χ / (s - 1)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hDiff : ∀ x ∈ Ici (1 : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne'
      (neg_ne_zero.mpr hs0)).differentiableAt
  have hDerivLoc : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    have hNeg : (-s).re < 0 := by rw [neg_re]; linarith
    refine ((integrableOn_Ioi_deriv_ofReal_cpow (t := (1 / 2 : ℝ)) (by norm_num) hNeg).mono_set
      (fun x hx => ?_)).locallyIntegrableOn
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)
  have hPowerLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
  have hBoundary : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hPowerLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [f, norm_mul, Complex.ofReal_natCast, norm_natCast_cpow_of_pos hn, neg_re,
      sum_seriesCoefficient_eq]
    calc
      _ ≤ (n : ℝ) ^ (-s.re) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_charPartialSum_le χ n) (Real.rpow_nonneg n.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_add_one (Nat.cast_ne_zero.mpr hn.ne'), neg_add_eq_sub]
  have hSumDom : (fun x : ℝ => ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k) =O[atTop]
      fun x : ℝ => x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sum_seriesCoefficient_eq, one_mul, Real.norm_of_nonneg hx.le]
    exact (norm_charPartialSum_le χ _).trans (Nat.floor_le hx.le)
  have hDerivativeDom : (fun x : ℝ => deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k)
      =O[atTop] fun x : ℝ => x ^ (-s.re) := by
    refine ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul hSumDom).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_re, ← Real.rpow_add_one hx.ne', sub_add_cancel]
  have hDominatingIntegral : IntegrableAtFilter (fun x : ℝ => x ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop _, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (seriesCoefficient χ)
    (by simp [seriesCoefficient]) hDiff hDerivLoc hBoundary hDerivativeDom hDominatingIntegral
  have hCoeff (n : ℕ) : f n * seriesCoefficient χ n =
      LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [seriesCoefficient]
    · simp [f, seriesCoefficient, hn, cpow_neg, div_eq_inv_mul]
  have hSum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      f k * seriesCoefficient χ k) atTop (𝓝 (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
    simp_rw [hCoeff, ← Nat.range_succ_eq_Icc_zero]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSeriesIdentity : DirichletCharacter.LFunction χ s = (0 : ℂ) -
      ∫ x : ℝ in Ioi (1 : ℝ), deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique hSum hAbel
  calc
    _ = (0 : ℂ) - ∫ x : ℝ in Ioi (1 : ℝ), (-s) *
        ((x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [hSeriesIdentity]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : x ≠ 0 := (zero_lt_one.trans (Set.mem_Ioi.mp hx)).ne'
      simp only [f, deriv_ofReal_cpow_const (-s) hx0, sum_seriesCoefficient_eq, mul_assoc]
    _ = s * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [integral_const_mul, zero_sub, neg_mul, neg_neg]
    _ = _ := by
      have hSplit (x : ℝ) : (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊ =
          (x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) +
            (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) := by ring
      simp_rw [hSplit]
      rw [integral_add (weightedRemainder_integrableOn χ (zero_lt_one.trans hs))
        (integral_centeringTerm χ hs).1, ← remainderMellin_eq_integral, (integral_centeringTerm χ hs).2]

private theorem eq_on_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ g z)
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) {s : ℂ} (hs : 0 < s.re) : f s = g s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUConnected : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have hFA : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUOpen
  have hGA : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUOpen
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hAbsConv : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hEq : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hAbsConv] with z hz
    exact hfg z hz
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hGA hUConnected h2 hEq hs

/-- The centered Mellin representation of a nonprincipal L-function on the right half-plane. -/
theorem LFunction_eq_remainderMellin (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = s * remainderMellin χ s := by
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunction χ)
    (g := fun z : ℂ => z * remainderMellin χ z)
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z) ?_ ?_ hs
  · intro z hz
    exact differentiableAt_id.mul (differentiableAt_remainderMellin χ hz)
  · intro z hz
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    simp only [charMean_eq, ite_eq_right hχ, zero_div, add_zero]

/-- The Mellin representation of the principal L-function after removing its pole. -/
theorem LFunctionTrivChar₁_eq_remainderMellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      (s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s +
        s * charMean (1 : DirichletCharacter ℂ q) := by
  let χ : DirichletCharacter ℂ q := 1
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunctionTrivChar₁ q)
    (g := fun z : ℂ => (z - 1) * z * remainderMellin χ z + z * charMean χ)
    (fun z _ => DirichletCharacter.differentiable_LFunctionTrivChar₁ q z) ?_ ?_ hs
  · intro z hz
    have hId : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hSub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := hId.sub_const 1
    exact (((hSub.mul hId).mul (differentiableAt_remainderMellin χ hz)).add (hId.mul_const _))
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      norm_num [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    change (z - 1) * DirichletCharacter.LFunction χ z = _
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    field_simp [sub_ne_zero.mpr hz1]

open scoped Classical in
/-- A uniform growth bound for the Dirichlet L-function, with the principal pole removed. -/
theorem norm_regularizedLFunction_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 8 ≤ s.re) :
    ‖(if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
      else DirichletCharacter.LFunction χ s)‖ ≤ 25 * (q : ℝ) * (1 + ‖s‖) ^ 2 := by
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hs
  have hRemainder : ‖remainderMellin χ s‖ ≤ 24 * (q : ℝ) := by
    calc
      _ ≤ (3 * (q : ℝ)) / s.re := norm_remainderMellin_le χ hs0
      _ ≤ (3 * (q : ℝ)) / (1 / 8 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
      _ = _ := by ring
  let M := 1 + ‖s‖
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [norm_nonneg s]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hSM : ‖s‖ ≤ M := by
    dsimp [M]
    linarith
  have hSubM : ‖s - 1‖ ≤ M := by
    simpa only [M, norm_one, add_comm] using norm_sub_le s (1 : ℂ)
  have hMSq : M ≤ M ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right hM0 hM
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
  have hMq : M ≤ (q : ℝ) * M ^ 2 :=
    hMSq.trans (le_mul_of_one_le_left (sq_nonneg _) hq)
  change ‖(if χ = 1 then _ else _)‖ ≤ 25 * (q : ℝ) * M ^ 2
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl, LFunctionTrivChar₁_eq_remainderMellin hs0]
    calc
      _ ≤ ‖(s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s‖ +
          ‖s * charMean (1 : DirichletCharacter ℂ q)‖ := norm_add_le _ _
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + M := by
        apply add_le_add
        · simp only [norm_mul, pow_two]
          exact mul_le_mul (mul_le_mul hSubM hSM (norm_nonneg _) hM0) hRemainder
            (norm_nonneg _) (mul_nonneg hM0 hM0)
        · rw [norm_mul]
          simpa only [mul_one] using mul_le_mul hSM (norm_charMean_le_one (1 : DirichletCharacter ℂ q))
            (norm_nonneg _) hM0
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + (q : ℝ) * M ^ 2 := add_le_add le_rfl hMq
      _ = _ := by ring
  · rw [ite_eq_right hχ, LFunction_eq_remainderMellin χ hχ hs0, norm_mul]
    calc
      _ ≤ M ^ 2 * (24 * (q : ℝ)) :=
        mul_le_mul (hSM.trans hMSq) hRemainder (norm_nonneg _) (sq_nonneg _)
      _ = 24 * (q : ℝ) * M ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) q.cast_nonneg) (sq_nonneg _)

end GoldbachGrhGrowth

namespace Goldbach

private theorem summable_inv_sq_shift (k : ℕ) :
    Summable (fun n : ℕ ↦ (((n + k : ℕ) : ℝ) ^ 2)⁻¹) :=
  (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) k).mpr
    (Real.summable_nat_pow_inv.mpr (by decide))

private theorem inv_sq_tail_le_three_fourths :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (3 / 4 : ℝ) := by
  let u : ℕ → ℝ := fun n ↦ ((n + 2 : ℕ) : ℝ)⁻¹
  have hTail : (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (1 / 2 : ℝ) := by
    apply le_of_tendsto' (summable_inv_sq_shift 3).hasSum.tendsto_sum_nat
    intro n
    calc
      _ ≤ ∑ m ∈ Finset.range n, (u m - u (m + 1)) := by
        apply Finset.sum_le_sum
        intro m _
        have hm₂ : 0 < (m : ℝ) + 2 := by positivity
        have hm₃ : 0 < (m : ℝ) + 3 := by positivity
        calc
          _ ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3))⁻¹ := by
            rw [Nat.cast_add, Nat.cast_ofNat]
            apply inv_anti₀ (mul_pos hm₂ hm₃)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) hm₃.le
          _ = _ := by
            simp only [u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
            rw [show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
            field_simp [hm₂.ne', hm₃.ne']
            ring
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ _ := (sub_le_self _ (by dsimp [u]; positivity)).trans_eq (by norm_num [u])
  have hSplit := (summable_inv_sq_shift 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.zero_add, Nat.add_assoc,
    show (1 + 2 : ℕ) = 3 by decide, Nat.cast_ofNat] at hSplit
  rw [← hSplit, show ((2 : ℝ) ^ 2)⁻¹ = 1 / 4 by norm_num]
  linarith only [hTail]

/-- A uniform positive lower bound for the Dirichlet L-function on `Re s = 2`. -/
theorem one_fourth_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  let s : ℂ := ⟨2, t⟩
  let term : ℕ → ℂ := LSeries.term (fun n : ℕ ↦ χ (n : ZMod q)) s
  have hs : 1 < s.re := by norm_num [s]
  have hTerm : Summable term := χ.LSeriesSummable_of_one_lt_re hs
  have hLFunction : χ.LFunction s = ∑' n : ℕ, term n := χ.LFunction_eq_LSeries hs
  have hTerm01 : (∑ n ∈ Finset.range 2, term n) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    simp [term]
  have hSplit := hTerm.sum_add_tsum_nat_add 2
  rw [hTerm01] at hSplit
  have hTermTail : Summable (fun n : ℕ ↦ term (n + 2)) :=
    (summable_nat_add_iff (f := term) 2).mpr hTerm
  have hTermNorm (n : ℕ) : ‖term (n + 2)‖ ≤ (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    dsimp [term]
    rw [LSeries.norm_term_eq, ite_eq_right (by omega : n + 2 ≠ 0), show s.re = 2 from rfl,
      show (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) = (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) by
        exact Real.rpow_natCast _ 2, ← one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hNormTail : ‖∑' n : ℕ, term (n + 2)‖ ≤ (3 / 4 : ℝ) :=
    (norm_tsum_le_tsum_norm hTermTail.norm).trans
      ((hTermTail.norm.tsum_le_tsum hTermNorm (summable_inv_sq_shift 2)).trans
        inv_sq_tail_le_three_fourths)
  have hSumNorm : (1 : ℝ) ≤ ‖χ.LFunction s‖ + ‖∑' n : ℕ, term (n + 2)‖ := calc
    _ = ‖(1 : ℂ)‖ := norm_one.symm
    _ = ‖χ.LFunction s - ∑' n : ℕ, term (n + 2)‖ := by
      rw [hLFunction, ← hSplit, add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
  change (1 / 4 : ℝ) ≤ ‖χ.LFunction s‖
  linarith only [hNormTail, hSumNorm]
end Goldbach
end


open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section

namespace GoldbachGrhLogDerivative

/- The argument uses the local zero separation and Borel–Carathéodory method in
`Zeta23/WeilEF/Landau.lean` (Anthropic, PBC), with direct Mathlib lemmas for primitives,
Jensen's inequality, factorized meromorphic functions and Cauchy's derivative bound. -/

private theorem exists_normalizedLog_on_ball {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R))
    (hg0 : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0) :
    ∃ J : ℂ → ℂ, J 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt J (logDeriv g z) z) ∧
      (∀ z ∈ ball (0 : ℂ) R, (J z).re = Real.log ‖g z‖ - Real.log ‖g 0‖) := by
  let U : Set ℂ := ball 0 R
  have hLog : DifferentiableOn ℂ (logDeriv g) U := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w => deriv g w / g w) U z
    exact ((hg z hz).deriv.differentiableAt.div (hg z hz).differentiableAt
      (hg0 z hz)).differentiableWithinAt
  obtain ⟨J, hJ0, hJ⟩ := hLog.isExactOn_ball.with_val_at 0 0
  refine ⟨J, hJ0, hJ, ?_⟩
  let k : ℂ → ℂ := fun z => exp (-J z) * g z
  have hk (z : ℂ) (hz : z ∈ U) : HasDerivAt k 0 z := by
    have hD := (hJ z hz).neg.cexp.mul (hg z hz).differentiableAt.hasDerivAt
    convert hD using 1
    simp only [logDeriv_apply]
    field_simp [hg0 z hz]
    norm_num
  have hc : (0 : ℂ) ∈ U := mem_ball_self hR
  have hConst : EqOn k (fun _ => g 0) U := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt) (differentiableOn_const (g 0))
      ?_ hc (by simp [k, hJ0])
    intro z hz
    rw [(hk z hz).deriv, deriv_const]
  intro z hz
  have hAt := hConst hz
  change exp (-J z) * g z = g 0 at hAt
  have hExp : exp (J z) * g 0 = g z := by
    rw [← hAt, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hNorm := congrArg norm hExp
  rw [norm_mul, norm_exp] at hNorm
  have hLn := congrArg Real.log hNorm
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (hg0 0 hc)), Real.log_exp] at hLn
  linarith

/-- On the inner disk, the derivative of the normalized logarithm is bounded by its upper real
part bound on the outer disk. The constants arise from Borel–Carathéodory and a Cauchy circle. -/
theorem norm_logDeriv_of_zeroFree_ball {g : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) (22 / 25)))
    (hg0 : ∀ z ∈ ball (0 : ℂ) (22 / 25), g z ≠ 0)
    (hgBound : ∀ z ∈ ball (0 : ℂ) (22 / 25),
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 83 / 100) :
    ‖logDeriv g z‖ ≤ 4200 * M := by
  have hR : (0 : ℝ) < 22 / 25 := by norm_num
  obtain ⟨J, hJ0, hJDeriv, hJRe⟩ := exists_normalizedLog_on_ball hR hg hg0
  have hJDiff : DifferentiableOn ℂ J (ball (0 : ℂ) (22 / 25)) :=
    fun w hw => (hJDeriv w hw).differentiableAt.differentiableWithinAt
  have hRadius : (0 : ℝ) < 1 / 100 := by norm_num
  have hLocalNorm (w : ℂ) (hw : w ∈ closedBall z (1 / 100)) : ‖w‖ ≤ 21 / 25 := by
    rw [mem_closedBall, Complex.dist_eq] at hw
    linarith [norm_le_norm_sub_add w z]
  have hLocal : closedBall z (1 / 100) ⊆ ball (0 : ℂ) (22 / 25) := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((hLocalNorm w hw).trans_lt (by norm_num))
  have hLocalDiff : DiffContOnCl ℂ J (ball z (1 / 100)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hRadius.ne']
    exact hJDiff.mono hLocal
  have hJImage : MapsTo J (ball (0 : ℂ) (22 / 25)) {w | w.re ≤ M} := by
    intro w hw
    change (J w).re ≤ M
    rw [hJRe w hw]
    exact hgBound w hw
  have hLocalBound (w : ℂ) (hw : w ∈ sphere z (1 / 100)) : ‖J w‖ ≤ 42 * M := by
    have hws := sphere_subset_closedBall hw
    have hwBig := hLocal hws
    have hSmall := hLocalNorm w hws
    have hDpos : 0 < (22 / 25 : ℝ) - ‖w‖ := by linarith
    refine (borelCaratheodory_zero hM hJDiff hJImage hR hwBig hJ0).trans ?_
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hSmall)]
  have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hRadius hLocalDiff hLocalBound
  have hzBig : z ∈ ball (0 : ℂ) (22 / 25) :=
    mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
  rw [(hJDeriv z hzBig).deriv] at hCauchy
  calc
    _ ≤ (42 * M) / (1 / 100 : ℝ) := hCauchy
    _ = _ := by ring

open MeromorphicOn in
private theorem factor_inner_divisor {f : ℂ → ℂ} {U V : Set ℂ}
    (hVU : V ⊆ U) (hCompact : IsCompact V) (hf : AnalyticOnNhd ℂ f U)
    (hFiniteOrder : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ V, g z ≠ 0) ∧
      EqOn f ((∏ᶠ ρ, (· - ρ) ^ divisor f V ρ) * g)
        (U \ Function.support (divisor f V)) := by
  let D := divisor f V
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  let Q : ℂ → ℂ := P⁻¹ • f
  let g := toMeromorphicNFOn Q U
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport hCompact
  have hPNF : MeromorphicNFOn P U := Function.FactorizedRational.meromorphicNFOn D U
  have hQMer : MeromorphicOn Q U := hPNF.meromorphicOn.inv.smul hf.meromorphicOn
  have hGNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn Q U
  have hPOrd (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hDfin
  have hGOrd (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [← meromorphicOrderAt_congr (hQMer.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm]
    change meromorphicOrderAt (P⁻¹ • f) z = _
    rw [meromorphicOrderAt_smul (hPNF.meromorphicOn z hz).inv (hf.meromorphicOn z hz),
      meromorphicOrderAt_inv, hPOrd]
  have hOrdInner (z : ℂ) (hz : z ∈ V) : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    change (divisor f V z : WithTop ℤ) = _
    rw [(hf.mono hVU).meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using hFiniteOrder z (hVU hz) with n hn
    simp
  have hGZeroOrder (z : ℂ) (hz : z ∈ V) : meromorphicOrderAt g z = 0 := by
    rw [hGOrd z (hVU hz), ← hOrdInner z hz, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    simp
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    apply (hGNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hzV : z ∈ V
    · rw [hGZeroOrder z hzV]
    · have hzD : D z = 0 := by
        by_contra h
        exact hzV (D.supportWithinDomain h)
      rw [hGOrd z hz, hzD, WithTop.coe_zero, neg_zero, zero_add]
      exact (hf z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hf z hz)
  · intro z hz
    exact (hGNF (hVU hz)).meromorphicOrderAt_eq_zero_iff.mp (hGZeroOrder z hz)
  · intro z hz
    have hzD : D z = 0 := by simpa only [Function.mem_support, not_not] using hz.2
    have hPOrd0 : meromorphicOrderAt P z = 0 := by rw [hPOrd, hzD, WithTop.coe_zero]
    have hPNZ : P z ≠ 0 := (hPNF hz.1).meromorphicOrderAt_eq_zero_iff.mp hPOrd0
    have hPA : AnalyticAt ℂ P z :=
      (hPNF hz.1).meromorphicOrderAt_nonneg_iff_analyticAt.mp hPOrd0.ge
    have hQA : AnalyticAt ℂ Q z := (hPA.inv hPNZ).mul (hf z hz.1)
    have hGQ : g z = Q z := by
      change toMeromorphicNFOn Q U z = Q z
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQMer hz.1,
        toMeromorphicNFAt_eq_self.mpr hQA.meromorphicNFAt]
    change f z = P z * g z
    rw [hGQ]
    change f z = P z * ((P z)⁻¹ * f z)
    rw [← mul_assoc, mul_inv_cancel₀ hPNZ, one_mul]

private theorem logDeriv_finset_zeroFactors {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  have hd (ρ : ℂ) : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have hProd : (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) =
      ∏ ρ ∈ Z, (fun w : ℂ => (w - ρ) ^ m ρ) := by
    funext w
    rw [Finset.prod_apply]
  rw [hProd, logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => (hd ρ).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [logDeriv_fun_pow (hd ρ).differentiableAt, logDeriv_apply, (hd ρ).deriv]
  ring

open MeromorphicOn in
/-- Landau's approximation by simple poles in a normalized unit disk. Jensen's inequality
bounds the sum of multiplicities. The remaining analytic factor is controlled on the smaller disk. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ sphere (0 : ℂ) (24 / 25), ‖f w‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (0 : ℂ) (22 / 25) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ z : ℂ, ‖z‖ ≤ 83 / 100 → f z ≠ 0 →
        ‖logDeriv f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          130200 * Real.log B := by
  classical
  let U := closedBall (0 : ℂ) 1
  let V := closedBall (0 : ℂ) (22 / 25)
  let W := closedBall (0 : ℂ) (24 / 25)
  have hVU : V ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hWU : W ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hVW : V ⊆ W := closedBall_subset_closedBall (by norm_num)
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self (by norm_num)
  have hf0NZ : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hFinA (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall _ _).isPreconnected h0U hz
      (by simp [(hf 0 h0U).analyticOrderAt_eq_zero.mpr hf0NZ])
  have hFinM (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf z hz).meromorphicOrderAt_eq]
    lift analyticOrderAt f z to ℕ using hFinA z hz with n hn
    simp
  let D := divisor f V
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall ..)
  let Z := hDfin.toFinset
  let K := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hSupport : V ∩ f ⁻¹' {0} = Function.support D :=
    (hf.mono hVU).meromorphicNFOn.zero_set_eq_divisor_support (fun v => hFinM v (hVU v.2))
  have hZeq : (↑Z : Set ℂ) = {ρ ∈ V | f ρ = 0} := by
    rw [show (↑Z : Set ℂ) = Function.support D from hDfin.coe_toFinset, ← hSupport]
    rfl
  have hρV (ρ : ℂ) (hρ : ρ ∈ Z) : ρ ∈ V := D.supportWithinDomain (hDfin.mem_toFinset.mp hρ)
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : D ρ = (analyticOrderNatAt f ρ : ℤ) := by
    change divisor f V ρ = _
    rw [(hf.mono hVU).divisor_apply (hρV ρ hρ), ← Nat.cast_analyticOrderNatAt (hFinA ρ (hVU (hρV ρ hρ)))]
    simp
  have hCount : (K : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
    have hFsum : (∑ᶠ u, D u) = ∑ ρ ∈ Z, D ρ :=
      finsum_eq_sum_of_support_subset _ fun _ hu => hDfin.mem_toFinset.mpr hu
    have hK : (K : ℤ) = ∑ ρ ∈ Z, D ρ := by
      simp only [K, Nat.cast_sum]
      exact Finset.sum_congr rfl fun ρ hρ => (hm ρ hρ).symm
    have hJ := AnalyticOnNhd.sum_divisor_le (r := (22 / 25 : ℝ)) (R := 24 / 25) (M := B)
      (by norm_num) (by norm_num) (by linarith)
      (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hf.mono hWU)
      hf0NZ (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hfB)
    have hRatio : (24 / 25 : ℝ) / (22 / 25) = 12 / 11 := by norm_num
    have hAbs : |(22 / 25 : ℝ)| = 22 / 25 := abs_of_nonneg (by norm_num)
    rw [hAbs] at hJ
    have hJ' : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
      simpa only [D, V, hf0, norm_one, div_one, hRatio] using hJ
    rw [hFsum, ← hK, Int.cast_natCast] at hJ'
    exact hJ'
  obtain ⟨g, hg, hgNZ, hFactor⟩ := factor_inner_divisor hVU (isCompact_closedBall ..) hf hFinM
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ
  have hProd : (∏ᶠ ρ, (· - ρ) ^ D ρ) = P := by
    have hDiff : (fun ρ : ℂ => (· - ρ) ^ D ρ).mulSupport ⊆ Z := by
      intro ρ hρ
      refine hDfin.mem_toFinset.mpr ?_
      by_contra hOutside
      have hD0 : D ρ = 0 := by simpa only [Function.mem_support, not_not] using hOutside
      exact hρ (by simp [hD0])
    rw [finprod_eq_prod_of_mulSupport_subset _ hDiff]
    funext w
    rw [Finset.prod_apply]
    exact Finset.prod_congr rfl fun ρ hρ => by simp [hm ρ hρ]
  have hFac : EqOn f (P * g) (U \ Function.support D) := by
    simpa only [← hProd] using hFactor
  have hOuter (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) :
      ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    have hwNorm : ‖w‖ = 24 / 25 := mem_sphere_zero_iff_norm.mp hw
    have hwU : w ∈ U := hWU (sphere_subset_closedBall hw)
    have hwNot : w ∉ Function.support D := by
      intro hwD
      have hwV : w ∈ V := D.supportWithinDomain hwD
      have hN : ‖w‖ ≤ 22 / 25 := by simpa only [V, mem_closedBall_iff_norm, sub_zero] using hwV
      linarith
    have hEq : f w = P w * g w := hFac ⟨hwU, hwNot⟩
    have hDist (ρ : ℂ) (hρ : ρ ∈ Z) : (2 / 25 : ℝ) ≤ ‖w - ρ‖ := by
      have hRho : ‖ρ‖ ≤ 22 / 25 := by
        simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
      exact (show (2 / 25 : ℝ) ≤ ‖w‖ - ‖ρ‖ by linarith).trans (norm_sub_norm_le w ρ)
    have hPBound : (2 / 25 : ℝ) ^ K ≤ ‖P w‖ := by
      simp only [P, norm_prod, norm_pow, K, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun ρ hρ => pow_le_pow_left₀ (by norm_num) (hDist ρ hρ) _)
    have hAt := hfB w hw
    rw [hEq, norm_mul] at hAt
    have hMul : ‖g w‖ * (2 / 25 : ℝ) ^ K ≤ B := by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right hPBound (norm_nonneg _)).trans hAt
    have hDiv := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2 / 25) K)).mpr hMul
    rw [div_eq_mul_inv, ← inv_pow, show ((2 / 25 : ℝ)⁻¹) = 25 / 2 by norm_num] at hDiv
    exact hDiv
  have hMax (w : ℂ) (hw : w ∈ W) : ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    apply norm_le_of_forall_mem_frontier_norm_le (U := W) isBounded_closedBall
    · apply DifferentiableOn.diffContOnCl
      simpa only [W, closure_closedBall] using (hg.mono hWU).differentiableOn
    · simpa only [W, frontier_closedBall'] using hOuter
    · simpa only [W, closure_closedBall] using hw
  have h0Not : (0 : ℂ) ∉ Function.support D := by
    rw [← hSupport]
    simp [hf0]
  have hP0 : ‖P 0‖ ≤ 1 := by
    simp only [P, norm_prod, norm_pow, zero_sub, norm_neg]
    refine Finset.prod_le_one₀ (fun _ _ => by positivity) fun ρ hρ => ?_
    have hρN : ‖ρ‖ ≤ 22 / 25 := by
      simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
    exact pow_le_one₀ (norm_nonneg _) (hρN.trans (by norm_num))
  have hG0 : 1 ≤ ‖g 0‖ := by
    have hFactor0 : f 0 = P 0 * g 0 := hFac ⟨h0U, h0Not⟩
    calc
      1 = ‖f 0‖ := by simp [hf0]
      _ = ‖P 0‖ * ‖g 0‖ := by rw [hFactor0, norm_mul]
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP0 (norm_nonneg _)
  have hLogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hLogRatio : 0 < Real.log (12 / 11 : ℝ) := Real.log_pos (by norm_num)
  have hLogPow : Real.log (25 / 2 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
    calc
      _ ≤ Real.log ((12 / 11 : ℝ) ^ (30 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hKLog : (K : ℝ) * Real.log (25 / 2 : ℝ) ≤ 30 * Real.log B := by
    calc
      _ ≤ (K : ℝ) * (30 * Real.log (12 / 11 : ℝ)) := mul_le_mul_of_nonneg_left hLogPow K.cast_nonneg
      _ = 30 * ((K : ℝ) * Real.log (12 / 11 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hLogRatio).mp hCount) (by norm_num)
  have hReg (w : ℂ) (hw : w ∈ ball (0 : ℂ) (22 / 25)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ 31 * Real.log B := by
    have hwV := ball_subset_closedBall hw
    have hL : Real.log ‖g w‖ ≤ Real.log (B * (25 / 2 : ℝ) ^ K) :=
      Real.log_le_log (norm_pos_iff.mpr (hgNZ w hwV)) (hMax w (hVW hwV))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hL
    linarith [Real.log_nonneg hG0]
  refine ⟨Z, hZeq, ?_, ?_⟩
  · simpa only [K, Nat.cast_sum] using hCount
  · intro z hz hfz
    have hzI : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
    have hzNot : z ∉ Function.support D := by
      rw [← hSupport]
      simp [hfz]
    have hLocal : f =ᶠ[𝓝 z] fun w => P w * g w := by
      filter_upwards [(isOpen_ball.sdiff hDfin.isClosed).mem_nhds ⟨hzI, hzNot⟩] with w hw
      exact hFac ⟨ball_subset_closedBall hw.1, hw.2⟩
    have hfacZ : f z = P z * g z := hLocal.eq_of_nhds
    have hPZ : P z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hGZ : g z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hdP : DifferentiableAt ℂ P z := DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
    have hFrac : logDeriv f z = logDeriv P z + logDeriv g z := by
      have hEq : logDeriv f z = logDeriv (fun w => P w * g w) z := by
        simp only [logDeriv_apply, hLocal.deriv_eq, hfacZ]
      rw [hEq]
      exact logDeriv_mul z hPZ hGZ hdP (hg z (ball_subset_closedBall hzI)).differentiableAt
    have hNonzero (ρ : ℂ) (hρ : ρ ∈ Z) : z ≠ ρ := by
      intro h
      have hρD : ρ ∈ Function.support D := hDfin.mem_toFinset.mp hρ
      exact hzNot (h ▸ hρD)
    rw [hFrac, show logDeriv P z = _ from logDeriv_finset_zeroFactors hNonzero, add_sub_cancel_left]
    calc
      _ ≤ 4200 * (31 * Real.log B) := norm_logDeriv_of_zeroFree_ball (by positivity)
        (hg.mono (ball_subset_closedBall.trans hVU))
        (fun w hw => hgNZ w (ball_subset_closedBall hw)) hReg hz
      _ = _ := by ring

/-- Landau's approximation on an arbitrary closed disk, obtained by affine scaling of the
normalized unit-disk statement. -/
theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf0 : f c ≠ 0) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ closedBall c (24 / 25 * R), ‖f w‖ ≤ B * ‖f c‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall c (22 / 25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ s ∈ closedBall c (83 / 100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          130200 / R * Real.log B := by
  let A : ℂ → ℂ := fun w => c + (R : ℂ) * w
  let G : ℂ → ℂ := fun w => (f c)⁻¹ * f (A w)
  have hRC : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hAanalytic (w : ℂ) : AnalyticAt ℂ A w :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hADeriv (w : ℂ) : deriv A w = (R : ℂ) := by
    simp [A]
  have hAinj : Function.Injective A := by
    intro z w hEq
    change c + (R : ℂ) * z = c + (R : ℂ) * w at hEq
    exact mul_left_cancel₀ hRC (add_left_cancel hEq)
  have hANorm (w : ℂ) : ‖A w - c‖ = R * ‖w‖ := by
    simp only [A, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hR.le]
  have hAInv (s : ℂ) : A ((s - c) / (R : ℂ)) = s := by
    simp only [A]
    field_simp [hRC]
    ring
  have hAMem {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) : A w ∈ closedBall c (r * R) := by
    rw [mem_closedBall_iff_norm, hANorm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw hR.le
  have hInvNorm {s : ℂ} {r : ℝ} (hs : s ∈ closedBall c (r * R)) :
      ‖(s - c) / (R : ℂ)‖ ≤ r := by
    rw [mem_closedBall_iff_norm] at hs
    rw [norm_div, Complex.norm_of_nonneg hR.le]
    exact (div_le_iff₀ hR).mpr hs
  have hAMemOne {w : ℂ} (hw : ‖w‖ ≤ 1) : A w ∈ closedBall c R := by
    simpa only [one_mul] using hAMem hw
  have hGanalytic : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 1 := by simpa only [mem_closedBall_iff_norm, sub_zero] using hw
    exact analyticAt_const.mul ((hf (A w) (hAMemOne hwNorm)).comp (hAanalytic w))
  have hG0 : G 0 = 1 := by simp [G, A, hf0]
  have hGBound (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) : ‖G w‖ ≤ B := by
    have hwNorm : ‖w‖ ≤ 24 / 25 := (mem_sphere_zero_iff_norm.mp hw).le
    have hNormPos := norm_pos_iff.mpr hf0
    calc
      _ = ‖f c‖⁻¹ * ‖f (A w)‖ := by simp only [G, norm_mul, norm_inv]
      _ ≤ ‖f c‖⁻¹ * (B * ‖f c‖) := mul_le_mul_of_nonneg_left (hfB (A w) (hAMem hwNorm))
        (inv_nonneg.mpr hNormPos.le)
      _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hNormPos.ne', one_mul]
  have hOrd (w : ℂ) (hw : ‖w‖ ≤ 1) :
      analyticOrderNatAt G w = analyticOrderNatAt f (A w) := by
    have hComp : AnalyticAt ℂ (f ∘ A) w := (hf (A w) (hAMemOne hw)).comp (hAanalytic w)
    calc
      _ = analyticOrderNatAt (f ∘ A) w := analyticOrderNatAt_fun_const_mul hComp (inv_ne_zero hf0)
      _ = _ := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_comp_of_deriv_ne_zero (hAanalytic w) (by rw [hADeriv]; exact hRC)]
  obtain ⟨Z₀, hZ₀, hCount, hBound⟩ := logDeriv_partial_fraction_unit hGanalytic hG0 hB hGBound
  have hZero (w : ℂ) : w ∈ Z₀ ↔ ‖w‖ ≤ 22 / 25 ∧ f (A w) = 0 := by
    change w ∈ (↑Z₀ : Set ℂ) ↔ _
    rw [hZ₀]
    simp [G, hf0]
  have hZeroNorm (w : ℂ) (hw : w ∈ Z₀) : ‖w‖ ≤ 1 :=
    ((hZero w).mp hw).1.trans (by norm_num)
  let embedding : ℂ ↪ ℂ := ⟨A, hAinj⟩
  let Z := Z₀.map embedding
  refine ⟨Z, ?_, ?_, ?_⟩
  · ext ρ
    change ρ ∈ Z ↔ ρ ∈ closedBall c (22 / 25 * R) ∧ f ρ = 0
    simp only [Z, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwNorm, hwZero⟩ := (hZero w).mp hw
      exact ⟨hAMem hwNorm, hwZero⟩
    · rintro ⟨hρ, hρZero⟩
      refine ⟨(ρ - c) / (R : ℂ), (hZero _).mpr ⟨hInvNorm hρ, ?_⟩, hAInv ρ⟩
      rwa [hAInv]
  · simp only [Z, Finset.sum_map]
    have hSum : (∑ w ∈ Z₀, (analyticOrderNatAt f (A w) : ℝ)) =
        ∑ w ∈ Z₀, (analyticOrderNatAt G w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by rw [hOrd w (hZeroNorm w hw)]
    exact hSum.le.trans hCount
  · intro s hs hfs
    let w := (s - c) / (R : ℂ)
    have hAw : A w = s := hAInv s
    have hw : ‖w‖ ≤ 83 / 100 := hInvNorm hs
    have hw₁ : ‖w‖ ≤ 1 := hw.trans (by norm_num)
    have hGw : G w ≠ 0 := by simp [G, hAw, hf0, hfs]
    have hG := hBound w hw hGw
    have hLD : logDeriv G w = (R : ℂ) * logDeriv f s := by
      calc
        _ = logDeriv (f ∘ A) w := logDeriv_const_mul w _ (inv_ne_zero hf0)
        _ = _ := by
          rw [logDeriv_comp (hf (A w) (hAMemOne hw₁)).differentiableAt
            (hAanalytic w).differentiableAt, hADeriv, hAw, mul_comm]
    have hLDF : logDeriv f s = (R : ℂ)⁻¹ * logDeriv G w := by
      rw [hLD, ← mul_assoc, inv_mul_cancel₀ hRC, one_mul]
    have hTerms : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) =
        (R : ℂ)⁻¹ * ∑ u ∈ Z₀, (analyticOrderNatAt G u : ℂ) / (w - u) := by
      simp only [Z, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      change (analyticOrderNatAt f (A u) : ℂ) / (s - A u) = _
      rw [← hOrd u (hZeroNorm u hu)]
      have hShift : s - A u = (R : ℂ) * (w - u) := by
        rw [← hAw]
        simp only [A]
        ring
      calc
        _ = ((analyticOrderNatAt G u : ℂ) / (w - u)) / (R : ℂ) := by
          rw [hShift, div_div, mul_comm]
        _ = _ := div_eq_inv_mul _ _
    rw [hLDF, hTerms, ← mul_sub, norm_mul, norm_inv, Complex.norm_of_nonneg hR.le]
    calc
      _ ≤ R⁻¹ * (130200 * Real.log B) := mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr hR.le)
      _ = _ := by ring

end GoldbachGrhLogDerivative
end

end

section

open Complex Metric Set

namespace Goldbach.Siegel

/-- The logarithmic derivative of the L-function of a nonprincipal character is
a sum over nearby zeros on the real interval (1, 2], with an error uniform in q. -/
theorem dirichlet_disk_expansion {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ Z : Finset ℂ,
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      (∀ β : ℝ, 1 / 2 ≤ β → β < 1 → χ.LFunction (β : ℂ) = 0 →
        (β : ℂ) ∈ Z ∧ 0 < analyticOrderNatAt χ.LFunction (β : ℂ)) ∧
      ∀ s : ℝ, 1 < s → s ≤ 2 →
        ‖logDeriv χ.LFunction (s : ℂ) -
          ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / ((s : ℂ) - ρ)‖ ≤
            (130200 * 2501 : ℝ) * Real.log q := by
  let R : ℝ := 15 / 8
  let B : ℝ := 2500 * q
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hR : 0 < R := by norm_num [R]
  have hB : 2 ≤ B := by dsimp [B]; linarith
  have hA : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    fun z _ => (χ.differentiable_LFunction hχ).analyticAt z
  have hAnchor : (1 / 4 : ℝ) ≤ ‖χ.LFunction 2‖ :=
    Goldbach.one_fourth_le_norm_LFunction_anchor χ 0
  have hne : χ.LFunction 2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hAnchor)
  have hfB (w : ℂ) (hw : w ∈ closedBall (2 : ℂ) (24 / 25 * R)) :
      ‖χ.LFunction w‖ ≤ B * ‖χ.LFunction 2‖ := by
    have hw' := mem_closedBall_iff_norm.mp hw
    have hRe := neg_le_abs (w.re - 2)
    have hdiff := Complex.abs_re_le_norm (w - 2)
    change |w.re - 2| ≤ ‖w - 2‖ at hdiff
    dsimp [R] at hw'
    have hreal : (1 / 8 : ℝ) ≤ w.re := by linarith
    have hnorm : 1 + ‖w‖ ≤ 5 := by
      have h := norm_le_norm_sub_add w (2 : ℂ)
      norm_num at h
      linarith
    have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hreal
    rw [if_neg hχ] at hg
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hg
      _ ≤ 25 * (q : ℝ) * 5 ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hnorm 2) (by positivity)
      _ = B * (1 / 4) := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAnchor (by linarith)
  obtain ⟨Z, hZ, _, hPF⟩ := GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk
    (f := χ.LFunction) (c := 2) hR (hA.mono (subset_univ _)) hne hB hfB
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro ρ hρ
    have hz : ρ ∈ {z ∈ closedBall (2 : ℂ) (22 / 25 * R) | χ.LFunction z = 0} := hZ ▸ hρ
    by_contra! h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) h hz.2
  · intro β hlo hhi hzero
    have hb : (β : ℂ) ∈ closedBall (2 : ℂ) (22 / 25 * R) := by
      rw [mem_closedBall_iff_norm, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : β - 2 ≤ 0)]
      dsimp [R]; linarith
    refine ⟨(show (β : ℂ) ∈ (Z : Set ℂ) from hZ.symm ▸ ⟨hb, hzero⟩), ?_⟩
    have hfin := (χ.differentiable_LFunction hχ).analyticAt (β : ℂ)
    have hntop : analyticOrderAt χ.LFunction (β : ℂ) ≠ ⊤ :=
      hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (Set.mem_univ (2 : ℂ)) (Set.mem_univ _) (by simp [(hA 2 trivial).analyticOrderAt_eq_zero.mpr hne])
    apply Nat.pos_of_ne_zero
    intro horder
    apply hfin.analyticOrderAt_ne_zero.mpr hzero
    rw [← Nat.cast_analyticOrderNatAt hntop, horder, Nat.cast_zero]
  · intro s hs hs₂
    have hsball : (s : ℂ) ∈ closedBall (2 : ℂ) (83 / 100 * R) := by
      rw [mem_closedBall_iff_norm, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : s - 2 ≤ 0)]
      dsimp [R]; linarith
    have hlogq : 1 ≤ Real.log (q : ℝ) :=
      ((Real.lt_log_iff_exp_lt hqpos).2 (Real.exp_one_lt_three.trans_le hq')).le
    have hl : Real.log B ≤ 2501 * Real.log q := by
      rw [show B = 2500 * (q : ℝ) from rfl, Real.log_mul (by norm_num) hqpos.ne']
      linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2500 : ℝ))]
    apply (hPF _ hsball (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hs.le)).trans
    calc
      _ ≤ (130200 / R) * (2501 * Real.log q) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ _ := by dsimp [R]; linarith

end Goldbach.Siegel

end

section

namespace Goldbach.SiegelDiskPole

open scoped BigOperators

/-- Every zero to the left of the vertical line contributes a nonnegative real part. -/
theorem poleTerm_re_nonneg (f : ℂ → ℂ) {σ : ℝ} {ρ : ℂ} (hρ : ρ.re ≤ σ) :
    0 ≤ ((analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) - ρ)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_im,
    zero_mul, zero_div, add_zero]
  have hgap : 0 ≤ σ - ρ.re := sub_nonneg.mpr hρ
  have hnorm := Complex.normSq_nonneg ((σ : ℂ) - ρ)
  positivity

/-- A real zero in the disk contributes at least one simple pole. The fallback
for a real zero below `1/2` loses at most two. -/
theorem logDeriv_re_lower (f : ℂ → ℂ) (Z : Finset ℂ) {σ β E : ℝ}
    (hσ : 1 < σ) (hβ : β < 1)
    (hleft : ∀ ρ ∈ Z, ρ.re ≤ 1)
    (hselected : 1 / 2 ≤ β → (β : ℂ) ∈ Z ∧ 0 < analyticOrderNatAt f (β : ℂ))
    (herr : ‖logDeriv f (σ : ℂ) -
      ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) - ρ)‖ ≤ E) :
    (σ - β)⁻¹ - (E + 2) ≤ (logDeriv f (σ : ℂ)).re := by
  classical
  let t (ρ : ℂ) := (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) - ρ)
  have ht (ρ) (hρ : ρ ∈ Z) : 0 ≤ (t ρ).re :=
    poleTerm_re_nonneg f ((hleft ρ hρ).trans hσ.le)
  have habs := (Complex.abs_re_le_norm (logDeriv f (σ : ℂ) - ∑ ρ ∈ Z, t ρ)).trans herr
  rw [Complex.sub_re, Complex.re_sum] at habs
  have hsmall := (abs_le.mp habs).1
  by_cases hb : 1 / 2 ≤ β
  · obtain ⟨hmem, hord⟩ := hselected hb
    have hsum := Finset.single_le_sum ht hmem
    have hx : (t (β : ℂ)).re = (analyticOrderNatAt f (β : ℂ) : ℝ) / (σ - β) := by
      change ((analyticOrderNatAt f (β : ℂ) : ℂ) / ((σ : ℂ) - (β : ℂ))).re = _
      norm_cast
    rw [hx] at hsum
    have hden : 0 ≤ σ - β := by linarith
    have horder : (1 : ℝ) ≤ analyticOrderNatAt f (β : ℂ) := by
      exact_mod_cast (show 1 ≤ analyticOrderNatAt f (β : ℂ) from hord)
    have hle := div_le_div_of_nonneg_right horder hden
    rw [one_div] at hle
    linarith
  · have hsum := Finset.sum_nonneg ht
    have hden : 0 < σ - β := by linarith
    have hrec : (σ - β)⁻¹ ≤ 2 := by
      rw [← one_div, div_le_iff₀ hden]
      linarith
    linarith

end Goldbach.SiegelDiskPole

end

section

namespace OAI.SiegelZeros.WeightedTorusJets
open Filter Set
open scoped Topology

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hne
  · simp
  · intro hz
    have h := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hne, hz, mul_zero] at h
    exact h rfl

lemma logDeriv_riemannZeta₁ {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta₁ s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta₁_ne_zero_of_one_le_re hs.le
  rw [logDeriv_apply, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne, riemannZeta_eq_inv_sub_mul hne]
  field_simp
  ring

theorem exists_bound_zeta_logDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖-logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)‖ ≤ C := by
  have hc : ContinuousOn (fun s : ℝ ↦ logDeriv riemannZeta₁ (s : ℂ)) (Icc 1 2) := by
    intro s hs
    have ha := differentiable_riemannZeta₁.analyticAt (s : ℂ)
    exact ((ha.deriv.continuousAt.div ha.continuousAt
      (riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs.1))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs hs2
  have heq : -logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1) =
      -logDeriv riemannZeta₁ (s : ℂ) := by
    rw [logDeriv_riemannZeta₁ (by simpa using hs)]
    ring
  rw [heq, norm_neg]
  exact (hC s ⟨hs.le, hs2⟩).trans (le_max_left _ _)

theorem exists_upper_bound_zeta_logDeriv_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-logDeriv riemannZeta (s : ℂ)).re ≤ 1 / (s - 1) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_zeta_logDeriv
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have h := (Complex.re_le_norm _).trans (hbound s hs hs2)
  have heq : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [Complex.sub_re, heq] at h
  linarith

end OAI.SiegelZeros.WeightedTorusJets

namespace Goldbach.Siegel

/-- The real pole of the zeta function and the selected real zero of the
Dirichlet L-function enter the upper bound with opposite signs. -/
theorem combined_logDeriv_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      ∀ s β : ℝ, 1 < s → s ≤ 2 → 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
        (-logDeriv riemannZeta (s : ℂ) - logDeriv χ.LFunction (s : ℂ)).re ≤
          K * Real.log q + 1 / (s - 1) - 1 / (s - β) := by
  obtain ⟨C, hC, hζ⟩ := OAI.SiegelZeros.WeightedTorusJets.exists_upper_bound_zeta_logDeriv_re
  refine ⟨130200 * 2501 + C + 2, by linarith, ?_⟩
  intro q _ hq χ _ hχ _ s β hs hs2 _ hβ hzero
  obtain ⟨Z, hleft, hselected, hdir⟩ := dirichlet_disk_expansion hq χ hχ
  have hχbound := Goldbach.SiegelDiskPole.logDeriv_re_lower χ.LFunction Z hs hβ
    (fun ρ hρ => (hleft ρ hρ).le) (fun hb => hselected β hb hβ hzero) (hdir s hs hs2)
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogq : 1 ≤ Real.log (q : ℝ) :=
    ((Real.lt_log_iff_exp_lt hqpos).2 (Real.exp_one_lt_three.trans_le hq')).le
  have hcost := mul_le_mul_of_nonneg_left hlogq (show 0 ≤ C + 2 by linarith)
  rw [Complex.sub_re, one_div (s - β)]
  linarith [hζ s hs hs2]

end Goldbach.Siegel

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.BiquadraticBasis. -/
section
namespace OAI
namespace SiegelZeros
open scoped Pointwise
namespace WeightedTorusJets
section
theorem finrank_sup_quadratic {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) (hK : Module.finrank F K = 2)
    (hL : Module.finrank F L = 2) (hne : K ≠ L) :
    Module.finrank F ↥(K ⊔ L) = 4 := by
  have : FiniteDimensional F K := Module.finite_of_finrank_eq_succ hK
  have : FiniteDimensional F L := Module.finite_of_finrank_eq_succ hL
  have hle : Module.finrank F ↥(K ⊔ L) ≤ 4 := by
    simpa [hK, hL] using K.finrank_sup_le L
  have hdiv : 2 ∣ Module.finrank F ↥(K ⊔ L) := by
    simpa [hK] using IntermediateField.finrank_dvd_of_le_right
      (show K ≤ K ⊔ L from le_sup_left)
  have hlt : 2 < Module.finrank F ↥(K ⊔ L) := by
    by_contra hc
    have hKeq : K = K ⊔ L := IntermediateField.eq_of_le_of_finrank_le le_sup_left
      (by omega)
    have hLK : L ≤ K := hKeq.symm ▸ le_sup_right
    have hLK_eq : L = K := IntermediateField.eq_of_le_of_finrank_le hLK (by omega)
    exact hne hLK_eq.symm
  omega

theorem biquadratic_monomials_integral {E : Type*} [CommRing E] [Algebra ℤ E]
    (a b : E) (d e : ℤ) (ha : a ^ 2 = d) (hb : b ^ 2 = e) :
    IsIntegral ℤ (1 : E) ∧ IsIntegral ℤ a ∧ IsIntegral ℤ b ∧ IsIntegral ℤ (a * b) := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow (by decide : 0 < 2)
    (hb ▸ isIntegral_intCast e)
  exact ⟨isIntegral_one, hai, hbi, hai.mul hbi⟩

theorem span_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) :
    Submodule.span F ({1, a} : Set E) = (Algebra.adjoin F {a}).toSubmodule := by
  have heval : Polynomial.aeval a (Polynomial.X ^ 2 - Polynomial.C d) = 0 := by
    simpa using sub_eq_zero.mpr ha
  have h := Submodule.span_range_natDegree_eq_adjoin
    (Polynomial.monic_X_pow_sub_C d (by decide : 2 ≠ 0)) heval
  simpa [Finset.range_add_one, Set.pair_comm] using h

theorem span_biquadratic_monomials {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    Submodule.span F (Set.range ![1, a, b, a * b]) =
      (Algebra.adjoin F ({a, b} : Set E)).toSubmodule := by
  have hsets : ({1, a} : Set E) * ({1, b} : Set E) = Set.range ![1, a, b, a * b] := by
    ext x
    simp only [Set.mem_mul, Matrix.range_cons, Matrix.range_empty, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
    aesop
  rw [← hsets, ← Submodule.span_mul_span, span_pair_sqrt a d ha,
    span_pair_sqrt b e hb, ← Algebra.adjoin_union_coe_submodule]
  simp [Set.pair_comm]

noncomputable def biquadraticBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) : Module.Basis (Fin 4) F E :=
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hdim
  basisOfTopLeSpanOfCardEqFinrank ![1, a, b, a * b]
    (by rw [span_biquadratic_monomials a b d e ha hb, hgen]; rfl)
    (by simpa using hdim.symm)

@[simp]
theorem biquadraticBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) (i : Fin 4) :
    biquadraticBasis a b d e ha hb hgen hdim i = ![1, a, b, a * b] i := by
  simp [biquadraticBasis]

theorem finrank_adjoin_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) (hd : ¬ IsSquare d) :
    Module.finrank F (IntermediateField.adjoin F {a}) = 2 := by
  have hai : IsIntegral F a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_algebraMap)
  have : FiniteDimensional F (IntermediateField.adjoin F {a}) :=
    IntermediateField.adjoin.finiteDimensional hai
  have hpos := Module.finrank_pos (R := F) (M := IntermediateField.adjoin F {a})
  have hne : Module.finrank F (IntermediateField.adjoin F {a}) ≠ 1 := by
    intro hone
    have hamem := IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hone
    obtain ⟨r, hr⟩ := (IntermediateField.mem_bot).mp hamem
    apply hd
    refine ⟨r, ?_⟩
    apply (algebraMap F E).injective
    simpa [map_mul, hr, sq] using ha.symm
  have hle : Module.finrank F (IntermediateField.adjoin F {a}) ≤ 2 := by
    rw [← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hai.isAlgebraic]
    change Module.finrank F (Algebra.adjoin F {a}).toSubmodule ≤ 2
    rw [← span_pair_sqrt a d ha]
    have h := finrank_range_le_card (R := F) ![(1 : E), a]
    change Module.finrank F (Submodule.span F (Set.range ![(1 : E), a])) ≤ 2 at h
    rwa [Matrix.range_cons_cons_empty] at h
  omega

theorem adjoin_pair_generators {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    let K := IntermediateField.adjoin F ({a, b} : Set E)
    let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
    let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
    Algebra.adjoin F ({a', b'} : Set K) = ⊤ := by
  dsimp only
  let K := IntermediateField.adjoin F ({a, b} : Set E)
  let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
  let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
  have hai : IsIntegral F a' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : a' ^ 2 = algebraMap F K d := Subtype.ext ha
        rw [h]; exact isIntegral_algebraMap)
  have hbi : IsIntegral F b' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : b' ^ 2 = algebraMap F K e := Subtype.ext hb
        rw [h]; exact isIntegral_algebraMap)
  apply Algebra.adjoin_eq_top_of_intermediateField
    (by intro x hx; rcases hx with rfl | rfl
        · exact hai.isAlgebraic
        · exact hbi.isAlgebraic)
  apply IntermediateField.map_injective K.val
  simp only [IntermediateField.adjoin_map, Set.image_pair, IntermediateField.val_mk]
  ext x
  simp [IntermediateField.mem_map, K]

theorem finrank_adjoin_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.finrank F (IntermediateField.adjoin F ({a, b} : Set E)) = 4 := by
  rw [← Set.singleton_union, IntermediateField.adjoin_union]
  exact finrank_sup_quadratic _ _ (finrank_adjoin_sqrt a d ha hd)
    (finrank_adjoin_sqrt b e hb he) hne

noncomputable def sqrtPairBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.Basis (Fin 4) F (IntermediateField.adjoin F ({a, b} : Set E)) :=
  let a' := (⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  let b' := (⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  biquadraticBasis a' b' d e (Subtype.ext ha) (Subtype.ext hb)
    (adjoin_pair_generators a b d e ha hb)
    (finrank_adjoin_pair_sqrt a b d e ha hb hd he hne)

@[simp]
theorem coe_sqrtPairBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) (i : Fin 4) :
    (sqrtPairBasis a b d e ha hb hd he hne i : E) = ![1, a, b, a * b] i := by
  fin_cases i <;> simp [sqrtPairBasis]

open Module
variable {K : Type*} [Field K] [Algebra ℚ K]
noncomputable def biquadraticLinearMap (v : Basis (Fin 4) ℚ K) (a' b' : K) : K →ₗ[ℚ] K :=
  v.constr ℚ ![1, a', b', a' * b']

lemma biquadraticLinearMap_basis (v : Basis (Fin 4) ℚ K) (a' b' : K) (i : Fin 4) :
    biquadraticLinearMap v a' b' (v i) = ![1, a', b', a' * b'] i :=
  v.constr_basis ℚ _ i

lemma biquadraticLinearMap_mul (v : Basis (Fin 4) ℚ K) (a b a' b' : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (ha' : a' * a' = algebraMap ℚ K d) (hb' : b' * b' = algebraMap ℚ K e) :
    ∀ x y, biquadraticLinearMap v a' b' (x * y) =
      biquadraticLinearMap v a' b' x * biquadraticLinearMap v a' b' y := by
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hfc (c : ℚ) (x : K) : f ((algebraMap ℚ K c) * x) = (algebraMap ℚ K c) * f x := by
    simpa only [Algebra.smul_def] using f.map_smul c x
  have hfq (c : ℚ) : f (algebraMap ℚ K c) = algebraMap ℚ K c := by simpa [hf1] using hfc c 1
  have h1 : a * (a * b) = (algebraMap ℚ K d) * b := by rw [← mul_assoc, ha]
  have h2 : b * (a * b) = (algebraMap ℚ K e) * a := by rw [mul_left_comm, hb, mul_comm]
  have h3 : (a * b) * (a * b) = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha, hb, map_mul]
  have h1' : a' * (a' * b') = (algebraMap ℚ K d) * b' := by rw [← mul_assoc, ha']
  have h2' : b' * (a' * b') = (algebraMap ℚ K e) * a' := by rw [mul_left_comm, hb', mul_comm]
  have h3' : (a' * b') * (a' * b') = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha', hb', map_mul]
  apply (LinearMap.map_mul_iff f).mpr
  apply v.ext
  intro i
  apply v.ext
  intro j
  change f (v i * v j) = f (v i) * f (v j)
  rw [hv i, hv j]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals simp_all [mul_comm]

noncomputable def biquadraticSignEquiv (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) : K ≃ₐ[ℚ] K := by
  let a' := if s then -a else a
  let b' := if t then -b else b
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hcomp : f.comp f = LinearMap.id := by
    apply v.ext
    intro i
    change f (f (v i)) = v i
    rw [hv i]
    cases s <;> cases t <;> fin_cases i <;> simp_all [a', b']
  have hinv : Function.Involutive f := fun x => LinearMap.congr_fun hcomp x
  refine AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive f hinv) hf1 ?_
  apply biquadraticLinearMap_mul v a b a' b' d e hv ha hb
  · cases s <;> simpa [a'] using ha
  · cases t <;> simpa [b'] using hb

lemma biquadraticSignEquiv_basis (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) (i : Fin 4) :
    biquadraticSignEquiv v a b d e hv ha hb s t (v i) =
      ![1, if s then -a else a, if t then -b else b,
        (if s then -a else a) * (if t then -b else b)] i :=
  biquadraticLinearMap_basis v _ _ i

lemma biquadratic_algEquiv_ext (v : Basis (Fin 4) ℚ K) (a b : K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (f g : K ≃ₐ[ℚ] K)
    (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply AlgEquiv.toLinearMap_injective
  apply v.ext
  intro i
  change f (v i) = g (v i)
  rw [hv i]
  fin_cases i <;> simp_all

lemma quadratic_algEquiv_dichotomy (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (f : K ≃ₐ[ℚ] K) :
    f a = a ∨ f a = -a := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  simpa only [pow_two, ← map_mul, ha] using f.commutes d

lemma biquadratic_automorphism_eq_sign (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    ∃ s t : Bool, f = biquadraticSignEquiv v a b d e hv ha hb s t := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  rcases quadratic_algEquiv_dichotomy a d ha f with hfa | hfa <;>
    rcases quadratic_algEquiv_dichotomy b e hb f with hfb | hfb
  · refine ⟨false, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false false 1).symm
    · exact hfb.trans (hs false false 2).symm
  · refine ⟨false, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false true 1).symm
    · exact hfb.trans (hs false true 2).symm
  · refine ⟨true, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true false 1).symm
    · exact hfb.trans (hs true false 2).symm
  · refine ⟨true, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true true 1).symm
    · exact hfb.trans (hs true true 2).symm

lemma biquadraticSignEquiv_injective (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Function.Injective (fun st : Bool × Bool =>
      biquadraticSignEquiv v a b d e hv ha hb st.1 st.2) := by
  let : CharZero K := algebraRat.charZero K
  have ha0 : a ≠ 0 := by simpa [hv] using v.ne_zero 1
  have hb0 : b ≠ 0 := by simpa [hv] using v.ne_zero 2
  have hana : a ≠ -a := fun h => ha0 (CharZero.eq_neg_self_iff.mp h)
  have hbna : b ≠ -b := fun h => hb0 (CharZero.eq_neg_self_iff.mp h)
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  intro st st' h
  have hA := congrArg (fun f : K ≃ₐ[ℚ] K => f a) h
  have hB := congrArg (fun f : K ≃ₐ[ℚ] K => f b) h
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  simp only [hsA] at hA
  simp only [hsB] at hB
  clear hs hsA hsB h
  rcases st with ⟨s, t⟩
  rcases st' with ⟨s', t'⟩
  cases s <;> cases s' <;> cases t <;> cases t' <;> simp_all

lemma biquadratic_card_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Nat.card (K ≃ₐ[ℚ] K) = 4 := by
  let f := fun st : Bool × Bool => biquadraticSignEquiv v a b d e hv ha hb st.1 st.2
  have hf : Function.Bijective f := by
    refine ⟨biquadraticSignEquiv_injective v a b d e hv ha hb, ?_⟩
    intro g
    obtain ⟨s, t, h⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
    exact ⟨⟨s, t⟩, h.symm⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

lemma biquadratic_isGalois (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    IsGalois ℚ K := by
  let : FiniteDimensional ℚ K := Module.Finite.of_basis v
  apply IsGalois.of_card_aut_eq_finrank
  rw [biquadratic_card_automorphisms v a b d e hv ha hb, Module.finrank_eq_card_basis v]
  rfl

lemma biquadraticSignEquiv_mul (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t s' t' : Bool) :
    biquadraticSignEquiv v a b d e hv ha hb s t *
        biquadraticSignEquiv v a b d e hv ha hb s' t' =
      biquadraticSignEquiv v a b d e hv ha hb (s.xor s') (t.xor t') := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  apply biquadratic_algEquiv_ext v a b hv
  · cases s <;> cases s' <;> simp [AlgEquiv.mul_apply, hsA]
  · cases t <;> cases t' <;> simp [AlgEquiv.mul_apply, hsB]

lemma biquadratic_automorphisms_commute (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f g : K ≃ₐ[ℚ] K) : Commute f g := by
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  obtain ⟨s', t', rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
  change _ = _
  simp only [biquadraticSignEquiv_mul, Bool.xor_comm]

lemma biquadraticSignEquiv_identity (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    biquadraticSignEquiv v a b d e hv ha hb false false = 1 := by
  have hs (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb false false i
  simp_rw [hv] at hs
  apply biquadratic_algEquiv_ext v a b hv
  · exact hs 1
  · exact hs 2

lemma biquadratic_four_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    let σ := biquadraticSignEquiv v a b d e hv ha hb true false
    let τ := biquadraticSignEquiv v a b d e hv ha hb false true
    f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ := by
  dsimp
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  cases s <;> cases t <;>
    simp [biquadraticSignEquiv_mul, biquadraticSignEquiv_identity]

end
lemma sqrtPair_isGalois {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    IsGalois ℚ (IntermediateField.adjoin ℚ ({a, b} : Set L)) := by
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  exact biquadratic_isGalois v a' b' d e hv ha' hb'

lemma sqrtPair_four_automorphisms {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  let σ := biquadraticSignEquiv v a' b' d e hv ha' hb' true false
  let τ := biquadraticSignEquiv v a' b' d e hv ha' hb' false true
  have hs (s t : Bool) (i : Fin 4) :=
    biquadraticSignEquiv_basis v a' b' d e hv ha' hb' s t i
  simp_rw [hv] at hs
  refine ⟨σ, τ, hs true false 1, hs true false 2, hs false true 1,
    hs false true 2, biquadratic_card_automorphisms v a' b' d e hv ha' hb', ?_, ?_⟩
  · exact biquadratic_four_automorphisms v a' b' d e hv ha' hb'
  · exact biquadratic_automorphisms_commute v a' b' d e hv ha' hb'

end WeightedTorusJets
open scoped NumberField
namespace WeightedTorusJets
theorem ringOfIntegers_map_dvd_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (a b : 𝓞 K) :
    NumberField.RingOfIntegers.mapRingHom f.toRingHom a ∣
      NumberField.RingOfIntegers.mapRingHom f.toRingHom b ↔ a ∣ b := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hF : Function.Injective F := by
    intro x y h
    apply NumberField.RingOfIntegers.ext
    apply f.injective
    exact congrArg (fun z : 𝓞 L ↦ (z : L)) h
  refine ⟨fun h ↦ ?_, fun h ↦ map_dvd F h⟩
  change F a ∣ F b at h
  by_cases ha : a = 0
  · subst a
    rw [map_zero, zero_dvd_iff] at h
    have hb : b = 0 := hF (h.trans (map_zero F).symm)
    simp [hb]
  · have haK : (a : K) ≠ 0 := fun h ↦ ha (NumberField.RingOfIntegers.ext h)
    have haL : f (a : K) ≠ 0 := fun h ↦ haK (f.injective (h.trans (map_zero f).symm))
    obtain ⟨c, hc⟩ := h
    have hquot : f ((b : K) / (a : K)) = (c : L) := by
      rw [map_div₀, div_eq_iff haL]
      simpa [F, map_mul, mul_comm] using congrArg (fun z : 𝓞 L ↦ (z : L)) hc
    have hint : IsIntegral ℤ ((b : K) / (a : K)) := by
      apply (isIntegral_algHom_iff (f.restrictScalars ℤ) f.injective).mp
      change IsIntegral ℤ (f ((b : K) / (a : K)))
      rw [hquot]
      exact c.2
    refine ⟨⟨(b : K) / (a : K), hint⟩, ?_⟩
    apply NumberField.RingOfIntegers.ext
    change (b : K) = (a : K) * ((b : K) / (a : K))
    rw [mul_comm, div_mul_cancel₀ _ haK]

theorem frobenius_congruence_descends
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (σ : K ≃ₐ[ℚ] K) (τ : L ≃ₐ[ℚ] L)
    (hcomm : ∀ x : K, f (σ x) = τ (f x)) (p : ℕ)
    (hfrob : ∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - τ • y) (x : 𝓞 K) :
    (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hmap : F (σ • x) = τ • F x := by
    apply NumberField.RingOfIntegers.ext
    exact hcomm (x : K)
  apply (ringOfIntegers_map_dvd_iff f (p : 𝓞 K) (x ^ p - σ • x)).mp
  change F (p : 𝓞 K) ∣ F (x ^ p - σ • x)
  simpa only [map_natCast, map_sub, map_pow, hmap] using hfrob (F x)

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Determinants.SqrtPairFrobeniusDirections. -/
section
namespace OAI
namespace SiegelZeros
open scoped Pointwise
open scoped NumberField
namespace WeightedTorusJets
open scoped NumberField
lemma sqrtPair_frobenius_directions {L : Type*} [Field L] [NumberField L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
      ∀ (p : ℕ) (φ : L ≃ₐ[ℚ] L), φ a = -a →
        (∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - φ • y) →
          ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
            (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm⟩ :=
    sqrtPair_four_automorphisms a b d e ha hb hd he hne
  have ha0 : a ≠ 0 := by
    intro h
    have hmap : algebraMap ℚ L d = 0 := by simpa [h] using ha.symm
    have hd0 : d = 0 := (algebraMap ℚ L).injective (hmap.trans (map_zero _).symm)
    exact hd (hd0 ▸ IsSquare.zero)
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg (fun x : B => (x : L)) h)
  have ha'neg : a' ≠ -a' := fun h => ha'0 (CharZero.eq_neg_self_iff.mp h)
  refine ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro p φ hφ hfrob
  let : IsGalois ℚ B := sqrtPair_isGalois a b d e ha hb hd he hne
  let ψ := φ.restrictNormal B
  have hψa : ψ a' = -a' := by
    apply Subtype.ext
    simpa [ψ, a', AlgEquiv.restrictNormal_apply] using hφ
  have hψcomm (x : B) : B.val (ψ x) = φ (B.val x) :=
    AlgEquiv.restrictNormal_apply B φ x
  have hψfrob : ∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - ψ • x :=
    frobenius_congruence_descends B.val ψ φ hψcomm p hfrob
  rcases hall ψ with hψ | hψ | hψ | hψ
  · rw [hψ, AlgEquiv.one_apply] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inl (hψ ▸ hψfrob)
  · rw [hψ, hτa] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inr (hψ ▸ hψfrob)

section
theorem mem_map_of_forall_mem_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [hP : P.IsMaximal]
    (hunr : Algebra.IsUnramifiedIn S P) {x : S}
    (hx : ∀ (Q : Ideal S) (_ : Q.IsPrime), Q.LiesOver P → x ∈ Q) :
    x ∈ P.map (algebraMap R S) := by
  apply Ideal.mem_of_localization_maximal
  intro Q hQ
  by_cases hle : P.map (algebraMap R S) ≤ Q
  · have hover : Q.LiesOver P := ⟨hP.eq_of_le (Ideal.IsPrime.ne_top' (I := Q.under R))
      (Ideal.map_le_iff_le_comap.mp hle)⟩
    have : Algebra.IsUnramifiedAt R Q := hunr Q inferInstance hover
    let := Localization.AtPrime.algebraOfLiesOver P Q
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ((Algebra.isUnramifiedAt_iff_map_eq R P Q).mp inferInstance).2]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q) Q x).mpr (hx Q inferInstance hover)
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]
    simp

theorem arithFrobAt_eq_of_under_eq
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G]
    (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    [Finite (S ⧸ Q)] [Finite (S ⧸ Q')]
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q = arithFrobAt R G Q' :=
  isConj_iff_eq.mp (isConj_arithFrobAt R G Q Q' h)

theorem arithFrobAt_sub_pow_mem_map
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G] [Algebra.EssFiniteType R S]
    [Ring.HasFiniteQuotients S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] (hP : P ≠ ⊥)
    (hunr : Algebra.IsUnramifiedIn S P)
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] [Finite (S ⧸ Q)] (x : S) :
    arithFrobAt R G Q • x - x ^ Nat.card (R ⧸ P) ∈ P.map (algebraMap R S) := by
  apply mem_map_of_forall_mem_primesOver P hunr
  intro Q' hQ' hover
  have : Q'.LiesOver P := hover
  have : Finite (S ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q')
  have hbase : Q.under R = Q'.under R := (Q.over_def P).symm.trans (Q'.over_def P)
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase, Q'.over_def P]
  exact IsArithFrobAt.arithFrobAt R G Q' x

theorem prime_dvd_pow_sub_arithFrobAt
    {S G : Type*} [CommRing S] [CommGroup G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] [Finite G] [Algebra.IsInvariant ℤ S G]
    [Algebra.EssFiniteType ℤ S] [Ring.HasFiniteQuotients S] [CharZero S]
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn S (Ideal.span {(p : ℤ)}))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    [Finite (S ⧸ Q)] (x : S) :
    (p : S) ∣ x ^ p - arithFrobAt ℤ G Q • x := by
  have hP : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have h := arithFrobAt_sub_pow_mem_map (G := G)
    (Ideal.span {(p : ℤ)}) hP hunr Q x
  rw [Int.card_ideal_quot, Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.mem_span_singleton] at h
  simpa only [neg_sub] using dvd_neg.mpr h

theorem ringOfIntegers_isInvariant
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply (Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)).isInvariant x
  intro g
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 K) K (galRestrict ℤ ℚ K (𝓞 K) g x) = algebraMap (𝓞 K) K x
  rw [algebraMap_galRestrict_apply]
  exact congrArg (fun z : 𝓞 K ↦ (z : K)) (hx g)

theorem exists_integer_frobenius_congruence
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (hcomm : ∀ f g : K ≃ₐ[ℚ] K, Commute f g)
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let : CommGroup (K ≃ₐ[ℚ] K) := .mk hcomm
  have : Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := ringOfIntegers_isInvariant
  obtain ⟨Q, hQ, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hover
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have : Finite ((𝓞 K) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q)
  refine ⟨arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q, ?_, prime_dvd_pow_sub_arithFrobAt p hunr Q⟩
  intro Q' hQ' hover'
  have : Q'.LiesOver (Ideal.span {(p : ℤ)}) := hover'
  have : Finite ((𝓞 K) ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q')
  have hbase : Q.under ℤ = Q'.under ℤ := hover.over.symm.trans hover'.over
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase]
  exact IsArithFrobAt.arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q'

theorem cyclotomic_isUnramifiedIn
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro Q hQ hover
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K Q hpn

theorem exists_cyclotomic_frobenius_congruence
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  apply exists_integer_frobenius_congruence (p := p)
  · intro σ τ
    change σ * τ = τ * σ
    apply (IsCyclotomicExtension.Rat.galEquivZMod n K).injective
    simp only [map_mul, mul_comm]
  · exact cyclotomic_isUnramifiedIn n K p hpn

theorem not_isSquare_rat_two : ¬ IsSquare (2 : ℚ) := by
  norm_num

theorem real_character_inv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  apply MulChar.ext'
  intro a
  exact Complex.conj_eq_iff_im.mpr (hreal a)

theorem real_character_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [pow_two, real_character_inv χ hreal]
    _ = 1 := inv_mul_cancel χ

open NumberField
scoped instance canonicalCyclotomicLevelNeZero (q : ℕ) [NeZero q] : NeZero (8 * q) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩

open scoped OAI.SiegelZeros.WeightedTorusJets
scoped instance canonicalCyclotomicExtension (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := by
  let : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  convert CyclotomicField.isCyclotomicExtension n ℚ using 1
  exact Subsingleton.elim _ _

open scoped OAI.SiegelZeros.WeightedTorusJets
scoped instance canonicalCyclotomicNumberField (n : ℕ) [NeZero n] :
    NumberField (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.numberField {n} ℚ (CyclotomicField n ℚ)

open scoped OAI.SiegelZeros.WeightedTorusJets
scoped instance canonicalCyclotomicAbelian (n : ℕ) [NeZero n] :
    IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {n} ℚ (CyclotomicField n ℚ)

open scoped OAI.SiegelZeros.WeightedTorusJets
end
theorem quadratic_factorsThrough_of_odd_kernel {q d : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q) (hχ : χ.IsQuadratic)
    (hd : d ∣ q) (hodd : Odd (Nat.card (ZMod.unitsMap hd).ker)) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  have hupow : u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : (ZMod.unitsMap hd).ker)))
  have hvpow : χ u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hupow, Units.val_one, map_one]
  have hchar := congrArg (fun ψ : DirichletCharacter R q ↦ ψ u) (hχ.pow_odd hodd)
  rw [MulChar.pow_apply_coe] at hchar
  exact hchar.symm.trans hvpow

theorem card_unitsMap_kernel_mul_totient {q d : ℕ} [NeZero q] (hd : d ∣ q) :
    Nat.card (ZMod.unitsMap hd).ker * d.totient = q.totient := by
  have : NeZero d := ⟨fun h ↦ (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  let f := ZMod.unitsMap hd
  have hind : f.ker.index = Nat.card (ZMod d)ˣ := by
    rw [← MonoidHom.comap_bot, Subgroup.index_comap_of_surjective ⊥
      (ZMod.unitsMap_surjective hd), Subgroup.index_bot]
  have hcard := f.ker.card_mul_index
  have hcd : Nat.card (ZMod d)ˣ = d.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcq : Nat.card (ZMod q)ˣ = q.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rwa [hind, hcd, hcq] at hcard

theorem card_unitsMap_kernel_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hpm : p ∣ m) :
    Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m p)).ker = p := by
  have : NeZero (p * m) := ⟨Nat.mul_ne_zero hp.ne_zero hm⟩
  have hcard := card_unitsMap_kernel_mul_totient (Nat.dvd_mul_left m p)
  rw [Nat.totient_mul_of_dvd hpm] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)) hcard

theorem primitive_quadratic_no_odd_prime_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬ p ^ 2 ∣ q := by
  intro hpq
  obtain ⟨k, hk⟩ := hpq
  have hq : q = p * (p * k) := by rw [hk]; ring
  have hdiv : p * k ∣ q := ⟨p, by rw [hq, mul_comm]⟩
  have hm : p * k ≠ 0 := by
    intro h
    exact (NeZero.ne q) (by rw [hq, h, mul_zero])
  have hcard : Nat.card (ZMod.unitsMap hdiv).ker = p := by
    clear hk
    subst q
    exact card_unitsMap_kernel_prime_mul hp hm (Nat.dvd_mul_right p k)
  have hfactor := quadratic_factorsThrough_of_odd_kernel χ hχ hdiv (hcard.symm ▸ hodd)
  have hle : q ≤ p * k := by
    rw [← hprim]
    exact Nat.sInf_le hfactor
  have hlt : p * k < q := by
    rw [hq]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hp.one_lt
  exact (not_lt_of_ge hle) hlt

theorem unitsMap_sixteen_mul_kernel_square {m : ℕ} [NeZero (16 * m)]
    (u : (ZMod (16 * m))ˣ)
    (hu : ZMod.unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩) u = 1) :
    ∃ y : ZMod (16 * m), y ^ 2 = (u : ZMod (16 * m)) := by
  let hd : 8 * m ∣ 16 * m := ⟨2, by ring⟩
  have hval : ((8 * m : ℕ) : ℤ) ∣ (u.val.val - 1 : ℤ) := by
    rw [← Units.val_inj, Units.val_one, ZMod.unitsMap_def, Units.coe_map] at hu
    have hcast : ZMod.castHom hd (ZMod (8 * m)) u.val =
        ((u.val.val : ℤ) : ZMod (8 * m)) := by simp
    rwa [MonoidHom.coe_coe, hcast, ← Int.cast_one, eq_comm,
      ZMod.intCast_eq_intCast_iff_dvd_sub] at hu
  obtain ⟨k, hk⟩ := hval
  have huval : u.val = 1 + (8 * m : ZMod (16 * m)) * (k : ZMod (16 * m)) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (16 * m))) hk
    push_cast at hcast
    rw [ZMod.natCast_zmod_val] at hcast
    rw [sub_eq_iff_eq_add] at hcast
    simpa only [add_comm] using hcast
  refine ⟨1 + (4 * m : ZMod (16 * m)) * (k : ZMod (16 * m)), ?_⟩
  rw [huval]
  have hz : (16 * m : ZMod (16 * m)) = 0 := by
    exact_mod_cast (ZMod.natCast_self (16 * m))
  calc
    (1 + (4 * m : ZMod (16 * m)) * k) ^ 2 =
        1 + (8 * m : ZMod (16 * m)) * k + (16 * m : ZMod (16 * m)) * (m * k ^ 2) := by ring
    _ = _ := by rw [hz, zero_mul, add_zero]

theorem quadratic_factorsThrough_eight_mul {m : ℕ} [NeZero (16 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (16 * m)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough (8 * m) := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩)]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  obtain ⟨y, hy⟩ := unitsMap_sixteen_mul_kernel_square u hu
  have hyunit : IsUnit y := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hy.symm ▸ u.isUnit)
  rw [← hy, map_pow]
  have hs := congrArg (fun ψ : DirichletCharacter R (16 * m) ↦ ψ hyunit.unit) hχ.sq_eq_one
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hs
  simpa only [hyunit.unit_spec] using hs

theorem primitive_quadratic_not_sixteen_dvd {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : ¬ 16 ∣ q := by
  rintro ⟨m, rfl⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (16 * m)) (by simp [h])
  have hle : 16 * m ≤ 8 * m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_eight_mul χ hχ)
  omega

theorem quadratic_factorsThrough_odd_two_mul {m : ℕ} [NeZero (2 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (2 * m))
    (hχ : χ.IsQuadratic) (hm : Odd m) : χ.FactorsThrough m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  have hcard : Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m 2)).ker = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hmpos)
    rw [one_mul, card_unitsMap_kernel_mul_totient, Nat.totient_two_mul_of_odd hm]
  apply quadratic_factorsThrough_of_odd_kernel χ hχ (Nat.dvd_mul_left m 2)
  rw [hcard]
  decide

theorem primitive_quadratic_mod_four_ne_two {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : q % 4 ≠ 2 := by
  intro hqmod
  have hq : q = 2 * (2 * (q / 4) + 1) := by omega
  obtain ⟨m, hm, hq⟩ : ∃ m, Odd m ∧ q = 2 * m :=
    ⟨2 * (q / 4) + 1, ⟨q / 4, rfl⟩, hq⟩
  subst q
  have hle : 2 * m ≤ m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_odd_two_mul χ hχ hm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  omega

theorem square_divisor_of_primitive_quadratic {q c : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hc : c ^ 2 ∣ q) : c = 1 ∨ c = 2 := by
  have hc0 : c ≠ 0 := by
    intro h
    apply NeZero.ne q
    apply Nat.eq_zero_of_zero_dvd
    simpa [h] using hc
  obtain ⟨k, hk⟩ : ∃ k, c = 2 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hc0 (by
    intro p hp hpc
    by_contra hne
    exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp (hp.odd_of_ne_two hne)
      ((pow_dvd_pow_of_dvd hpc 2).trans hc))⟩
  have hk1 : k ≤ 1 := by
    by_contra! hk2
    have h16 : 16 ∣ c ^ 2 := by
      rw [hk, ← pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ k * 2)
    exact primitive_quadratic_not_sixteen_dvd χ hχ hprim (h16.trans hc)
  interval_cases k <;> simp_all

theorem primitive_quadratic_radicand_eq_or_four_mul {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D c d : ℤ} (hD : D.natAbs = q) (hDc : D = c ^ 2 * d) : D = d ∨ D = 4 * d := by
  have hdiv : c.natAbs ^ 2 ∣ q := by
    have h := Int.natAbs_dvd_natAbs.mpr (show c ^ 2 ∣ D from ⟨d, hDc⟩)
    simpa only [Int.natAbs_pow, hD] using h
  rcases square_divisor_of_primitive_quadratic χ hχ hprim hdiv with hc | hc
  · have hsq : c ^ 2 = 1 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      rcases h with rfl | rfl <;> norm_num
    left
    simpa only [hsq, one_mul] using hDc
  · have hsq : c ^ 2 = 4 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      exact h
    right
    simpa only [hsq] using hDc

theorem odd_divisor_primitive_quadratic_squarefree {q m : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hm : Odd m) (hmq : m ∣ q) :
    Squarefree m := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact hm.not_two_dvd_nat ((Nat.dvd_mul_right 2 2).trans hpp)
  · exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp hodd
      ((by simpa only [pow_two] using hpp : p ^ 2 ∣ m).trans hmq)

theorem primitive_quadratic_conductor_shape {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ u : ℕ, Odd u ∧ Squarefree u ∧ (q = u ∨ q = 4 * u ∨ q = 8 * u) := by
  have h16 : q % 16 ≠ 0 := fun h ↦
    primitive_quadratic_not_sixteen_dvd χ hχ hprim (Nat.dvd_of_mod_eq_zero h)
  have h4 := primitive_quadratic_mod_four_ne_two χ hχ hprim
  by_cases hodd : q % 2 = 1
  · have ho : Odd q := Nat.odd_iff.mpr hodd
    exact ⟨q, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho dvd_rfl,
      Or.inl rfl⟩
  · by_cases h8 : q % 8 = 0
    · have hq : q = 8 * (q / 8) := by omega
      have ho : Odd (q / 8) := Nat.odd_iff.mpr (by omega)
      have hd : q / 8 ∣ q := ⟨8, by omega⟩
      exact ⟨q / 8, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inr hq)⟩
    · have hq : q = 4 * (q / 4) := by omega
      have ho : Odd (q / 4) := Nat.odd_iff.mpr (by omega)
      have hd : q / 4 ∣ q := ⟨4, by omega⟩
      exact ⟨q / 4, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inl hq)⟩

end WeightedTorusJets
open scoped NumberField
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.IntegerCharacter. -/
section
namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets
section
open AddChar MulChar
theorem primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ =
        ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [sum_mulShift _ he]
      simp [sub_eq_zero]

theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * q := by
  rw [pow_two, ← primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), e.inv_mulShift]
  rfl

theorem primitive_gaussSum_ne_zero {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) : gaussSum χ e ≠ 0 := by
  intro h
  have hq := primitive_gaussSum_mul_inv hχ he
  rw [h, zero_mul] at hq
  exact (Nat.cast_ne_zero.mpr (NeZero.ne q)) hq.symm

theorem primitive_quadratic_gaussSum_integer_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    ∃ D : ℤ, D.natAbs = q ∧ gaussSum χ e ^ 2 = (D : R) := by
  have hnonzero : χ (-1) ≠ 0 := (isUnit_neg_one.map χ).ne_zero
  rcases hquad (-1) with h | h | h
  · exact (hnonzero h).elim
  · exact ⟨q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩
  · exact ⟨-q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩

end
theorem factorsThrough_ringHomComp_iff {q d : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.FactorsThrough (χ.ringHomComp f) d ↔ χ.FactorsThrough d := by
  by_cases hd : d ∣ q
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    change (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1) ↔
      (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1)
    simp only [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one,
      MulChar.ringHomComp_apply, ← f.map_one, hf.eq_iff]
  · exact iff_of_false (fun h ↦ hd h.dvd) (fun h ↦ hd h.dvd)

theorem conductor_ringHomComp {q : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact factorsThrough_ringHomComp_iff χ f hf

noncomputable def integerCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : DirichletCharacter ℤ q := by
  let v : ZMod q → ℤ := fun a ↦ ⌊(χ a).re⌋
  have hv (a : ZMod q) : (v a : ℂ) = χ a := by
    rcases hquad a with h | h | h <;> norm_num [v, h]
  exact
    { toFun := v
      map_one' := by
        apply Int.cast_injective (α := ℂ)
        rw [hv, map_one, Int.cast_one]
      map_mul' := fun a b ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [Int.cast_mul, hv, hv, hv, map_mul]
      map_nonunit' := fun a ha ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [hv, MulChar.map_nonunit χ ha, Int.cast_zero] }

@[simp]
theorem integerCharacter_cast {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (a : ZMod q) : (integerCharacter χ hquad a : ℂ) = χ a := by
  change (⌊(χ a).re⌋ : ℂ) = χ a
  rcases hquad a with h | h | h <;> norm_num [h]

theorem integerCharacter_ringHomComp {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) :
    (integerCharacter χ hquad).ringHomComp (Int.castRingHom ℂ) = χ := by
  ext a
  exact integerCharacter_cast χ hquad a

theorem integerCharacter_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    (integerCharacter χ hquad).IsPrimitive := by
  change DirichletCharacter.conductor (integerCharacter χ hquad) = q
  rw [← conductor_ringHomComp (integerCharacter χ hquad) (Int.castRingHom ℂ)
    (Int.cast_injective (α := ℂ)), integerCharacter_ringHomComp]
  exact hprim

theorem integerCharacter_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : (integerCharacter χ hquad).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply MulChar.injective_ringHomComp (f := Int.castRingHom ℂ) (Int.cast_injective (α := ℂ))
  dsimp only
  rw [← MulChar.ringHomComp_pow, integerCharacter_ringHomComp,
    MulChar.ringHomComp_one, hquad.sq_eq_one]

open NumberField IsCyclotomicExtension.Rat
theorem cyclotomic_gaussSum_action {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (χ : DirichletCharacter K n) (hχ : χ.IsQuadratic)
    (e : AddChar (ZMod n) K) (σ : Gal(K/ℚ)) :
    σ (gaussSum χ e) = χ (galEquivZMod n K σ) * gaussSum χ e := by
  have hroot (x : ZMod n) : e x ^ n = 1 := by
    rw [← e.map_nsmul_eq_pow, nsmul_eq_mul]
    simp
  have he (x : ZMod n) : σ (e x) = e ((galEquivZMod n K σ) * x) := by
    rw [galEquivZMod_apply_of_pow_eq n K σ (hroot x), ← e.map_nsmul_eq_pow,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    σ (gaussSum χ e) = gaussSum χ (e.mulShift (galEquivZMod n K σ)) := by
      simp only [gaussSum, map_sum, map_mul, AddChar.mulShift_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [he]
      congr 1
      rcases hχ x with h | h | h <;> simp [h]
    _ = χ (galEquivZMod n K σ) * gaussSum χ e := by
      rw [gaussSum_mulShift_eq, hχ.inv]

section
open NumberField IsCyclotomicExtension.Rat
variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
noncomputable def characterField (χ : DirichletCharacter R n) : IntermediateField ℚ K :=
  (intermediateFieldEquivSubgroupChar n K R).symm (Subgroup.zpowers χ)

theorem characterField_finrank (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic)
    (hne : χ ≠ 1) : Module.finrank ℚ (characterField n K R χ) = 2 := by
  rw [← card_intermediateFieldEquivSubgroupChar n K R, characterField,
    OrderIso.apply_symm_apply, Nat.card_zpowers]
  exact orderOf_eq_prime hχ.sq_eq_one hne

theorem mem_characterField_fixingSubgroup (χ : DirichletCharacter R n)
    (hχ : χ.IsQuadratic) (σ : Gal(K/ℚ)) :
    σ ∈ (characterField n K R χ).fixingSubgroup ↔ χ (galEquivZMod n K σ) = 1 := by
  change σ ∈ (IntermediateField.fixedField
    ((subgroupGalEquivSubgroupChar n K R).symm
      (OrderDual.toDual (Subgroup.zpowers χ)))).fixingSubgroup ↔ _
  rw [IntermediateField.fixingSubgroup_fixedField, mem_subgroupGalEquivSubgroupChar_symm_iff]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simp only [zpow_natCast, MulChar.pow_apply_coe, h, one_pow]
    · simp only [zpow_neg, zpow_natCast, ← inv_pow, hχ.inv, MulChar.pow_apply_coe, h, one_pow]

theorem characterField_changeLevel [IsDomain R] {m : ℕ} [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [IsAbelianGalois ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)]
    (hdiv : n ∣ m) (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic) :
    characterField m L R (DirichletCharacter.changeLevel hdiv χ) =
      (characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L) := by
  have hχ' : (DirichletCharacter.changeLevel hdiv χ).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hχ.sq_eq_one, map_one]
  apply (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := L)).injective
  change (characterField m L R (DirichletCharacter.changeLevel hdiv χ)).fixingSubgroup =
    ((characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup
  ext σ
  have hm : σ ∈ ((characterField n K R χ).map
      (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup ↔
      σ.restrictNormal K ∈ (characterField n K R χ).fixingSubgroup := by
    simp only [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      apply (algebraMap K L).injective
      rw [AlgEquiv.restrictNormal_commutes]
      exact h _ ⟨x, hx, rfl⟩
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := hy
      change σ (algebraMap K L x) = algebraMap K L x
      rw [← AlgEquiv.restrictNormal_commutes, h x hx]
  rw [hm, mem_characterField_fixingSubgroup n K R χ hχ,
    mem_characterField_fixingSubgroup m L R _ hχ']
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ]
  simp [DirichletCharacter.changeLevel_def]

end
section
open NumberField IsCyclotomicExtension.Rat
theorem mem_adjoin_fixingSubgroup_iff {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : K) (σ : Gal(K/F)) :
    σ ∈ (IntermediateField.adjoin F {g}).fixingSubgroup ↔ σ g = g := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
    IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff,
    Subgroup.forall_mem_zpowers]
  simpa only [MulAction.mem_fixedBy, AlgEquiv.smul_def] using
    (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ) (a := g))

theorem gaussSum_adjoin_eq_characterField {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℤ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod n) K) (he : e.IsPrimitive) :
    IntermediateField.adjoin ℚ {gaussSum (χ.ringHomComp (Int.castRingHom K)) e} =
      characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) := by
  have hprimK : DirichletCharacter.IsPrimitive (χ.ringHomComp (Int.castRingHom K)) := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  have hg := primitive_gaussSum_ne_zero hprimK he
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  change (IntermediateField.adjoin ℚ {_}).fixingSubgroup =
    (characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ))).fixingSubgroup
  ext σ
  rw [mem_adjoin_fixingSubgroup_iff, mem_characterField_fixingSubgroup _ _ _ _
    (hχ.comp (Int.castRingHom ℂ)), cyclotomic_gaussSum_action _
    (hχ.comp (Int.castRingHom K)), mul_eq_right₀ hg]
  change ((χ (galEquivZMod n K σ) : K) = 1) ↔
    ((χ (galEquivZMod n K σ) : ℂ) = 1)
  norm_cast

end
theorem exists_squarefree_generator {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {D : ℤ} (hD : D ≠ 0) {g : K} (hg : g ^ 2 = (D : K)) :
    ∃ (d c : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ D.natAbs ∧ c ≠ 0 ∧
      D = c ^ 2 * d ∧ a ^ 2 = (d : K) ∧ IsIntegral ℤ a ∧ g = (c : K) * a ∧
      IntermediateField.adjoin ℚ {a} = IntermediateField.adjoin ℚ {g} := by
  obtain ⟨c, d, hcd, hd⟩ := exists_sq_mul_squarefree D
  have hc : c ≠ 0 := by
    intro h
    apply hD
    rw [← hcd, h]
    simp
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have had : (g / (c : K)) ^ 2 = (d : K) := by
    rw [div_pow, hg, ← hcd]
    push_cast
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hcK)
  refine ⟨d, c, g / (c : K), hd, ?_, hc, hcd.symm, had, ?_, ?_, ?_⟩
  · apply Nat.le_of_dvd (Int.natAbs_pos.mpr hD)
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [← hcd, mul_comm]⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [had]
    exact isIntegral_algebraMap
  · exact (mul_div_cancel₀ g hcK).symm
  · simpa only [div_eq_mul_inv, map_inv₀, map_intCast] using
      IntermediateField.adjoin_simple_mul_algebraMap (F := ℚ) g ((c : ℚ)⁻¹)
        (inv_ne_zero (Int.cast_ne_zero.mpr hc))

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem not_isSquare_of_quadratic_adjoin {K : Type*} [Field K] [Algebra ℚ K]
    {d : ℤ} {a : K} (ha : a ^ 2 = (d : K))
    (hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2) :
    ¬ IsSquare (d : ℚ) := by
  rintro ⟨r, hr⟩
  have hs : a ^ 2 = (algebraMap ℚ K r) ^ 2 := by
    calc
      a ^ 2 = (d : K) := ha
      _ = algebraMap ℚ K (d : ℚ) := by simp
      _ = (algebraMap ℚ K r) ^ 2 := by rw [hr, map_mul, pow_two]
  have hmem : a ∈ (⊥ : IntermediateField ℚ K) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · rw [h]
      exact IntermediateField.algebraMap_mem _ _
    · rw [h]
      exact (⊥ : IntermediateField ℚ K).neg_mem (IntermediateField.algebraMap_mem _ _)
  rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem,
    IntermediateField.finrank_bot] at hdim
  norm_num at hdim

theorem exists_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ σ : Gal(K/ℚ), σ a = (integerCharacter χ hχ (galEquivZMod n K σ) : K) * a := by
  let χI := integerCharacter χ hχ
  let χK := χI.ringHomComp (Int.castRingHom K)
  have hI := integerCharacter_isQuadratic χ hχ
  have hpI := integerCharacter_isPrimitive χ hχ hprim
  have hK : χK.IsQuadratic := hI.comp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χI (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hpI
  let e := AddChar.zmodChar n (zeta_spec n ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root n (zeta_spec n ℚ K)
  obtain ⟨D, hDabs, hgD⟩ := primitive_quadratic_gaussSum_integer_square hpK hK he
  have hD : D ≠ 0 := by
    intro h
    have := hDabs
    rw [h, Int.natAbs_zero] at this
    exact (NeZero.ne n) this.symm
  obtain ⟨d, c, a, hd, hbound, hc, hdc, ha, hint, hga, hadj⟩ :=
    exists_squarefree_generator hD hgD
  have hadjχ : IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ := by
    rw [hadj, gaussSum_adjoin_eq_characterField χI hI hpI e he]
    congr 1
    exact integerCharacter_ringHomComp χ hχ
  have hdiv : d.natAbs ∣ n := by
    rw [← hDabs]
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [hdc, mul_comm]⟩
  have hnsq : ¬ IsSquare (d : ℚ) := by
    apply not_isSquare_of_quadratic_adjoin ha
    rw [hadjχ]
    exact characterField_finrank n K ℂ χ hχ hne
  refine ⟨d, a, hd, hDabs ▸ hbound, hdiv, hnsq, ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

section
open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem galEquivZMod_arithFrob (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {p : ℕ} (hp : p.Prime) (hpn : p.Coprime n)
    (P : Ideal (𝓞 K)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    galEquivZMod n K σ = ZMod.unitOfCoprime p hpn := by
  have hn : (n : 𝓞 K) ∉ P := by
    intro hn
    have hn' : (n : ℤ) ∈ P.under ℤ := by simpa [Ideal.under, Ideal.mem_comap] using hn
    rw [hP, Ideal.mem_span_singleton] at hn'
    exact hp.not_dvd_one (hpn ▸ Nat.dvd_gcd (dvd_refl p) (Int.natCast_dvd_natCast.mp hn'))
  have hc : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hP, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  let ζ := (zeta_spec n ℚ K).toInteger
  have hζ : IsPrimitiveRoot ζ n := (zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have he : ζ ^ (galEquivZMod n K σ).val.val = ζ ^ p := by
    rw [← galEquivZMod_smul_of_pow_eq n K σ hζ.pow_eq_one]
    simpa only [hc, MulSemiringAction.toAlgHom_apply] using hσ.apply_of_pow_eq_one hζ.pow_eq_one hn
  have hmod := (hζ.isOfFinOrder (NeZero.ne n)).pow_inj_mod.mp he
  rw [← hζ.eq_orderOf] at hmod
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (galEquivZMod n K σ).val]
  exact (ZMod.natCast_eq_natCast_iff' _ _ n).mpr hmod

theorem arithFrob_map_character_eigenvector (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℤ n) (a : K)
    (ha : ∀ τ : Gal(K/ℚ), τ a = (χ (galEquivZMod n K τ) : K) * a)
    {p : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    (P : Ideal (𝓞 L)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    σ (algebraMap K L a) = (χ p : L) * algebraMap K L a := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  rw [← AlgEquiv.restrictNormal_commutes, ha, map_mul, map_intCast]
  congr 2
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ,
    galEquivZMod_arithFrob m L hp hpm P hP σ hσ]
  simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hdiv]

theorem exists_squarefree_generator_frobenius_sign (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ (p : ℕ), p.Prime → p.Coprime m →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 →
            σ (algebraMap K L a) = -algebraMap K L a := by
  obtain ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, hact⟩ :=
    exists_squarefree_characterField_generator (K := K) χ hχ hprim hne
  refine ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, ?_⟩
  intro p hp hpm P hP σ hσ hχp
  have hi : integerCharacter χ hχ (p : ZMod n) = -1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_neg, Int.cast_one] using
      (integerCharacter_cast χ hχ (p : ZMod n)).trans hχp
  have he := arithFrob_map_character_eigenvector n m K L hdiv
    (integerCharacter χ hχ) a hact hp hpm P hP σ hσ
  simpa only [hi, Int.cast_neg, Int.cast_one, neg_one_mul] using he

end
section
open NumberField IsCyclotomicExtension
noncomputable def cyclotomicDivisorField (n m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] :
    IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ {zeta m ℚ L ^ (m / n)}

theorem cyclotomicDivisorField_isCyclotomicExtension (n m : ℕ) [NeZero n] [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] (hdiv : n ∣ m) :
    IsCyclotomicExtension {n} ℚ (cyclotomicDivisorField n m L) := by
  have hζ : IsPrimitiveRoot (zeta m ℚ L ^ (m / n)) n :=
    IsPrimitiveRoot.pow (NeZero.pos m) (zeta_spec m ℚ L) (Nat.div_mul_cancel hdiv).symm
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ

end
theorem primitive_eighth_root_difference_sq {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 8) : (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h4 : ζ ^ 4 = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    simpa using hζ.pow_div_gcd 4 (by decide : Nat.gcd 8 4 ≠ 0)
  linear_combination (ζ ^ 2 - 2) * h4

end WeightedTorusJets
open scoped Pointwise
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.CharacterEstimates. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators Topology
open scoped BigOperators
namespace WeightedTorusJets
section
open ArithmeticFunction DirichletCharacter
theorem combined_vonMangoldt_LSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) s =
      -deriv riemannZeta s / riemannZeta s -
        deriv (LFunction χ) s / LFunction χ s := by
  have heq : (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) =
      (fun n : ℕ => (vonMangoldt n : ℂ)) +
        ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) := by
    funext n
    simp [mul_add, mul_comm]
  rw [heq, LSeries_add (LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_twist_vonMangoldt χ hs),
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_twist_vonMangoldt_eq χ hs,
    deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  simp [sub_eq_add_neg, neg_div]

theorem combined_vonMangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) s := by
  convert (LSeriesSummable_vonMangoldt hs).add
    (LSeriesSummable_twist_vonMangoldt χ hs) using 1
  funext n
  simp [mul_add, mul_comm]

theorem re_combined_vonMangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℝ) (n : ℕ) :
    (LSeries.term (fun m : ℕ => (vonMangoldt m : ℂ) * (1 + χ m)) s n).re =
      vonMangoldt n * (1 + (χ n).re) / (n : ℝ) ^ s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    change (((vonMangoldt n : ℂ) * (1 + χ n)) /
      (((n : ℝ) : ℂ) ^ (s : ℂ))).re = _
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp [Complex.div_ofReal_re]

theorem prime_sum_rpow_le_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p = 1) :
    2 * ∑ p ∈ P, Real.log p / (p : ℝ) ^ s ≤
      (-deriv riemannZeta (s : ℂ) / riemannZeta s -
        deriv (LFunction χ) (s : ℂ) / LFunction χ s).re := by
  have hsc : 1 < (s : ℂ).re := hs
  have hsum := combined_vonMangoldt_summable χ hsc
  have hnonneg (n : ℕ) :
      0 ≤ (LSeries.term (fun m : ℕ => (vonMangoldt m : ℂ) * (1 + χ m)) s n).re := by
    rw [re_combined_vonMangoldt_term]
    apply div_nonneg (mul_nonneg vonMangoldt_nonneg ?_) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hnorm := χ.norm_le_one (n : ZMod q)
    have hre := (abs_le.mp (Complex.abs_re_le_norm (χ n))).1
    linarith
  have hbound := (Complex.hasSum_re hsum.hasSum).summable.sum_le_tsum P
    (fun n _ => hnonneg n)
  rw [← Complex.re_tsum hsum] at hbound
  change _ ≤ (LSeries _ (s : ℂ)).re at hbound
  rw [combined_vonMangoldt_LSeries χ hsc] at hbound
  refine le_trans ?_ hbound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [re_combined_vonMangoldt_term, (hP p hp).2, Complex.one_re,
    vonMangoldt_apply_prime (hP p hp).1]
  ring_nf
  exact le_rfl

theorem log_rpow_compare {x X : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) (hX : 1 < X) :
    (2 / Real.exp 1) * (Real.log x / x) ≤
      2 * (Real.log x / x ^ (1 + 1 / Real.log X)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : x ^ (1 + 1 / Real.log X) ≤ x * Real.exp 1 := by
    rw [Real.rpow_add hx0, Real.rpow_one, one_div]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow hx0.le hxX (inv_nonneg.mpr hlogX.le)).trans
        Real.rpow_inv_log_le_exp_one) hx0.le
  calc
    (2 / Real.exp 1) * (Real.log x / x) = (2 * Real.log x) / (x * Real.exp 1) := by
      ring
    _ ≤ (2 * Real.log x) / x ^ (1 + 1 / Real.log X) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hlogx)
        (Real.rpow_pos_of_pos hx0 _) hpow
    _ = 2 * (Real.log x / x ^ (1 + 1 / Real.log X)) := by ring

theorem positive_prime_mass_le_logDeriv_floor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 1 < X) :
    (2 / Real.exp 1) *
        ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => χ p = 1),
          Real.log p / (p : ℝ) ≤
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
          riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) -
        deriv (LFunction χ) ((1 + 1 / Real.log X : ℝ) : ℂ) /
          LFunction χ ((1 + 1 / Real.log X : ℝ) : ℂ)).re := by
  classical
  have hs : 1 < 1 + 1 / Real.log X :=
    lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos hX))
  have hprime : ∀ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => χ p = 1),
      p.Prime ∧ χ p = 1 := by
    intro p hp
    obtain ⟨hp, hχp⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE hp, hχp⟩
  apply le_trans _ (prime_sum_rpow_le_logDeriv χ hs _ hprime)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp := (Finset.mem_filter.mp hp).1
  exact log_rpow_compare
    (Nat.one_le_cast.mpr (Nat.prime_of_mem_primesLE hp).one_le)
    ((Nat.le_floor_iff (by linarith)).mp (Nat.le_of_mem_primesLE hp)) hX

end
theorem reciprocal_gap_identity {s β : ℝ} (hs : 1 < s) (hβ : β < 1) :
    1 / (s - 1) - 1 / (s - β) = (1 - β) / ((s - 1) * (s - β)) := by
  have hs1 : s - 1 ≠ 0 := by linarith
  have hsβ : s - β ≠ 0 := by linarith
  field_simp
  ring

theorem reciprocal_gap_le {L β : ℝ} (hL : 0 < L) (hβ : β < 1) :
    1 / ((1 + 1 / L) - 1) - 1 / ((1 + 1 / L) - β) ≤ (1 - β) * L ^ 2 := by
  have hLi : 0 < 1 / L := one_div_pos.mpr hL
  have hs : 1 < 1 + 1 / L := by linarith
  rw [reciprocal_gap_identity hs hβ, add_sub_cancel_left]
  calc
    (1 - β) / ((1 / L) * (1 + 1 / L - β)) ≤
        (1 - β) / ((1 / L) * (1 / L)) := by
      apply div_le_div_of_nonneg_left (by linarith) (mul_pos hLi hLi)
      exact mul_le_mul_of_nonneg_left (by linarith) hLi.le
    _ = (1 - β) * L ^ 2 := by field_simp

theorem primebias_sampling_point {X : ℝ} (hX : 3 ≤ X) :
    1 < 1 + 1 / Real.log X ∧ 1 + 1 / Real.log X ≤ 2 := by
  have hlog : 1 < Real.log X := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    exact Real.exp_one_lt_three.trans_le hX
  constructor
  · have := one_div_pos.mpr (show 0 < Real.log X by linarith)
    linarith
  · have := (div_le_one (show 0 < Real.log X by linarith)).mpr hlog.le
    linarith

theorem positive_prime_mass_of_logDeriv_upper {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X β K : ℝ} (hX : 1 < X) (hβ : β < 1)
    (hupper :
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
          riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) -
        deriv (DirichletCharacter.LFunction χ) ((1 + 1 / Real.log X : ℝ) : ℂ) /
          DirichletCharacter.LFunction χ ((1 + 1 / Real.log X : ℝ) : ℂ)).re ≤
        K * Real.log q + 1 / ((1 + 1 / Real.log X) - 1) -
          1 / ((1 + 1 / Real.log X) - β)) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1,
      Real.log p / p) ≤
        (Real.exp 1 / 2) * K * Real.log q +
          (Real.exp 1 / 2) * ((1 - β) * (Real.log X) ^ 2) := by
  have hgap := reciprocal_gap_le (Real.log_pos hX) hβ
  have hbound := (positive_prime_mass_le_logDeriv_floor χ hX).trans hupper
  have hbound' : (2 / Real.exp 1) *
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        K * Real.log q + (1 - β) * (Real.log X) ^ 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbound'
    (show 0 ≤ Real.exp 1 / 2 by positivity)
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp [he] at hscaled
  nlinarith

end WeightedTorusJets
namespace RealCharacterAnalysis
open Complex Filter
open scoped Topology ComplexConjugate
theorem real_values_iff_quadratic {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ a : ZMod q, (χ a).im = 0) ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hc : star χ = χ := by
      ext a
      exact Complex.conj_eq_iff_im.mpr (h a)
    have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hc
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ * χ := sq χ
      _ = χ * χ⁻¹ := congrArg (χ * ·) hi.symm
      _ = 1 := mul_inv_cancel χ
  · intro h a
    rcases h a with h | h | h <;> simp [h]

theorem apply_prime_eq_zero_iff {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) : χ (p : ZMod q) = 0 ↔ p ∣ q := by
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_prime_iff_not_dvd hp, not_not]

end RealCharacterAnalysis
namespace WeightedTorusJets.Mertens
open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem prime_log_div_bounded_error :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  refine ⟨log 4 + 6 + E₁, by positivity [E₁.nonneg], fun x hx => ?_⟩
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ log 4 + 6 + E₁
  have hlog : 0 ≤ log 4 := by positivity
  exact abs_le.mpr
    ⟨by linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx],
     by linarith [E₁Λ.le hx, E₁p.le_E₁Λ x, E₁.nonneg]⟩

end WeightedTorusJets.Mertens
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.SumLogPrimeFactors. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators Topology
open scoped BigOperators
namespace WeightedTorusJets
theorem sum_log_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp : ∀ p ∈ q.primeFactors, 0 < (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (Finset.prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

theorem sum_log_div_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum fun p hp => ?_).trans (sum_log_primeFactors_le q)
  have hp1 : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_le
  exact div_le_self (Real.log_nonneg hp1) hp1

theorem sum_log_div_filter_dvd_le (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s with p ∣ q, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
    (sum_log_div_primeFactors_le q)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hpq⟩
    exact Nat.mem_primeFactors.mpr ⟨hprime p hps, hpq, hq⟩
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem sum_log_div_filter_le_cutoff (s : Finset ℕ) (H : ℕ) :
    ∑ p ∈ s with p ≤ H, Real.log p / p ≤
      ∑ p ∈ Finset.range (H + 1), Real.log p / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem prime_mass_partition_le {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1) :
    ∑ p ∈ s, Real.log p / p ≤
      (∑ p ∈ s with c p = 1, Real.log p / p) +
      (∑ p ∈ s with p ∣ q, Real.log p / p) +
      (∑ p ∈ s with p ≤ H, Real.log p / p) +
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hn : 0 ≤ Real.log p / p := by
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast (hprime p hp).one_lt.le
  by_cases hsmall : p ≤ H
  · simp only [hsmall, ite_true]
    split_ifs <;> linarith
  have hlarge : H < p := lt_of_not_ge hsmall
  rcases hclass p hp with hpos | hram | hneg
  · simp only [hpos, ite_true]
    split_ifs <;> linarith
  · simp only [hram, ite_true]
    split_ifs <;> linarith
  · by_cases hram : p ∣ q
    · simp only [hram, ite_true]
      split_ifs <;> linarith
    have htwo : ¬ p ∣ 2 := by
      intro hp2
      have := Nat.le_of_dvd (by decide : 0 < 2) hp2
      omega
    simp only [hsmall, hram, hneg, hlarge, (hprime p hp).not_dvd_mul htwo hram,
      ite_false, ite_true, and_self, not_false_eq_true]
    split_ifs <;> linarith

theorem good_mass_of_estimates {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1)
    {L ell E A B D CH : ℝ} (hell : 0 ≤ ell) (hE : 0 ≤ E)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htotal : L - D ≤ ∑ p ∈ s, Real.log p / p)
    (hpositive : (∑ p ∈ s with c p = 1, Real.log p / p) ≤ A * ell + B * E)
    (hramified : (∑ p ∈ s with p ∣ q, Real.log p / p) ≤ ell)
    (hsmall : (∑ p ∈ s with p ≤ H, Real.log p / p) ≤ CH) :
    L - (A + B + 1) * ell - (A + B + 1) * E - (D + CH) ≤
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  have hpartition := prime_mass_partition_le hH s c hprime hclass
  nlinarith [mul_nonneg hB hell, mul_nonneg hA hE]

section
theorem good_prime_mass_of_primebias {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      (∀ a : ZMod q, (χ a).im = 0) → ∀ X δ : ℝ, 3 ≤ X → 0 ≤ δ →
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        A * Real.log q + B * (δ * (Real.log X) ^ 2 / Real.log q) →
      Real.log X - C * Real.log q - C * (δ * (Real.log X) ^ 2 / Real.log q) - CH ≤
        ∑ p ∈ Nat.primesLE ⌊X⌋₊ with
          H < p ∧ ¬ p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p := by
  classical
  obtain ⟨D, _, hD⟩ := Mertens.prime_log_div_bounded_error
  refine ⟨A + B + 1, by linarith, fun H hH =>
    ⟨D + ∑ p ∈ Finset.range (H + 1), Real.log p / p, ?_⟩⟩
  intro q _ hq χ hreal X δ hX hδ hbias
  have hprime : ∀ p ∈ Nat.primesLE ⌊X⌋₊, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hquadratic := (RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal
  have hclass : ∀ p ∈ Nat.primesLE ⌊X⌋₊,
      χ ((p : ℕ) : ZMod q) = 1 ∨ p ∣ q ∨ χ ((p : ℕ) : ZMod q) = -1 := by
    intro p hp
    rcases hquadratic ((p : ℕ) : ZMod q) with hz | ho | hm
    · exact Or.inr (Or.inl ((RealCharacterAnalysis.apply_prime_eq_zero_iff χ
        (hprime p hp)).mp hz))
    · exact Or.inl ho
    · exact Or.inr (Or.inr hm)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hE : 0 ≤ δ * (Real.log X) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg hδ (sq_nonneg _)) hlogq
  have htotal : Real.log X - D ≤
      ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p := by
    have := (abs_le.mp (hD X (by linarith))).1
    linarith
  exact good_mass_of_estimates hH (Nat.primesLE ⌊X⌋₊) (fun p => χ ((p : ℕ) : ZMod q))
    hprime hclass hlogq hE hA hB htotal hbias
    (sum_log_div_filter_dvd_le q (by omega) _ hprime)
    (sum_log_div_filter_le_cutoff _ H)

theorem source_analytic_lemma :
    ∃ C : ℝ, 0 < C ∧
      (∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ X : ℝ, 3 ≤ X →
        (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
          C * Real.log q + C * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q)) ∧
      (∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ X : ℝ, 3 ≤ X →
        Real.log X - C * Real.log q -
          C * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q) - CH ≤
          ∑ p ∈ Nat.primesLE ⌊X⌋₊ with
            H < p ∧ ¬ p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p) := by
  classical
  obtain ⟨K, hK, hupper⟩ := Goldbach.Siegel.combined_logDeriv_upper
  let A := Real.exp 1 / 2 * K
  let B := Real.exp 1 / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let Cb := A + B + 1
  have hCb : 0 < Cb := by dsimp [Cb]; linarith
  have hbias : ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      ∀ X : ℝ, 3 ≤ X →
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        Cb * Real.log q + Cb * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q) := by
    intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hs := primebias_sampling_point hX
    have hu := hupper q hq χ hprim hχ hreal (1 + 1 / Real.log X) β hs.1 hs.2 hβ0 hβ1 hzero
    have hp := positive_prime_mass_of_logDeriv_upper χ (X := X) (β := β) (K := K) (by linarith) hβ1
      (by simpa only [logDeriv_apply, neg_div] using hu)
    have hell : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell.le
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell.le
    have heq : ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q =
        (1 - β) * (Real.log X) ^ 2 := by field_simp
    rw [← heq] at hp
    dsimp [A, B, Cb] at *
    nlinarith [mul_nonneg hB hell.le, mul_nonneg hA hE]
  obtain ⟨Cg, _, hgood⟩ := good_prime_mass_of_primebias hCb.le hCb.le
  refine ⟨max Cb Cg, hCb.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hp := hbias q hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hell) (sq_nonneg _)) hell
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left Cb Cg)) hell,
      mul_nonneg (sub_nonneg.mpr (le_max_left Cb Cg)) hE]
  · intro H hH
    obtain ⟨CH, hCH⟩ := hgood H hH
    refine ⟨CH, ?_⟩
    intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell
    have hg := hCH q hq χ hreal X ((1 - β) * Real.log q) hX hdelta
      (hbias q hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX)
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_right Cb Cg)) hell,
      mul_nonneg (sub_nonneg.mpr (le_max_right Cb Cg)) hE]

end
theorem exists_radius_LFunction_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, |β - 1| < ε →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  have hcont : ContinuousAt (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hnonzero : DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ) ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hnonzero)
  refine ⟨ε, hε, fun β hβ => hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_radius_LFunction_ne_zero_fixed_modulus (q : ℕ) [NeZero q] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, |β - 1| < ε → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  classical
  have h : ∀ᶠ β : ℝ in nhds 1, ∀ χ : DirichletCharacter ℂ q,
      χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro χ
    by_cases hχ : χ = 1
    · exact Filter.Eventually.of_forall fun _ hne => (hne hχ).elim
    · obtain ⟨ε, hε, hzero⟩ := exists_radius_LFunction_ne_zero χ hχ
      have hr : ∀ᶠ β : ℝ in nhds 1, |β - 1| < ε := by
        filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hε] with β hβ
        simpa [Metric.mem_ball, Real.dist_eq] using hβ
      exact hr.mono fun β hβ _ => hzero β hβ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε, hε, fun χ hχ β hβ => hball ?_ χ hχ⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_gap_fixed_modulus (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨ε, hε, hne⟩ := exists_radius_LFunction_ne_zero_fixed_modulus q
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  refine ⟨ε * Real.log (q : ℝ), mul_pos hε hlog, ?_⟩
  intro χ hχ β hβ
  apply mul_le_mul_of_nonneg_right _ hlog.le
  by_contra! hlt
  have habs : |β - 1| = 1 - β := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hβ.2.1)]
  exact hne χ hχ β (by simpa [habs] using hlt) hβ.2.2

theorem exists_gap_bounded_moduli (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  induction Q with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro q _ hq hQ
    omega
  | succ Q ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    by_cases hQ : 3 ≤ Q + 1
    · let : NeZero (Q + 1) := ⟨by omega⟩
      obtain ⟨d, hd, hlast⟩ := exists_gap_fixed_modulus (Q + 1) hQ
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro q _ hq hqQ χ hχ β hβ
      rcases Nat.lt_or_eq_of_le hqQ with hlt | rfl
      · exact (min_le_left _ _).trans (hbound q hq (by omega) χ hχ β hβ)
      · exact (min_le_right _ _).trans (hlast χ hχ β hβ)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro q _ hq hqQ
      omega

theorem exists_small_gap_large_modulus (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ)))
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ hq : NeZero q, 3 ≤ q ∧ Q < q ∧
      ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ ≠ 1 ∧ (∀ a : ZMod q, (χ a).im = 0) ∧
        ∃ β : ℝ, (0 < β ∧ β < 1 ∧ @DirichletCharacter.LFunction q hq χ (β : ℂ) = 0) ∧
          (1 - β) * Real.log (q : ℝ) < ε := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_gap_bounded_moduli Q
  have hfail : ¬ (∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            min c ε ≤ (1 - β) * Real.log (q : ℝ)) := fun h =>
    hnot ⟨min c ε, lt_min hc hε, h⟩
  push Not at hfail
  obtain ⟨q, hq0, hq, χ, hprim, hχ, hreal, β, hβ, hsmall⟩ := hfail
  let := hq0
  have hQ : Q < q := by
    by_contra! hle
    exact (not_lt_of_ge (hbound q hq hle χ hχ β hβ))
      (hsmall.trans_le (min_le_left _ _))
  exact ⟨q, hq0, hq, hQ, χ, hprim, hχ, hreal, β, hβ,
    hsmall.trans_le (min_le_right _ _)⟩

theorem exists_contrary_sequence (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ))) :
    ∃ q : ℕ → ℕ, ∃ hq : ∀ n, NeZero (q n),
      ∃ χ : ∀ n, DirichletCharacter ℂ (q n), ∃ β : ℕ → ℝ,
        (∀ n, 3 ≤ q n ∧ (χ n).IsPrimitive ∧ χ n ≠ 1 ∧ (∀ a : ZMod (q n), (χ n a).im = 0) ∧
          (0 < β n ∧ β n < 1 ∧ @DirichletCharacter.LFunction (q n) (hq n) (χ n) (β n : ℂ) = 0)) ∧
        Filter.Tendsto q Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => (1 - β n) * Real.log (q n : ℝ))
          Filter.atTop (nhds 0) := by
  classical
  have hex (n : ℕ) := exists_small_gap_large_modulus hnot n
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq hq3 hn χ hprim hχ hreal β hβ hsmall using hex
  refine ⟨q, hq, χ, β, fun n => ⟨hq3 n, hprim n, hχ n, hreal n, hβ n⟩,
    Filter.tendsto_atTop_mono (fun n => (hn n).le) Filter.tendsto_id, ?_⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hsmall n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact mul_nonneg (sub_nonneg.mpr (hβ n).2.1.le) (Real.log_natCast_nonneg (q n))

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.SumLogDivFilterDvdTwoMul. -/
section
namespace OAI
namespace SiegelZeros
section
open scoped BigOperators Topology
open scoped BigOperators
namespace WeightedTorusJets
theorem source_good_prime_mass_with_chebyshev_constant :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ∀ U : ℝ, 3 ≤ U →
            Real.log U - C * Real.log q -
              C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH ≤
              ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
                H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1,
                  Real.log p / p := by
  obtain ⟨C₀, hC₀, _hpositive, hgood⟩ := source_analytic_lemma
  refine ⟨max C₀ (Real.log 4), hC₀.trans_le (le_max_left _ _), le_max_right _ _, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hgood H hH
  refine ⟨CH, ?_⟩
  intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero U hU
  have hbase := hCH q hq χ hprim hχ hreal β hβ0 hβ1 hzero U hU
  have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
  have herror : 0 ≤ ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell
  have hlinear := mul_le_mul_of_nonneg_right (le_max_left C₀ (Real.log 4)) hell
  have hquadratic := mul_le_mul_of_nonneg_right (le_max_left C₀ (Real.log 4)) herror
  have hbound : Real.log U - max C₀ (Real.log 4) * Real.log q -
      max C₀ (Real.log 4) *
        (((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q) - CH ≤
      ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
        H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p := by
    linarith
  convert hbound using 1
  ring

end WeightedTorusJets
end
open scoped BigOperators
namespace WeightedTorusJets
theorem good_prime_filter_max_two (q H : ℕ) (c : ℕ → ℂ) (U : ℝ) :
    (Nat.primesLE ⌊U⌋₊).filter (fun p => max H 2 < p ∧ ¬p ∣ 2 * q ∧ c p = -1) =
      (Nat.primesLE ⌊U⌋₊).filter (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1) := by
  apply Finset.filter_congr
  intro p hp
  by_cases hq : p ∣ 2 * q
  · simp [hq]
  have hpgt : 2 < p := lt_of_le_of_ne (Nat.prime_of_mem_primesLE hp).two_le (by
    rintro rfl
    exact hq (dvd_mul_right 2 q))
  simp [max_lt_iff, hpgt]

theorem good_prime_mass_extend_small_parameters (q H : ℕ) (c : ℕ → ℂ)
    {C ell delta CH : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ ell) (hdelta : 0 ≤ delta)
    (hlarge : ∀ U : ℝ, 3 ≤ U →
      Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH ≤
        ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
          (fun p => max H 2 < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ))
    {U : ℝ} (hU : 0 ≤ U) :
    Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - max CH (Real.log 3) ≤
      ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ) := by
  by_cases hU3 : 3 ≤ U
  · have h := hlarge U hU3
    rw [good_prime_filter_max_two] at h
    exact le_trans (sub_le_sub_left (le_max_left _ _) _) h
  · have hlog : Real.log U ≤ Real.log 3 := by
      by_cases hU0 : U = 0
      · rw [hU0, Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (lt_of_le_of_ne hU (Ne.symm hU0)) (by linarith)
    have hsum : 0 ≤ ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ) :=
      by positivity
    have hlin : 0 ≤ C * ell := by positivity
    have herr : 0 ≤ C * delta * (Real.log U) ^ 2 / ell := by positivity
    have hCH := le_max_right CH (Real.log 3)
    linarith

theorem source_good_prime_mass_all_parameters :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ∀ U : ℝ, 0 ≤ U →
            Real.log U - C * Real.log q -
              C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH ≤
              ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
                H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1,
                  Real.log p / p := by
  obtain ⟨C, hC, hC4, hmass⟩ := source_good_prime_mass_with_chebyshev_constant
  refine ⟨C, hC, hC4, ?_⟩
  intro H
  obtain ⟨CH, hCH⟩ := hmass (max H 2) (le_max_right _ _)
  refine ⟨max CH (Real.log 3), ?_⟩
  intro q _ hq χ hprim hne hreal β hβ0 hβ1 hzero U hU
  have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
  exact good_prime_mass_extend_small_parameters q H (fun p => χ (p : ZMod q))
    hC.le hell hdelta (fun X hX => hCH q hq χ hprim hne hreal β hβ0 hβ1 hzero X hX) hU

open NumberField IsCyclotomicExtension.Rat
end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.QuadraticAdjoinBasis. -/
section
namespace OAI
namespace SiegelZeros
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets
open Module NumberField
theorem trace_norm_quadratic_basis {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.trace ℚ K ((r : K) + s * a) = 2 * r ∧
      Algebra.norm ℚ ((r : K) + s * a) = r ^ 2 - d * s ^ 2 := by
  have hu0 : u 0 = 1 := congrFun hu 0
  have hu1 : u 1 = a := congrFun hu 1
  have hr0 : u.repr 1 = Finsupp.single 0 1 := by rw [← hu0, u.repr_self]
  have hr1 : u.repr a = Finsupp.single 1 1 := by rw [← hu1, u.repr_self]
  have hrc (c : ℚ) : u.repr (c : K) = c • Finsupp.single 0 1 := by
    simpa [Algebra.smul_def, hr0] using u.repr.map_smul c (1 : K)
  have hm0 : ((r : K) + s * a) * 1 = r • (1 : K) + s • a := by
    simp [Algebra.smul_def]
  have hm1 : ((r : K) + s * a) * a = (d * s) • (1 : K) + r • a := by
    calc
      _ = (s : K) * a ^ 2 + r * a := by ring
      _ = _ := by rw [ha]; simp [Algebra.smul_def, mul_comm]
  have hmat : Algebra.leftMulMatrix u ((r : K) + s * a) = !![r, d*s; s,r] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    all_goals simp [-Rat.cast_mul, hu0, hu1, hm0, hm1, hrc, hr1]
  rw [Algebra.trace_eq_matrix_trace u, Algebra.norm_eq_matrix_det u, hmat]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
  constructor <;> ring

theorem rat_int_of_squarefree_mul_sq_eq_int (d n : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : (d : ℚ) * x ^ 2 = n) : ∃ m : ℤ, x = m := by
  have heq : d * x.num ^ 2 = n * (x.den : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← x.num_div_den] at hx
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp at hx
    nlinarith [hx]
  have hdiv : (x.den : ℤ) * (x.den : ℤ) ∣ d * x.num ^ 2 := by
    rw [heq, ← pow_two]
    exact dvd_mul_left _ _
  have hden := hd.dvd_of_squarefree_of_mul_dvd_mul_right hdiv
  have hden_nat : x.den ∣ x.num.natAbs ^ 2 := by
    simpa only [Int.natCast_dvd, Int.natAbs_pow] using hden
  have hone : x.den = 1 := Nat.eq_one_of_dvd_coprimes (x.reduced.pow_left 2)
    hden_nat (dvd_refl _)
  exact ⟨x.num, ((Rat.den_eq_one_iff x).mp hone).symm⟩

theorem integral_quadratic_half_coordinates {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ) (r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hx : IsIntegral ℤ ((r : K) + s * a)) :
    ∃ m k : ℤ, 2 * r = m ∧ 2 * s = k ∧ 4 ∣ m ^ 2 - d * k ^ 2 := by
  obtain ⟨ht, hn⟩ := trace_norm_quadratic_basis u a (d : ℚ) r s hu (by simpa using ha)
  have hit : IsIntegral ℤ (2 * r) := ht ▸ Algebra.isIntegral_trace hx
  have hin : IsIntegral ℤ (r ^ 2 - (d : ℚ) * s ^ 2) := hn ▸ Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hit
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hin
  change (m : ℚ) = 2 * r at hm
  change (n : ℚ) = r ^ 2 - (d : ℚ) * s ^ 2 at hn
  have hsq : (d : ℚ) * (2 * s) ^ 2 = (m ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [hm, hn]
    ring
  obtain ⟨k, hk⟩ := rat_int_of_squarefree_mul_sq_eq_int d (m ^ 2 - 4 * n) hd (2 * s) hsq
  refine ⟨m, k, hm.symm, hk, n, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, ← hk, hn]
  ring

theorem even_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even m ∧ Even k := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four] at heq
  simp only [Int.even_iff]
  rcases hd with hd | hd <;> rw [hd] at heq <;> omega

theorem even_sub_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 1)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even (m - k) := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four, hd] at heq
  simp only [Int.even_iff]
  omega

theorem integral_quadratic_eq_int_add_int_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * a := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨hm2, hk2⟩ := even_coordinates_of_four_dvd d m k hd4 hmk
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp hm2
  obtain ⟨j, hj⟩ := even_iff_two_dvd.mp hk2
  have hri : r = (i : ℚ) := by
    have hi' : (m : ℚ) = 2 * i := by exact_mod_cast hi
    linarith
  have hsj : s = (j : ℚ) := by
    have hj' : (k : ℚ) = 2 * j := by exact_mod_cast hj
    linarith
  refine ⟨i, j, ?_⟩
  rw [← hrep, hri, hsj]
  norm_cast

theorem integral_quadratic_eq_int_add_int_mul_half {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * ((1 + a) / 2) := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp (even_sub_coordinates_of_four_dvd d m k hd4 hmk)
  have hri : r = (i : ℚ) + (k : ℚ) / 2 := by
    have hi' : (m : ℚ) - k = 2 * i := by exact_mod_cast hi
    linarith
  have hsk : s = (k : ℚ) / 2 := by linarith
  refine ⟨i, k, ?_⟩
  rw [← hrep, hri, hsk]
  push_cast
  ring

theorem integral_quadratic_half_generator {K : Type*} [Field K] [CharZero K]
    (a : K) (d : ℤ) (ha : a ^ 2 = d) (hd : d % 4 = 1) :
    IsIntegral ℤ ((1 + a) / 2) := by
  have hdv : d = 4 * (d / 4) + 1 := by omega
  refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4)),
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num), ?_⟩
  change Polynomial.aeval ((1 + a) / 2)
    (Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4))) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_add, Polynomial.aeval_C]
  have hdK : (d : K) = 4 * ((d / 4 : ℤ) : K) + 1 := by exact_mod_cast hdv
  field_simp
  linear_combination ha + hdK

theorem exists_ringOfIntegers_pair_basis {K : Type*} [Field K] [NumberField K]
    (w : K) (hw : IsIntegral ℤ w) (hdim : Module.finrank ℚ K = 2)
    (hspan : ∀ x : K, IsIntegral ℤ x → ∃ m n : ℤ, x = m + n * w) :
    ∃ B : Basis (Fin 2) ℤ (𝓞 K),
      (fun i => ((B i : 𝓞 K) : K)) = ![1, w] := by
  let W : 𝓞 K := ⟨w, hw⟩
  let v : Fin 2 → 𝓞 K := ![1, W]
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    obtain ⟨m, n, hmn⟩ := hspan x x.property
    have hmn' : x = m • (1 : 𝓞 K) + n • W := by
      apply RingOfIntegers.ext
      change (x : K) = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + n • W)
      rw [map_add, map_zsmul, map_zsmul, map_one]
      change (x : K) = m • (1 : K) + n • w
      simpa [Algebra.smul_def] using hmn
    rw [hmn']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))
  have hc : Fintype.card (Fin 2) = Module.finrank ℤ (𝓞 K) := by
    simpa [RingOfIntegers.rank] using hdim.symm
  let B : Basis (Fin 2) ℤ (𝓞 K) := basisOfTopLeSpanOfCardEqFinrank v hs hc
  refine ⟨B, ?_⟩
  ext i
  fin_cases i <;> simp [B, v, W]
  rfl

theorem discr_quadratic_pair {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.discr ℚ ![1, (r : K) + s * a] = 4 * d * s ^ 2 := by
  have ht := (trace_norm_quadratic_basis u a d r s hu ha).1
  have ht1 : Algebra.trace ℚ K 1 = 2 := by
    simpa using Algebra.trace_algebraMap_of_basis u (1 : ℚ)
  have hww : ((r : K) + s * a) * ((r : K) + s * a) =
      ((r ^ 2 + d * s ^ 2 : ℚ) : K) + ((2 * r * s : ℚ) : K) * a := by
    push_cast
    linear_combination (s : K) ^ 2 * ha
  have htww : Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) =
      2 * (r ^ 2 + d * s ^ 2) := by
    rw [hww]
    exact (trace_norm_quadratic_basis u a d (r ^ 2 + d * s ^ 2) (2 * r * s) hu ha).1
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change Algebra.trace ℚ K (1 * 1) *
      Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) -
    Algebra.trace ℚ K (1 * ((r : K) + s * a)) *
      Algebra.trace ℚ K (((r : K) + s * a) * 1) = _
  rw [one_mul, one_mul, mul_one, ht, ht1, htww]
  ring

theorem coe_discr_eq_pair_of_integer_basis {K : Type*} [Field K] [NumberField K]
    (B : Basis (Fin 2) ℤ (𝓞 K)) (w : K)
    (hB : (fun i => ((B i : 𝓞 K) : K)) = ![1, w]) :
    (NumberField.discr K : ℚ) = Algebra.discr ℚ ![1, w] := by
  rw [← NumberField.discr_eq_discr K B]
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ B) = _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K B]
  congr 1
  funext i
  rw [Basis.localizationLocalization_apply]
  exact congrFun hB i

theorem numberField_discr_quadratic_eq_four_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) : NumberField.discr K = 4 * d := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis a hai hdim
    (integral_quadratic_eq_int_add_int_mul u a d hu ha hd hd4)
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [coe_discr_eq_pair_of_integer_basis B a hB]
  simpa using discr_quadratic_pair u a (d : ℚ) 0 1 hu (by simpa using ha)

theorem numberField_discr_quadratic_eq_self {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) : NumberField.discr K = d := by
  have hwi := integral_quadratic_half_generator a d ha hd4
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis ((1 + a) / 2) hwi hdim
    (integral_quadratic_eq_int_add_int_mul_half u a d hu ha hd hd4)
  have hw : (1 + a) / 2 = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * a := by
    push_cast
    ring
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_eq_pair_of_integer_basis B ((1 + a) / 2) hB, hw,
    discr_quadratic_pair u a (d : ℚ) (1 / 2) (1 / 2) hu (by simpa using ha)]
  ring

theorem isFundamentalDiscr_quadratic {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hd1, hd⟩)
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨hd, hd4⟩

theorem isUnramifiedIn_two_iff_radical_mod_four {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1 := by
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
    ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two)]
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    have hodd : ¬ (2 : ℤ) ∣ d := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    simp [hodd, hd1]
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    have hdiv : (2 : ℤ) ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num) d
    simp [hdiv, hd1]

end WeightedTorusJets
namespace WeightedTorusJets
theorem isUnramifiedIn_of_numberField_extension
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (P : Ideal ℤ) (hunr : Algebra.IsUnramifiedIn (𝓞 L) P) :
    Algebra.IsUnramifiedIn (𝓞 K) P := by
  intro Q hQ hover
  obtain ⟨⟨Q', hQ', hover'⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) Q
  have : Q'.LiesOver P := Ideal.LiesOver.trans Q' Q P
  have : Algebra.IsUnramifiedAt ℤ Q' := hunr Q' inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ Q Q'

theorem quadratic_radical_mod_four_of_odd_cyclotomic_overfield
    (n : ℕ) [NeZero n] (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [IsCyclotomicExtension {n} ℚ L]
    (u : Module.Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d)
    (hd : Squarefree d) (hn : Odd n) : d % 4 = 1 := by
  apply (isUnramifiedIn_two_iff_radical_mod_four u a d hu ha hd).mp
  exact isUnramifiedIn_of_numberField_extension (L := L) _
    (cyclotomic_isUnramifiedIn n L 2 hn.not_two_dvd_nat)

noncomputable def quadraticAdjoinBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) :
    Module.Basis (Fin 2) F (IntermediateField.adjoin F {a}) :=
  let pb := IntermediateField.adjoin.powerBasis ha
  pb.basis.reindex (finCongr (pb.finrank.symm.trans hdim))

@[simp]
theorem quadraticAdjoinBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) (i : Fin 2) :
    quadraticAdjoinBasis a ha hdim i = ![1, IntermediateField.AdjoinSimple.gen F a] i := by
  fin_cases i <;>
    simp [quadraticAdjoinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem primitive_odd_quadratic_signed_level_mod_four {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hodd : Odd q) : (χ (-1) * (q : ℤ)) % 4 = 1 := by
  classical
  by_cases hne : χ = 1
  · subst χ
    have hq : q = 1 := hprim.symm.trans DirichletCharacter.conductor_one
    subst q
    rw [MulChar.one_apply isUnit_neg_one]
    norm_num
  let K := CyclotomicField q ℚ
  let : IsCyclotomicExtension {q} ℚ K := CyclotomicField.isCyclotomicExtension q ℚ
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  let χK := χ.ringHomComp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  let e := AddChar.zmodChar q (zeta_spec q ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q (zeta_spec q ℚ K)
  let g := gaussSum χK e
  let D : ℤ := χ (-1) * q
  have hgD : g ^ 2 = (D : K) := by
    change gaussSum χK e ^ 2 = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [primitive_quadratic_gaussSum_sq hpK (hχ.comp (Int.castRingHom K)) he]
    change (χ (-1) : K) * (q : K) = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [Int.cast_mul, Int.cast_natCast]
  have hqsf : Squarefree q := odd_divisor_primitive_quadratic_squarefree χ hχ hprim hodd dvd_rfl
  have hDsf : Squarefree D := by
    apply Int.squarefree_natAbs.mp
    change Squarefree (χ (-1) * (q : ℤ)).natAbs
    rw [Int.natAbs_mul, Int.natAbs_of_isUnit (isUnit_neg_one.map χ), one_mul]
    exact hqsf
  have hneC : χ.ringHomComp (Int.castRingHom ℂ) ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ)
      (Int.cast_injective (α := ℂ))).mpr hne
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {g}) = 2 := by
    rw [show IntermediateField.adjoin ℚ {g} =
        characterField q K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) from
      gaussSum_adjoin_eq_characterField χ hχ hprim e he]
    exact characterField_finrank q K ℂ _ (hχ.comp (Int.castRingHom ℂ)) hneC
  have hgi : IsIntegral ℚ g := IsIntegral.of_pow (by decide : 0 < 2)
    (hgD ▸ isIntegral_intCast D)
  let F := IntermediateField.adjoin ℚ {g}
  let a : F := IntermediateField.AdjoinSimple.gen ℚ g
  let u := quadraticAdjoinBasis g hgi hdim
  have hu : (u : Fin 2 → F) = ![1, a] := by
    funext i
    exact quadraticAdjoinBasis_apply g hgi hdim i
  have ha : a ^ 2 = (D : F) := by
    apply Subtype.ext
    exact hgD
  exact quadratic_radical_mod_four_of_odd_cyclotomic_overfield q F K u a D hu ha hDsf hodd

end WeightedTorusJets
namespace WeightedTorusJets
noncomputable def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

@[simp]
theorem crtUnits_fst {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).1 = ZMod.unitsMap (Nat.dvd_mul_right m n) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m))) (u : ZMod (m * n))

@[simp]
theorem crtUnits_snd {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).2 = ZMod.unitsMap (Nat.dvd_mul_left n m) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n))) (u : ZMod (m * n))

noncomputable def crtCharacterLeft {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R m :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inl _ _)))

noncomputable def crtCharacterRight {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R n :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inr _ _)))

@[simp]
theorem crtCharacterLeft_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod m)ˣ) :
    crtCharacterLeft h χ u = χ ((crtUnits h).symm (u, 1)) := by
  simp [crtCharacterLeft]

@[simp]
theorem crtCharacterRight_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod n)ˣ) :
    crtCharacterRight h χ u = χ ((crtUnits h).symm (1, u)) := by
  simp [crtCharacterRight]

theorem crtCharacter_decomposition {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ = DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ) *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ) := by
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply]
  simp only [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe,
    MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [crtCharacterLeft_apply_unit, crtCharacterRight_apply_unit, ← map_mul]
  congr 1
  have hu : u = (crtUnits h).symm (ZMod.unitsMap (Nat.dvd_mul_right m n) u, 1) *
      (crtUnits h).symm (1, ZMod.unitsMap (Nat.dvd_mul_left n m) u) := by
    apply (crtUnits h).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Prod.ext <;> simp
  exact congrArg Units.val hu

theorem crtCharacterLeft_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterLeft h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterLeft h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_right (NeZero.pos n)
  exact hdiv.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ n)
    ((crtCharacterRight h χ).conductor_dvd_level.trans (Nat.dvd_mul_left n _)))

theorem crtCharacterRight_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterRight h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterRight h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_left (NeZero.pos m)
  exact hdiv.trans (Nat.lcm_dvd
    ((crtCharacterLeft h χ).conductor_dvd_level.trans (Nat.dvd_mul_right m _))
    (Nat.dvd_mul_left _ m))

theorem changeLevel_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m ∣ n) (χ : DirichletCharacter R m) :
    DirichletCharacter.changeLevel h χ (-1) = χ (-1) := by
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (-1 : (ZMod n)ˣ)
  simpa only [Units.val_neg, Units.val_one, ZMod.cast_neg h, ZMod.cast_one h] using he

theorem crtCharacter_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ (-1) = crtCharacterLeft h χ (-1) * crtCharacterRight h χ (-1) := by
  have he := congrArg (fun ψ : DirichletCharacter R (m * n) => ψ (-1))
    (crtCharacter_decomposition h χ)
  simpa only [MulChar.mul_apply, changeLevel_neg_one] using he

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.SqrtTwoField. -/
section
namespace OAI
namespace SiegelZeros
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets
theorem primitive_mod_four_character_neg_one (χ : DirichletCharacter ℤ 4)
    (hprim : χ.IsPrimitive) : χ (-1) = -1 := by
  have hne : χ ≠ 1 := by
    intro h
    have hc := hprim
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  have hu_cases : u = 1 ∨ u = -1 := by
    exact (by decide : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1) u
  rcases hu_cases with rfl | rfl
  · simp at hu
  · have hval := Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod 4)).map χ)
    exact hval.resolve_left (by simpa only [Units.val_neg, Units.val_one] using hu)

theorem primitive_four_mul_exists_odd_part {u : ℕ} [NeZero u] (hu : Odd u)
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) :
    ∃ η : DirichletCharacter ℤ u, η.IsPrimitive ∧ χ (-1) = -η (-1) := by
  have hc : Nat.Coprime 4 u := by
    simpa using hu.coprime_two_left.pow_left 2
  refine ⟨crtCharacterRight hc χ, crtCharacterRight_isPrimitive hc χ hprim, ?_⟩
  rw [crtCharacter_neg_one hc χ, primitive_mod_four_character_neg_one _
    (crtCharacterLeft_isPrimitive hc χ hprim), neg_one_mul]

theorem primitive_four_mul_quadratic_signed_part_mod_four {u : ℕ} [NeZero u]
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) (hu : Odd u) :
    (χ (-1) * (u : ℤ)) % 4 = 3 := by
  obtain ⟨η, hηprim, hneg⟩ := primitive_four_mul_exists_odd_part hu χ hprim
  have hηquad : η.IsQuadratic := by
    intro a
    by_cases ha : IsUnit a
    · exact Or.inr (Int.isUnit_eq_one_or (ha.map η))
    · exact Or.inl (η.map_nonunit ha)
  have hodd := primitive_odd_quadratic_signed_level_mod_four η hηquad hηprim hu
  rw [hneg, neg_mul]
  omega

theorem fundamentalDiscr_eight_odd_case {D d : ℤ} {u : ℕ} (hu : Odd u)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) (hD : D.natAbs = 8 * u) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Nat.squarefree_iff_prime_squarefree.mp (Int.squarefree_natAbs.mpr hd)
    exact (hf 2 Nat.prime_two ⟨2 * u, by omega⟩).elim
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inl ?_⟩
    have heq : 4 * d.natAbs = 8 * u := by simpa [hDd, Int.natAbs_mul] using hD
    have hn : d.natAbs = 2 * u := by omega
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hn
    rw [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] at hh
    obtain ⟨k, hk⟩ := hu
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h] at hh
      omega
    · rw [abs_of_nonpos h] at hh
      omega

theorem fundamentalDiscr_four_parity_case {D d s : ℤ} {u : ℕ}
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d)
    (hD : D = s * (4 * (u : ℤ))) (hparity : (s * (u : ℤ)) % 4 = 3) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
    apply (hf ?_).elim
    refine ⟨s * (u : ℤ), ?_⟩
    rw [hD]
    ring
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inr ?_⟩
    have heq : d = s * (u : ℤ) := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
      calc
        4 * d = D := hDd.symm
        _ = s * (4 * (u : ℤ)) := hD
        _ = 4 * (s * (u : ℤ)) := by ring
    rwa [heq]

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem exists_signed_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (D d : ℤ) (a : K), D = integerCharacter χ hχ (-1) * (n : ℤ) ∧
      D.natAbs = n ∧ Squarefree d ∧ (D = d ∨ D = 4 * d) ∧
      d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ σ : Gal(K/ℚ), σ a = (integerCharacter χ hχ (galEquivZMod n K σ) : K) * a := by
  let χI := integerCharacter χ hχ
  let χK := χI.ringHomComp (Int.castRingHom K)
  have hI := integerCharacter_isQuadratic χ hχ
  have hpI := integerCharacter_isPrimitive χ hχ hprim
  have hK : χK.IsQuadratic := hI.comp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χI (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hpI
  let e := AddChar.zmodChar n (zeta_spec n ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root n (zeta_spec n ℚ K)
  obtain ⟨D, hDabs, hgD⟩ := primitive_quadratic_gaussSum_integer_square hpK hK he
  have hD : D ≠ 0 := by
    intro h
    have := hDabs
    rw [h, Int.natAbs_zero] at this
    exact (NeZero.ne n) this.symm
  obtain ⟨d, c, a, hd, hbound, hc, hdc, ha, hint, hga, hadj⟩ :=
    exists_squarefree_generator hD hgD
  have hadjχ : IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ := by
    rw [hadj, gaussSum_adjoin_eq_characterField χI hI hpI e he]
    congr 1
    exact integerCharacter_ringHomComp χ hχ
  have hdiv : d.natAbs ∣ n := by
    rw [← hDabs]
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [hdc, mul_comm]⟩
  have hnsq : ¬ IsSquare (d : ℚ) := by
    apply not_isSquare_of_quadratic_adjoin ha
    rw [hadjχ]
    exact characterField_finrank n K ℂ χ hχ hne
  have hDchar : D = χI (-1) * (n : ℤ) := by
    apply Int.cast_injective (α := K)
    push_cast
    calc
      (D : K) = gaussSum χK e ^ 2 := hgD.symm
      _ = χK (-1) * (n : K) := primitive_quadratic_gaussSum_sq hpK hK he
      _ = (χI (-1) : K) * (n : K) := rfl
  have hcases := primitive_quadratic_radicand_eq_or_four_mul χ hχ hprim hDabs hdc
  refine ⟨D, d, a, hDchar, hDabs, hd, hcases, hDabs ▸ hbound, hdiv, hnsq,
    ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

end WeightedTorusJets
namespace WeightedTorusJets
open Module NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem normalized_signed_conductor_isFundamentalDiscr {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D d : ℤ} (hDsign : D = χ (-1) * (q : ℤ)) (hDabs : D.natAbs = q)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) : Int.IsFundamentalDiscr D := by
  obtain ⟨u, hu, hsfu, hq | hq | hq⟩ := primitive_quadratic_conductor_shape χ hχ hprim
  · have hodd : Odd q := hq ▸ hu
    apply Int.isFundamentalDiscr_iff_squarefree.mpr
    refine Or.inl ⟨?_, Int.squarefree_natAbs.mp ?_⟩
    · rw [hDsign]
      exact primitive_odd_quadratic_signed_level_mod_four χ hχ hprim hodd
    · rwa [hDabs, hq]
  · subst hq
    let : NeZero u := ⟨hsfu.ne_zero⟩
    exact fundamentalDiscr_four_parity_case hd hDd
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDsign)
      (primitive_four_mul_quadratic_signed_part_mod_four χ hprim hu)
  · exact fundamentalDiscr_eight_odd_case hu hd hDd (hDabs.trans hq)

theorem characterField_discr_eq_signed_conductor {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField n K ℂ χ) = integerCharacter χ hχ (-1) * (n : ℤ) := by
  obtain ⟨D, d, a, hDsign, hDabs, hd, hDd, _, _, _, ha, hint, hadj, _⟩ :=
    exists_signed_squarefree_characterField_generator (K := K) χ hχ hprim hne
  have hfund := normalized_signed_conductor_isFundamentalDiscr (integerCharacter χ hχ)
    (integerCharacter_isQuadratic χ hχ) (integerCharacter_isPrimitive χ hχ hprim)
    hDsign hDabs hd hDd
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2 := by
    rw [hadj]
    exact characterField_finrank n K ℂ χ hχ hne
  have hai : IsIntegral ℚ a := hint.tower_top
  let u := quadraticAdjoinBasis a hai hdim
  let a' := IntermediateField.AdjoinSimple.gen ℚ a
  have hu : (u : Fin 2 → IntermediateField.adjoin ℚ {a}) = ![1, a'] := by
    funext i
    exact quadraticAdjoinBasis_apply a hai hdim i
  have ha' : a' ^ 2 = (d : IntermediateField.adjoin ℚ {a}) := by
    apply Subtype.ext
    exact ha
  have hdiscr : NumberField.discr (IntermediateField.adjoin ℚ {a}) = D := by
    rcases hDd with hDd | hDd
    · rw [hDd] at hfund ⊢
      have hd4 : d % 4 ≠ 0 := by
        intro h
        exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
          (by simpa using Int.dvd_of_emod_eq_zero h)
      exact numberField_discr_quadratic_eq_self u a' d hu ha' hd
        (hfund.emod_four_eq_zero_or_one.resolve_left hd4)
    · rw [hDd] at hfund ⊢
      exact numberField_discr_quadratic_eq_four_mul u a' d hu ha' hd
        (Int.isFundamentalDiscr_four_mul.mp hfund).2
  rw [hadj, hDsign] at hdiscr
  exact hdiscr

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem characterField_changeLevel_discr_eq_signed_conductor {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ)) =
      integerCharacter χ hχ (-1) * (q : ℤ) := by
  let K := cyclotomicDivisorField q m L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q m L hdiv
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  rw [characterField_changeLevel q K ℂ L hdiv χ hχ]
  exact (NumberField.discr_eq_discr_of_algEquiv (characterField q K ℂ χ)
    ((characterField q K ℂ χ).equivMap (IsScalarTower.toAlgHom ℚ K L))).symm.trans
      (characterField_discr_eq_signed_conductor χ hχ hprim hne)

theorem characterField_changeLevel_discr_natAbs {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    (NumberField.discr
      (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ))).natAbs = q := by
  rw [characterField_changeLevel_discr_eq_signed_conductor hdiv χ hχ hprim hne]
  rcases Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod q)).map
    (integerCharacter χ hχ)) with h | h <;> simp [h]

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField
theorem quadraticAdjoin_discriminant {L : Type*} [Field L] [NumberField L]
    (a : L) (d : ℤ) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hns : ¬ IsSquare (d : ℚ)) :
    NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d) ∧
    Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
    (Algebra.IsUnramifiedIn (𝓞 (IntermediateField.adjoin ℚ {a}))
      (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1) := by
  let F := IntermediateField.adjoin ℚ {a}
  let A : F := IntermediateField.AdjoinSimple.gen ℚ a
  have hroot : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hi : IsIntegral ℚ a := IsIntegral.of_pow (by decide : 0 < 2)
    (hroot ▸ isIntegral_algebraMap)
  have hdim := finrank_adjoin_sqrt a (d : ℚ) hroot hns
  let u : Module.Basis (Fin 2) ℚ F := quadraticAdjoinBasis a hi hdim
  have hu : (u : Fin 2 → F) = ![1, A] := by
    funext i
    exact quadraticAdjoinBasis_apply a hi hdim i
  have hA : A ^ 2 = (d : F) := by
    apply Subtype.ext
    exact ha
  refine ⟨?_, isFundamentalDiscr_quadratic u A d hu hA hd,
    isUnramifiedIn_two_iff_radical_mod_four u A d hu hA hd⟩
  by_cases hd1 : d % 4 = 1
  · simp only [ite_eq_left hd1]
    exact numberField_discr_quadratic_eq_self u A d hu hA hd hd1
  · simp only [ite_eq_right hd1]
    have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    exact numberField_discr_quadratic_eq_four_mul u A d hu hA hd (by omega)

open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
end WeightedTorusJets
namespace WeightedTorusJets
open IsCyclotomicExtension IsCyclotomicExtension.Rat
noncomputable def sourceSqrtTwoField (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    IntermediateField ℚ L :=
  let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  IntermediateField.adjoin ℚ ({ζ - ζ ^ 3} : Set L)

theorem sourceSqrtTwoField_root_sq (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
    (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  exact primitive_eighth_root_difference_sq
    ((zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm)

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat
theorem exists_auxiliary_sqrt_pair_of_field_ne (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IsIntegral ℤ a ∧ IsIntegral ℤ b ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 → σ a = -a := by
  have hqm : q ∣ 8 * q := dvd_mul_left q 8
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  let K := cyclotomicDivisorField q (8 * q) L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q (8 * q) L hqm
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  obtain ⟨d, aK, hd, hbound, hddiv, hdns, haK, _, hadjK, hsign⟩ :=
    exists_squarefree_generator_frobenius_sign q (8 * q) K L hqm χ hχ hprim hne
  let a : L := algebraMap K L aK
  have ha : a ^ 2 = (d : L) := by
    change (algebraMap K L aK) ^ 2 = _
    rw [← map_pow, haK, map_intCast]
  let ζ : L := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  have hζ : IsPrimitiveRoot ζ 8 :=
    (zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm
  let b := ζ - ζ ^ 3
  have hb : b ^ 2 = 2 := primitive_eighth_root_difference_sq hζ
  have hadj : IntermediateField.adjoin ℚ {a} =
      characterField (8 * q) L ℂ (DirichletCharacter.changeLevel hqm χ) := by
    rw [characterField_changeLevel q K ℂ L hqm χ hχ, ← hadjK,
      IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hneq : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} := by
    intro heq
    exact hfield (hadj.symm.trans heq)
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, ?_, ?_, hadj, hneq, ?_⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [ha]
    exact isIntegral_algebraMap
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [hb]
    exact isIntegral_natCast 2
  · intro p hp hpn P hP σ hσ hχp
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    exact hsign p hp (h8.mul_right hq) P hP σ hσ hχp

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField
theorem source_biquadratic_arithmetic_of_field_ne (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  have hquad := real_character_isQuadratic χ hreal
  obtain ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, _, _, hadj, hfields, hsign⟩ :=
    exists_auxiliary_sqrt_pair_of_field_ne q L χ hquad hprim hne hfield
  have haRat : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hbRat : b ^ 2 = algebraMap ℚ L (2 : ℚ) := by simpa using hb
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
  have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
  have hint := biquadratic_monomials_integral a' b' d 2 ha' (by simpa using hb')
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hdesc⟩ :=
    sqrtPair_frobenius_directions a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  obtain ⟨hformula, hfund, _⟩ := quadraticAdjoin_discriminant a d ha hd hdns
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, hadj, ?_, hfund, hformula, v, hv, ?_, ?_,
    σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  · rw [hadj]
    exact characterField_changeLevel_discr_natAbs (dvd_mul_left q 8) χ hquad hprim hne
  · intro i
    rw [hv]
    fin_cases i
    · exact hint.1
    · exact hint.2.1
    · exact hint.2.2.1
    · exact hint.2.2.2
  · exact finrank_adjoin_pair_sqrt a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  · intro p hp hpn hχp
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero (8 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    have hpm : ¬ p ∣ 8 * q := hp.coprime_iff_not_dvd.mp (h8.mul_right hq)
    obtain ⟨φ, hfrob, hglobal⟩ := exists_cyclotomic_frobenius_congruence (8 * q) L p hpm
    obtain ⟨P, hP, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    exact hdesc p φ (hsign p hp hpn P hover.over.symm φ (hfrob P inferInstance hover) hχp) hglobal

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_biquadratic_arithmetic_canonical_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    let L := CyclotomicField (8 * q) ℚ
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  exact source_biquadratic_arithmetic_of_field_ne q (CyclotomicField (8 * q) ℚ)
    χ hreal hprim hne hfield

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.BiquadraticArithmeticFull. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets
theorem exists_lower_triangular_replacement
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A B : Matrix ι ι K)
    (hspan : ∀ i, B i - A i ∈ Submodule.span K (A '' {j | j < i})) :
    ∃ L : Matrix ι ι K, L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ B = L * A := by
  classical
  have hcoeff (i : ι) : ∃ c : ι → K,
      ∑ j ∈ Finset.univ.filter (fun j => j < i), c j • A j = B i - A i := by
    apply (Submodule.mem_span_image_finset_iff_exists_fun' K).mp
    simpa using hspan i
  choose c hc using hcoeff
  refine ⟨Matrix.of (fun i j =>
    (if j < i then c i j else 0) + (if i = j then 1 else 0)),
    ?_, ?_, ?_⟩
  · intro i j hij
    change i < j at hij
    simp [not_lt_of_ge hij.le, hij.ne]
  · intro i
    simp
  · apply Matrix.ext
    intro i k
    have hi := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
    simpa only [Matrix.mul_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_filter] using (eq_sub_iff_add_eq.mp hi).symm

theorem determinant_dvd_of_earlier_row_replacement
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (A B : Matrix ι ι R)
    (hspan : ∀ i, f.mapMatrix B i - f.mapMatrix A i ∈
      Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (p : R) (e : ι → ℕ) (hdiv : ∀ i j, p ^ e i ∣ B i j) :
    p ^ (∑ i, e i) ∣ A.det := by
  classical
  obtain ⟨L, hL, hdiag, hreplace⟩ :=
    exists_lower_triangular_replacement (f.mapMatrix A) (f.mapMatrix B) hspan
  have hdet : B.det = A.det := hf <| by
    rw [f.map_det, f.map_det, hreplace, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL]
    simp [hdiag]
  choose C hC using hdiv
  have hB : B = Matrix.of (fun i j => p ^ e i * (Matrix.of C) i j) := by
    ext i j
    exact hC i j
  rw [← hdet, hB, Matrix.det_mul_column (fun i => p ^ e i) (Matrix.of C),
    Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem replacement_row_expansion {K ι : Type*} [CommRing K]
    (x y z : ι → K) (p k r b c : ℕ) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c =
      ∑ m ∈ Finset.range (k + 1),
        (((-1) ^ m * (k.choose m : K)) •
          (x ^ (p * (k - m) + r) * y ^ (b + m) * z ^ c)) := by
  rw [sub_eq_add_neg, add_comm (x ^ p), add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
    Pi.natCast_apply, pow_add, pow_mul]
  rw [neg_pow]
  ring

theorem replacement_row_sub_mem {K ι : Type*} [CommRing K]
    (x y z : ι → K) (W : Submodule K (ι → K)) (H p k r b c : ℕ) (hp : H < p)
    (hspan : ∀ a b' c', a + H * b' + H * c' < p * k + r + H * b + H * c →
      x ^ a * y ^ b' * z ^ c' ∈ W) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c -
      x ^ (p * k + r) * y ^ b * z ^ c ∈ W := by
  rw [replacement_row_expansion, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
    Nat.sub_zero, Nat.add_zero, add_sub_cancel_right]
  apply W.sum_mem
  intro m hm
  apply W.smul_mem
  apply hspan
  have hmle : m + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
  have hprod : H * (m + 1) < p * (m + 1) :=
    Nat.mul_lt_mul_of_pos_right hp (Nat.succ_pos m)
  have hdecomp : p * k = p * (k - (m + 1)) + p * (m + 1) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmle]
  simp only [Nat.mul_add, Nat.mul_one] at hprod hdecomp ⊢
  omega

theorem weighted_interpolation_determinant_dvd
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : ∀ n, (p : R) ∣ x n ^ p - y n) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  classical
  let B : Matrix ι ι R := Matrix.of fun i n =>
    x n ^ (a i % p) * (x n ^ p - y n) ^ (a i / p) * y n ^ b i * z n ^ c i
  apply determinant_dvd_of_earlier_row_replacement f hf A B
  · intro i
    have h := replacement_row_sub_mem (f ∘ x) (f ∘ y) (f ∘ z)
      (Submodule.span K (f.mapMatrix A '' {j | j < i}))
      H p (a i / p) (a i % p) (b i) (c i) hp (by
        intro a' b' c' hw
        apply hspan i a' b' c'
        simpa only [Nat.div_add_mod] using hw)
    have heq : f.mapMatrix B i - f.mapMatrix A i =
        (f ∘ x) ^ (a i % p) * ((f ∘ x) ^ p - f ∘ y) ^ (a i / p) *
          (f ∘ y) ^ b i * (f ∘ z) ^ c i -
          (f ∘ x) ^ a i * (f ∘ y) ^ b i * (f ∘ z) ^ c i := by
      ext n
      simp [B, hA, map_mul, map_pow, map_sub]
    rw [heq]
    simpa only [Nat.div_add_mod] using h
  · intro i n
    exact (((pow_dvd_pow_of_dvd (hFrob n) (a i / p)).mul_left
      (x n ^ (a i % p))).mul_right (y n ^ b i)).mul_right (z n ^ c i)

theorem weighted_interpolation_determinant_dvd_of_frobenius_choice
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : (∀ n, (p : R) ∣ x n ^ p - y n) ∨
      (∀ n, (p : R) ∣ x n ^ p - z n)) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  rcases hFrob with hFrob | hFrob
  · exact weighted_interpolation_determinant_dvd f hf x y z a b c A hA H p hp
      hspan hFrob
  · apply weighted_interpolation_determinant_dvd f hf x z y a c b A
      (fun i n => by rw [hA]; ring) H p hp _ hFrob
    intro i a' c' b' hw
    have h := hspan i a' b' c' (by omega)
    convert h using 1
    ring

open NumberField
theorem galois_derivative_determinant_mem_prime_power
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (θ : ι → 𝓞 K) (ν₂ ν₃ : K →+* K) (a b c : ι → ℕ)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (fun n => (θ n : K) ^ a' * ν₂ (θ n) ^ b' * ν₃ (θ n) ^ c') ∈
        Submodule.span K ((fun i n =>
          (θ n : K) ^ a i * ν₂ (θ n) ^ b i * ν₃ (θ n) ^ c i) '' {j | j < i}))
    (hFrob : (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₂ (θ n))) ∨
      (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₃ (θ n)))) :
    (Matrix.of (fun i n => θ n ^ a i * (RingOfIntegers.mapRingHom ν₂ (θ n)) ^ b i *
      (RingOfIntegers.mapRingHom ν₃ (θ n)) ^ c i)).det ∈
      (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, a i / p) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply weighted_interpolation_determinant_dvd_of_frobenius_choice (algebraMap (𝓞 K) K)
    RingOfIntegers.coe_injective θ
    ((RingOfIntegers.mapRingHom ν₂) ∘ θ) ((RingOfIntegers.mapRingHom ν₃) ∘ θ)
    a b c _ (fun _ _ => rfl) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : ι → ι → K => f '' {j | j < i})
      ext j n
      change algebraMap (𝓞 K) K (_ * _ * _) = _
      simp
    · funext n
      rfl
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))
    · exact Or.inr fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))

theorem integral_jet_matrix_lift {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    ∃ θ₀ : Fin m → 𝓞 K,
      (∀ j, (θ₀ j : K) = θ j) ∧
      let A₀ := Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2
      A₀.map (algebraMap (𝓞 K) K) = A ∧
        (A₀.det : K) = A.det ∧ (A.det ≠ 0 → A₀.det ≠ 0) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  obtain ⟨h1, hai, hbi, hab⟩ :=
    biquadratic_monomials_integral a b d 2 ha (by simpa using hb)
  have hθ (j : Fin m) : IsIntegral ℤ (θ j) := by
    apply IsIntegral.sum
    intro i _
    apply (isIntegral_natCast _).mul
    fin_cases i <;> assumption
  let θ₀ : Fin m → 𝓞 K := fun j => ⟨θ j, hθ j⟩
  refine ⟨θ₀, fun _ => rfl, ?_⟩
  dsimp only
  have hmap :
      (Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2).map
          (algebraMap (𝓞 K) K) =
      Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
        (σ.comp τ) (θ j) ^ α i 2 := by
    ext i j
    change algebraMap (𝓞 K) K (_ * _ * _) = _
    simp only [map_mul, map_pow]
    rfl
  refine ⟨hmap, ?_⟩
  have hdet := congrArg Matrix.det hmap
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  exact ⟨hdet, fun h => NumberField.RingOfIntegers.coe_ne_zero_iff.mp (hdet.symm ▸ h)⟩

theorem exists_integral_jet_determinant_divisible
    {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) (H : ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    (∀ i a' b' c', a' + H * b' + H * c' < α i 0 + H * α i 1 + H * α i 2 →
      (fun j => θ j ^ a' * σ (θ j) ^ b' * (σ.comp τ) (θ j) ^ c') ∈
        Submodule.span K (A '' {j | j < i})) →
    A.det ≠ 0 →
    ∃ Δ : 𝓞 K, (Δ : K) = A.det ∧ Δ ≠ 0 ∧
      ∀ p : ℕ, H < p →
        ((∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom σ t)) ∨
          (∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
              (RingOfIntegers.mapRingHom (σ.comp τ) t))) →
        Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p) := by
  dsimp only
  intro hspan hnonzero
  obtain ⟨θ₀, hθ₀, _hmap, hdet, hne⟩ := integral_jet_matrix_lift σ τ ha hb n α
  refine ⟨_, hdet, hne hnonzero, ?_⟩
  intro p hp hFrob
  apply galois_derivative_determinant_mem_prime_power θ₀ σ (σ.comp τ)
    (fun i => α i 0) (fun i => α i 1) (fun i => α i 2) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : Fin m → Fin m → K => f '' {j | j < i})
      ext k j
      simp only [Matrix.of_apply, hθ₀]
    · funext j
      simp only [hθ₀]
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun j => hFrob (θ₀ j)
    · exact Or.inr fun j => hFrob (θ₀ j)

end WeightedTorusJets
open scoped NumberField
namespace WeightedTorusJets
theorem frobenius_action_choice_iff_mapRingHom
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ) :
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) ↔
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom σ.toRingHom x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x)) := by
  rfl

theorem frobenius_action_choice_quotient
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ)
    (hFrob : (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) :
    ((∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom σ.toRingHom x)) ∨
      (∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x))) := by
  rcases (frobenius_action_choice_iff_mapRingHom σ τ p).mp hFrob with h | h
  · exact Or.inl fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))
  · exact Or.inr fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))

end WeightedTorusJets
open scoped BigOperators
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.GreedyPivots. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
namespace WeightedTorusJets
theorem pivot_floor_square_bound {t : ℝ} (ht : 1 ≤ t) :
    ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 ≤ 97 ^ 2 * t ^ 2 := by
  have hf := Nat.floor_le (show 0 ≤ 96 * t by positivity)
  have hupper : ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ≤ 97 * t := by
    push_cast
    linarith
  nlinarith [sq_nonneg (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) - 97 * t)]

theorem pivot_second_sum_bound {ι : Type*} (s : Finset ι) (b c : ι → ℕ)
    {t : ℝ} (hb : ∀ i ∈ s, (b i : ℝ) ≤ 96 * t)
    (hc : ∀ i ∈ s, (c i : ℝ) ≤ 96 * t) :
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ 192 * s.card * t := by
  calc
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ ∑ _i ∈ s, (192 * t) :=
      Finset.sum_le_sum fun i hi => by linarith [hb i hi, hc i hi]
    _ = 192 * s.card * t := by simp; ring

theorem pivot_lower_bound_quarter {M Q S : ℝ} (hQ : 0 < Q) (hM : 2 * Q ≤ M)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) : M ^ 2 / (4 * Q) ≤ S := by
  have hnonneg : 0 ≤ M * (M - 2 * Q) := mul_nonneg (by linarith) (by linarith)
  have h : M ^ 2 / (4 * Q) ≤ M ^ 2 / (2 * Q) - M / 2 := by
    apply (div_le_iff₀ (show 0 < 4 * Q by positivity)).mpr
    field_simp
    nlinarith
  exact h.trans hS

theorem pivot_lower_constant {M Q H t S : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (hH : 0 < H) (hM : M = H * t ^ 3) (hMQ : 2 * Q ≤ M)
    (hQt : Q ≤ 97 ^ 2 * t ^ 2)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) :
    M * H * t / (4 * 97 ^ 2) ≤ S := by
  have hquarter := pivot_lower_bound_quarter hQ hMQ hS
  have hlower : M * H * t / (4 * 97 ^ 2) ≤ M ^ 2 / (4 * Q) := by
    apply (le_div_iff₀ (show 0 < 4 * Q by positivity)).mpr
    have hnonneg : 0 ≤ M * H * t := by rw [hM]; positivity
    have h := mul_le_mul_of_nonneg_left hQt hnonneg
    rw [hM] at h ⊢
    nlinarith
  exact hlower.trans hquarter

theorem pivot_scale_ge_one {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    1 ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
  have hHpos : 0 < H := by linarith
  calc
    1 ≤ H := hH
    _ = H ^ (-(1 / 3 : ℝ)) * H ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add hHpos]
      norm_num
    _ ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hHpos.le _)
      exact Real.rpow_le_rpow hHpos.le hHN (by norm_num)

theorem pivot_dimension_eq_cube {N : ℝ} (hN : 0 ≤ N) :
    (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem pivot_scale_cube {H N : ℝ} (hH : 0 < H) (hN : 0 ≤ N) :
    H * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [mul_pow, pivot_dimension_eq_cube hN, ← Real.rpow_natCast,
    ← Real.rpow_mul hH.le]
  norm_num
  rw [Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hH.ne']
  simp

theorem pivot_primary_scale {H U : ℝ} (hH : 0 < H) :
    H * (H ^ (-(1 / 3 : ℝ)) * U) = H ^ (2 / 3 : ℝ) * U := by
  rw [← mul_assoc]
  have hp := Real.rpow_add hH (1 : ℝ) (-(1 / 3 : ℝ))
  norm_num at hp
  rw [← hp]

theorem pivot_count_threshold {H t Q : ℝ} (hQ : Q ≤ 97 ^ 2 * t ^ 2)
    (hscale : 2 * 97 ^ 2 ≤ H * t) : 2 * Q ≤ H * t ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg t)]

theorem pivot_primary_scale_ge_N {H N : ℝ} (hH : 1 ≤ H) (hN : 1 ≤ N) :
    N ≤ H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hHp : 1 ≤ H ^ (2 / 3 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hNp : N ≤ N ^ (4 / 3 : ℝ) := Real.self_le_rpow_of_one_le hN (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hHp (show 0 ≤ N ^ (4 / 3 : ℝ) by positivity)
  simp only [one_mul] at hprod
  exact hNp.trans hprod

theorem pivot_floor_count_eventually {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hN : 18818 ≤ N) :
    2 * (((⌊96 * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ))⌋₊ + 1 : ℕ) : ℝ) ^ 2)
      ≤ N ^ 4 := by
  have hHpos : 0 < H := by linarith
  have hNnonneg : 0 ≤ N := by linarith
  rw [← pivot_scale_cube hHpos hNnonneg]
  apply pivot_count_threshold (pivot_floor_square_bound (pivot_scale_ge_one hH hHN))
  rw [pivot_primary_scale hHpos]
  have h := pivot_primary_scale_ge_N hH (show 1 ≤ N by linarith)
  norm_num
  linarith

theorem pivot_coordinates_of_weight {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (hw : (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (b : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) ∧
      (c : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) := by
  have hs := pivot_primary_scale (U := U) hH
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : 0 ≤ H * b := mul_nonneg hH.le (Nat.cast_nonneg b)
  have hc : 0 ≤ H * c := mul_nonneg hH.le (Nat.cast_nonneg c)
  constructor
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith

theorem pivot_weight_of_rectangle {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (ha : (a : ℝ) ≤ 32 * H ^ (2 / 3 : ℝ) * U)
    (hb : (b : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U)
    (hc : (c : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U) :
    (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
  have hs := pivot_primary_scale (U := U) hH
  have hbH := mul_le_mul_of_nonneg_left hb hH.le
  have hcH := mul_le_mul_of_nonneg_left hc hH.le
  nlinarith

end WeightedTorusJets
open scoped BigOperators
namespace WeightedTorusJets
theorem card_filter_lt_le_mul {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q t : ℕ)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.filter fun i => a i < t).card ≤ Q * t := by
  classical
  have h := Finset.card_le_mul_card_image_of_maps_to
    (s := s.filter fun i => a i < t) (t := Finset.range t) (f := a)
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) Q
    (fun k _ => le_trans (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
          (Finset.mem_filter.mp hi).2⟩)) (hQ k))
  simpa using h

theorem card_sq_le_twice_mul_sum_add {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    s.card * s.card ≤ 2 * Q * (∑ i ∈ s, a i) + Q * s.card := by
  classical
  have hswap :
      (∑ i ∈ s, (s.filter fun j => a i < a j).card) =
        ∑ i ∈ s, (s.filter fun j => a j < a i).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hsplit : s.card * s.card =
      2 * (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
        ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
    calc
      s.card * s.card = ∑ i ∈ s, ∑ j ∈ s, (1 : ℕ) := by simp
      _ = ∑ i ∈ s, ∑ j ∈ s,
          ((if a j < a i then 1 else 0) + (if a i < a j then 1 else 0) +
            (if a j = a i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> omega
      _ = (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
          (∑ i ∈ s, (s.filter fun j => a i < a j).card) +
          ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
        simp only [Finset.sum_add_distrib, ← Finset.card_filter]
      _ = _ := by rw [hswap]; omega
  have hlt : (∑ i ∈ s, (s.filter fun j => a j < a i).card) ≤
      Q * (∑ i ∈ s, a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => card_filter_lt_le_mul s a Q (a i) hQ
  have heq : (∑ i ∈ s, (s.filter fun j => a j = a i).card) ≤ Q * s.card := by
    calc
      _ ≤ ∑ i ∈ s, Q := Finset.sum_le_sum fun i _ => hQ (a i)
      _ = _ := by simp [mul_comm]
  nlinarith

theorem sum_lower_of_bounded_multiplicity {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.card : ℝ) ^ 2 / (2 * Q) - s.card / 2 ≤ ∑ i ∈ s, (a i : ℝ) := by
  have h : (s.card : ℝ) * s.card ≤
      2 * (Q : ℝ) * (∑ i ∈ s, (a i : ℝ)) + (Q : ℝ) * s.card := by
    exact_mod_cast card_sq_le_twice_mul_sum_add s a Q hQ
  have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQpos
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)]
  nlinarith

theorem coordinate_fiber_card_le (s : Finset (Fin 3 → ℕ)) (B k : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.filter fun a => a 0 = k).card ≤ (B + 1) ^ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := s.filter fun a => a 0 = k)
    (t := Finset.range (B + 1) ×ˢ Finset.range (B + 1))
    (fun a => (a 1, a 2)) ?_ ?_
  · simpa [pow_two] using h
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).1
    obtain ⟨h1, h2⟩ := hB a ha'
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show a 1 < B + 1 by omega),
      Finset.mem_range.mpr (show a 2 < B + 1 by omega)⟩
  · intro a ha b hb hab
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    have ha1 := congrArg Prod.fst hab
    have ha2 := congrArg Prod.snd hab
    funext i
    fin_cases i <;> simp_all

theorem first_coordinate_sum_lower (s : Finset (Fin 3 → ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.card : ℝ) ^ 2 / (2 * ((B + 1 : ℕ) : ℝ) ^ 2) - s.card / 2 ≤
      ∑ a ∈ s, (a 0 : ℝ) := by
  have h := sum_lower_of_bounded_multiplicity s (fun a => a 0) ((B + 1)^2)
    (by positivity) (coordinate_fiber_card_le s B · hB)
  simpa using h

theorem weighted_pivot_bounds (P : Finset (Fin 3 → ℕ)) (H N : ℕ)
    (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : P.card = N ^ 4)
    (hw : ∀ a ∈ P, (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let t : ℝ := (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNreal : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hNreal : (18818 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have htone : 1 ≤ t := pivot_scale_ge_one hHone hHNreal
  have htpos : 0 < t := by linarith
  have hcardreal : (P.card : ℝ) = (N : ℝ) ^ 4 := by exact_mod_cast hcard
  have hcoords : ∀ a ∈ P, (a 1 : ℝ) ≤ 96 * t ∧ (a 2 : ℝ) ≤ 96 * t := by
    intro a ha
    exact pivot_coordinates_of_weight hHpos (a 0) (a 1) (a 2) (hw a ha)
  have hcoordsNat : ∀ a ∈ P, a 1 ≤ ⌊96 * t⌋₊ ∧ a 2 ≤ ⌊96 * t⌋₊ := by
    intro a ha
    exact ⟨Nat.le_floor (hcoords a ha).1, Nat.le_floor (hcoords a ha).2⟩
  have hlower := first_coordinate_sum_lower P ⌊96 * t⌋₊ hcoordsNat
  have hlarge : 2 * (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2) ≤ P.card := by
    rw [hcardreal]
    exact pivot_floor_count_eventually hHone hHNreal hNreal
  have hscale : (P.card : ℝ) = (H : ℝ) * t ^ 3 := by
    rw [hcardreal]
    exact (pivot_scale_cube hHpos hNnonneg).symm
  have hfirst := pivot_lower_constant
    (show 0 < ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 by positivity)
    htpos hHpos hscale hlarge (pivot_floor_square_bound htone) hlower
  constructor
  · have hs := pivot_primary_scale (U := (N : ℝ) ^ (4 / 3 : ℝ)) hHpos
    change (H : ℝ) * t = _ at hs
    rw [hcardreal] at hfirst
    simpa only [mul_assoc, hs] using hfirst
  · have hsecond := pivot_second_sum_bound P (fun a => a 1) (fun a => a 2)
      (fun a ha => (hcoords a ha).1) (fun a ha => (hcoords a ha).2)
    rw [hcardreal] at hsecond
    simpa [t, mul_assoc] using hsecond

open Submodule
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
noncomputable def greedyPivots
    {V : Type u_1} [AddCommGroup V] (K : Type u_2) [DivisionRing K] (v : ℕ → V)
    [Module K V] : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => by
      classical
      exact if v n ∈ span K (v '' (greedyPivots K v n : Set ℕ))
        then greedyPivots K v n else insert n (greedyPivots K v n)

theorem greedyPivots_subset_range (v : ℕ → V) (n : ℕ) :
    greedyPivots K v n ⊆ Finset.range n := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs
      · exact ih.trans (Finset.range_mono (Nat.le_succ n))
      · exact Finset.insert_subset (Finset.mem_range.mpr (Nat.lt_succ_self n))
          (ih.trans (Finset.range_mono (Nat.le_succ n)))

theorem greedyPivots_linearIndepOn (v : ℕ → V) (n : ℕ) :
    LinearIndepOn K v (greedyPivots K v n : Set ℕ) := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · exact ih
      · simpa only [Finset.coe_insert] using ih.insert h

theorem span_greedyPivots (v : ℕ → V) (n : ℕ) :
    span K (v '' (greedyPivots K v n : Set ℕ)) =
      span K (v '' (Finset.range n : Set ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · rw [Finset.range_add_one, Finset.coe_insert, Set.image_insert_eq,
          span_insert_eq_span (ih ▸ h), ih]
      · rw [Finset.coe_insert, Finset.range_add_one, Finset.coe_insert,
          Set.image_insert_eq, Set.image_insert_eq, span_insert, span_insert, ih]

theorem mem_greedyPivots_succ_self (v : ℕ → V) (n : ℕ) :
    n ∈ greedyPivots K v (n + 1) ↔
      v n ∉ span K (v '' (Finset.range n : Set ℕ)) := by
  classical
  have hn : n ∉ greedyPivots K v n := fun h =>
    (Nat.lt_irrefl n) (Finset.mem_range.mp (greedyPivots_subset_range v n h))
  rw [greedyPivots, span_greedyPivots]
  split_ifs with h
  · exact iff_of_false hn (not_not_intro h)
  · exact iff_of_true (Finset.mem_insert_self _ _) h

theorem greedyPivots_mono (v : ℕ → V) : Monotone (greedyPivots K v) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [greedyPivots]
  split_ifs
  · rfl
  · exact Finset.subset_insert _ _

theorem mem_greedyPivots_iff (v : ℕ → V) (i n : ℕ) :
    i ∈ greedyPivots K v n ↔
      i < n ∧ v i ∉ span K (v '' (Finset.range i : Set ℕ)) := by
  classical
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      by_cases hin : i < n
      · have hne : i ≠ n := Nat.ne_of_lt hin
        rw [greedyPivots]
        split_ifs
        · simpa only [hin, Nat.lt_succ_of_lt hin, true_and] using ih
        · simpa only [Finset.mem_insert, hne, false_or, hin,
            Nat.lt_succ_of_lt hin, true_and] using ih
      · by_cases hieq : i = n
        · subst i
          simpa only [Nat.lt_succ_self, true_and] using mem_greedyPivots_succ_self v n
        · have hnle : n + 1 ≤ i := by omega
          have hi : i ∉ greedyPivots K v (n + 1) := fun h =>
            (Nat.not_lt.mpr hnle)
              (Finset.mem_range.mp (greedyPivots_subset_range v (n + 1) h))
          exact iff_of_false hi (fun h => Nat.not_lt.mpr hnle h.1)

theorem card_greedyPivots (v : ℕ → V) (n : ℕ) :
    (greedyPivots K v n).card =
      Module.finrank K (span K (v '' (Finset.range n : Set ℕ))) := by
  classical
  have h := finrank_span_eq_card (greedyPivots_linearIndepOn (K := K) v n)
  rw [← Set.image_eq_range, span_greedyPivots] at h
  rw [Fintype.card_of_finset' (greedyPivots K v n) (fun _ => Iff.rfl)] at h
  exact h.symm

theorem earlier_row_mem_span_greedyPivots (v : ℕ → V) {i n : ℕ} (hi : i < n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  rw [span_greedyPivots]
  exact subset_span ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem smaller_weight_row_mem_span_greedyPivots (v : ℕ → V) (w : ℕ → ℕ)
    (hw : Monotone w) {i n : ℕ} (hi : w i < w n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  apply earlier_row_mem_span_greedyPivots
  exact lt_of_not_ge (fun h => (not_le_of_gt hi) (hw h))

theorem card_greedyPivots_of_span_eq_top (v : ℕ → V) (n : ℕ)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    (greedyPivots K v n).card = Module.finrank K V := by
  rw [card_greedyPivots, hspan, finrank_top]

theorem greedyPivots_eq_of_span_eq_top (v : ℕ → V) {n m : ℕ} (hnm : n ≤ m)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    greedyPivots K v n = greedyPivots K v m := by
  have hspanm : span K (v '' (Finset.range m : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact span_mono (Set.image_mono (Finset.range_mono hnm))
  apply Finset.eq_of_subset_of_card_le (greedyPivots_mono v hnm)
  rw [card_greedyPivots_of_span_eq_top v n hspan,
    card_greedyPivots_of_span_eq_top v m hspanm]

end WeightedTorusJets
namespace WeightedTorusJets
def extendFiniteFamily {α : Type*} {n : ℕ} (f : Fin n → α) (fallback : α) (i : ℕ) : α :=
  if hi : i < n then f ⟨i, hi⟩ else fallback

theorem image_extendFiniteFamily_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (fallback : α) :
    extendFiniteFamily f fallback '' (Finset.range n : Set ℕ) = Set.range f := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i < n := Finset.mem_range.mp hi
    exact ⟨⟨i, hin⟩, by simp [extendFiniteFamily, hin]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_range.mpr i.isLt, by simp [extendFiniteFamily, i.isLt]⟩

theorem monotone_extendFiniteFamily {α : Type*} [Preorder α] {n : ℕ}
    (f : Fin n → α) (fallback : α) (hf : Monotone f) (hb : ∀ i, f i ≤ fallback) :
    Monotone (extendFiniteFamily f fallback) := by
  intro i j hij
  simp only [extendFiniteFamily]
  split_ifs with hi hj hj
  · exact hf hij
  · exact hb _
  · exact (hi (lt_of_le_of_lt hij hj)).elim
  · exact le_rfl

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.WeightedJetIndices. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets
def weightedJetIndices (H B : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.range (B + 1))).filter
    (fun α => α 0 + H * α 1 + H * α 2 ≤ B)

theorem mem_weightedJetIndices_iff {H B : ℕ} (hH : 0 < H) (α : Fin 3 → ℕ) :
    α ∈ weightedJetIndices H B ↔ α 0 + H * α 1 + H * α 2 ≤ B := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h1 : α 1 ≤ H * α 1 := Nat.le_mul_of_pos_left _ hH
    have h2 : α 2 ≤ H * α 2 := Nat.le_mul_of_pos_left _ hH
    fin_cases i
    · change α 0 < B + 1
      omega
    · change α 1 < B + 1
      omega
    · change α 2 < B + 1
      omega

theorem extendFiniteFamily_injOn_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (hf : Function.Injective f) (fallback : α) :
    Set.InjOn (extendFiniteFamily f fallback) (Finset.range n : Set ℕ) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have heq : f ⟨i, hi'⟩ = f ⟨j, hj'⟩ := by
    simpa [extendFiniteFamily, hi', hj'] using hij
  exact congrArg Fin.val (hf heq)

noncomputable def finiteGreedyPivots (K : Type*) [DivisionRing K]
    {α V : Type*} [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α) : Finset α := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  exact (greedyPivots K (R ∘ a) s.card).image a

theorem finiteGreedyPivots_spec {K α V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α)
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    finiteGreedyPivots K s R e fallback ⊆ s ∧
      (finiteGreedyPivots K s R e fallback).card = Module.finrank K V ∧
      LinearIndepOn K R (finiteGreedyPivots K s R e fallback : Set α) ∧
      Submodule.span K (R '' (finiteGreedyPivots K s R e fallback : Set α)) = ⊤ := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let I := greedyPivots K v s.card
  have hI : I ⊆ Finset.range s.card := greedyPivots_subset_range v s.card
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvimage : v '' (Finset.range s.card : Set ℕ) = R '' (s : Set α) := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage]
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [hvimage, hspan]
  change I.image a ⊆ s ∧ (I.image a).card = _ ∧
    LinearIndepOn K R (I.image a : Set α) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    change a i ∈ (s : Set α)
    rw [← haimage]
    exact Set.mem_image_of_mem a (hI hi)
  · rw [Finset.card_image_of_injOn (hainj.mono hI)]
    exact card_greedyPivots_of_span_eq_top v s.card hvspan
  · rw [Finset.coe_image]
    exact LinearIndepOn.image_of_comp a R (greedyPivots_linearIndepOn v s.card)
  · change Submodule.span K (R '' (I.image a : Set α)) = ⊤
    rw [Finset.coe_image, ← Set.image_comp]
    exact (span_greedyPivots v s.card).trans hvspan

theorem finiteGreedyPivots_sum {K α V β : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommMonoid β]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α) (f : α → β) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∑ x ∈ finiteGreedyPivots K s R e fallback, f x =
      ∑ i ∈ greedyPivots K (R ∘ a) s.card, f (a i) := by
  classical
  dsimp only [finiteGreedyPivots]
  apply Finset.sum_image
  have hinj := extendFiniteFamily_injOn_range (fun i => (e i : α))
    (Subtype.val_injective.comp e.injective) fallback
  exact hinj.mono (greedyPivots_subset_range _ _)

theorem sum_embedding_eq_sum_of_range {β : Type*} [AddCommMonoid β]
    (I : Finset ℕ) (m : ℕ) (e : Fin m ↪ ℕ) (he : Set.range e = (I : Set ℕ))
    (f : ℕ → β) : (∑ i : Fin m, f (e i)) = ∑ i ∈ I, f i := by
  apply Finset.sum_bij (fun i _ => e i)
  · intro i _
    change e i ∈ (I : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    have hj' : j ∈ Set.range e := he ▸ hj
    obtain ⟨i, rfl⟩ := hj'
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl

theorem weightedJetIndices_real_weight {H : ℕ} (hH : 0 < H) {W : ℝ}
    (hW : 0 ≤ W) {a : Fin 3 → ℕ} (ha : a ∈ weightedJetIndices H ⌊W⌋₊) :
    (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ W := by
  have hnat := (mem_weightedJetIndices_iff hH a).mp ha
  have hreal : (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤ (⌊W⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (Nat.floor_le hW)

theorem mem_weightedJetIndices_of_rectangle {H : ℕ} {U : ℝ} (hH : 0 < H)
    (a : Fin 3 → ℕ)
    (ha₀ : (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U)
    (ha₁ : (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U)
    (ha₂ : (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U) :
    a ∈ weightedJetIndices H ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ := by
  apply (mem_weightedJetIndices_iff hH a).mpr
  apply Nat.le_floor
  push_cast
  exact pivot_weight_of_rectangle (by exact_mod_cast hH) (a 0) (a 1) (a 2) ha₀ ha₁ ha₂

theorem span_cutoff_eq_top_of_rectangle {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {H : ℕ} {U : ℝ} (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * U ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U}) = ⊤) :
    Submodule.span K (R '' (weightedJetIndices H
      ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * U⌋₊ : Set (Fin 3 → ℕ))) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  apply Set.image_mono
  intro a ha
  exact mem_weightedJetIndices_of_rectangle hH a ha.1 ha.2.1 ha.2.2

end WeightedTorusJets
open Module
open scoped BigOperators
namespace WeightedTorusJets
theorem det_ne_zero_of_linearIndepOn_rows
    {K ι n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (s : Finset ι) (R : ι → n → K) (e : n ≃ s)
    (hlin : LinearIndepOn K R (s : Set ι)) :
    Matrix.det (fun i j => R (e i) j) ≠ 0 := by
  classical
  have hrows : LinearIndependent K (fun i j => R (e i) j) :=
    hlin.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

theorem finite_weighted_greedy_package {K α : Type*} [Field K] {M : ℕ}
    (s : Finset α) (R : α → Fin M → K) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    let v := R ∘ a
    let wt := extendFiniteFamily (fun i => w (e i)) B
    let P := finiteGreedyPivots K s R e fallback
    ∃ (g : Fin M ↪o ℕ) (p : Fin M ↪ α),
      Set.range g = (greedyPivots K v s.card : Set ℕ) ∧
      (∀ i, p i = a (g i)) ∧ Set.range p = (P : Set α) ∧
      Monotone wt ∧ Monotone (fun i => w (p i)) ∧
      (∀ i, g i < s.card) ∧
      (∀ r < s.card, wt r = w (a r)) ∧
      (∀ i, v (g i) = R (p i) ∧ wt (g i) = w (p i) ∧ w (p i) ≤ B) ∧
      (∀ b, w b ≤ B → ∃ r < s.card, a r = b ∧ wt r = w b ∧ v r = R b) ∧
      Matrix.det (fun i j => R (p i) j) ≠ 0 ∧ P.card = M ∧
      (∀ (β : Type) [AddCommMonoid β] (F : α → β),
        (∑ i, F (p i)) = ∑ b ∈ P, F b) := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  let G := greedyPivots K v s.card
  have haimage : a '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
    rw [show a = extendFiniteFamily (fun i => (e i : α)) fallback from rfl,
      image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  have hvspan : Submodule.span K (v '' (Finset.range s.card : Set ℕ)) = ⊤ := by
    rw [show v = R ∘ a from rfl, Set.image_comp, haimage, hspan]
  have hcard : G.card = M := by
    simpa [G] using card_greedyPivots_of_span_eq_top v s.card hvspan
  let g := G.orderEmbOfFin hcard
  have hg : Set.range g = (G : Set ℕ) := G.range_orderEmbOfFin hcard
  have hgT : ∀ i, g i < s.card := fun i =>
    Finset.mem_range.mp (greedyPivots_subset_range v s.card
      (G.orderEmbOfFin_mem hcard i))
  have hainj : Set.InjOn a (Finset.range s.card : Set ℕ) :=
    extendFiniteFamily_injOn_range _ (Subtype.val_injective.comp e.injective) fallback
  let p : Fin M ↪ α := ⟨a ∘ g, fun i j hij => g.injective
    (hainj (Finset.mem_range.mpr (hgT i)) (Finset.mem_range.mpr (hgT j)) hij)⟩
  have hpe : ∀ i, p i = (e ⟨g i, hgT i⟩ : α) := by
    intro i
    change a (g i) = _
    simp only [a, extendFiniteFamily, dite_eq_left (hgT i)]
  have hpbound : ∀ i, w (p i) ≤ B := by
    intro i
    rw [hpe i]
    exact (hs _).mp (e ⟨g i, hgT i⟩).property
  have hpmono : Monotone (fun i => w (p i)) := by
    intro i j hij
    change w (p i) ≤ w (p j)
    rw [hpe i, hpe j]
    exact hsort (show (⟨g i, hgT i⟩ : Fin s.card) ≤ ⟨g j, hgT j⟩ from g.monotone hij)
  refine ⟨g, p, hg, fun _ => rfl, ?_, ?_, hpmono, hgT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Set.range (a ∘ g) = ((greedyPivots K v s.card).image a : Set α)
    rw [Set.range_comp, hg, Finset.coe_image]
  · exact monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
  · intro r hr
    simp [extendFiniteFamily, hr]
  · intro i
    refine ⟨rfl, ?_, hpbound i⟩
    rw [hpe i]
    simp only [extendFiniteFamily, dite_eq_left (hgT i)]
  · intro b hb
    let r : Fin s.card := e.symm ⟨b, (hs b).mpr hb⟩
    refine ⟨r, r.isLt, ?_, ?_, ?_⟩
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
    · simp [extendFiniteFamily, r.isLt, r]
  · exact det_ne_zero_of_linearIndepOn_rows G v (G.orderIsoOfFin hcard).toEquiv
      (greedyPivots_linearIndepOn v s.card)
  · simpa using (finiteGreedyPivots_spec s R e fallback hspan).2.1
  · intro β _ F
    rw [finiteGreedyPivots_sum]
    exact sum_embedding_eq_sum_of_range G M g.toEmbedding hg (F ∘ a)

open Submodule
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
theorem greedyPivots_filter_lt (v : ℕ → V) (n r : ℕ) (hrn : r ≤ n) :
    (greedyPivots K v n).filter (fun j => j < r) = greedyPivots K v r := by
  classical
  ext j
  simp only [Finset.mem_filter, mem_greedyPivots_iff]
  constructor
  · rintro ⟨⟨_, hind⟩, hjr⟩
    exact ⟨hjr, hind⟩
  · rintro ⟨hjr, hind⟩
    exact ⟨⟨hjr.trans_le hrn, hind⟩, hjr⟩

theorem span_greedyPivots_eq_span_earlier_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ)) (i : ι) :
    span K (v '' (greedyPivots K v (e i) : Set ℕ)) =
      span K ((v ∘ e) '' {j | j < i}) := by
  have hei : e i ∈ greedyPivots K v n := by
    change e i ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self i
  have hein : e i ≤ n :=
    (Finset.mem_range.mp (greedyPivots_subset_range v n hei)).le
  rw [← greedyPivots_filter_lt v n (e i) hein]
  congr 1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hr, hri⟩ := Finset.mem_filter.mp hr
    have hrange : r ∈ Set.range e := by rwa [he]
    obtain ⟨j, rfl⟩ := hrange
    exact ⟨j, e.lt_iff_lt.mp hri, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨e j, Finset.mem_filter.mpr ⟨?_, e.strictMono hj⟩, rfl⟩
    change e j ∈ (greedyPivots K v n : Set ℕ)
    rw [← he]
    exact Set.mem_range_self j

theorem smaller_weight_mem_span_earlier_retained_rows {ι : Type*} [LinearOrder ι]
    (v : ℕ → V) (w : ℕ → ℕ) (hw : Monotone w) (n : ℕ) (e : ι ↪o ℕ)
    (he : Set.range e = (greedyPivots K v n : Set ℕ))
    (rows : ι → V) (hrows : rows = v ∘ e) (i : ι) (r : ℕ)
    (hr : w r < w (e i)) :
    v r ∈ span K (rows '' {j | j < i}) := by
  rw [hrows, ← span_greedyPivots_eq_span_earlier_rows v n e he i]
  exact smaller_weight_row_mem_span_greedyPivots v w hw hr

end WeightedTorusJets
namespace WeightedTorusJets
theorem jet_weight_ball_span_eq_top {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2) ''
        (weightedJetIndices H (M - 1) : Set (Fin 3 → ℕ))) = ⊤ := by
  classical
  let V : Matrix (Fin M) (Fin M) K := (Matrix.vandermonde θ).transpose
  have hdet : V.det ≠ 0 := by
    simpa only [V, Matrix.det_transpose] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hθ)
  have hspan : Submodule.span K (Set.range V) = ⊤ :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet).span_eq_top_of_card_eq_finrank'
      (by simp)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  refine ⟨![k.val, 0, 0], ?_, ?_⟩
  · apply (mem_weightedJetIndices_iff hH _).mpr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.mul_zero, Nat.add_zero]
    omega
  · funext j
    simp [V, Matrix.vandermonde_apply]

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.RestrictWeightSortedEquiv. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
namespace WeightedTorusJets
theorem basis_nat_sum_injective {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) := by
  intro n m h
  funext i
  have hi := congrArg (fun v => b.repr v i) h
  simp only [Basis.repr_sum_self] at hi
  exact_mod_cast hi

theorem basis_nat_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) :
    Function.Injective (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
  have h : (fun n : ι → ℕ => ∑ i, (n i : ℚ) • b i) =
      (fun n : ι → ℕ => ∑ i, (n i : K) * b i) := by
    funext n
    simp [Algebra.smul_def]
  rw [← h]
  exact basis_nat_sum_injective b

theorem basis_fin_sum_mul_injective {ι K : Type*} [Fintype ι]
    [CommRing K] [Algebra ℚ K] (b : Basis ι ℚ K) (N : ℕ) :
    Function.Injective (fun n : ι → Fin N => ∑ i, ((n i : ℕ) : K) * b i) := by
  intro n m h
  have hcoords := basis_nat_sum_mul_injective b h
  funext i
  exact Fin.ext (congrFun hcoords i)

theorem exists_first_greedy_jet_rows_of_sorted_enumeration {K : Type*} [Field K] {M : ℕ}
    (θ y z : Fin M → K) (hθ : Function.Injective θ) (H : ℕ) (hH : 0 < H) :
    let s := weightedJetIndices H (M - 1)
    let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
    let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
    ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
      let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
      ∃ (g : Fin M ↪o ℕ) (α : Fin M ↪ (Fin 3 → ℕ)),
        Set.range g = (greedyPivots K (R ∘ β) s.card : Set ℕ) ∧
        (∀ i, α i = β (g i)) ∧
        Set.range α = (finiteGreedyPivots K s R e 0 : Set (Fin 3 → ℕ)) ∧
        Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ M - 1) ∧
        (∀ i a b c, a + H * b + H * c < w (α i) →
          (fun j => θ j ^ a * y j ^ b * z j ^ c) ∈
            Submodule.span K ((R ∘ α) '' {j | j < i})) ∧
        Matrix.det (fun i j => R (α i) j) ≠ 0 := by
  classical
  dsimp only
  let s := weightedJetIndices H (M - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  let R := fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * y j ^ α 1 * z j ^ α 2
  intro e he
  have hs : ∀ α, α ∈ s ↔ w α ≤ M - 1 := mem_weightedJetIndices_iff hH
  obtain ⟨g, α, hg, hα, hrange, hmono, hαmono, hlt, hprefix,
    hselected, hcoverage, hdet, hcard, hsum⟩ :=
    finite_weighted_greedy_package s R e 0 w (M - 1) hs he
      (jet_weight_ball_span_eq_top θ y z hθ H hH)
  refine ⟨g, α, hg, hα, hrange, hαmono,
    fun i => (hselected i).2.2, ?_, hdet⟩
  intro i a b c hweight
  have habc : w ![a, b, c] ≤ M - 1 :=
    Nat.le_trans (Nat.le_of_lt hweight) (hselected i).2.2
  obtain ⟨r, _, _, hwr, hvr⟩ := hcoverage ![a, b, c] habc
  have hrows : R ∘ α = (R ∘ extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0) ∘ g := by
    funext j
    exact (hselected j).1.symm
  have hstrict : (extendFiniteFamily (fun j => w (e j)) (M - 1)) r <
      (extendFiniteFamily (fun j => w (e j)) (M - 1)) (g i) := by
    rw [hwr, (hselected i).2.1]
    exact hweight
  have hmem := smaller_weight_mem_span_earlier_retained_rows _ _ hmono s.card g hg
    (R ∘ α) hrows i r hstrict
  rw [hvr] at hmem
  simpa only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] using hmem

open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_character_fixed_greedy_determinant_divisibility_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) →
                let β := extendFiniteFamily (fun i => (e i : Fin 3 → ℕ)) 0
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ β) s.card : Set ℕ) ∧
                  (∀ i, α i = β (g i)) ∧
                  Set.range α = (finiteGreedyPivots B s R e 0 : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hFrob⟩ :=
    source_biquadratic_arithmetic_canonical_of_field_ne q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hspan, hdet⟩ :=
    exists_first_greedy_jet_rows_of_sorted_enumeration
      θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, ?_⟩
  have ha' : a' ^ 2 = (d : B) := by
    apply Subtype.ext
    exact ha
  have hb' : b' ^ 2 = (2 : B) := by
    apply Subtype.ext
    exact hb
  obtain ⟨Δ, hΔ, hneΔ, hdiv⟩ := exists_integral_jet_determinant_divisible
    σ.toRingHom τ.toRingHom ha' hb' (fun j i => (n j i : ℕ)) α H hspan hdet
  refine ⟨Δ, hΔ, hneΔ, ?_⟩
  intro p hp hHp hpq hχp
  exact hdiv p hHp (frobenius_action_choice_quotient σ τ p (hFrob p hp hpq hχp))

end WeightedTorusJets
namespace WeightedTorusJets
theorem greedyPivots_congr_prefix {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v v' : ℕ → V) (n : ℕ)
    (h : ∀ i < n, v i = v' i) : greedyPivots K v n = greedyPivots K v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      have hprevious := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast := h n (Nat.lt_succ_self n)
      have himage : v '' (greedyPivots K v' n : Set ℕ) =
          v' '' (greedyPivots K v' n : Set ℕ) := by
        apply Set.image_congr
        intro i hi
        exact h i (Nat.lt_succ_of_lt
          (Finset.mem_range.mp (greedyPivots_subset_range v' n hi)))
      simp only [greedyPivots, hprevious, hlast, himage]

theorem weight_sorted_equiv_mem_iff_lt_card {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : ℕ) :
    e i ∈ s ↔ i < s.card := by
  classical
  let t := s.map e.symm.toEmbedding
  have htmem : ∀ j, j ∈ t ↔ e j ∈ s := fun j => Finset.mem_map_equiv
  have htcard : t.card = s.card := Finset.card_map _
  have hsub : t ⊆ Finset.range s.card := by
    intro j hj
    have hlow : Finset.range (j + 1) ⊆ t := by
      intro k hk
      apply (htmem k).mpr
      apply (hs _).mpr
      exact (he (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans
        ((hs _).mp ((htmem j).mp hj))
    have hcard := Finset.card_le_card hlow
    rw [Finset.card_range, htcard] at hcard
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le hcard)
  have ht : t = Finset.range s.card :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, htcard])
  rw [← htmem, ht, Finset.mem_range]

noncomputable def restrictWeightSortedEquiv {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) : Fin s.card ≃ s where
  toFun i := ⟨e i, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr i.isLt⟩
  invFun a := ⟨e.symm a, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    (by rw [e.apply_symm_apply]; exact a.property)⟩
  left_inv i := Fin.ext (e.symm_apply_apply i)
  right_inv a := Subtype.ext (e.apply_symm_apply a)

theorem restrictWeightSortedEquiv_apply {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : Fin s.card) :
    (restrictWeightSortedEquiv s w B hs e he i : α) = e i := rfl

theorem restrictWeightSortedEquiv_monotone {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    Monotone (fun i => w (restrictWeightSortedEquiv s w B hs e he i)) := by
  intro i j hij
  exact he hij

theorem extend_restrictWeightSortedEquiv_eq {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (fallback : α)
    (i : ℕ) (hi : i < s.card) :
    extendFiniteFamily (fun j => (restrictWeightSortedEquiv s w B hs e he j : α))
      fallback i = e i := by
  simp only [extendFiniteFamily, dite_eq_left hi, restrictWeightSortedEquiv_apply]

theorem greedyPivots_restrictWeightSortedEquiv {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    greedyPivots K
      (R ∘ extendFiniteFamily
        (fun j => (restrictWeightSortedEquiv s w B hs e he j : α)) fallback) s.card =
      greedyPivots K (R ∘ e) s.card := by
  apply greedyPivots_congr_prefix
  intro i hi
  exact congrArg R (extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i hi)

theorem weight_sorted_equiv_image_range {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) :
    e '' (Finset.range s.card : Set ℕ) = (s : Set α) := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr
      (Finset.mem_range.mp hi)
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    apply Finset.mem_range.mpr
    apply (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    simpa using ha

theorem span_global_weight_cutoff_eq_top {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i)))
    (hspan : Submodule.span K (R '' (s : Set α)) = ⊤) :
    Submodule.span K ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ := by
  rw [Set.image_comp, weight_sorted_equiv_image_range s w B hs e he]
  exact hspan

open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_character_global_greedy_determinant_divisibility (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_fixed_greedy_determinant_divisibility_of_field_ne
      q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH n
  dsimp only
  intro e he
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun α : Fin 3 → ℕ => fun j =>
    θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
  have hs : ∀ α, α ∈ s ↔ w α ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have he₀ : Monotone (fun i => w (e₀ i)) :=
    restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he
  obtain ⟨g, α, hg, hα, _, hmono, hweight, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e₀ he₀
  have hgGlobal : Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) :=
    hg.trans (congrArg (fun t : Finset ℕ => (t : Set ℕ))
      (greedyPivots_restrictWeightSortedEquiv s R w (N ^ 4 - 1) hs e he 0))
  have hαGlobal : ∀ i, α i = e (g i) := by
    intro i
    have hi : g i ∈ greedyPivots B (R ∘ e) s.card := by
      change g i ∈ (greedyPivots B (R ∘ e) s.card : Set ℕ)
      rw [← hgGlobal]
      exact Set.mem_range_self i
    have hiT := Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi)
    exact (hα i).trans
      (extend_restrictWeightSortedEquiv_eq s w (N ^ 4 - 1) hs e he 0 (g i) hiT)
  have hθ : Function.Injective θ := by
    have hinj := (basis_fin_sum_mul_injective v N).comp n.injective
    simpa only [Function.comp_def, hv, θ, a', b'] using hinj
  have hball : Submodule.span B (R '' (s : Set (Fin 3 → ℕ))) = ⊤ :=
    jet_weight_ball_span_eq_top θ (σ ∘ θ) ((σ * τ) ∘ θ) hθ H hH
  have hspan : Submodule.span B ((R ∘ e) '' (Finset.range s.card : Set ℕ)) = ⊤ :=
    span_global_weight_cutoff_eq_top s R w (N ^ 4 - 1) hs e he hball
  refine ⟨g, α, hgGlobal, hαGlobal, ?_, hmono, hweight, ?_, Δ, hΔ, hneΔ, hdiv⟩
  · rw [show (α : Fin (N ^ 4) → Fin 3 → ℕ) = e ∘ g from funext hαGlobal,
      Set.range_comp, hgGlobal, Finset.coe_image]
  · intro t ht
    exact hgGlobal.trans (congrArg (fun u : Finset ℕ => (u : Set ℕ))
      (greedyPivots_eq_of_span_eq_top (R ∘ e) ht hspan))

end WeightedTorusJets
open scoped BigOperators
open InnerProductSpace
namespace SiegelJets
theorem norm_det_le_prod_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (A i)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let b := gramSchmidtOrthonormalBasis hdim v
  have hchange : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    have h := congrArg (fun f : (EuclideanSpace ℂ (Fin n)) [⋀^Fin n]→ₗ[ℂ] ℂ => f v)
      (e.toBasis.det.eq_smul_basis_det b.toBasis)
    simpa using h
  have hnorm : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    rw [hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  have hdet : e.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr
  rw [← hdet, hnorm]
  change ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖
  rw [show b.toBasis.det v = ∏ i, inner ℂ (b i) (v i) from
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
    simpa using norm_inner_le_norm (b i) (v i)

theorem norm_det_le_of_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    ‖A.det‖ ≤ (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
  have hrow (i : Fin n) :
      ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ ≤
        Real.sqrt n * B ^ d i := by
    rw [EuclideanSpace.norm_eq]
    calc
      Real.sqrt (∑ j, ‖A i j‖ ^ 2) ≤ Real.sqrt (∑ _ : Fin n, (B ^ d i) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = Real.sqrt n * B ^ d i := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (pow_nonneg hB _)]
  calc
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ :=
      norm_det_le_prod_norm A
    _ ≤ ∏ i, (Real.sqrt n * B ^ d i) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hrow i)
    _ = (Real.sqrt n) ^ n * B ^ (∑ i, d i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp

theorem log_norm_det_le_of_entry_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdet : A.det ≠ 0)
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 < B)
    (hA : ∀ i j, ‖A i j‖ ≤ B ^ d i) :
    Real.log ‖A.det‖ ≤ (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    Real.log ‖A.det‖ ≤ Real.log ((Real.sqrt n) ^ n * B ^ (∑ i, d i)) :=
      Real.log_le_log (norm_pos_iff.mpr hdet) (norm_det_le_of_entry_bound A d hB.le hA)
    _ = (n : ℝ) / 2 * Real.log n + (∑ i, d i : ℕ) * Real.log B := by
      rw [Real.log_mul (pow_ne_zero _ (Real.sqrt_pos.mpr hn').ne')
        (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_pow,
        Real.log_sqrt hn'.le]
      ring

theorem log_norm_det_archimedean {m N q : ℕ} (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (A : Matrix (Fin m) (Fin m) ℂ) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖A i j‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hB : (0 : ℝ) < 8 * N * Real.sqrt q := by positivity
  have hlog : Real.log (8 * N * Real.sqrt q) =
      Real.log N + 1 / 2 * Real.log q + Real.log 8 := by
    rw [Real.log_mul (mul_pos (by norm_num) hN').ne' (Real.sqrt_pos.mpr hq').ne',
      Real.log_mul (by norm_num) hN'.ne', Real.log_sqrt hq'.le]
    ring
  simpa only [hlog] using log_norm_det_le_of_entry_bound hm A hdet d hB hA

theorem log_norm_map_det_archimedean {K : Type*} [Field K] {m N q : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hq : 0 < q)
    (ν : K →+* ℂ) (A : Matrix (Fin m) (Fin m) K) (hdet : A.det ≠ 0)
    (d : Fin m → ℕ)
    (hA : ∀ i j, ‖ν (A i j)‖ ≤ (8 * N * Real.sqrt q) ^ d i) :
    Real.log ‖ν A.det‖ ≤ (m : ℝ) / 2 * Real.log m +
      (∑ i, d i : ℕ) * (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  have hmapped : (ν.mapMatrix A).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero ν).mpr hdet
  simpa only [← RingHom.map_det] using
    log_norm_det_archimedean hm hN hq (ν.mapMatrix A) hmapped d hA

end SiegelJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Determinants.NormSqReal. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace
namespace WeightedTorusJets
theorem norm_of_sq_eq_real {z : ℂ} {r : ℝ} (hz : z ^ 2 = (r : ℂ)) :
    ‖z‖ = Real.sqrt |r| := by
  rw [← Real.sqrt_sq (norm_nonneg z), ← norm_pow, hz, Complex.norm_real, Real.norm_eq_abs]

theorem norm_biquadratic_box_le {a b : ℂ} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n₁ n₂ n₃ n₄ : ℕ) (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N)
    (hn₃ : n₃ ≤ N) (hn₄ : n₄ ≤ N) :
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
      8 * N * Real.sqrt q := by
  have hna : ‖a‖ ≤ Real.sqrt q := by
    rw [norm_of_sq_eq_real (r := (d : ℝ)) (by simpa using ha)]
    exact Real.sqrt_le_sqrt hd
  have hnb : ‖b‖ ≤ 2 := by
    rw [norm_of_sq_eq_real (r := 2) (by simpa using hb), Real.sqrt_le_iff]
    norm_num
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt q := (Real.one_le_sqrt).mpr hq'
  have hnN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hab : ‖a * b‖ ≤ 2 * Real.sqrt q := by
    simpa only [mul_comm] using norm_mul_le_of_le hna hnb
  calc
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
        ‖(n₁ : ℂ)‖ + ‖(n₂ : ℂ) * a‖ + ‖(n₃ : ℂ) * b‖ +
          ‖(n₄ : ℂ) * (a * b)‖ := norm_add₄_le
    _ = n₁ + n₂ * ‖a‖ + n₃ * ‖b‖ + n₄ * ‖a * b‖ := by simp
    _ ≤ N + N * Real.sqrt q + N * 2 + N * (2 * Real.sqrt q) := by
      gcongr
    _ ≤ 8 * N * Real.sqrt q := by nlinarith [mul_le_mul_of_nonneg_left hsq hnN]

theorem norm_embedding_biquadratic_box_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν ((n 0 : K) + n 1 * a + n 2 * b + n 3 * (a * b))‖ ≤
      8 * N * Real.sqrt q := by
  simp only [map_add, map_mul, map_natCast]
  refine norm_biquadratic_box_le ?_ ?_ hd hq _ _ _ _
    (hn 0).le (hn 1).le (hn 2).le (hn 3).le
  · simpa using congrArg ν ha
  · simpa only [map_pow, map_ofNat] using congrArg ν hb

theorem norm_three_powers_le {x y z : ℂ} {B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ B)
    (i j k : ℕ) : ‖x ^ i * y ^ j * z ^ k‖ ≤ B ^ (i + j + k) := by
  have hB : 0 ≤ B := (norm_nonneg x).trans hx
  simp only [norm_mul, norm_pow, pow_add]
  gcongr

theorem norm_embedding_basis_sum_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν (∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i)‖ ≤
      8 * N * Real.sqrt q := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    norm_embedding_biquadratic_box_le ν ha hb hd hq n hn

theorem norm_embedding_derivative_entry_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) (α : Fin 3 → ℕ) :
    let θ := ∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i
    ‖ν (θ ^ (α 0) * σ θ ^ (α 1) * (σ.comp τ) θ ^ (α 2))‖ ≤
      (8 * N * Real.sqrt q) ^ (α 0 + α 1 + α 2) := by
  dsimp only
  simp only [map_mul, map_pow]
  apply norm_three_powers_le
  · exact norm_embedding_basis_sum_le ν ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp σ) ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp (σ.comp τ)) ha hb hd hq n hn

end WeightedTorusJets
open Finset
namespace WeightedTorusJets
variable {K : Type*} [Field K] [NumberField K]
theorem abs_field_norm_eq_prod_embeddings (a : K) :
    |(Algebra.norm ℚ a : ℝ)| = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ a‖ := by
  simpa only [eq_ratCast, Complex.norm_ratCast, norm_prod] using
    congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)

theorem log_abs_field_norm_eq_sum_embeddings {a : K} (ha : a ≠ 0) :
    Real.log |(Algebra.norm ℚ a : ℝ)| =
      ∑ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ := by
  rw [abs_field_norm_eq_prod_embeddings, Real.log_prod]
  simp [ha]

theorem quarter_log_field_norm_le_of_embeddings {a : K} (ha : a ≠ 0)
    (hdegree : Module.finrank ℚ K = 4) {B : ℝ}
    (hbound : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ ≤ B) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ a : ℝ)| ≤ B := by
  rw [log_abs_field_norm_eq_sum_embeddings ha]
  have hsum := Finset.sum_le_card_nsmul Finset.univ _ B (fun σ _ ↦ hbound σ)
  simp only [Finset.card_univ, AlgHom.card, hdegree, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

end WeightedTorusJets
namespace WeightedTorusJets
theorem archimedean_jet_determinant_bound {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    A.det ≠ 0 →
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤
      ((N ^ 4 : ℕ) : ℝ) / 2 * Real.log (N ^ 4 : ℕ) +
        ((∑ i, α i 0 : ℕ) + (∑ i, (α i 1 + α i 2) : ℕ)) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  dsimp only
  intro hdet
  apply quarter_log_field_norm_le_of_embeddings hdet hdegree
  intro ν
  convert SiegelJets.log_norm_map_det_archimedean (pow_pos hN 4) hN
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hq) ν.toRingHom _ hdet
    (fun i => α i 0 + α i 1 + α i 2)
    (fun i j => norm_embedding_derivative_entry_le ν.toRingHom σ τ ha hb hd hq
      (n j) (hn j) (α i)) using 1
  simp only [Finset.sum_add_distrib, Nat.cast_add, add_assoc]

open scoped NumberField BigOperators
theorem archimedean_bound_of_integral_jet_determinant {K : Type*}
    [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) (Δ : 𝓞 K) (hne : Δ ≠ 0)
    (hΔ : (Δ : K) =
      Matrix.det (fun i j =>
        (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 0 *
        σ (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 1 *
        (σ.comp τ) (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 2)) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| ≤
      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  let A : Matrix (Fin (N ^ 4)) (Fin (N ^ 4)) K :=
    Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 * (σ.comp τ) (θ j) ^ α i 2
  change (Δ : K) = A.det at hΔ
  have hcast : (Δ : K) ≠ 0 := fun h => hne (Subtype.ext h)
  have hdet : A.det ≠ 0 := hΔ ▸ hcast
  have hbound := archimedean_jet_determinant_bound hdegree σ τ ha hb hd hq hN n hn α hdet
  change (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤ _ at hbound
  rw [← hΔ] at hbound
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_add] using hbound

end WeightedTorusJets
open scoped BigOperators NumberField
namespace WeightedTorusJets
theorem quarter_log_field_norm_lower {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (x : 𝓞 K) (hx : x ≠ 0)
    (P : Finset ℕ) (E : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p ∈ P, (p : 𝓞 K) ^ E p ∣ x) :
    ∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (x : K) : ℝ)| := by
  have hd : (∏ p ∈ P, (p : ℤ) ^ (4 * E p)) ∣ Algebra.norm ℤ x := by
    apply Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hpm q hqm hpq
      exact ((Nat.coprime_primes (hp p hpm) (hp q hqm)).mpr hpq).isCoprime.pow
    · intro p hpm
      simpa [map_pow, Algebra.norm_natCast, NumberField.RingOfIntegers.rank,
        hdegree, ← pow_mul] using map_dvd (Algebra.norm ℤ) (hdvd p hpm)
  have hle : (∏ p ∈ P, p ^ (4 * E p)) ≤ (Algebra.norm ℤ x).natAbs := by
    simpa only [← Nat.cast_pow, ← Nat.cast_prod, Int.natAbs_natCast] using
      Int.natAbs_le_of_dvd_ne_zero hd (Algebra.norm_ne_zero_iff.mpr hx)
  have hpos : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) ^ (4 * E p) :=
    Finset.prod_pos fun p hpm => pow_pos (by exact_mod_cast (hp p hpm).pos) _
  have hlog := Real.log_le_log (y := ((Algebra.norm ℤ x).natAbs : ℝ)) hpos
    (by exact_mod_cast hle)
  rw [Real.log_prod (fun p hpm => pow_ne_zero _
    (by exact_mod_cast (hp p hpm).ne_zero))] at hlog
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    ← Finset.mul_sum] at hlog
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  linarith

theorem prime_floor_sum_lower_raw {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (U : ℝ) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p := by
  have hlog : (∑ p ∈ P, Real.log p) ≤ ∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => Real.log_natCast_nonneg p)
  calc
    _ ≤ (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ P, Real.log p) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card)) _
    _ = ∑ p ∈ P, ((∑ i ∈ s, (a i : ℝ)) / p - s.card) * Real.log p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
      have h := Finset.sum_le_sum (s := s)
        (fun i _ => (Nat.sub_one_lt_floor ((a i : ℝ) / p)).le)
      simpa [Finset.sum_sub_distrib, ← Finset.sum_div, Nat.floor_div_eq_div] using h

theorem finite_place_raw_norm_bounds {K ι : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (s : Finset ι) (a : ι → ℕ) (U : ℝ) (P : Finset ℕ)
    (hP : P ⊆ Nat.primesLE ⌊U⌋₊)
    (hdiv : ∀ p ∈ P, (p : 𝓞 K) ^ (∑ i ∈ s, a i / p) ∣ Δ) :
    (∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    ((∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p) :=
  ⟨quarter_log_field_norm_lower hdegree Δ hΔ P (fun p => ∑ i ∈ s, a i / p)
      (fun _ hp => Nat.prime_of_mem_primesLE (hP hp)) hdiv,
    prime_floor_sum_lower_raw s a U P hP⟩

theorem prime_floor_sum_lower {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {U : ℝ} (hU : 0 ≤ U) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        Real.log 4 * s.card * U ≤
      ∑ p ∈ P, (∑ i ∈ s, ((a i / p : ℕ) : ℝ)) * Real.log p := by
  have hlog : (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤ Real.log 4 * U := by
    rw [← Chebyshev.theta_eq_sum_primesLE]
    exact Chebyshev.theta_le_log4_mul_x hU
  have hraw := prime_floor_sum_lower_raw s a U P hP
  simp only [Nat.cast_sum] at hraw
  apply le_trans _ hraw
  apply sub_le_sub_left
  convert mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card) using 1
  ring

open scoped BigOperators NumberField
theorem finite_place_bounds_of_source_determinant {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) {m : ℕ}
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0) (α : Fin m → Fin 3 → ℕ)
    (q H : ℕ) (χ : ℕ → ℂ)
    (hdiv : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ p = -1 →
      Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p))
    (U : ℝ) (hU : 0 ≤ U) :
    let P := (Nat.primesLE ⌊U⌋₊).filter
      (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
    let E := fun p => ∑ i, α i 0 / p
    let S₁ := ∑ i, (α i 0 : ℝ)
    (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
      (m : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
        ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) - Real.log 4 * m * U ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) := by
  dsimp only
  let P := (Nat.primesLE ⌊U⌋₊).filter
    (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
  have hdiv' (p : ℕ) (hp : p ∈ P) : (p : 𝓞 K) ^ (∑ i, α i 0 / p) ∣ Δ := by
    obtain ⟨hpprime, hH, hpq, hχ⟩ := Finset.mem_filter.mp hp
    simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using
      hdiv p (Nat.prime_of_mem_primesLE hpprime) hH hpq hχ
  have hraw := finite_place_raw_norm_bounds hdegree Δ hΔ Finset.univ
    (fun i => α i 0) U P (Finset.filter_subset _ _) hdiv'
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  refine ⟨hraw.1, hraw.2, ?_⟩
  have hcheb := prime_floor_sum_lower Finset.univ (fun i => α i 0)
    hU P (Finset.filter_subset _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hcheb
  exact hcheb.trans (by simpa only [Nat.cast_sum] using hraw.1)

end WeightedTorusJets
namespace WeightedTorusJets
open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_character_global_greedy_determinant_local_bounds (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    ∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) := by
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_global_greedy_determinant_divisibility q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, ?_, hdiv, ?_⟩
  · let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
    have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
    have hdreal : |(d : ℝ)| ≤ q := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        (show (d.natAbs : ℝ) ≤ q from Nat.cast_le.mpr hbound)
    exact archimedean_bound_of_integral_jet_determinant hdegree σ.toRingHom τ.toRingHom
      ha' hb' hdreal (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (hH.trans_le hHN)
      (fun j i => (n j i : ℕ)) (fun j i => (n j i).isLt) α Δ hneΔ hΔ

  · intro U hU
    simpa only [Nat.cast_pow] using finite_place_bounds_of_source_determinant hdegree
      Δ hneΔ α q H (fun p => χ p) hdiv U hU

end WeightedTorusJets
namespace WeightedTorusJets
open scoped BigOperators NumberField
theorem finite_place_lower_of_source_determinant {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) {m : ℕ}
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0) (α : Fin m → Fin 3 → ℕ)
    (q H : ℕ) (χ : ℕ → ℂ)
    (hdiv : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ p = -1 →
      Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p))
    {U C ell delta CH : ℝ} (hU : 0 ≤ U) (hC : Real.log 4 ≤ C)
    (hbias : Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH ≤
      ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1), Real.log p / (p : ℝ)) :
    (∑ i, (α i 0 : ℝ)) *
        (Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH) -
      C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  have hbound := (finite_place_bounds_of_source_determinant
    hdegree Δ hΔ α q H χ hdiv U hU).2.2
  refine le_trans ?_ hbound
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left hbias (Finset.sum_nonneg fun i _ => Nat.cast_nonneg (α i 0)))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg m)) hU)

theorem three_le_level_of_nonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : 3 ≤ q := by
  by_contra hq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hsmall : q = 1 ∨ q = 2 := by omega
  rcases hsmall with rfl | rfl
  · exact hne (DirichletCharacter.level_one χ)
  · apply hne
    apply MulChar.eq_one_iff.mpr
    intro u
    rw [(by decide : ∀ u : (ZMod 2)ˣ, u = 1) u]
    simp

end WeightedTorusJets
namespace WeightedTorusJets
open scoped BigOperators NumberField
theorem source_given_determinant_finite_lower_of_real_zero :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ x : ZMod q, (χ x).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K = 4 →
        ∀ (m : ℕ) (Δ : 𝓞 K), Δ ≠ 0 → ∀ α : Fin m → Fin 3 → ℕ,
          (∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ (p : ZMod q) = -1 →
            Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p)) →
        ∀ U : ℝ, 0 ≤ U →
          (∑ i, (α i 0 : ℝ)) *
              (Real.log U - C * Real.log q -
                C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH) -
            C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  obtain ⟨C, hC, hC4, hmass⟩ := source_good_prime_mass_all_parameters
  refine ⟨C, hC, hC4, ?_⟩
  intro H
  obtain ⟨CH, hCH⟩ := hmass H
  refine ⟨CH, ?_⟩
  intro q _ χ hprim hne hreal β hβ0 hβ1 hzero K _ _ hdegree m Δ hΔ α hdiv U hU
  exact finite_place_lower_of_source_determinant hdegree Δ hΔ α q H
    (fun p => χ (p : ZMod q)) hdiv hU hC4
    (hCH q (three_le_level_of_nonprincipal χ hne) χ hprim hne hreal
      β hβ0 hβ1 hzero U hU)

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantFullLocalBounds. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace
open Finset
open scoped BigOperators NumberField
namespace WeightedTorusJets
open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_character_global_greedy_determinant_full_local_bounds :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧ ∃ CH : ℕ → ℝ,
    ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)),
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    (∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ) ∧
                    ∀ β : ℝ, 0 < β → β < 1 →
                      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                    ∀ U : ℝ, 0 ≤ U →
                      (∑ i, (α i 0 : ℝ)) *
                          (Real.log U - C * Real.log q -
                            C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH H) -
                        C * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| := by
  classical
  obtain ⟨C, hC, hC4, hfinite⟩ := source_given_determinant_finite_lower_of_real_zero
  choose CH hCH using hfinite
  refine ⟨C, hC, hC4, CH, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_global_greedy_determinant_local_bounds q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
      harch, hdiv, hraw⟩ := hsource N H hH hHN n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
    harch, hdiv, hraw, ?_⟩
  intro β hβ0 hβ1 hzero U hU
  simpa only [Nat.cast_pow] using hCH H q χ hprim hne hreal β hβ0 hβ1 hzero
    _ hdegree (N ^ 4) Δ hneΔ α hdiv U hU

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Determinants.NormalizedMasterBound. -/
section
namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets.FinalComparison
theorem normalized_master_bound
    {L S₁ S₂ M U ℓ logN logU logM δ C C_H : ℝ}
    (hS₁ : 0 < S₁) (hlogU : 0 < logU) (hℓ : 0 < ℓ)
    (hN : logN = 3 / 4 * logU)
    (harch : L ≤ M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (logU - C * ℓ - C * δ * logU ^ 2 / ℓ - C_H) - C * M * U ≤ L) :
    1 ≤ 3 / 4 * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
      (C * M * U + 1 / 2 * M * logM) / (S₁ * logU) := by
  apply (mul_le_mul_iff_left₀ (mul_pos hS₁ hlogU)).mp
  have hEq : S₁ * logU *
      (3 / 4 * (1 + S₂ / S₁) +
        (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / logU) + C * δ * (logU / ℓ) +
        (C_H + (1 + S₂ / S₁) * Real.log 8) / logU +
        (C * M * U + 1 / 2 * M * logM) / (S₁ * logU)) =
      M / 2 * logM + (S₁ + S₂) * (logN + 1 / 2 * ℓ + Real.log 8) +
        S₁ * (C * ℓ + C * δ * logU ^ 2 / ℓ + C_H) + C * M * U := by
    rw [hN]
    field_simp
    ring
  conv_rhs => rw [mul_comm]
  rw [hEq, one_mul]
  linarith

end WeightedTorusJets.FinalComparison
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.GreedyPivotsWeightLowSpan. -/
section
namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets
open Submodule
theorem greedyPivots_weight_le_of_low_span {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ) (hwt : Monotone wt)
    (T B : ℕ) (hspan : span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤) :
    ∀ i ∈ greedyPivots K v T, wt i ≤ B := by
  intro i hi
  by_contra h
  have hiweight : B < wt i := Nat.lt_of_not_ge h
  have hprevious : span K (v '' (Finset.range i : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply span_mono
    apply Set.image_mono
    intro j hj
    apply Finset.mem_range.mpr
    exact lt_of_not_ge (fun hij => (not_le_of_gt (hj.2.trans_lt hiweight)) (hwt hij))
  have hnot := ((mem_greedyPivots_iff v i T).mp hi).2
  apply hnot
  rw [hprevious]
  exact mem_top

theorem span_low_sequence_eq_top_of_coverage {K V α : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : ℕ → V) (wt : ℕ → ℕ)
    (R : α → V) (w : α → ℕ) (T B : ℕ)
    (hcover : ∀ a, w a ≤ B → ∃ j < T, wt j = w a ∧ v j = R a)
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    span K (v '' {j : ℕ | j < T ∧ wt j ≤ B}) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply span_mono
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨j, hj, hjw, hjv⟩ := hcover a ha
  exact ⟨j, ⟨hj, hjw.trans_le ha⟩, hjv⟩

end WeightedTorusJets
namespace WeightedTorusJets
open Submodule
theorem finite_sorted_greedy_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    let a := extendFiniteFamily (fun i => (e i : α)) fallback
    ∀ i ∈ greedyPivots K (R ∘ a) s.card, w (a i) ≤ B := by
  classical
  dsimp only
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  let v := R ∘ a
  change ∀ i ∈ greedyPivots K v s.card, w (a i) ≤ B
  by_cases hB₀B : B₀ ≤ B
  · intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    change w (extendFiniteFamily (fun i => (e i : α)) fallback i) ≤ B
    simp only [extendFiniteFamily, dite_eq_left hiT]
    exact ((hs _).mp (e ⟨i, hiT⟩).property).trans hB₀B
  · have hBB₀ : B ≤ B₀ := Nat.le_of_lt (Nat.lt_of_not_ge hB₀B)
    let wt := extendFiniteFamily (fun i => w (e i)) B₀
    have hwt : Monotone wt :=
      monotone_extendFiniteFamily _ _ hsort (fun i => (hs _).mp (e i).property)
    have hcover : ∀ b, w b ≤ B → ∃ j < s.card, wt j = w b ∧ v j = R b := by
      intro b hb
      let j : Fin s.card := e.symm ⟨b, (hs b).mpr (hb.trans hBB₀)⟩
      refine ⟨j, j.isLt, ?_, ?_⟩
      · simp [wt, extendFiniteFamily, j.isLt, j]
      · simp [v, a, extendFiniteFamily, j.isLt, j]
    have hlow := span_low_sequence_eq_top_of_coverage v wt R w s.card B hcover hspan
    intro i hi
    have hiT : i < s.card := Finset.mem_range.mp (greedyPivots_subset_range v s.card hi)
    have hbound := greedyPivots_weight_le_of_low_span v wt hwt s.card B hlow i hi
    simpa [wt, a, extendFiniteFamily, hiT] using hbound

theorem finiteGreedyPivots_weight_le_of_spanning_cutoff
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (e : Fin s.card ≃ s) (fallback : α)
    (w : α → ℕ) (B₀ B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B₀)
    (hsort : Monotone (fun i => w (e i)))
    (hspan : span K (R '' {a : α | w a ≤ B}) = ⊤) :
    ∀ b ∈ finiteGreedyPivots K s R e fallback, w b ≤ B := by
  classical
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact finite_sorted_greedy_weight_le_of_spanning_cutoff
    s R e fallback w B₀ B hs hsort hspan i hi

end WeightedTorusJets
namespace WeightedTorusJets
theorem fixed_first_greedy_rectangle_weight_bound {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (R : (Fin 3 → ℕ) → V)
    (e : Fin (weightedJetIndices H (N ^ 4 - 1)).card ≃ weightedJetIndices H (N ^ 4 - 1))
    (hsort : Monotone (fun i => (e i).1 0 + H * (e i).1 1 + H * (e i).1 2))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    ∀ a ∈ finiteGreedyPivots K (weightedJetIndices H (N ^ 4 - 1)) R e 0,
      (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let B := ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊
  have hsets : (weightedJetIndices H B : Set (Fin 3 → ℕ)) = {a | w a ≤ B} := by
    ext a
    exact mem_weightedJetIndices_iff hH a
  have hlow : Submodule.span K (R '' {a : Fin 3 → ℕ | w a ≤ B}) = ⊤ := by
    rw [← hsets]
    exact span_cutoff_eq_top_of_rectangle hH R hspan
  have hbound := finiteGreedyPivots_weight_le_of_spanning_cutoff
    (weightedJetIndices H (N ^ 4 - 1)) R e 0 w (N ^ 4 - 1) B
    (mem_weightedJetIndices_iff hH) hsort hlow
  intro a ha
  exact weightedJetIndices_real_weight hH (by positivity)
    ((mem_weightedJetIndices_iff hH a).mpr (hbound a ha))

theorem finiteGreedyPivots_restrictWeightSortedEquiv_map
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).map e.toEmbedding := by
  classical
  unfold finiteGreedyPivots
  dsimp only
  rw [greedyPivots_restrictWeightSortedEquiv s R w B hs e he fallback,
    Finset.map_eq_image]
  apply Finset.image_congr
  intro i hi
  exact extend_restrictWeightSortedEquiv_eq s w B hs e he fallback i
    (Finset.mem_range.mp (greedyPivots_subset_range (R ∘ e) s.card hi))

theorem finiteGreedyPivots_restrictWeightSortedEquiv
    {K V α : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [DecidableEq α]
    (s : Finset α) (R : α → V) (w : α → ℕ) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) (e : ℕ ≃ α)
    (he : Monotone (fun i => w (e i))) (fallback : α) :
    finiteGreedyPivots K s R (restrictWeightSortedEquiv s w B hs e he) fallback =
      (greedyPivots K (R ∘ e) s.card).image e := by
  rw [finiteGreedyPivots_restrictWeightSortedEquiv_map, Finset.map_eq_image]
  rfl

theorem sum_embedding_eq_sum_finset_of_range {ι α A : Type*} [Fintype ι]
    [AddCommMonoid A] (p : ι ↪ α) (s : Finset α)
    (hp : Set.range p = (s : Set α)) (f : α → A) :
    ∑ i, f (p i) = ∑ a ∈ s, f a := by
  classical
  have hs : Finset.univ.map p = s := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hp
  rw [← hs, Finset.sum_map]

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.GlobalRectanglePivotBounds. -/
section
namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets
open scoped BigOperators
theorem global_source_rectangle_pivot_bounds {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (hHN : H ≤ N) (hN : 18818 ≤ N) (R : (Fin 3 → ℕ) → V)
    (e : ℕ ≃ (Fin 3 → ℕ))
    (he : Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2))
    (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ))
    (hα : Set.range α =
      ((greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e :
        Set (Fin 3 → ℕ)))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    let P := (greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  dsimp only
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let P := (greedyPivots K (R ∘ e) s.card).image e
  have hs : ∀ a, a ∈ s ↔ w a ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have hmap : Finset.univ.map α = P := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hα
  have hcard : P.card = N ^ 4 := by rw [← hmap]; simp
  have hfinite := finiteGreedyPivots_restrictWeightSortedEquiv
    (K := K) s R w (N ^ 4 - 1) hs e he 0
  change finiteGreedyPivots K s R e₀ 0 = P at hfinite
  apply weighted_pivot_bounds P H N hH hHN hN hcard
  intro a ha
  apply fixed_first_greedy_rectangle_weight_bound H N hH R e₀
    (restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he) hspan a
  rw [hfinite]
  exact ha

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.InvariantJetLinearMap. -/
section
namespace OAI
namespace SiegelZeros
open scoped BigOperators
namespace WeightedTorusJets
variable {K : Type*} [Field K]
def biquadraticDirections (a b : K) : Fin 3 → Fin 4 → K :=
  ![![1, a, b, a * b], ![1, -a, b, -(a * b)], ![1, -a, -b, a * b]]

def biquadraticCoefficients (a b : K) : Fin 4 → K :=
  ![1, a⁻¹, -b⁻¹, -(a * b)⁻¹]

def biquadraticForm (a b : K) : (Fin 4 → K) →ₗ[K] K :=
  dotProductBilin K K (biquadraticCoefficients a b)

theorem biquadraticForm_apply (a b : K) (v : Fin 4 → K) :
    biquadraticForm a b v = v 0 + a⁻¹ * v 1 - b⁻¹ * v 2 - (a * b)⁻¹ * v 3 := by
  simp [biquadraticForm, biquadraticCoefficients, dotProductBilin, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

theorem biquadraticForm_direction {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (i : Fin 3) : biquadraticForm a b (biquadraticDirections a b i) = 0 := by
  fin_cases i <;> simp [biquadraticForm_apply, biquadraticDirections, ha, hb, mul_assoc]

theorem biquadraticDirections_linearIndependent [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (biquadraticDirections a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_succ, biquadraticDirections] at h0 h1 h2
  have hc0 : c 0 = 0 := by
    apply (mul_eq_zero.mp (show 2 * a * c 0 = 0 by linear_combination a * h0 + h1)).resolve_left
    exact mul_ne_zero two_ne_zero ha
  have hc2 : c 2 = 0 := by
    apply (mul_eq_zero.mp (show 2 * b * c 2 = 0 by linear_combination b * h0 - h2)).resolve_left
    exact mul_ne_zero two_ne_zero hb
  have hc1 : c 1 = 0 := by linear_combination h0 - hc0 - hc2
  fin_cases i <;> assumption

theorem finrank_ker_biquadraticForm (a b : K) :
    Module.finrank K (LinearMap.ker (biquadraticForm a b)) = 3 := by
  have hs : Function.Surjective (biquadraticForm a b) := fun y =>
    ⟨![y, 0, 0, 0], by simp [biquadraticForm_apply]⟩
  have h := (biquadraticForm a b).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact Nat.add_left_cancel h

theorem span_biquadraticDirections_eq_ker [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span K (Set.range (biquadraticDirections a b)) =
      LinearMap.ker (biquadraticForm a b) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact biquadraticForm_direction ha hb i
  · rw [finrank_span_eq_card (biquadraticDirections_linearIndependent ha hb),
      finrank_ker_biquadraticForm]
    rfl

theorem biquadraticCoefficients_linearIndependent [Algebra ℚ K] {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients a b) := by
  have ha : a ≠ 0 := by simpa using h.ne_zero 1
  have hb : b ≠ 0 := by simpa using h.ne_zero 2
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hscaled : ∑ j, (![ -c 3, -c 2, c 1, c 0] : Fin 4 → ℚ) j •
      (![1, a, b, a * b] : Fin 4 → K) j = 0 := by
    simp [Fin.sum_univ_succ, biquadraticCoefficients, Algebra.smul_def] at hc ⊢
    field_simp at hc
    linear_combination hc
  have hz := Fintype.linearIndependent_iff.mp h _ hscaled
  fin_cases i
  · simpa using hz 3
  · simpa using hz 2
  · simpa using hz 1
  · simpa using hz 0

theorem map_biquadraticCoefficients {L : Type*} [Field L] (f : K →+* L) (a b : K) :
    f ∘ biquadraticCoefficients a b = biquadraticCoefficients (f a) (f b) := by
  ext i
  fin_cases i <;> simp [biquadraticCoefficients]

theorem biquadraticCoefficients_linearIndependent_map [Algebra ℚ K]
    {L : Type*} [Field L] [Algebra ℚ L] (f : K →ₐ[ℚ] L) {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients (f a) (f b)) := by
  have h' := (biquadraticCoefficients_linearIndependent h).map' f.toLinearMap
    (LinearMap.ker_eq_bot.mpr f.injective)
  exact (map_biquadraticCoefficients f.toRingHom a b) ▸ h'

noncomputable def biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) K (LinearMap.ker (biquadraticForm a b)) :=
  (Module.Basis.span (biquadraticDirections_linearIndependent ha hb)).map
    (LinearEquiv.ofEq _ _ (span_biquadraticDirections_eq_ker ha hb))

theorem coe_biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticDirectionBasis ha hb i : Fin 4 → K) = biquadraticDirections a b i := by
  simp [biquadraticDirectionBasis]

end WeightedTorusJets
namespace WeightedTorusJets
 theorem source_same_witness_hyperplane {K : Type*} [Field K] [CharZero K]
    (a b : K) (φ : K →+* ℂ) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b) :
    LinearIndependent ℚ (biquadraticCoefficients (φ a) (φ b)) ∧
    ∃ D : Module.Basis (Fin 3) ℂ (LinearMap.ker (biquadraticForm (φ a) (φ b))),
      ∀ j i, (D j : Fin 4 → ℂ) i =
        φ ((![![1, a, b, a * b], (fun i => σ (![1, a, b, a * b] i)),
          (fun i => (σ * τ) (![1, a, b, a * b] i))] : Fin 3 → Fin 4 → K) j i) := by
  have hbase : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K) :=
    (funext hv) ▸ v.linearIndependent
  have ha : a ≠ 0 := by simpa using hbase.ne_zero 1
  have hb : b ≠ 0 := by simpa using hbase.ne_zero 2
  have hφa : φ a ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr ha
  have hφb : φ b ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hb
  refine ⟨biquadraticCoefficients_linearIndependent_map φ.toRatAlgHom hbase,
    biquadraticDirectionBasis hφa hφb, ?_⟩
  intro j i
  rw [coe_biquadraticDirectionBasis]
  fin_cases j <;> fin_cases i <;>
    simp [biquadraticDirections, AlgEquiv.mul_apply, hσa, hσb, hτa, hτb]

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from PaperLemma3.Lemma3. -/
section

/-!
# Lemma 3 (`lem:interpolation`) of Uniform exclusion of Landau–Siegel zeros: skeleton

Paper: refs/siegel-paper.tex lines 252–267 (statement) and 269–407 (proof).
Plan: docs/plan-remaining-gaps.md, step 3c.

`interpolation` is the paper's statement. Its proof below is complete *given* the
sub-lemmas, which are stated separately and are proved in the piece files and merged here. Each sub-lemma is
one self-contained piece of the paper's proof and can be proved independently.
The step numbers refer to docs/lemma3-audit.md.

| Piece | Sub-lemmas | Paper steps |
|---|---|---|
| 1. Nearest point and face | `exists_nearest`, `quarter_mem_face` | 5–7 |
| 2. Carathéodory and the move off the face | `exists_heavy_vertex`, `closer_point` | 8–11 |
| 3. Rational hyperplane | `exists_int_hyperplane`, `int_comb_ne_zero` | 12 |
| 4. Lagrange polynomial | `exists_lagrange` | 13–14 |
| 5. Counting and degrees | `exists_annihilator`, `four_hull_subset_cube`, `exists_vanishing`, `exists_lattice_nonvanishing`, `exists_translate` | 1–4, 15 |
-/

open MvPolynomial Pointwise

namespace Lemma3

noncomputable section

/-- An integer vector as a real vector. -/
def zR (m : Fin 4 → ℤ) : Fin 4 → ℝ := fun i => (m i : ℝ)

/-- An integer vector as a complex vector. -/
def zC (m : Fin 4 → ℤ) : Fin 4 → ℂ := fun i => (m i : ℂ)

/-- A point of `E_N = {0,…,N−1}⁴` as an integer vector. -/
def emb {N : ℕ} (n : Fin 4 → Fin N) : Fin 4 → ℤ := fun i => ((n i : ℕ) : ℤ)

/-- Squared Euclidean distance on `ℝ⁴`. -/
def sqd (x y : Fin 4 → ℝ) : ℝ := dotProduct (x - y) (x - y)

/-- `𝒫_t`: polynomials in `z₁, z₂, z₃` with `deg_{z_j} B ≤ t_j`. -/
def Pt (t : Fin 3 → ℤ) : Set (MvPolynomial (Fin 3) ℂ) :=
  {B | ∀ j, (B.degreeOf j : ℤ) ≤ t j}

/-! ## Sub-lemmas, proved (merged from the five piece files) -/

/-! ### Piece 1 (from lean-checks/Lemma3_P1.lean) -/
lemma p1_dot_self_nonneg (v : Fin 4 → ℝ) : 0 ≤ dotProduct v v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma p1_coord_le_sqd (a z : Fin 4 → ℝ) (i : Fin 4) :
    (a i - z i) * (a i - z i) ≤ sqd a z := by
  unfold sqd dotProduct
  exact Finset.single_le_sum (f := fun j => (a - z) j * (a - z) j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- The variational inequality for a nearest point in a convex set. -/
lemma p1_var_ineq (K : Set (Fin 4 → ℝ)) (hKcv : Convex ℝ K) (a y : Fin 4 → ℝ) (hy : y ∈ K)
    (hmin : ∀ z ∈ K, sqd a y ≤ sqd a z) : ∀ x ∈ K, dotProduct (a - y) (x - y) ≤ 0 := by
  intro x hx
  by_contra hpos
  push Not at hpos
  set c := dotProduct (a - y) (x - y) with hc
  set b := dotProduct (x - y) (x - y) with hb
  have hb0 : 0 ≤ b := p1_dot_self_nonneg _
  set t := c / (c + b) with ht
  have hcb : 0 < c + b := by linarith
  have ht0 : 0 < t := div_pos hpos hcb
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hcb]; linarith
  have htb : t * b ≤ c := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ hcb]; nlinarith
  have hz : (1 - t) • y + t • x ∈ K := hKcv hy hx (by linarith) ht0.le (by ring)
  have key := hmin _ hz
  have expand : sqd a ((1 - t) • y + t • x) = sqd a y - 2 * t * c + t ^ 2 * b := by
    simp only [sqd, hc, hb, dotProduct, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [expand] at key
  have h2 : 2 * t * c ≤ t ^ 2 * b := by linarith
  have h3 : 2 * c ≤ t * b := by
    have : t * (2 * c) ≤ t * (t * b) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  linarith

/-- Step 5 and the nearest-point inequality. Among the lattice points in `W`, one, `m`,
is at least distance from the compact convex set `K`; `y` is its nearest point in `K`.
(The distance from `m'` to `K` is the infimum of `sqd (zR m') z` over `z ∈ K`.) -/
theorem exists_nearest (K : Set (Fin 4 → ℝ)) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty) (W : Set (Fin 4 → ℤ)) (hW : W.Nonempty) :
    ∃ m ∈ W, ∃ y ∈ K, (∀ x ∈ K, dotProduct (zR m - y) (x - y) ≤ 0) ∧
      ∀ m' ∈ W, ∀ z ∈ K, sqd (zR m) y ≤ sqd (zR m') z := by
  classical
  have hcont : ∀ a, ContinuousOn (fun z => sqd a z) K := fun a => by
    unfold sqd dotProduct
    fun_prop
  have hsel : ∀ a : Fin 4 → ℝ, ∃ y ∈ K, ∀ z ∈ K, sqd a y ≤ sqd a z := fun a => by
    obtain ⟨y, hy, hmin⟩ := hKc.exists_isMinOn hKne (hcont a)
    exact ⟨y, hy, fun z hz => hmin hz⟩
  choose g hgK hgmin using hsel
  obtain ⟨m0, hm0⟩ := hW
  set D := sqd (zR m0) (g (zR m0)) with hD
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin 4 → ℝ)).1 hKc.isBounded
  have hRb : ∀ z ∈ K, ∀ i, |z i| ≤ r := by
    intro z hz i
    have h1 := hr hz
    rw [mem_closedBall_zero_iff] at h1
    have h2 := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at h2
    linarith
  set W' : Set (Fin 4 → ℤ) := {m' | m' ∈ W ∧ sqd (zR m') (g (zR m')) ≤ D} with hW'
  set C : ℝ := r + 1 + D with hC
  set B : ℤ := ⌈C⌉ with hB
  have hfin : W'.Finite := by
    refine (Set.finite_Icc (fun _ : Fin 4 => -B) (fun _ => B)).subset ?_
    rintro m' ⟨-, hm'D⟩
    have hbd : ∀ i, |(m' i : ℝ)| ≤ C := by
      intro i
      set z := g (zR m')
      have hz := hRb z (hgK _) i
      have hc := p1_coord_le_sqd (zR m') z i
      simp only [zR] at hc
      set e := (m' i : ℝ) - z i
      have he : |e| ≤ e * e + 1 := by
        rcases abs_cases e with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
      have : (m' i : ℝ) = z i + e := by simp [e]
      rw [this]
      calc |z i + e| ≤ |z i| + |e| := abs_add_le _ _
        _ ≤ C := by rw [hC]; linarith
    have hCB : C ≤ (B : ℝ) := Int.le_ceil C
    constructor
    · intro i
      have h := (abs_le.1 (hbd i)).1
      have : ((-B : ℤ) : ℝ) ≤ (m' i : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · intro i
      have h := (abs_le.1 (hbd i)).2
      have : (m' i : ℝ) ≤ ((B : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  obtain ⟨m, hmW', hmmin⟩ :=
    Set.exists_min_image W' (fun m' => sqd (zR m') (g (zR m'))) hfin ⟨m0, hm0, le_rfl⟩
  refine ⟨m, hmW'.1, g (zR m), hgK _, p1_var_ineq K hKcv _ _ (hgK _) (hgmin _), ?_⟩
  intro m' hm' z hz
  by_cases h' : sqd (zR m') (g (zR m')) ≤ D
  · exact (hmmin m' ⟨hm', h'⟩).trans (hgmin _ z hz)
  · push Not at h'
    exact (hmW'.2.trans h'.le).trans (hgmin _ z hz)

/-- Step 6. `y/4` lies in the face `G` of `P = conv S` maximizing `h·`. Here the face is
given by its points of `S`, so this also records the unstated fact that `G = conv(S ∩ G)`. -/
theorem quarter_mem_face {ι : Type*} (p : ι → Fin 4 → ℝ) (S : Finset ι) (h y : Fin 4 → ℝ)
    (hy : y ∈ (4 : ℝ) • convexHull ℝ (p '' S))
    (hmax : ∀ x ∈ (4 : ℝ) • convexHull ℝ (p '' S), dotProduct h (x - y) ≤ 0) :
    (1 / 4 : ℝ) • y ∈ convexHull ℝ
      (p '' {s | s ∈ S ∧ ∀ s' ∈ S, dotProduct h (p s') ≤ dotProduct h (p s)}) := by
  classical
  set T : Finset (Fin 4 → ℝ) := S.image p with hT
  have hTc : p '' (S : Set ι) = (T : Set (Fin 4 → ℝ)) := by simp [hT]
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.1 hy
  have hq : (1 / 4 : ℝ) • (4 : ℝ) • x = x := by rw [smul_smul]; norm_num
  rw [hq]
  rw [hTc] at hx hmax
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
  set a := dotProduct h x with ha
  -- every point of `T` has `h·v ≤ a`
  have hle : ∀ v ∈ T, dotProduct h v ≤ a := by
    intro v hv
    have h1 := hmax ((4 : ℝ) • v)
      (Set.smul_mem_smul_set (subset_convexHull ℝ _ (Finset.mem_coe.2 hv)))
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_smul,
      smul_eq_mul] at h1
    linarith
  have hsum : ∑ v ∈ T, w v * (a - dotProduct h v) = 0 := by
    have e1 : a = ∑ v ∈ T, w v * dotProduct h v := by
      rw [ha, ← hwx, dotProduct_sum]
      simp [dotProduct_smul]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v hv => mul_nonneg (hw0 v hv) (sub_nonneg.2 (hle v hv)))).1 hsum
  set G : Finset (Fin 4 → ℝ) := T.filter (fun v => ∀ v' ∈ T, dotProduct h v' ≤ dotProduct h v)
    with hG
  have hout : ∀ v ∈ T, v ∉ G → w v = 0 := by
    intro v hv hvG
    have hnot : ¬ ∀ v' ∈ T, dotProduct h v' ≤ dotProduct h v := by
      intro hc; exact hvG (Finset.mem_filter.2 ⟨hv, hc⟩)
    push Not at hnot
    obtain ⟨v', hv', hlt⟩ := hnot
    have hlt' : dotProduct h v < a := lt_of_lt_of_le hlt (hle v' hv')
    have := hzero v hv
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 (by linarith)
  have hGT : G ⊆ T := Finset.filter_subset _ _
  have hsub : ↑G ⊆ p '' {s | s ∈ S ∧ ∀ s' ∈ S, dotProduct h (p s') ≤ dotProduct h (p s)} := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    obtain ⟨hvT, hvmax⟩ := hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hvT
    exact ⟨s, ⟨hs, fun s' hs' => hvmax (p s') (Finset.mem_image_of_mem p hs')⟩, rfl⟩
  apply convexHull_mono hsub
  rw [Finset.mem_convexHull']
  refine ⟨w, fun v hv => hw0 v (hGT hv), ?_, ?_⟩
  · rw [← hw1]
    exact Finset.sum_subset hGT (fun v hv hvG => hout v hv hvG)
  · rw [← hwx]
    exact Finset.sum_subset hGT (fun v hv hvG => by rw [hout v hv hvG, zero_smul])

/-! ### Piece 2 (from lean-checks/Lemma3_P2.lean) -/
/-! ## Piece 2: Carathéodory and the move off the face -/

theorem p2_dot_expand (h w : Fin 4 → ℝ) (s : ℝ) :
    dotProduct (h + s • w) (h + s • w) =
      dotProduct h h + 2 * s * dotProduct h w + s ^ 2 * dotProduct w w := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm w h]
  ring

theorem p2_dot_self_nonneg (w : Fin 4 → ℝ) : 0 ≤ dotProduct w w := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))

/-- Steps 7–8 (eq:vertex). A point of the hull of points lying in a hyperplane `h· = const`
(`h ≠ 0`, so affine dimension ≤ 3) is a combination of at most four of them, one with
coefficient ≥ 1/4; call it `u`. Then `4x − u ∈ 3·conv`. -/
theorem exists_heavy_vertex {ι : Type*} (p : ι → Fin 4 → ℝ) (T : Set ι) (h : Fin 4 → ℝ)
    (hh : h ≠ 0) (hT : ∀ s ∈ T, ∀ s' ∈ T, dotProduct h (p s) = dotProduct h (p s'))
    (x : Fin 4 → ℝ) (hx : x ∈ convexHull ℝ (p '' T)) :
    ∃ u ∈ T, (4 : ℝ) • x - p u ∈ (3 : ℝ) • convexHull ℝ (p '' T) := by
  classical
  obtain ⟨ι', hfin, z, w, hzs, hai, hw0, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let f : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => dotProduct h v
      map_add' := fun a b => dotProduct_add h a b
      map_smul' := fun c v => by simp [dotProduct_smul] }
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro htop
    have hm : h ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
    exact hh (dotProduct_self_eq_zero.1 hm)
  have hlt := Submodule.finrank_lt hker
  rw [Module.finrank_fin_fun] at hlt
  have hvs : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker f := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    obtain ⟨si, hsi, hzi⟩ := hzs ⟨i, rfl⟩
    obtain ⟨sj, hsj, hzj⟩ := hzs ⟨j, rfl⟩
    show dotProduct h (z i - z j) = 0
    rw [dotProduct_sub, ← hzi, ← hzj, hT si hsi sj hsj, sub_self]
  have hne : Nonempty ι' := by
    by_contra hem
    rw [not_nonempty_iff] at hem
    simp at hw1
  have hcard : Fintype.card ι' ≤ 4 := by
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι' = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
    have h1 := hai.finrank_vectorSpan hk
    have h2 := Submodule.finrank_mono hvs
    omega
  obtain ⟨i, hi⟩ : ∃ i, 1 / 4 ≤ w i := by
    by_contra hc
    push Not at hc
    have hs : ∑ j, w j < ∑ _j : ι', (1 / 4 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hc j)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have : (Fintype.card ι' : ℝ) ≤ 4 := by exact_mod_cast hcard
    linarith
  obtain ⟨u, huT, hzu⟩ := hzs ⟨i, rfl⟩
  refine ⟨u, huT, ?_⟩
  set v : ι' → ℝ := fun j => (4 * w j - if j = i then 1 else 0) / 3 with hvdef
  have hv0 : ∀ j ∈ Finset.univ, 0 ≤ v j := by
    intro j _
    have := hw0 j
    simp only [hvdef]
    split_ifs with hj
    · subst hj; linarith
    · linarith
  have hv1 : ∑ j, v j = 1 := by
    simp only [hvdef, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1]
    simp
    norm_num
  have hmem : ∑ j, v j • z j ∈ convexHull ℝ (p '' T) :=
    (convex_convexHull ℝ _).sum_mem hv0 hv1 (fun j _ => subset_convexHull ℝ _ (hzs ⟨j, rfl⟩))
  have hterm : ∀ j, (3 : ℝ) • (v j • z j) =
      (4 : ℝ) • (w j • z j) - (if j = i then z j else 0) := by
    intro j
    by_cases hj : j = i
    · simp only [hvdef, hj, ↓reduceIte]
      module
    · simp only [hvdef, hj, ↓reduceIte]
      module
  have heq : (3 : ℝ) • ∑ j, v j • z j = (4 : ℝ) • x - p u := by
    rw [Finset.smul_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
      ← Finset.smul_sum, hwx, hzu]
    simp
  rw [← heq]
  exact Set.smul_mem_smul_set hmem

/-- Steps 9–10 (eq:distance). With `m = y + h`, `y' = y + n − u ∈ 4P` and
`h·(u − n) > 0`, some point of `4P` is closer to `m' = m + n − u` than `y` is to `m`. -/
theorem closer_point (P : Set (Fin 4 → ℝ)) (hP : Convex ℝ P) (h y u n : Fin 4 → ℝ)
    (hyu : y - u ∈ (3 : ℝ) • P) (hn : n ∈ P) (hy : y ∈ (4 : ℝ) • P)
    (hpos : 0 < dotProduct h (u - n)) :
    ∃ z ∈ (4 : ℝ) • P, sqd (y + h + (n - u)) z < sqd (y + h) y := by
  set w := n - u with hwdef
  set a := -dotProduct h w with hadef
  set b := dotProduct w w with hbdef
  have ha : 0 < a := by
    have e : dotProduct h (u - n) = -dotProduct h w := by
      rw [hwdef, ← dotProduct_neg, neg_sub]
    rw [hadef, ← e]
    exact hpos
  have hb : 0 ≤ b := p2_dot_self_nonneg w
  set s := a / (a + b) with hsdef
  have hab : 0 < a + b := by linarith
  have hs : s * (a + b) = a := div_mul_cancel₀ a (ne_of_gt hab)
  have hs0 : 0 < s := div_pos ha hab
  have hs1 : s ≤ 1 := (div_le_one hab).2 (by linarith)
  have h4 : (4 : ℝ) • P = (3 : ℝ) • P + (1 : ℝ) • P := by
    rw [← hP.add_smul (by norm_num) (by norm_num)]
    norm_num
  have hyw : y + w ∈ (4 : ℝ) • P := by
    rw [h4]
    have e : y + w = (y - u) + n := by rw [hwdef]; abel
    rw [e]
    exact Set.add_mem_add hyu (by rw [one_smul]; exact hn)
  have hconv : Convex ℝ ((4 : ℝ) • P) := hP.smul 4
  refine ⟨y + (1 - s) • w, ?_, ?_⟩
  · have := hconv.add_smul_sub_mem hy hyw ⟨by linarith, by linarith⟩ (t := 1 - s)
    simpa using this
  · have e1 : y + h + w - (y + (1 - s) • w) = h + s • w := by module
    have e2 : y + h - y = h := by abel
    unfold sqd
    rw [e1, e2, p2_dot_expand]
    have e3 : s ^ 2 * b = s * a - s ^ 2 * a := by linear_combination s * hs
    have e4 : dotProduct h w = -a := by rw [hadef]; ring
    rw [← hbdef, e3, e4]
    nlinarith [mul_pos hs0 ha, mul_pos (mul_pos hs0 hs0) ha]

/-! ### Piece 3 (from lean-checks/Lemma3_P3.lean) -/
/-- The `ℚ`-linear functional `v ↦ ∑ h i * v i` on `ℚ⁴`, with values in `ℝ`. -/
def p3_g (h : Fin 4 → ℝ) : (Fin 4 → ℚ) →ₗ[ℚ] ℝ where
  toFun v := ∑ i, h i * (v i : ℝ)
  map_add' v w := by
    simp only [Pi.add_apply, Rat.cast_add, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, RingHom.id_apply, Rat.smul_def,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem p3_g_apply (h : Fin 4 → ℝ) (v : Fin 4 → ℚ) : p3_g h v = ∑ i, h i * (v i : ℝ) := rfl

/-- Clearing denominators of a rational vector. -/
theorem p3_clear (w : Fin 4 → ℚ) :
    ∃ (L : ℕ) (r : Fin 4 → ℤ), L ≠ 0 ∧ ∀ i, (r i : ℚ) = w i * L := by
  classical
  refine ⟨∏ i, (w i).den, ?_⟩
  have hex : ∀ i, ∃ z : ℤ, (z : ℚ) = w i * ((∏ j, (w j).den : ℕ) : ℚ) := by
    intro i
    obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem (fun j => (w j).den) (Finset.mem_univ i)
    refine ⟨(w i).num * M, ?_⟩
    rw [hM]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  choose r hr using hex
  exact ⟨r, Finset.prod_ne_zero_iff.2 fun i _ => (w i).den_nz, hr⟩

/-- Step 12. Integer points on a real hyperplane `h· = const` (`h ≠ 0`) lie on an integer
hyperplane `r· = k`, `0 ≠ r ∈ ℤ⁴`. -/
theorem exists_int_hyperplane (T : Set (Fin 4 → ℤ)) (h : Fin 4 → ℝ) (hh : h ≠ 0)
    (hT : ∀ s ∈ T, ∀ s' ∈ T, dotProduct h (zR s) = dotProduct h (zR s')) :
    ∃ r : Fin 4 → ℤ, r ≠ 0 ∧ ∃ k : ℤ, ∀ s ∈ T, dotProduct r s = k := by
  classical
  rcases T.eq_empty_or_nonempty with hTe | ⟨s0, hs0⟩
  · refine ⟨fun _ => 1, fun h0 => by simpa using congrFun h0 0, 0, ?_⟩
    intro s hs
    simp [hTe] at hs
  set D : Set (Fin 4 → ℚ) :=
    {v | ∃ s ∈ T, v = fun i => (((s i - s0 i : ℤ)) : ℚ)} with hDdef
  set V : Submodule ℚ (Fin 4 → ℚ) := Submodule.span ℚ D with hVdef
  have hDker : D ⊆ LinearMap.ker (p3_g h) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, p3_g_apply]
    have := hT s hs s0 hs0
    simp only [dotProduct, zR] at this
    simp only [Int.cast_sub, Rat.cast_sub, Rat.cast_intCast, mul_sub, Finset.sum_sub_distrib]
    linarith
  have hVlt : V < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hV => hh ?_
    have hle : V ≤ LinearMap.ker (p3_g h) := Submodule.span_le.2 hDker
    rw [hV] at hle
    funext j
    have hj := hle (Submodule.mem_top (x := Pi.single j (1 : ℚ)))
    rw [LinearMap.mem_ker, p3_g_apply] at hj
    simpa [Pi.single_apply, apply_ite, mul_ite, Finset.sum_ite_eq'] using hj
  obtain ⟨f, hf0, hVf⟩ := V.exists_le_ker_of_lt_top hVlt
  set w : Fin 4 → ℚ := fun i => f (fun j => if i = j then 1 else 0) with hwdef
  have hfw : ∀ x, f x = ∑ i, x i * w i := by
    intro x
    rw [f.pi_apply_eq_sum_univ x]
    rfl
  obtain ⟨L, r, hL, hr⟩ := p3_clear w
  refine ⟨r, ?_, dotProduct r s0, ?_⟩
  · intro hr0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfw x, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hr i
    rw [hr0, Pi.zero_apply, Int.cast_zero] at this
    have hw : w i = 0 := by
      rcases mul_eq_zero.1 this.symm with h1 | h1
      · exact h1
      · exact absurd (by exact_mod_cast h1) hL
    rw [hw, mul_zero]
  · intro s hs
    have hd : (fun i => (((s i - s0 i : ℤ)) : ℚ)) ∈ LinearMap.ker f :=
      hVf (Submodule.subset_span ⟨s, hs, rfl⟩)
    rw [LinearMap.mem_ker, hfw] at hd
    have key : ((dotProduct r s - dotProduct r s0 : ℤ) : ℚ) = 0 := by
      have e : ((dotProduct r s - dotProduct r s0 : ℤ) : ℚ) =
          (L : ℚ) * ∑ i, (((s i - s0 i : ℤ)) : ℚ) * w i := by
        simp only [dotProduct, Int.cast_sub, Int.cast_sum, Int.cast_mul, hr, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hd, mul_zero]
    have : dotProduct r s - dotProduct r s0 = 0 := by exact_mod_cast key
    linarith

/-- Step 12. Rational independence of the coordinates of `c` gives `r·c ≠ 0`. -/
theorem int_comb_ne_zero (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c) (r : Fin 4 → ℤ)
    (hr : r ≠ 0) : ∑ i, (r i : ℂ) * c i ≠ 0 := by
  intro hsum
  apply hr
  have h0 : ∑ i, ((r i : ℚ)) • c i = 0 := by
    simpa only [Rat.smul_def, Rat.cast_intCast] using hsum
  funext i
  have := Fintype.linearIndependent_iff.1 hc (fun i => (r i : ℚ)) h0 i
  exact_mod_cast this

/-! ### Piece 4 (from lean-checks/Lemma3_P4.lean) -/
/-- The polynomial of a linear functional on `ℂ³`. -/
def p4_linP (ψ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : MvPolynomial (Fin 3) ℂ :=
  ∑ j, C (ψ (fun l => if j = l then 1 else 0)) * X j

theorem p4_eval_linP (ψ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (z : Fin 3 → ℂ) :
    eval z (p4_linP ψ) = ψ z := by
  rw [LinearMap.pi_apply_eq_sum_univ ψ z]
  simp only [p4_linP, map_sum, map_mul, eval_C, eval_X, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem p4_deg_linP (ψ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : (p4_linP ψ).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

/-- The linear functional `x ↦ ∑ r_j x_j`. -/
def p4_rL (r : Fin 4 → ℤ) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  ∑ j, (r j : ℂ) • LinearMap.proj j

theorem p4_rL_apply (r : Fin 4 → ℤ) (x : Fin 4 → ℂ) :
    p4_rL r x = ∑ j, (r j : ℂ) * x j := by
  simp [p4_rL]

/-- Steps 13–14. `A` restricted to `ℋ = {r·v = k}` is an affine bijection (`r·c ≠ 0`), so
there is a Lagrange polynomial `Q` of total degree ≤ `3(N−1)` equal to 1 at `Au` and 0 at
`An` for the other `n ∈ E_N ∩ ℋ` in `T`. -/
theorem exists_lagrange (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (hA : Function.Surjective A)
    (c : Fin 4 → ℂ) (hker : LinearMap.ker A = Submodule.span ℂ {c}) (r : Fin 4 → ℤ)
    (hrc : ∑ i, (r i : ℂ) * c i ≠ 0) (k : ℤ) (N : ℕ) (T : Set (Fin 4 → Fin N))
    (hT : ∀ n ∈ T, dotProduct r (emb n) = k) (u : Fin 4 → Fin N) (hu : u ∈ T) :
    ∃ Q : MvPolynomial (Fin 3) ℂ, Q.totalDegree ≤ 3 * (N - 1) ∧
      eval (A (zC (emb u))) Q = 1 ∧ ∀ n ∈ T, n ≠ u → eval (A (zC (emb n))) Q = 0 := by
  classical
  -- `r ≠ 0`, pick `i₀` with `r i₀ ≠ 0`.
  have hr : ∃ i₀, r i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hrc (by simp [h])
  obtain ⟨i₀, hi₀⟩ := hr
  set s : ℂ := ∑ i, (r i : ℂ) * c i with hs
  obtain ⟨g, hg⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hAg : ∀ z, A (g z) = z := fun z => by
    simpa using LinearMap.congr_fun hg z
  -- The affine functionals recovering the coordinates on `ℋ`.
  let ψ : Fin 4 → (Fin 3 → ℂ) →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i ∘ₗ g) - (c i / s) • (p4_rL r ∘ₗ g)
  let lam : Fin 4 → MvPolynomial (Fin 3) ℂ := fun i =>
    p4_linP (ψ i) + C (c i * (k : ℂ) / s)
  have hlam_deg : ∀ i, (lam i).totalDegree ≤ 1 := fun i =>
    (totalDegree_add _ _).trans (by rw [totalDegree_C]; simpa using p4_deg_linP (ψ i))
  have hlam_eval : ∀ x : Fin 4 → ℂ, ∑ j, (r j : ℂ) * x j = k →
      ∀ i, eval (A x) (lam i) = x i := by
    intro x hx i
    have hw : x - g (A x) ∈ LinearMap.ker A := by
      rw [LinearMap.mem_ker, map_sub, hAg, sub_self]
    rw [hker, Submodule.mem_span_singleton] at hw
    obtain ⟨t, ht⟩ := hw
    have hx' : x = g (A x) + t • c := by rw [ht]; abel
    have hrx : p4_rL r (g (A x)) = k - t * s := by
      have h1 : p4_rL r x = k := by rw [p4_rL_apply, hx]
      rw [hx', map_add, map_smul, smul_eq_mul, p4_rL_apply r c, ← hs] at h1
      linear_combination h1
    have hxi : x i = g (A x) i + t * c i := by
      conv_lhs => rw [hx']
      simp
    simp only [lam, eval_add, eval_C, p4_eval_linP, ψ, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, hrx, hxi]
    field_simp
    ring
  have hTC : ∀ n ∈ T, ∑ j, (r j : ℂ) * zC (emb n) j = k := by
    intro n hn
    have := hT n hn
    simp only [dotProduct] at this
    simp only [zC]
    exact_mod_cast this
  have hzC : ∀ (n : Fin 4 → Fin N) i, zC (emb n) i = ((n i : ℕ) : ℂ) := by
    intro n i; simp [zC, emb]
  let I : Finset (Fin 4) := Finset.univ.erase i₀
  let fac : Fin 4 → ℕ → MvPolynomial (Fin 3) ℂ := fun i a =>
    (lam i - C (a : ℂ)) * C ((((u i : ℕ) : ℂ) - a)⁻¹)
  refine ⟨∏ i ∈ I, ∏ a ∈ (Finset.range N).erase (u i : ℕ), fac i a, ?_, ?_, ?_⟩
  · -- degree bound
    refine (totalDegree_finsetProd _ _).trans ?_
    have hI : I.card = 3 := by simp [I]
    have : ∀ i ∈ I, (∏ a ∈ (Finset.range N).erase (u i : ℕ), fac i a).totalDegree ≤ N - 1 := by
      intro i _
      refine (totalDegree_finsetProd _ _).trans ?_
      have hcard : ((Finset.range N).erase (u i : ℕ)).card = N - 1 := by
        rw [Finset.card_erase_of_mem (by simp), Finset.card_range]
      calc ∑ a ∈ (Finset.range N).erase (u i : ℕ), (fac i a).totalDegree
          ≤ ∑ _a ∈ (Finset.range N).erase (u i : ℕ), 1 := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine (totalDegree_mul _ _).trans ?_
            rw [totalDegree_C, add_zero]
            exact (totalDegree_sub_C_le _ _).trans (hlam_deg i)
        _ = N - 1 := by simp [hcard]
    calc ∑ i ∈ I, (∏ a ∈ (Finset.range N).erase (u i : ℕ), fac i a).totalDegree
        ≤ ∑ _i ∈ I, (N - 1) := Finset.sum_le_sum this
      _ = 3 * (N - 1) := by simp [hI]
  · -- value 1 at `Au`
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_eq_one fun a ha => ?_
    have hne : ((u i : ℕ) : ℂ) - a ≠ 0 := by
      rw [sub_ne_zero, Ne, Nat.cast_inj]
      exact fun h => (Finset.ne_of_mem_erase ha) h.symm
    simp only [fac, eval_mul, eval_sub, eval_C, hlam_eval _ (hTC u hu), hzC]
    exact mul_inv_cancel₀ hne
  · -- value 0 at the other points
    intro n hn hnu
    have hex : ∃ i ∈ I, n i ≠ u i := by
      by_contra h
      push Not at h
      apply hnu
      have hoff : ∀ i, i ≠ i₀ → n i = u i := fun i hi => h i (by simp [I, hi])
      have h0 : n i₀ = u i₀ := by
        have e1 := hT n hn
        have e2 := hT u hu
        rw [← e2] at e1
        simp only [dotProduct, emb] at e1
        rw [Fin.sum_univ_four, Fin.sum_univ_four] at e1
        have key : r i₀ * ((n i₀ : ℕ) : ℤ) = r i₀ * ((u i₀ : ℕ) : ℤ) := by
          fin_cases i₀ <;> simp_all
        have := mul_left_cancel₀ hi₀ key
        exact Fin.ext (by exact_mod_cast this)
      funext i
      by_cases hi : i = i₀
      · subst hi; exact h0
      · exact hoff i hi
    obtain ⟨i, hiI, hni⟩ := hex
    rw [map_prod]
    refine Finset.prod_eq_zero hiI ?_
    rw [map_prod]
    refine Finset.prod_eq_zero (i := (n i : ℕ)) ?_ ?_
    · simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨fun h => hni (Fin.ext h), (n i).isLt⟩
    · simp only [fac, eval_mul, eval_sub, eval_C, hlam_eval _ (hTC n hn), hzC, sub_self,
        zero_mul]

/-! ### Piece 5 (from lean-checks/Lemma3_P5.lean) -/
/-! ## Piece 5 helpers -/

/-- `𝒫_t` as a submodule when `t ≥ 0`. -/
def p5_PtSub (t : Fin 3 → ℤ) (ht0 : ∀ j, 0 ≤ t j) :
    Submodule ℂ (MvPolynomial (Fin 3) ℂ) := by
  refine ⟨⟨⟨Pt t, ?_⟩, ?_⟩, ?_⟩
  · intro a b ha hb
    simp only [Pt, Set.mem_ofPred_eq] at *
    intro j
    have h := degreeOf_add_le j a b
    have h' : ((a + b).degreeOf j : ℤ) ≤ max (a.degreeOf j : ℤ) (b.degreeOf j : ℤ) := by
      exact_mod_cast h
    exact h'.trans (max_le (ha j) (hb j))
  · simp only [Pt, Set.mem_ofPred_eq]
    intro j
    simp [ht0 j]
  · intro c a ha
    simp only [Pt, Set.mem_ofPred_eq] at *
    intro j
    rw [smul_eq_C_mul]
    exact le_trans (by exact_mod_cast degreeOf_C_mul_le a j c) (ha j)

theorem p5_eval_aeval {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (y : τ → ℂ)
    (p : MvPolynomial σ ℂ) :
    eval y (aeval g p) = eval (fun j => eval y (g j)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, eval_X]

/-! ## Piece 5 theorems -/

theorem exists_annihilator {ι : Type*} [Fintype ι] (t : Fin 3 → ℤ) (ht0 : ∀ j, 0 ≤ t j)
    (f : ι → Fin 3 → ℂ) (h : ¬ Function.Surjective
      (fun B : Pt t => fun n => eval (f n) (B : MvPolynomial (Fin 3) ℂ))) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ ∀ B ∈ Pt t, ∑ n, v n * eval (f n) B = 0 := by
  classical
  let E : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] (ι → ℂ) :=
    LinearMap.pi (fun n => (aeval (f n)).toLinearMap)
  have hE : ∀ B n, E B n = eval (f n) B := by
    intro B n
    simp [E, coe_aeval_eq_eval]
  let M : Submodule ℂ (ι → ℂ) := (p5_PtSub t ht0).map E
  have hM : M ≠ ⊤ := by
    intro hM
    apply h
    intro y
    have hy : y ∈ M := hM ▸ Submodule.mem_top
    obtain ⟨B, hB, hBy⟩ := Submodule.mem_map.1 hy
    refine ⟨⟨B, hB⟩, ?_⟩
    funext n
    rw [← hBy, hE]
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top M (lt_top_iff_ne_top.2 hM)
  refine ⟨fun n => φ (fun j => if n = j then 1 else 0), ?_, ?_⟩
  · intro hv
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have := congrFun hv i
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  · intro B hB
    have hmem : E B ∈ LinearMap.ker φ := hle (Submodule.mem_map_of_mem (p := p5_PtSub t ht0) hB)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ φ] at hmem
    refine Eq.trans (Finset.sum_congr rfl (fun n _ => ?_)) hmem
    show _ * _ = _
    rw [hE, smul_eq_mul, mul_comm]

theorem four_hull_subset_cube (L : ℝ) (X : Set (Fin 4 → ℝ))
    (hX : ∀ x ∈ X, ∀ i, 0 ≤ x i ∧ x i ≤ L) :
    ∀ x ∈ (4 : ℝ) • convexHull ℝ X, ∀ i, 0 ≤ x i ∧ x i ≤ 4 * L := by
  intro x hx i
  obtain ⟨y, hy, rfl⟩ := hx
  have hbox : convexHull ℝ X ⊆ {y : Fin 4 → ℝ | ∀ i, 0 ≤ y i ∧ y i ≤ L} := by
    apply convexHull_min
    · intro z hz
      exact hX z hz
    · intro a ha b hb μ ν hμ hν hμν
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      obtain ⟨a0, a1⟩ := ha i
      obtain ⟨b0, b1⟩ := hb i
      constructor <;> nlinarith
  obtain ⟨h0, h1⟩ := hbox hy i
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor <;> linarith

theorem exists_vanishing (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (b : Fin 3 → ℕ)
    (Z : Finset (Fin 4 → ℤ)) (hZ : Z.card < ∏ j, (b j + 1)) :
    ∃ R : MvPolynomial (Fin 3) ℂ, R ≠ 0 ∧ (∀ j, R.degreeOf j ≤ b j) ∧
      ∀ m ∈ Z, eval (A (zC m)) R = 0 := by
  classical
  set I := Fintype.piFinset (fun j : Fin 3 => Finset.range (b j + 1)) with hI
  let e : (Fin 3 → ℕ) → (Fin 3 →₀ ℕ) := fun s => Finsupp.equivFunOnFinite.symm s
  have he : Function.Injective e := Finsupp.equivFunOnFinite.symm.injective
  let M : Matrix Z I ℂ := fun m s => (e s.1).prod (fun i k => (A (zC m.1)) i ^ k)
  have hcard : Module.finrank ℂ (Z → ℂ) < Module.finrank ℂ (I → ℂ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hI,
      Fintype.card_piFinset, Finset.card_range]
    exact hZ
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin) hcard)
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  obtain ⟨s0, hs0⟩ : ∃ s0, c s0 ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hc0 (funext hne)
  have hcoeff : ∀ m, (∑ s : I, monomial (e s.1) (c s)).coeff m =
      ∑ s : I, if e s.1 = m then c s else 0 := by
    intro m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
  refine ⟨∑ s : I, monomial (e s.1) (c s), ?_, ?_, ?_⟩
  · intro h0
    have h1 := hcoeff (e s0.1)
    rw [h0, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single s0] at h1
    · simp at h1
      exact hs0 h1.symm
    · intro s _ hs
      rw [if_neg]
      intro hes
      exact hs (Subtype.ext (he hes))
    · simp
  · intro j
    rw [degreeOf_le_iff]
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hsm : e s.1 = m := by
      by_contra hne
      simp [hne] at hs
    have hsI : s.1 ∈ Fintype.piFinset (fun j : Fin 3 => Finset.range (b j + 1)) := s.2
    rw [Fintype.mem_piFinset] at hsI
    have := Finset.mem_range.1 (hsI j)
    rw [← hsm]
    have hk : (e s.1) j = s.1 j := by simp [e]
    omega
  · intro m hm
    have h1 := congrFun hc ⟨m, hm⟩
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M] at h1
    rw [map_sum, ← h1]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [eval_monomial, mul_comm]

theorem exists_lattice_nonvanishing (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (hA : Function.Surjective A) (R : MvPolynomial (Fin 3) ℂ) (hR : R ≠ 0) :
    ∃ m : Fin 4 → ℤ, eval (A (zC m)) R ≠ 0 := by
  classical
  let g : Fin 3 → MvPolynomial (Fin 4) ℂ :=
    fun j => ∑ i, C (A (fun k => if i = k then 1 else 0) j) * X i
  have hg : ∀ y, (fun j => eval y (g j)) = A y := by
    intro y
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ A y]
    simp [g, Finset.sum_apply, mul_comm]
  have hP : ∀ y, eval y (aeval g R) = eval (A y) R := fun y => by
    rw [p5_eval_aeval, hg]
  by_contra hcon
  push Not at hcon
  apply hR
  have hP0 : aeval g R = 0 := by
    apply funext_set (fun _ => Set.range (fun n : ℤ => (n : ℂ)))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_range] at hx
    choose m hm using hx
    have hx' : x = zC m := by
      funext i
      simp [zC, hm]
    rw [hx', hP, hcon m, map_zero]
  apply MvPolynomial.funext
  intro z
  obtain ⟨y, rfl⟩ := hA z
  rw [← hP, hP0]
  simp

theorem exists_translate (R : MvPolynomial (Fin 3) ℂ) (w : Fin 3 → ℂ) :
    ∃ R' : MvPolynomial (Fin 3) ℂ, (∀ j, R'.degreeOf j ≤ R.degreeOf j) ∧
      ∀ z, eval z R' = eval (z + w) R := by
  classical
  refine ⟨aeval (fun j => X j + C (w j)) R, ?_, ?_⟩
  · intro j
    conv_lhs => rw [R.as_sum]
    rw [map_sum]
    refine Finset.sum_induction _
      (fun q : MvPolynomial (Fin 3) ℂ => degreeOf j q ≤ degreeOf j R) ?_ ?_ ?_
    · intro a b ha hb
      exact (degreeOf_add_le j a b).trans (max_le ha hb)
    · simp
    · intro s hs
      rw [aeval_monomial, algebraMap_eq, Finsupp.prod_fintype _ _ (by simp)]
      refine (degreeOf_C_mul_le _ _ _).trans ?_
      refine (degreeOf_prod_le _ _ _).trans ?_
      refine le_trans ?_ (monomial_le_degreeOf j hs)
      calc ∑ i, ((X i + C (w i) : MvPolynomial (Fin 3) ℂ) ^ s i).degreeOf j
          ≤ ∑ i, if i = j then s i else 0 := by
            apply Finset.sum_le_sum
            intro i _
            refine (degreeOf_pow_le _ _ _).trans ?_
            have hd : (X i + C (w i) : MvPolynomial (Fin 3) ℂ).degreeOf j ≤
                if i = j then 1 else 0 := by
              refine (degreeOf_add_le _ _ _).trans ?_
              rcases eq_or_ne i j with rfl | hij
              · simp [degreeOf_X, degreeOf_C]
              · simp [degreeOf_X, degreeOf_C, hij, hij.symm]
            rcases eq_or_ne i j with rfl | hij
            · simp only [ite_true] at hd ⊢
              nlinarith
            · simp only [hij, ite_false] at hd ⊢
              simp [Nat.le_zero.1 hd]
        _ = s j := by simp
  · intro z
    rw [p5_eval_aeval]
    have hzw : (fun j => eval z (X j + C (w j) : MvPolynomial (Fin 3) ℂ)) = z + w := by
      funext j
      simp
    rw [hzw]

/-! ## The lemma -/

/-- **Lemma 3** (`lem:interpolation`, tex lines 252–267). -/
theorem interpolation
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (hA : Function.Surjective A)
    (c : Fin 4 → ℂ) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c)
    (N : ℕ) (hN : 1 ≤ N) (t : Fin 3 → ℤ)
    (ht : ∀ j, 3 * ((N : ℤ) - 1) ≤ t j)
    (hbudget : (4 * (N : ℤ) - 3) ^ 4 < ∏ j, (t j - 3 * ((N : ℤ) - 1) + 1)) :
    Function.Surjective
      (fun B : Pt t => fun n : Fin 4 → Fin N =>
        eval (A (fun i => ((n i : ℕ) : ℂ))) (B : MvPolynomial (Fin 3) ℂ)) := by
  classical
  by_contra hns
  -- Step 1: the annihilating weights `v`.
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨v, hv0, hmom⟩ :=
    exists_annihilator t (fun j => by linarith [ht j]) _ hns
  have hfC : ∀ n : Fin 4 → Fin N, (fun i => ((n i : ℕ) : ℂ)) = zC (emb n) := by
    intro n; ext i; simp [zC, emb]
  -- Step 2: `S`, `P`, `𝒦`.
  set S : Finset (Fin 4 → Fin N) := Finset.univ.filter (fun n => v n ≠ 0) with hSdef
  set p : (Fin 4 → Fin N) → Fin 4 → ℝ := fun n => zR (emb n) with hpdef
  set P : Set (Fin 4 → ℝ) := convexHull ℝ (p '' S) with hPdef
  set K : Set (Fin 4 → ℝ) := (4 : ℝ) • P with hKdef
  have hSne : S.Nonempty := by
    by_contra hS
    apply hv0
    ext n
    by_contra hn
    exact hS ⟨n, by simpa [hSdef] using hn⟩
  -- Step 3: `R`.
  set b : Fin 3 → ℕ := fun j => (t j - 3 * ((N : ℤ) - 1)).toNat with hbdef
  have hb : ∀ j, ((b j : ℕ) : ℤ) = t j - 3 * ((N : ℤ) - 1) := fun j =>
    Int.toNat_of_nonneg (by linarith [ht j])
  set Z : Finset (Fin 4 → ℤ) :=
    (Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (4 * ((N : ℤ) - 1))).filter
      (fun m => zR m ∈ K) with hZdef
  have hZcard : Z.card < ∏ j, (b j + 1) := by
    have h1 : Z.card ≤ ((4 * (N : ℤ) - 3).toNat) ^ 4 := by
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      rw [Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      ring
    have h2 : (((4 * (N : ℤ) - 3).toNat ^ 4 : ℕ) : ℤ) < ((∏ j, (b j + 1) : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
      simp only [hb]
      exact hbudget
    exact lt_of_le_of_lt h1 (by exact_mod_cast h2)
  obtain ⟨R, hR0, hRdeg, hRZ⟩ := exists_vanishing A b Z hZcard
  have hpbox : ∀ x ∈ p '' S, ∀ i, 0 ≤ x i ∧ x i ≤ (N : ℝ) - 1 := by
    rintro _ ⟨s, -, rfl⟩ i
    have hlt := (s i).isLt
    refine ⟨by simp [hpdef, zR, emb], ?_⟩
    have : ((s i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hlt
    simp only [hpdef, zR, emb, Int.cast_natCast]
    linarith
  have hRK : ∀ m : Fin 4 → ℤ, zR m ∈ K → eval (A (zC m)) R = 0 := by
    intro m hm
    apply hRZ
    have hc4 := four_hull_subset_cube _ _ hpbox _ hm
    simp only [hZdef, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun i => ?_, hm⟩
    obtain ⟨h0, h1⟩ := hc4 i
    simp only [zR] at h0 h1
    constructor
    · exact_mod_cast h0
    · have : ((m i : ℤ) : ℝ) ≤ ((4 * ((N : ℤ) - 1) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  -- Step 4: lattice points where `R ∘ A` does not vanish.
  set W : Set (Fin 4 → ℤ) := {m | eval (A (zC m)) R ≠ 0} with hWdef
  have hW : W.Nonempty := exists_lattice_nonvanishing A hA R hR0
  -- Step 5: the nearest such point `m`, and `y`, `h`.
  have hKc : IsCompact K := by
    have : IsCompact P :=
      Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((Finset.finite_toSet S).image p)
    simpa [hKdef] using this.image (continuous_const_smul (4 : ℝ))
  have hKcv : Convex ℝ K := (convex_convexHull ℝ _).smul 4
  have hKne : K.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    exact ⟨(4 : ℝ) • p s, Set.smul_mem_smul_set (subset_convexHull ℝ _ ⟨s, hs, rfl⟩)⟩
  obtain ⟨m, hmW, y, hyK, hnear, hmin⟩ := exists_nearest K hKc hKcv hKne W hW
  set h : Fin 4 → ℝ := zR m - y with hhdef
  have hh : h ≠ 0 := by
    intro h0
    have : zR m = y := sub_eq_zero.1 h0
    exact hmW (hRK m (this ▸ hyK))
  -- Step 6: the face `G`, given by its points `F` of `S`.
  set F : Set (Fin 4 → Fin N) :=
    {s | s ∈ S ∧ ∀ s' ∈ S, dotProduct h (p s') ≤ dotProduct h (p s)} with hFdef
  have hq := quarter_mem_face p S h y hyK hnear
  have hFpair : ∀ s ∈ F, ∀ s' ∈ F, dotProduct h (p s) = dotProduct h (p s') :=
    fun s hs s' hs' => le_antisymm (hs'.2 s hs.1) (hs.2 s' hs'.1)
  -- Steps 7–8: the vertex `u`.
  obtain ⟨u, huF, hu4⟩ := exists_heavy_vertex p F h hh hFpair _ hq
  have hyu : y - p u ∈ (3 : ℝ) • P := by
    have e : (4 : ℝ) • ((1 / 4 : ℝ) • y) = y := by
      rw [smul_smul]; norm_num
    rw [e] at hu4
    have hFS : F ⊆ (S : Set _) := fun _ hs => hs.1
    exact Set.smul_set_mono (convexHull_mono (Set.image_mono hFS)) hu4
  -- Steps 9–11: `R` vanishes at `m + n − u` for `n ∈ S` off the face.
  have hoff : ∀ n ∈ S, n ∉ F → eval (A (zC (m + emb n - emb u))) R = 0 := by
    intro n hn hnF
    have hpos : 0 < dotProduct h (p u - p n) := by
      have : ∃ s' ∈ S, dotProduct h (p n) < dotProduct h (p s') := by
        by_contra hc'
        push Not at hc'
        exact hnF ⟨hn, hc'⟩
      obtain ⟨s', hs', hlt⟩ := this
      have := huF.2 s' hs'
      rw [dotProduct_sub]
      linarith
    have hnP : p n ∈ P := subset_convexHull ℝ _ ⟨n, hn, rfl⟩
    obtain ⟨z, hzK, hz⟩ :=
      closer_point P (convex_convexHull ℝ _) h y (p u) (p n) hyu hnP hyK hpos
    by_contra hne
    have hle := hmin (m + emb n - emb u) hne z hzK
    have e1 : zR m = y + h := by simp [hhdef]
    have e2 : zR (m + emb n - emb u) = y + h + (p n - p u) := by
      ext i; simp [zR, hpdef, hhdef]; ring
    rw [e1] at hle
    rw [e2] at hle
    linarith
  -- Step 12: the integer hyperplane `ℋ` through the face, and `r·c ≠ 0`.
  obtain ⟨r, hr0, k, hrk⟩ := exists_int_hyperplane (emb '' F) h hh (by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    exact hFpair s hs s' hs')
  have hrc := int_comb_ne_zero c hc r hr0
  -- Steps 13–14: the Lagrange polynomial `Q`.
  obtain ⟨Q, hQdeg, hQu, hQ0⟩ :=
    exists_lagrange A hA c hker r hrc k N F (fun n hn => hrk _ ⟨n, hn, rfl⟩) u huF
  -- Step 15: `B = Q · R(z + A(m − u)) ∈ 𝒫_t`.
  obtain ⟨R', hR'deg, hR'eval⟩ := exists_translate R (A (zC (m - emb u)))
  have hB : Q * R' ∈ Pt t := by
    intro j
    have h1 := degreeOf_mul_le j Q R'
    have h2 := degreeOf_le_totalDegree Q j
    have h3 := hR'deg j
    have h4 := hRdeg j
    have h5 := hb j
    have h6 : ((Q * R').degreeOf j : ℤ) ≤ (3 * (N - 1) : ℕ) + (b j : ℤ) := by
      exact_mod_cast (h1.trans (Nat.add_le_add (h2.trans hQdeg) (h3.trans h4)))
    have h7 : (((3 * (N - 1) : ℕ)) : ℤ) = 3 * ((N : ℤ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hN]; simp
    linarith
  -- Step 16: the moment sum equals `v_u R(Am) ≠ 0`.
  have hsum := hmom _ hB
  have hterm : ∀ n : Fin 4 → Fin N,
      v n * eval (A (fun i => ((n i : ℕ) : ℂ))) (Q * R') =
        v n * (eval (A (zC (emb n))) Q * eval (A (zC (m + emb n - emb u))) R) := by
    intro n
    have e : zC (emb n) + zC (m - emb u) = zC (m + emb n - emb u) := by
      ext i; simp only [zC, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]; ring
    rw [hfC n, eval_mul, hR'eval, ← map_add, e]
  simp only [hterm] at hsum
  rw [Finset.sum_eq_single u] at hsum
  · have hu : v u ≠ 0 := by
      have := huF.1
      simpa [hSdef] using this
    rw [hQu, one_mul, add_sub_cancel_right] at hsum
    exact mul_ne_zero hu hmW hsum
  · intro n _ hnu
    by_cases hvn : v n = 0
    · simp [hvn]
    have hnS : n ∈ S := by simp [hSdef, hvn]
    by_cases hnF : n ∈ F
    · rw [hQ0 n hnF hnu]; simp
    · rw [hoff n hnS hnF]; simp
  · intro hu; exact absurd (Finset.mem_univ u) hu

end

end Lemma3

end

/-! Adapted from PaperLemma3.Bridge. -/
section
open MvPolynomial Pointwise
namespace Lemma3
noncomputable section
lemma cor4_rpow_nat (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (x ^ (1 / 3 : ℝ)) ^ k = x ^ ((k : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; ring_nf

lemma cor4_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [cor4_rpow_nat x hx 3]; norm_num

lemma cor4_real (H N : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    let T0 := 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)
    let T1 := 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)
    32 * (N : ℝ) ≤ T0 ∧ 32 * (N : ℝ) ≤ T1 ∧ T0 * T1 * T1 = 32 ^ 3 * (N : ℝ) ^ 4 := by
  intro T0 T1
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  set a := (H : ℝ) ^ (1 / 3 : ℝ) with ha
  set b := (N : ℝ) ^ (1 / 3 : ℝ) with hb
  have ha1 : 1 ≤ a := Real.one_le_rpow (by exact_mod_cast hH) (by norm_num)
  have hab : a ≤ b := Real.rpow_le_rpow hH0 (by exact_mod_cast hHN) (by norm_num)
  have hb1 : 1 ≤ b := ha1.trans hab
  have hA2 : (H : ℝ) ^ (2 / 3 : ℝ) = a ^ 2 := by
    rw [ha, cor4_rpow_nat _ hH0 2]; norm_num
  have hAm : (H : ℝ) ^ (-(1 / 3 : ℝ)) = a⁻¹ := by rw [Real.rpow_neg hH0]
  have hB4 : (N : ℝ) ^ (4 / 3 : ℝ) = b ^ 4 := by
    rw [hb, cor4_rpow_nat _ hN0 4]; norm_num
  have hN3 : (N : ℝ) = b ^ 3 := (cor4_cube _ hN0).symm
  have hT0 : T0 = 32 * a ^ 2 * b ^ 4 := by simp only [T0, hA2, hB4]
  have hT1 : T1 = 32 * a⁻¹ * b ^ 4 := by simp only [T1, hAm, hB4]
  have ha0 : 0 < a := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hT0, hN3]
    have : b ^ 3 ≤ a ^ 2 * b ^ 4 := by
      have h1 : 1 ≤ a ^ 2 := one_le_pow₀ ha1
      have h2 : b ^ 3 ≤ b ^ 4 := pow_le_pow_right₀ hb1 (by norm_num)
      nlinarith [pow_pos (by linarith : (0:ℝ) < b) 4]
    nlinarith
  · rw [hT1, hN3]
    have : b ^ 3 ≤ a⁻¹ * b ^ 4 := by
      rw [le_inv_mul_iff₀ ha0]
      have : a * b ^ 3 ≤ b * b ^ 3 :=
        mul_le_mul_of_nonneg_right hab (by positivity)
      nlinarith
    nlinarith
  · rw [hT0, hT1, hN3]
    field_simp

lemma cor4_budget (N : ℕ) (hN : 1 ≤ N) (T : Fin 3 → ℝ) (hT : ∀ j, 32 * (N : ℝ) ≤ T j)
    (hprod : T 0 * T 1 * T 2 = 32 ^ 3 * (N : ℝ) ^ 4) :
    (∀ j, 3 * ((N : ℤ) - 1) ≤ ⌊T j⌋) ∧
      (4 * (N : ℤ) - 3) ^ 4 < ∏ j, (⌊T j⌋ - 3 * ((N : ℤ) - 1) + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨fun j => ?_, ?_⟩
  · rw [Int.le_floor]; push_cast; linarith [hT j]
  · rw [← @Int.cast_lt ℝ]
    push_cast
    rw [Fin.prod_univ_three]
    have hx : ∀ j, T j / 2 < (⌊T j⌋ : ℝ) - 3 * ((N : ℝ) - 1) + 1 := fun j => by
      have := Int.lt_floor_add_one (T j)
      linarith [hT j]
    have hpos : ∀ j, 0 ≤ T j / 2 := fun j => by linarith [hT j]
    have hp : T 0 / 2 * (T 1 / 2) * (T 2 / 2) <
        ((⌊T 0⌋ : ℝ) - 3 * ((N : ℝ) - 1) + 1) * ((⌊T 1⌋ : ℝ) - 3 * ((N : ℝ) - 1) + 1) *
          ((⌊T 2⌋ : ℝ) - 3 * ((N : ℝ) - 1) + 1) :=
      mul_lt_mul'' (mul_lt_mul'' (hx 0) (hx 1) (hpos 0) (hpos 1)) (hx 2)
        (mul_nonneg (hpos 0) (hpos 1)) (hpos 2)
    have he : T 0 / 2 * (T 1 / 2) * (T 2 / 2) = (8 * (N : ℝ)) ^ 4 := by
      have : T 0 / 2 * (T 1 / 2) * (T 2 / 2) = (T 0 * T 1 * T 2) / 8 := by ring
      rw [this, hprod]; ring
    have hl : (4 * (N : ℝ) - 3) ^ 4 < (8 * (N : ℝ)) ^ 4 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
    linarith

theorem rectangle
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (hA : Function.Surjective A)
    (c : Fin 4 → ℂ) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c)
    (H N : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    Submodule.span ℂ
      ((fun α : Fin 3 → ℕ => fun n : Fin 4 → Fin N =>
          A (fun i => ((n i : ℕ) : ℂ)) 0 ^ α 0 * A (fun i => ((n i : ℕ) : ℂ)) 1 ^ α 1 *
            A (fun i => ((n i : ℕ) : ℂ)) 2 ^ α 2) ''
        {α : Fin 3 → ℕ |
          (α 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  classical
  have hN : 1 ≤ N := le_trans hH hHN
  obtain ⟨h0, h1, hprod⟩ := cor4_real H N hH hHN
  set T : Fin 3 → ℝ := ![32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ),
    32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ),
    32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)] with hTdef
  have hT : ∀ j, 32 * (N : ℝ) ≤ T j := by
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h1
  obtain ⟨ht, hb⟩ := cor4_budget N hN T hT hprod
  have hsurj := interpolation A hA c hker hc N hN (fun j => ⌊T j⌋) ht hb
  rw [eq_top_iff]
  rintro w -
  obtain ⟨⟨B, hB⟩, hBw⟩ := hsurj w
  rw [← hBw]
  have hsum : (fun n : Fin 4 → Fin N => eval (A (fun i => ((n i : ℕ) : ℂ))) B) =
      ∑ d ∈ B.support, B.coeff d • (fun n : Fin 4 → Fin N =>
        A (fun i => ((n i : ℕ) : ℂ)) 0 ^ d 0 * A (fun i => ((n i : ℕ) : ℂ)) 1 ^ d 1 *
          A (fun i => ((n i : ℕ) : ℂ)) 2 ^ d 2) := by
    funext n
    rw [eval_eq', Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Fin.prod_univ_three, mul_assoc]
  simp only
  rw [hsum]
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨fun i => d i, ?_, rfl⟩)
  have hdj : ∀ j, (d j : ℝ) ≤ T j := fun j => by
    have h1 := monomial_le_degreeOf j hd
    have h2 := hB j
    have : ((d j : ℕ) : ℤ) ≤ ⌊T j⌋ := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast (Int.le_floor.1 this)
  exact ⟨hdj 0, hdj 1, hdj 2⟩

theorem bridge_descent {K κ ι E : Type*} [Field K] [Fintype κ] [DecidableEq κ]
    [DecidableEq E] (φ : K →+* ℂ) {g : ι → κ → K} {f : ι → E → ℂ} {S : Set ι}
    (ν : κ → E) (hν : Function.Injective ν)
    (hgf : ∀ i j, φ (g i j) = f i (ν j))
    (hf : Submodule.span ℂ (f '' S) = ⊤) :
    Submodule.span K (g '' S) = ⊤ := by
  by_contra hne
  obtain ⟨F, hF0, hFle⟩ :=
    Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let lam : κ → K := fun j => F (fun k => if j = k then 1 else 0)
  have hFapp : ∀ w : κ → K, F w = ∑ j, w j * lam j := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ F w]
    simp [lam, smul_eq_mul]
  obtain ⟨j0, hj0⟩ : ∃ j, lam j ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (LinearMap.ext fun w => by simp [hFapp w, h])
  let G : (E → ℂ) →ₗ[ℂ] ℂ := ∑ j, φ (lam j) • LinearMap.proj (ν j)
  have hGapp : ∀ h : E → ℂ, G h = ∑ j, φ (lam j) * h (ν j) := by
    intro h
    simp [G]
  have hle : Submodule.span ℂ (f '' S) ≤ LinearMap.ker G := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hgi : g i ∈ LinearMap.ker F := hFle (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [LinearMap.mem_ker, hFapp] at hgi
    change G (f i) = 0
    rw [hGapp]
    have : ∑ j, φ (lam j) * f i (ν j) = φ (∑ j, g i j * lam j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hgf, mul_comm]
    rw [this, hgi, map_zero]
  have hzero : G (fun e => if e = ν j0 then 1 else 0) = 0 := by
    have hmem : (fun e => if e = ν j0 then (1 : ℂ) else 0) ∈ LinearMap.ker G :=
      hle (hf ▸ Submodule.mem_top)
    exact hmem
  rw [hGapp, Finset.sum_eq_single j0] at hzero
  · simp only [ite_true, mul_one] at hzero
    exact hj0 ((map_eq_zero_iff φ φ.injective).mp hzero)
  · intro j _ hj
    simp [hν.ne hj]
  · intro h
    exact absurd (Finset.mem_univ j0) h

open OAI.SiegelZeros.WeightedTorusJets in
theorem bridge_main
    {K κ : Type*} [Field K] [NumberField K] [Fintype κ]
    (a b : K) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n) (hn : ∀ j i, n j i < N) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * σ (θ j) ^ α 1 *
        (σ * τ) (θ j) ^ α 2) '' {α : Fin 3 → ℕ |
          (α 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  intro θ
  classical
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨hc, D, hD⟩ := source_same_witness_hyperplane a b φ v hv σ τ hσa hσb hτa hτb
  set c := biquadraticCoefficients (φ a) (φ b) with hcdef
  let M : Matrix (Fin 3) (Fin 4) ℂ := fun j i => (D j : Fin 4 → ℂ) i
  let A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := M.mulVecLin
  -- rows of `M` are linearly independent
  have hrows : LinearIndependent ℂ M.row :=
    D.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  have hrank : Module.finrank ℂ (LinearMap.range A) = 3 := by
    have := hrows.rank_matrix
    simpa [Matrix.rank, A] using this
  have hsurj : Function.Surjective A := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank]
    simp
  -- kernel
  have hform : ∀ x : Fin 4 → ℂ, biquadraticForm (φ a) (φ b) x = ∑ i, c i * x i := by
    intro x
    simp [biquadraticForm, dotProductBilin, dotProduct, c]
  have hcker : c ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker]
    funext j
    have h0 : biquadraticForm (φ a) (φ b) (D j : Fin 4 → ℂ) = 0 := (D j).2
    rw [hform] at h0
    change Matrix.mulVec M c j = 0
    simp only [Matrix.mulVec, dotProduct, M]
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => mul_comm (_ : ℂ) _
  have hc0 : c ≠ 0 := fun h => hc.ne_zero 0 (by rw [h]; rfl)
  have hkerdim : Module.finrank ℂ (LinearMap.ker A) = 1 := by
    have h := A.finrank_range_add_finrank_ker
    rw [hrank] at h
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hker : LinearMap.ker A = Submodule.span ℂ {c} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hcker
    · rw [finrank_span_singleton hc0, hkerdim]
  have hspan := rectangle A hsurj c hker hc H N hH hHN
  -- the column embedding
  let ν : κ → (Fin 4 → Fin N) := fun j i => ⟨n j i, hn j i⟩
  have hν : Function.Injective ν := by
    intro j j' h
    apply hninj
    funext i
    exact congrArg Fin.val (congrFun h i)
  have hAk : ∀ (x : Fin 4 → ℂ) (k : Fin 3), A x k =
      ∑ i, φ ((![![1, a, b, a * b], (fun i => σ (![1, a, b, a * b] i)),
          (fun i => (σ * τ) (![1, a, b, a * b] i))] : Fin 3 → Fin 4 → K) k i) * x i := by
    intro x k
    change Matrix.mulVec M x k = _
    simp only [Matrix.mulVec, dotProduct, M, hD]
  refine bridge_descent φ ν hν ?_ hspan
  intro α j
  have e0 : φ (θ j) = A (fun i => ((ν j i : ℕ) : ℂ)) 0 := by
    rw [hAk]
    simp only [θ, map_sum, map_mul, map_natCast, ν]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have e1 : φ (σ (θ j)) = A (fun i => ((ν j i : ℕ) : ℂ)) 1 := by
    rw [hAk]
    simp only [θ, map_sum, map_mul, map_natCast, ν]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have e2 : φ ((σ * τ) (θ j)) = A (fun i => ((ν j i : ℕ) : ℂ)) 2 := by
    rw [hAk]
    simp only [θ, map_sum, map_mul, map_natCast, ν]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, e0, e1, e2]

end
end Lemma3

end

namespace OAI.SiegelZeros.WeightedTorusJets
theorem actual_biquadratic_rectangle_span
    {K κ : Type*} [Field K] [NumberField K] [Fintype κ]
    (a b : K) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n) (hn : ∀ j i, n j i < N) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * σ (θ j) ^ α 1 *
        (σ * τ) (θ j) ^ α 2) '' {α : Fin 3 → ℕ |
          (α 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  exact Lemma3.bridge_main a b v hv σ τ hσa hσb hτa hτb H N hH hHN n hninj hn

end OAI.SiegelZeros.WeightedTorusJets

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantMasterBounds. -/
section
namespace OAI
namespace SiegelZeros
namespace WeightedTorusJets
open NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_character_global_greedy_determinant_master_bounds :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧ ∃ CH : ℕ → ℝ,
    ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)),
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    (∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ) ∧
                    (∀ β : ℝ, 0 < β → β < 1 →
                      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                    ∀ U : ℝ, 0 ≤ U →
                      (∑ i, (α i 0 : ℝ)) *
                          (Real.log U - C * Real.log q -
                            C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH H) -
                        C * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ) ∧
                    (18818 ≤ N →
                      let P := (greedyPivots B (R ∘ e) s.card).image e
                      let S₁ := ∑ a ∈ P, (a 0 : ℝ)
                      let S₂ := ∑ a ∈ P, ((a 1 : ℝ) + a 2)
                      let M := (N : ℝ) ^ 4
                      let U := (N : ℝ) ^ (4 / 3 : ℝ)
                      M * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁ ∧
                      S₂ ≤ 192 * M * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U ∧
                      0 < S₁ ∧
                      ∀ β : ℝ, 0 < β → β < 1 →
                        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
                        1 ≤ 3 / 4 * (1 + S₂ / S₁) +
                          (C + 1 / 2 * (1 + S₂ / S₁)) * (Real.log q / Real.log U) +
                          C * ((1 - β) * Real.log q) * (Real.log U / Real.log q) +
                          (CH H + (1 + S₂ / S₁) * Real.log 8) / Real.log U +
                          (C * M * U + 1 / 2 * M * Real.log M) / (S₁ * Real.log U)) := by
  classical
  obtain ⟨C, hC, hC4, CH, hlocal⟩ :=
    source_character_global_greedy_determinant_full_local_bounds
  refine ⟨C, hC, hC4, CH, ?_⟩
  intro q _ χ hreal hprim hne hfield
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    hlocal q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
      harch, hdiv, hraw, hfinite⟩ := hsource N H hH hHN n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ,
    harch, hdiv, hraw, hfinite, ?_⟩
  intro hN
  let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let R := fun a : Fin 3 → ℕ => fun j =>
    θ j ^ a 0 * σ (θ j) ^ a 1 * (σ * τ) (θ j) ^ a 2
  let P := (greedyPivots B (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
  let U := (N : ℝ) ^ (4 / 3 : ℝ)
  have hninj : Function.Injective (fun j i => (n j i : ℕ)) := by
    intro j k h
    apply n.injective
    funext i
    exact Fin.ext (congrFun h i)
  have hspan := actual_biquadratic_rectangle_span a' b' v hv σ τ
    hσa hσb hτa hτb H N hH hHN (fun j i => (n j i : ℕ)) hninj
    (fun j i => (n j i).isLt)
  have hpivots := global_source_rectangle_pivot_bounds H N hH hHN hN R e he α hrange hspan
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hH.trans_le hHN
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hS₁ : 0 < ∑ a ∈ P, (a 0 : ℝ) := lt_of_lt_of_le (by positivity) hpivots.1
  refine ⟨hpivots.1, hpivots.2, hS₁, ?_⟩
  intro β hβ0 hβ1 hzero
  have hUone : 1 < U := by
    exact Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α P hrange (fun a => ((a 1 : ℝ) + a 2))
  have hlower := hfinite β hβ0 hβ1 hzero U (le_of_lt (zero_lt_one.trans hUone))
  rw [hS₁eq, hS₂eq] at harch
  rw [hS₁eq] at hlower
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U := by
    dsimp only [U]
    rw [Real.log_rpow hNpos]
    ring
  have hq : 1 < (q : ℝ) := by
    exact_mod_cast (show 1 < q from lt_of_lt_of_le (by decide) (three_le_level_of_nonprincipal χ hne))
  exact FinalComparison.normalized_master_bound hS₁ (Real.log_pos hUone)
    (Real.log_pos hq) hlogN harch hlower

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Selection.GlobalWeightSortedJetEquiv. -/
section
namespace OAI
namespace SiegelZeros
section
namespace WeightedTorusJets
theorem exists_weight_sorted_equiv {α : Type*} [Infinite α] [Encodable α]
    (w : α → ℕ) (hfinite : ∀ B : ℕ, {a : α | w a ≤ B}.Finite) :
    ∃ e : ℕ ≃ α, Monotone (w ∘ e) := by
  classical
  let pred : α → α → Prop := fun a b =>
    w a < w b ∨ (w a = w b ∧ Encodable.encode a < Encodable.encode b)
  let F : α → Finset α := fun b => (hfinite (w b)).toFinset.filter (fun a => pred a b)
  have hmem : ∀ a b, a ∈ F b ↔ pred a b := by
    intro a b
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pred]
    omega
  let rank : α → ℕ := fun a => (F a).card
  have hrank (a b : α) (hab : pred a b) : rank a < rank b := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro c hc
      apply (hmem c b).mpr
      have hca := (hmem c a).mp hc
      dsimp only [pred] at *
      omega
    · intro hEq
      have ha : a ∈ F b := (hmem a b).mpr hab
      rw [← hEq] at ha
      have h := (hmem a a).mp ha
      simp only [pred, lt_self_iff_false, and_false, or_self] at h
  have hinj : Function.Injective rank := by
    intro a b hab
    by_contra hne
    have hcode : Encodable.encode a ≠ Encodable.encode b := fun h =>
      hne (Encodable.encode_injective h)
    have horder : pred a b ∨ pred b a := by
      dsimp only [pred]
      omega
    rcases horder with h | h
    · have := hrank a b h
      omega
    · have := hrank b a h
      omega
  have hweight (a b : α) (hab : rank a ≤ rank b) : w a ≤ w b := by
    by_contra h
    have hlt := hrank b a (Or.inl (Nat.lt_of_not_ge h))
    omega
  let : Infinite (Set.range rank) := (Set.infinite_range_of_injective hinj).to_subtype
  let o : ℕ ≃o Set.range rank := Nat.Subtype.orderIsoOfNat (Set.range rank)
  let r : α ≃ Set.range rank := Equiv.ofInjective rank hinj
  let e : ℕ ≃ α := o.toEquiv.trans r.symm
  have he (i : ℕ) : rank (e i) = (o i : ℕ) :=
    congrArg Subtype.val (r.apply_symm_apply (o i))
  refine ⟨e, ?_⟩
  intro i j hij
  apply hweight
  rw [he, he]
  exact o.monotone hij

theorem exists_global_weight_sorted_jet_equiv (H : ℕ) (hH : 0 < H) :
    ∃ e : ℕ ≃ (Fin 3 → ℕ),
      Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2) := by
  let : Infinite (Fin 3 → ℕ) := Infinite.of_injective
    (fun n : ℕ => fun _ : Fin 3 => n) (fun _ _ h => congrFun h 0)
  apply exists_weight_sorted_equiv (fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2)
  intro B
  apply (Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Iic B)).subset
  intro a ha i
  change a 0 + H * a 1 + H * a 2 ≤ B at ha
  have h1 : a 1 ≤ H * a 1 := Nat.le_mul_of_pos_left _ hH
  have h2 : a 2 ≤ H * a 2 := Nat.le_mul_of_pos_left _ hH
  change a i ≤ B
  fin_cases i <;> dsimp <;> omega

end WeightedTorusJets
end
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.NotEventuallyMaster. -/
section
namespace OAI
namespace SiegelZeros
section
section
open Filter Topology
namespace WeightedTorusJets.FinalComparison
theorem not_eventually_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    {r x e : ι → ℝ} {C A : ℝ}
    (hA : 0 < A) (hchoice : (C + 13 / 24) / A ≤ 1 / 16)
    (hr : ∀ᶠ n in l, r n ≤ 1 / 12)
    (hx : Tendsto x l (𝓝 A)) (he : Tendsto e l (𝓝 0)) :
    ¬ (∀ᶠ n in l,
      1 ≤ 3 / 4 * (1 + r n) + (C + 1 / 2 * (1 + r n)) / x n + e n) := by
  intro hmaster
  have hxpos : ∀ᶠ n in l, 0 < x n := hx.eventually (eventually_gt_nhds hA)
  have hlim : Tendsto
      (fun n ↦ 13 / 16 + (C + 13 / 24) / x n + e n) l
      (𝓝 (13 / 16 + (C + 13 / 24) / A)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div hx hA.ne')).add he
  have hle : 1 ≤ 13 / 16 + (C + 13 / 24) / A := ge_of_tendsto hlim (by
    filter_upwards [hr, hxpos, hmaster] with n hrn hxn hn
    have hfirst : 3 / 4 * (1 + r n) ≤ (13 : ℝ) / 16 := by linarith
    have hsecond : (C + 1 / 2 * (1 + r n)) / x n ≤ (C + 13 / 24) / x n :=
      (div_le_div_iff_of_pos_right hxn).mpr (by linarith)
    linarith)
  linarith

end WeightedTorusJets.FinalComparison
end
section
open Filter Real
open scoped Topology
namespace WeightedTorusJets
theorem tendsto_log_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log (⌈q ^ γ⌉₊ : ℝ) / log q) atTop (𝓝 γ) := by
  have hpow := tendsto_rpow_atTop hγ
  have hratio : Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) / q ^ γ) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop.comp hpow
  have hlog : Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) / q ^ γ)) atTop (𝓝 0) := by
    simpa using hratio.log one_ne_zero
  have herr := hlog.div_atTop tendsto_log_atTop
  have hsum := herr.add_const γ
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
  have hq₀ : 0 < q := lt_trans zero_lt_one hq
  have hqp : 0 < q ^ γ := rpow_pos_of_pos hq₀ γ
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) := lt_of_lt_of_le hqp (Nat.le_ceil _)
  rw [log_div hceil.ne' hqp.ne', log_rpow hq₀]
  field_simp [(log_pos hq).ne']
  ring

theorem tendsto_log_scale_natCeil_rpow_div_log {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ log ((⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) / log q)
      atTop (𝓝 (4 * γ / 3)) := by
  have h := (tendsto_log_natCeil_rpow_div_log hγ).const_mul (4 / 3 : ℝ)
  have heq : (4 / 3 : ℝ) * γ = 4 * γ / 3 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  have hceil : 0 < (⌈q ^ γ⌉₊ : ℝ) :=
    lt_of_lt_of_le (rpow_pos_of_pos hq γ) (Nat.le_ceil _)
  rw [log_rpow hceil]
  ring

theorem tendsto_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ ⌈q ^ γ⌉₊) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop hγ)

theorem tendsto_scale_natCeil_rpow_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ ↦ (⌈q ^ γ⌉₊ : ℝ) ^ (4 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_natCeil_rpow_atTop hγ))

theorem exists_gamma_second_term_bound (C : ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ (C + 13 / 24) / (4 * γ / 3) < 1 / 16 := by
  refine ⟨12 * (|C| + 1), by positivity, ?_⟩
  have hC : C ≤ |C| := le_abs_self C
  rw [div_lt_iff₀ (by positivity : 0 < 4 * (12 * (|C| + 1)) / 3)]
  linarith

theorem log_degree_four_eq_three_log_scale {N : ℝ} (hN : 0 < N) :
    log (N ^ (4 : ℕ)) = 3 * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_pow, log_rpow hN]
  ring

theorem log_eq_three_quarters_log_scale {N : ℝ} (hN : 0 < N) :
    log N = (3 / 4 : ℝ) * log (N ^ (4 / 3 : ℝ)) := by
  rw [log_rpow hN]
  ring

end WeightedTorusJets
end
section
namespace WeightedTorusJets
theorem weight_rpow_shift {H : ℝ} (hH : 0 < H) :
    H ^ (-1 / 3 : ℝ) * H = H ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_add_one hH.ne']
  norm_num

theorem pivot_ratio_le {H M U S₁ S₂ : ℝ} (hH : 0 < H) (hM : 0 < M)
    (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 7226112 / H := by
  have hpow : 0 < H ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hH _
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  rw [div_le_div_iff₀ hS₁pos hH]
  have hmul := mul_le_mul_of_nonneg_right hS₂ hH.le
  have hlower := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 * 97 ^ 2)).mp hS₁
  calc
    S₂ * H ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U * H := hmul
    _ = 192 * (M * H ^ (2 / 3 : ℝ) * U) := by rw [← weight_rpow_shift hH]; ring
    _ ≤ 7226112 * S₁ := by nlinarith

theorem pivot_ratio_le_one_twelfth {H M U S₁ S₂ : ℝ} (hH : 86713344 ≤ H)
    (hM : 0 < M) (hU : 0 < U)
    (hS₁ : M * H ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * H ^ (-1 / 3 : ℝ) * U) :
    S₂ / S₁ ≤ 1 / 12 := by
  have hHpos : 0 < H := by linarith
  exact (pivot_ratio_le hHpos hM hU hS₁ hS₂).trans
    ((div_le_iff₀ hHpos).mpr (by linarith))

end WeightedTorusJets
end
section
open Filter
open scoped Topology
namespace WeightedTorusJets
theorem normalized_error_component_bounds {M U S A : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    M * U / (S * Real.log U) ≤ 1 / (A * Real.log U) ∧
      M * Real.log M / (S * Real.log U) ≤ 3 / (A * U) := by
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hL : 0 < Real.log U := Real.log_pos hU
  have hden : 0 < A * M * U * Real.log U := by positivity
  have hden_le : A * M * U * Real.log U ≤ S * Real.log U :=
    mul_le_mul_of_nonneg_right hS hL.le
  constructor
  · calc
      M * U / (S * Real.log U) ≤ M * U / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left (by positivity) hden hden_le
      _ = _ := by field_simp
  · have hnum : 0 ≤ M * Real.log M := by rw [hlog]; positivity
    calc
      M * Real.log M / (S * Real.log U) ≤
          M * Real.log M / (A * M * U * Real.log U) :=
        div_le_div_of_nonneg_left hnum hden hden_le
      _ = _ := by rw [hlog]; field_simp

theorem determinant_error_le {M U S A C : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hA : 0 < A) (hC : 0 ≤ C)
    (hS : A * M * U ≤ S) (hlog : Real.log M = 3 * Real.log U) :
    (C * M * U + (1 / 2 : ℝ) * M * Real.log M) / (S * Real.log U) ≤
      C / (A * Real.log U) + 3 / (2 * A * U) := by
  obtain ⟨hfirst, hsecond⟩ := normalized_error_component_bounds hM hU hA hS hlog
  calc
    _ = C * (M * U / (S * Real.log U)) +
        (1 / 2 : ℝ) * (M * Real.log M / (S * Real.log U)) := by ring
    _ ≤ C * (1 / (A * Real.log U)) + (1 / 2 : ℝ) * (3 / (A * U)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst hC)
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by ring

end WeightedTorusJets
end
section
namespace WeightedTorusJets.FinalComparison
theorem uniform_master_bound {L M U ℓ S₁ S₂ δ C C_H D : ℝ}
    (hM : 0 < M) (hU : 1 < U) (hℓ : 0 < ℓ) (hD : 0 < D) (hC : 0 ≤ C)
    (hS₁ : D * M * U ≤ S₁) (hr : S₂ / S₁ ≤ 1 / 12)
    (hlogM : Real.log M = 3 * Real.log U)
    (hupper : L ≤ M / 2 * Real.log M +
      (S₁ + S₂) * (3 / 4 * Real.log U + 1 / 2 * ℓ + Real.log 8))
    (hlower : S₁ * (Real.log U - C * ℓ - C * δ * Real.log U ^ 2 / ℓ - C_H) -
      C * M * U ≤ L) :
    1 ≤ 13 / 16 + (C + 13 / 24) * (ℓ / Real.log U) +
      C * δ * (Real.log U / ℓ) + (C_H + 13 / 12 * Real.log 8) / Real.log U +
      C / (D * Real.log U) + 3 / (2 * D * U) := by
  have hUpos : 0 < U := zero_lt_one.trans hU
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hS₁pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  have hmaster := normalized_master_bound hS₁pos hlogU hℓ rfl hupper hlower
  have hfirst : 3 / 4 * (1 + S₂ / S₁) ≤ (13 : ℝ) / 16 := by linarith
  have hsecond : (C + 1 / 2 * (1 + S₂ / S₁)) * (ℓ / Real.log U) ≤
      (C + 13 / 24) * (ℓ / Real.log U) :=
    mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hℓ.le hlogU.le)
  have hfixed : (C_H + (1 + S₂ / S₁) * Real.log 8) / Real.log U ≤
      (C_H + 13 / 12 * Real.log 8) / Real.log U := by
    apply (div_le_div_iff_of_pos_right hlogU).mpr
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have := mul_le_mul_of_nonneg_right (by linarith : 1 + S₂ / S₁ ≤ 13 / 12) hlog8
    linarith
  have hdet := WeightedTorusJets.determinant_error_le hM hU hD hC hS₁ hlogM
  linarith

end WeightedTorusJets.FinalComparison
end
section
namespace WeightedTorusJets
open Filter Topology
theorem exists_fixed_parameters_not_eventually_uniform_bound (C : ℝ) :
    ∃ H : ℕ, 86713344 ≤ H ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ (q δ : ℕ → ℝ) (C_H : ℝ),
        Tendsto q atTop atTop → Tendsto δ atTop (𝓝 0) →
        let N : ℕ → ℝ := fun k ↦ (⌈q k ^ γ⌉₊ : ℝ)
        let U : ℕ → ℝ := fun k ↦ N k ^ (4 / 3 : ℝ)
        let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
        ¬ (∀ᶠ k in atTop,
          1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q k) / Real.log (U k)) +
            C * δ k * (Real.log (U k) / Real.log (q k)) +
            (C_H + 13 / 12 * Real.log 8) / Real.log (U k) +
            C / (D * Real.log (U k)) + 3 / (2 * D * U k)) := by
  obtain ⟨γ, hγ, hchoice⟩ := exists_gamma_second_term_bound C
  refine ⟨86713344, le_rfl, γ, hγ, ?_⟩
  intro q δ C_H hq hδ N U D hbound
  have hD : 0 < D := by dsimp [D]; positivity
  have hU : Tendsto U atTop atTop := (tendsto_scale_natCeil_rpow_atTop hγ).comp hq
  have hlogU := Real.tendsto_log_atTop.comp hU
  have hratio : Tendsto (fun k ↦ Real.log (U k) / Real.log (q k))
      atTop (𝓝 (4 * γ / 3)) := (tendsto_log_scale_natCeil_rpow_div_log hγ).comp hq
  have hδterm : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)))
      atTop (𝓝 0) := by simpa using (hδ.const_mul C).mul hratio
  have hfixed := (tendsto_const_nhds (x := C_H + 13 / 12 * Real.log 8)).div_atTop hlogU
  have hdet₁ := (tendsto_const_nhds (x := C)).div_atTop (hlogU.const_mul_atTop hD)
  have hdet₂ := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop
    (hU.const_mul_atTop (by positivity : 0 < 2 * D))
  have herror : Tendsto (fun k ↦ C * δ k * (Real.log (U k) / Real.log (q k)) +
      (C_H + 13 / 12 * Real.log 8) / Real.log (U k) + C / (D * Real.log (U k)) +
      3 / (2 * D * U k)) atTop (𝓝 0) := by
    simpa using ((hδterm.add hfixed).add hdet₁).add hdet₂
  apply FinalComparison.not_eventually_master (r := fun _ ↦ (1 / 12 : ℝ))
    (by positivity) hchoice.le (.of_forall fun _ ↦ le_rfl) hratio herror
  filter_upwards [hbound] with k hk
  simpa only [show (3 / 4 : ℝ) * (1 + 1 / 12) = 13 / 16 by norm_num,
    show (1 / 2 : ℝ) * (1 + 1 / 12) = 13 / 24 by norm_num,
    div_div_eq_mul_div, mul_div_assoc, add_assoc] using hk

end WeightedTorusJets
end
end
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Structure.QuadraticEigencharacter. -/
section
namespace OAI
namespace SiegelZeros
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem characterField_ne_sourceSqrtTwoField_of_ne_eight (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) := by
  intro hfield
  have hdiscr := characterField_changeLevel_discr_natAbs
    (L := CyclotomicField (8 * q) ℚ) (dvd_mul_left q 8) χ hquad hprim hne
  have htwo := (quadraticAdjoin_discriminant _ 2
    (sourceSqrtTwoField_root_sq q (CyclotomicField (8 * q) ℚ))
    (Int.squarefree_natAbs.mp Nat.prime_two.squarefree) not_isSquare_rat_two).1
  change NumberField.discr (sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) = _ at htwo
  norm_num at htwo
  rw [hfield, htwo] at hdiscr
  exact hq8 (by simpa using hdiscr.symm)

end WeightedTorusJets
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.EntireFunctions.RealZeroUniformMasterBound. -/
section
namespace OAI
namespace SiegelZeros
section
namespace WeightedTorusJets
open scoped BigOperators NumberField
open scoped OAI.SiegelZeros.WeightedTorusJets
theorem source_real_zero_uniform_master_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 86713344 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 →
      ∀ χ : DirichletCharacter ℂ q,
        (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      ∀ N : ℕ, H ≤ N → 18818 ≤ N →
      let U : ℝ := (N : ℝ) ^ (4 / 3 : ℝ)
      let D : ℝ := (H : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)
      1 ≤ 13 / 16 + (C + 13 / 24) * (Real.log (q : ℝ) / Real.log U) +
        C * ((1 - β) * Real.log (q : ℝ)) * (Real.log U / Real.log (q : ℝ)) +
        (CH + 13 / 12 * Real.log 8) / Real.log U +
        C / (D * Real.log U) + 3 / (2 * D * U) := by
  classical
  obtain ⟨C, hC, _hC4, CH, hsource⟩ :=
    source_character_global_greedy_determinant_master_bounds
  refine ⟨C, hC, ?_⟩
  intro H hH
  have hHnat : 0 < H := by omega
  obtain ⟨e, he⟩ := exists_global_weight_sorted_jet_equiv H hHnat
  refine ⟨CH H, ?_⟩
  intro q _ hq hq8 χ hreal hprim hne
  have hfield := characterField_ne_sourceSqrtTwoField_of_ne_eight q χ hprim
    (real_character_isQuadratic χ hreal) hne hq8
  obtain ⟨d, a, b, _hd, _hdsize, _hddiv, _hdns, _ha, _hb, _hfield, _hdisc,
    _hfund, _hformula, v, _hv, _hint, _hdegree, σ, τ, _hσa, _hσb, _hτa, _hτb,
    _hcard, _hall, _hcomm, hdata⟩ := hsource q χ hreal hprim hne hfield
  intro β hβ0 hβ1 hzero N hHN hN U D
  let n : Fin (N ^ 4) ≃ (Fin 4 → Fin N) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin 4 → Fin N) = N ^ 4)).symm
  obtain ⟨g, α, _hg, _hα, hrange, _hmono, _hweight, _hstable,
    Δ, _hΔ, _hΔne, harch, _hdiv, _hraw, hfinite, hlarge⟩ := hdata N H hHnat hHN n e he
  obtain ⟨hpivot₁, hpivot₂, _hSpos, _hmaster⟩ := hlarge hN
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α _ hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α _ hrange
    (fun a => ((a 1 : ℝ) + a 2))
  rw [← hS₁eq] at hpivot₁
  rw [← hS₂eq] at hpivot₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hHnat.trans_le hHN
  have hM : 0 < (N : ℝ) ^ 4 := pow_pos hNpos _
  have hUone : 1 < U := Real.one_lt_rpow
    (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hS₁ : D * (N : ℝ) ^ 4 * U ≤ ∑ i, (α i 0 : ℝ) := by
    convert hpivot₁ using 1
    dsimp [D, U]
    ring
  have hratio : (∑ i, ((α i 1 : ℝ) + α i 2)) / (∑ i, (α i 0 : ℝ)) ≤ 1 / 12 :=
    pivot_ratio_le_one_twelfth (H := (H : ℝ)) (M := (N : ℝ) ^ 4) (U := U)
      (by exact_mod_cast hH) hM (zero_lt_one.trans hUone)
      (by simpa only [U] using hpivot₁)
      (by simpa only [U, neg_div] using hpivot₂)
  have hlower := hfinite β hβ0 hβ1 hzero U (zero_lt_one.trans hUone).le
  have hlogM : Real.log ((N : ℝ) ^ 4) = 3 * Real.log U :=
    log_degree_four_eq_three_log_scale hNpos
  have hlogN : Real.log (N : ℝ) = 3 / 4 * Real.log U :=
    log_eq_three_quarters_log_scale hNpos
  apply FinalComparison.uniform_master_bound hM hUone
    (Real.log_pos (by exact_mod_cast (show 1 < q by omega))) hD hC.le hS₁ hratio hlogM
    ?_ hlower
  simpa only [hlogN] using harch

end WeightedTorusJets
end
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.DirichletRealZeroBound. -/
section
namespace OAI
namespace SiegelZeros
section
namespace WeightedTorusJets
open Filter Topology
theorem dirichlet_real_zero_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  by_contra hnot
  obtain ⟨q, hq, χ, β, hadm, hqtop, hgap⟩ := exists_contrary_sequence hnot
  obtain ⟨C, _hC, hsource⟩ := source_real_zero_uniform_master_bound
  obtain ⟨H, hH, γ, hγ, hno⟩ := exists_fixed_parameters_not_eventually_uniform_bound C
  obtain ⟨CH, hCH⟩ := hsource H hH
  have hqreal : Tendsto (fun n => (q n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqtop
  apply hno (fun n => (q n : ℝ)) (fun n => (1 - β n) * Real.log (q n : ℝ)) CH hqreal hgap
  have hNtop : Tendsto (fun n => ⌈(q n : ℝ) ^ γ⌉₊) atTop atTop :=
    (tendsto_natCeil_rpow_atTop hγ).comp hqreal
  filter_upwards [hNtop.eventually_ge_atTop H, hNtop.eventually_ge_atTop 18818,
    hqtop.eventually_ne_atTop 8] with n hnH hnN hn8
  let := hq n
  exact hCH (q n) (hadm n).1 hn8 (χ n) (hadm n).2.2.2.1
    (hadm n).2.1 (hadm n).2.2.1 (β n) (hadm n).2.2.2.2.1
    (hadm n).2.2.2.2.2.1 (hadm n).2.2.2.2.2.2
    ⌈(q n : ℝ) ^ γ⌉₊ hnH hnN

end WeightedTorusJets
end
end SiegelZeros
end OAI

end

/-! Adapted from OAI.NumberTheory.SiegelZeros.Characters.DirichletRealZeroBoundProof. -/
section
namespace OAI
namespace SiegelZeros
section
theorem WeightedTorusJets.dirichletRealZeroBound_proof :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  exact WeightedTorusJets.dirichlet_real_zero_bound

end
end SiegelZeros
end OAI

end

namespace GoldbachResearch.PrimitiveSiegel

open DirichletCharacter

def PrimitiveGap : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ, 0 < β → β < 1 →
        χ.LFunction (β : ℂ) = 0 → c ≤ (1 - β) * Real.log (q : ℝ)

private theorem real_of_square_one {m : ℕ} {χ : DirichletCharacter ℂ m}
    (h : χ ^ 2 = 1) (a : ZMod m) : (χ a).im = 0 := by
  by_cases hu : IsUnit a
  · have hval := congrArg (fun ξ : DirichletCharacter ℂ m => ξ a) h
    have hsq : (χ a)^2 = 1 := by
      simpa [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using hval
    rcases sq_eq_one_iff.mp hsq with h1 | h1 <;> simp [h1]
  · simp [χ.map_nonunit hu]

private theorem level_lower_bound {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hχ : χ ≠ 1) : 3 ≤ m := by
  by_contra! h
  have hm := NeZero.ne m
  have hsmall : m = 1 ∨ m = 2 := by omega
  rcases hsmall with rfl | rfl
  · exact hχ (DirichletCharacter.level_one χ)
  · apply hχ
    apply MulChar.eq_one_iff.mpr
    intro u
    have hu : u = 1 := (by decide : ∀ u : (ZMod 2)ˣ, u = 1) u
    simp [hu]

private theorem changeLevel_nonzero {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m ∣ q) (χ : DirichletCharacter ℂ m) {β : ℝ} (hβ : 0 < β) (hβ' : β < 1)
    (hL : χ.LFunction (β : ℂ) ≠ 0) :
    ((changeLevel hmq) χ).LFunction (β : ℂ) ≠ 0 := by
  have hne : (β : ℂ) ≠ 1 := by exact_mod_cast hβ'.ne
  rw [LFunction_changeLevel hmq χ (.inr hne)]
  apply mul_ne_zero hL
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hs : ‖(p : ℂ) ^ (-(β : ℂ))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt)
      (by simpa using neg_lt_zero.mpr hβ)
  have hl : ‖χ (p : ZMod m) * (p : ℂ) ^ (-(β : ℂ))‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans_lt hs
  intro he
  rw [(sub_eq_zero.mp he).symm, norm_one] at hl
  exact lt_irrefl _ hl

open Filter Set
open scoped Topology

private theorem principal_window : ∃ d : ℝ, 0 < d ∧
    ∀ β : ℝ, 1 - d < β → β < 1 → riemannZeta (β : ℂ) ≠ 0 := by
  have hev := riemannZeta_residue_one.eventually_ne (show (1 : ℂ) ≠ 0 by norm_num)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨d, hd, ?_⟩
  intro β hβl hβu hzero
  have hb : (β : ℂ) ∈ Metric.ball (1 : ℂ) d := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : β - 1 < 0)]
    linarith
  have hn : (β : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hβu)
  have h := hball ⟨hb, hn⟩
  exact h (by simp [hzero])

theorem no_siegel_zero_of_primitive_gap (hgap : PrimitiveGap) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
      χ ^ 2 = 1 → 1 - c / Real.log ((q : ℝ) + 2) < β → β < 1 →
        DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  obtain ⟨u, hu, hzero⟩ := hgap
  obtain ⟨d, hd, hprincipal⟩ := principal_window
  let c := min u (min 1 d * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c, lt_min hu (mul_pos (lt_min zero_lt_one hd) hlog2), ?_⟩
  intro q _ χ β hsq hleft hright
  have hlog : Real.log 2 ≤ Real.log ((q:ℝ)+2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hlogpos := hlog2.trans_le hlog
  have hwidth : c / Real.log ((q:ℝ)+2) ≤ min 1 d := by
    apply (div_le_iff₀ hlogpos).mpr
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hlog (le_min (by norm_num) hd.le))
  have hβ : 0 < β := by linarith [hwidth.trans (min_le_left 1 d)]
  by_cases hχ : χ = 1
  · subst χ
    have hζ := hprincipal β (by linarith [hwidth.trans (min_le_right 1 d)]) hright
    have hbase : (1 : DirichletCharacter ℂ 1).LFunction (β:ℂ) ≠ 0 := by
      simpa only [LFunction_modOne_eq] using hζ
    simpa only [map_one] using changeLevel_nonzero (one_dvd q) 1 hβ hright hbase
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have heq := χ.changeLevel_primitiveCharacter
  have hprim : χ.primitiveCharacter ≠ 1 := fun h => hχ (by simpa [h] using heq.symm)
  have hs : χ.primitiveCharacter ^ 2 = 1 := by
    apply (changeLevel_eq_one_iff χ.conductor_dvd_level).1
    rw [map_pow, heq, hsq]
  have hn := level_lower_bound χ.primitiveCharacter hprim
  have hle : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hclog : Real.log (χ.conductor : ℝ) ≤ Real.log ((q:ℝ)+2) :=
    Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt hn) (by linarith)
  have hbase : χ.primitiveCharacter.LFunction (β:ℂ) ≠ 0 := by
    intro hL
    have h := hzero χ.conductor hn χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hprim
      (real_of_square_one hs) β hβ hright hL
    have hsmall : (1-β) * Real.log ((q:ℝ)+2) < c := (lt_div_iff₀ hlogpos).mp (by linarith)
    exact (not_lt_of_ge (min_le_left _ _)) ((h.trans
      (mul_le_mul_of_nonneg_left hclog (sub_nonneg.mpr hright.le))).trans_lt hsmall)
  simpa only [heq] using changeLevel_nonzero χ.conductor_dvd_level χ.primitiveCharacter hβ hright hbase

end GoldbachResearch.PrimitiveSiegel

theorem PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ), χ ^ 2 = 1 → 1 - c / Real.log ((q : ℝ) + 2) < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  apply GoldbachResearch.PrimitiveSiegel.no_siegel_zero_of_primitive_gap
  obtain ⟨c, hc, hbound⟩ := OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof
  refine ⟨c, hc, ?_⟩
  intro q hq hthree χ hprim hne hreal β hpos hlt hzero
  exact hbound q hthree χ hprim hne hreal β ⟨hpos, hlt, hzero⟩
