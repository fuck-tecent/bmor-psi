import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import PEqualNP.Outside.L_goldbach_continuous_parseval
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli

/-
Prime arrivals with a small prime summand in the dyadic square-root window.
SPDX-License-Identifier: Apache-2.0. The license text accompanies this file in LICENSE.

This proof adapts the zero-density, explicit-formula, and window-average arguments in
goldbach-proofs, including LogTruSoul's PRs 2845 and 3746. The weighted moment
bounds below retain exponent 3, include the reflected zeros, and use adjacent dyadic
windows at the edge of the smoothed prime sum. The Fourier comparison uses the
published Estermann almost-all estimate and the continuous Parseval development.

Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Sources credited in the analytic development include openai/math, revision
3344da59991ed94f9ba711217b29c1d760badfa6, and
AlexKontorovich/PrimeNumberTheoremAnd, revision c39a751132c88b6e8080b74c74023fd95b3d8be0,
with rectangle calculations at 2c476fa6441c607096d93c8fc7ac0a227a655dae.
Additional goldbach-proofs contributions used in that development are DNZJSJ
(PR 2486), muxkin (PR 2458), DFQDZZ (PR 316), XianWu18 (PR 207), and wzhxzkk (PR 203).
-/

-- FrozenModel
section

open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped ComplexConjugate BigOperators

namespace ThinWindowModel

private theorem phase_addition (u v : ℝ) : phase (u+v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_negation (u : ℝ) : phase (-u) = conj (phase u) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The expected value of the model after averaging the long prime over the units
of a modulus. The frozen large target n and the small prime n-b enter with opposite signs. -/
theorem reduced_mean (q n : ℕ) :
    (∑ b ∈ (range q).filter (fun r => Nat.Coprime r q),
      ∑ a ∈ (range q).filter (fun r => Nat.Coprime r q),
        unitMean q a * phase (((b:ℝ)-n)*a/q)) / (q.totient:ℂ) =
      coefficient q n := by
  let U := (range q).filter (fun r => Nat.Coprime r q)
  change (∑ b ∈ U, ∑ a ∈ U, _) / _ = _
  rw [sum_comm, sum_div]
  have row (a : ℕ) (ha : a ∈ U) :
      (∑ b ∈ U, unitMean q a * phase (((b:ℝ)-n)*a/q)) / (q.totient:ℂ) =
      (ram q 1/(q.totient:ℂ))^2 * conj (phase ((n:ℝ)*a/q)) := by
    let scalar := unitMean q a * conj (phase ((n:ℝ)*a/q))
    have split (b : ℕ) : unitMean q a * phase (((b:ℝ)-n)*a/q) =
        scalar * phase ((a:ℝ)*b/q) := by
      rw [show ((b:ℝ)-n)*a/q = -((n:ℝ)*a/q)+(a:ℝ)*b/q by ring,
        phase_addition, phase_negation]
      dsimp [scalar]
      ring
    simp_rw [split]
    rw [← mul_sum]
    change (unitMean q a * conj (phase ((n:ℝ)*a/q))) * ram q a / _ = _
    rw [unitMean_eq_ram (mem_filter.mp ha).2, ram_unit _ _ (mem_filter.mp ha).2]
    ring
  rw [sum_congr rfl row, ← mul_sum]
  unfold coefficient ram
  rw [map_sum]

theorem even_series_floor {Q n : ℕ} (hQ : 1 ≤ Q) (hn : Even n) :
    (1:ℝ)/3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re := by
  let w : ℕ → ℝ := fun q => if q ≤ Q then 1 else 0
  have h := arithmetic_floor (Q := Q) hn w
    (by intro q; dsimp [w]; split <;> norm_num)
    (by intro i j hi hij; dsimp [w]; split <;> split <;> norm_num <;> omega)
    (by intro q hq; simp [w,not_le.mpr hq])
  calc
    (1:ℝ)/3 = w 1 / 3 := by simp [w,hQ]
    _ ≤ _ := h
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      simp [w,(mem_Icc.mp hq).2]

end ThinWindowModel

end

-- ResidueMass
section

open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped BigOperators
namespace ThinWindowModel

def units (q : ℕ) := (range q).filter (fun r => Nat.Coprime r q)

private lemma units_card (q : ℕ) : (units q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext k
  simp [units, Nat.coprime_comm]

private lemma phase_abs (u : ℝ) : ‖phase u‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma unit_mean_norm {q : ℕ} (hq : 0 < q) (a : ℕ) : ‖unitMean q a‖ ≤ 1 := by
  have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  apply (norm_sum_le _ _).trans
  change ∑ r ∈ units q, ‖phase ((r:ℝ) * ((a:ℝ)/q))‖ ≤ _
  simp only [phase_abs, sum_const, nsmul_eq_mul, mul_one, units_card, le_refl]

noncomputable def rowWeight (q n b : ℕ) : ℂ :=
  ∑ a ∈ units q, unitMean q a * phase (((b:ℝ)-n)*a/q)

noncomputable def measuredRow (q n : ℕ) (F : ℕ → ℝ) : ℂ :=
  ∑ b ∈ units q, (F b : ℂ) * rowWeight q n b

theorem row_weight_bound {q : ℕ} (hq : 0 < q) (n b : ℕ) :
    ‖rowWeight q n b‖ ≤ (q.totient:ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ units q, (1:ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [norm_mul]
      simpa only [phase_abs,mul_one] using unit_mean_norm hq a
    _ = _ := by simp [units_card]

theorem constant_row (q n : ℕ) (D : ℝ) :
    measuredRow q n (fun _ => D / (q.totient:ℝ)) = (D:ℂ) * coefficient q n := by
  unfold measuredRow
  rw [← mul_sum]
  push_cast
  have hrow : (∑ b ∈ units q, rowWeight q n b) / (q.totient:ℂ) = coefficient q n := reduced_mean q n
  rw [← hrow]
  ring

theorem row_discrepancy {q : ℕ} (hq : 0 < q) (n : ℕ) (D : ℝ) (F : ℕ → ℝ) :
    ‖measuredRow q n F - (D:ℂ)*coefficient q n‖ ≤
      (q.totient:ℝ) * ∑ b ∈ units q, |F b - D/(q.totient:ℝ)| := by
  rw [← constant_row,measuredRow,measuredRow,← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum (fun b hb => ?_)
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (row_weight_bound hq n b) (abs_nonneg _)

theorem model_floor_with_errors {Q n : ℕ} (hQ : 1 ≤ Q) (hn : Even n)
    (D : ℝ) (hD : 0 ≤ D) (F : ℕ → ℕ → ℝ) :
    D/3 - ∑ q ∈ Icc 1 Q, (q.totient:ℝ) * ∑ b ∈ units q, |F q b - D/q.totient| ≤
      (∑ q ∈ Icc 1 Q, measuredRow q n (F q)).re := by
  have floor := mul_le_mul_of_nonneg_left (even_series_floor hQ hn) hD
  have sumerr : (∑ q ∈ Icc 1 Q, D * (coefficient q n).re) -
      ∑ q ∈ Icc 1 Q, (measuredRow q n (F q)).re ≤
      ∑ q ∈ Icc 1 Q, (q.totient:ℝ) * ∑ b ∈ units q, |F q b-D/q.totient| := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro q hq
    have h := row_discrepancy (show 0 < q from (mem_Icc.mp hq).1) n D (F q)
    rw [norm_sub_rev] at h
    have reBound := (Complex.re_le_norm ((D:ℂ)*coefficient q n - measuredRow q n (F q))).trans h
    simpa [Complex.sub_re,Complex.mul_re] using reBound
  rw [Complex.re_sum]
  rw [mul_sum] at floor
  linarith
end ThinWindowModel

end

-- ModelWeights
section

open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped BigOperators ComplexConjugate
namespace ThinWindowModel

lemma phase_conj (u : ℝ) : phase (-u) = conj (phase u) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma ram_im_zero (q k : ℕ) : (ram q k).im = 0 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j =>
      rw [ram_primePower p j k hp]
      split_ifs <;> simp only [Complex.sub_im, Complex.natCast_im, Complex.zero_im, sub_zero]
  | coprime u v hu hv hc h1 h2 =>
    rw [ram_mul (by omega) (by omega) hc,Complex.mul_im,h1,h2]
    ring

/-- Small-prime log weight predicted by the reduced fractions with denominator at most Q. -/
noncomputable def realWeight (Q k : ℕ) : ℝ :=
  (∑ q ∈ Icc 1 Q, (ram q 1 / (q.totient:ℂ)) * conj (ram q k)).re

theorem realWeight_cast (Q k : ℕ) :
    (realWeight Q k : ℂ) = ∑ q ∈ Icc 1 Q,
      ∑ a ∈ units q, unitMean q a * phase (-((k:ℝ)*a/q)) := by
  have row (q : ℕ) : (∑ a ∈ units q, unitMean q a * phase (-((k:ℝ)*a/q))) =
      (ram q 1 / (q.totient:ℂ)) * conj (ram q k) := by
    unfold ram units
    rw [map_sum, mul_sum]
    refine sum_congr rfl (fun a ha => ?_)
    rw [phase_conj,unitMean_eq_ram (mem_filter.mp ha).2]
    rfl
  simp_rw [row]
  unfold realWeight
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Complex.im_sum, Complex.mul_im, Complex.conj_im,
      ram_im_zero, neg_zero, mul_zero, zero_mul]
    simp [Complex.div_im, ram_im_zero]

noncomputable def transform (I : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ I, (w k:ℂ)*phase ((k:ℝ)*t)

noncomputable def dirichletWindow (I : Finset ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ I, phase ((k:ℝ)*u)

theorem transform_weight (I : Finset ℕ) (Q : ℕ) (t : ℝ) :
    transform I (realWeight Q) t = ∑ q ∈ Icc 1 Q, ∑ a ∈ units q,
      unitMean q a * dirichletWindow I (t-(a:ℝ)/q) := by
  unfold transform dirichletWindow
  simp_rw [realWeight_cast, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun q hq => ?_)
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [mul_assoc, ← BulkCircle.phase_add]
  congr 2
  ring

end ThinWindowModel

end

-- MixedBessel
section

open Finset MeasureTheory Filter

namespace ThinWindowMinor

/-- On a fixed measurable set the short factor can be bounded uniformly while the
long factor retains its full Parseval energy. The frequencies may be any finite set. -/
theorem mixed_bessel (A : Set ℝ) (ha : MeasurableSet A) (short long : ℝ → ℂ)
    (hs : Continuous short) (hl : Continuous long) (F : Finset ℕ) (T : ℝ)
    (bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ A → ‖short t‖ ≤ T) :
    ∑ n ∈ F, ‖fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
       (A.indicator (fun t => short t * long t)) (n : ℤ)‖^2 ≤
      T^2 * ∫ t in (0 : ℝ)..1, ‖long t‖^2 := by
  let f := A.indicator (fun t => short t * long t)
  have hc : Continuous (fun t => short t * long t) := hs.mul hl
  have hmem : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply MemLp.indicator ha.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hb := sum_le_hasSum (F.map emb)
    (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖)
    (hasSum_sq_fourierCoeffOn zero_lt_one hmem)
  simp only [Finset.sum_map, sub_zero, inv_one, one_smul] at hb
  have hint : IntervalIntegrable (fun t => ‖f t‖^2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  calc _ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 := hb
       _ ≤ ∫ t in (0 : ℝ)..1, T^2 * ‖long t‖^2 := by
         apply intervalIntegral.integral_mono_on zero_le_one hint
           ((continuous_const.mul (hl.norm.pow 2)).intervalIntegrable _ _)
         intro t ht
         change ‖f t‖^2 ≤ T^2 * ‖long t‖^2
         by_cases h : t ∈ A
         · simp only [f, Set.indicator_of_mem h, norm_mul, mul_pow]
           exact mul_le_mul_of_nonneg_right
             (pow_le_pow_left₀ (norm_nonneg _) (bound t ht h) 2) (sq_nonneg _)
         · simpa only [f, Set.indicator_of_notMem h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
             using mul_nonneg (sq_nonneg T) (sq_nonneg ‖long t‖)
       _ = _ := intervalIntegral.integral_const_mul _ _

end ThinWindowMinor

end

-- ThinMinor
section

open Finset Filter MeasureTheory
open scoped Topology
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

namespace ThinWindowMinor

noncomputable section

def major (X : ℕ) : Set ℝ :=
  GoldbachBlockGeometry.arcs (Polylog.cutoff 36 (2 * Nat.sqrt X)) (Nat.sqrt X - 1)

def shortSum (X : ℕ) : ℝ → ℂ :=
  BulkCircle.S (Nat.sqrt X - 1) (Nat.sqrt X - 1)

def minorCoefficient (X n : ℕ) : ℂ :=
  fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
    ((major X)ᶜ.indicator (fun t => shortSum X t * primeSum (2*X) t)) (n : ℤ)

theorem minorCoefficient_eq (X n : ℕ) : minorCoefficient X n =
    ∫ t in (0 : ℝ)..1, (major X)ᶜ.indicator (fun u =>
      shortSum X u * primeSum (2*X) u * phase (-(n : ℝ)*u)) t := by
  rw [minorCoefficient, fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h : t ∈ (major X)ᶜ
  · simp only [Set.indicator_of_mem h, smul_eq_mul, fourier_coe_apply]
    rw [mul_comm]
    congr 2
    dsimp [phase]
    push_cast
    ring
  · simp [h]

theorem shortSum_eq {X : ℕ} (hY : 2 ≤ Nat.sqrt X) (t : ℝ) :
    shortSum X t = ∑ p ∈ (Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime,
      (Real.log (p : ℝ) : ℂ) * phase ((p : ℝ)*t) := by
  let Y := Nat.sqrt X
  change 2 ≤ Y at hY
  let primes := (Icc Y (2*Y)).filter Nat.Prime
  have sub : primes ⊆ range (2*Y+1) := fun p hp =>
    mem_range.mpr (by have := (mem_Icc.mp (mem_filter.mp hp).1).2; omega)
  have notprime : ¬ (2*Y).Prime := Nat.not_prime_mul (by decide) (by omega)
  change BulkCircle.S (Y-1) (Y-1) t = _
  rw [BulkCircle.as_mask (2*Y) (Y-1) (Y-1) (by omega)]
  calc
    _ = ∑ k ∈ primes, (BulkCircle.ww (Y-1) (Y-1) k : ℂ) * phase ((k:ℝ)*t) := by
      symm
      apply sum_subset sub
      intro k hk hn
      have no : ¬ (Y-1<k ∧ k≤Y-1+(Y-1)+1 ∧ k.Prime) := by
        rintro ⟨h1, h2, hp⟩
        exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hp⟩)
      by_cases hs : Y-1<k ∧ k≤Y-1+(Y-1)+1
      · have hnp : ¬ k.Prime := fun h => no ⟨hs.1, hs.2, h⟩
        simp [BulkCircle.ww, hs, primeWeight, hnp]
      · simp [BulkCircle.ww, hs]
    _ = _ := by
      apply sum_congr rfl; intro k hk
      obtain ⟨hk', hp⟩ := mem_filter.mp hk
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hk'
      have hneq : k ≠ 2*Y := fun h => notprime (h ▸ hp)
      have hr : Y-1<k ∧ k≤Y-1+(Y-1)+1 := by omega
      simp [BulkCircle.ww, hr, primeWeight, hp]

theorem long_energy (X : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖primeSum (2*X) t‖^2) ≤
      ((2*X:ℕ)+1 : ℝ) * (Real.log (2*X : ℕ))^2 := by
  have hParse := PEqualNP.Outside.L_goldbach_continuous_parseval (2*X) primeWeight
  change (∫ t in (0:ℝ)..1, ‖primeSum (2*X) t‖^2) = _ at hParse
  rw [hParse]
  calc _ ≤ ∑ _k ∈ range (2*X+1), (Real.log (2*X:ℕ))^2 := by
         apply sum_le_sum; intro k hk
         by_cases hp : k.Prime
         · simp only [primeWeight, ite_eq_left hp]
           apply pow_le_pow_left₀ (Real.log_natCast_nonneg _) _ 2
           exact Real.log_le_log (by exact_mod_cast hp.pos)
             (by exact_mod_cast (show k ≤ 2*X by simpa using hk))
         · simp [primeWeight, hp, sq_nonneg]
       _ = _ := by simp

theorem root_tends : Tendsto (fun X : ℕ => 2 * Nat.sqrt X) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with X hX
  have := Nat.le_sqrt.mpr hX
  omega

theorem small_minor_eventually :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ major X →
      ‖shortSum X t‖ ≤ 4096 * (Nat.sqrt X : ℝ) / (Real.log (2 * (Nat.sqrt X : ℝ)))^10 := by
  have hm := root_tends.eventually (BulkCircle.minor_window 0)
  filter_upwards [hm, eventually_ge_atTop (16:ℕ)] with X h hX
  have hY : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  intro t ht hminor
  have hS := h (Nat.sqrt X-1) (Nat.sqrt X-1) (by omega) (by omega) le_rfl (by omega) t ht hminor
  unfold shortSum
  convert hS using 1
  push_cast
  norm_num
  ring

theorem minor_energy_tends :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, ∀ F : Finset ℕ,
      (∑ n ∈ F, ‖minorCoefficient X n‖^2) ≤ ε * (X:ℝ)^2 := by
  intro ε hε
  let K : ℝ := 4096^2 * 27
  have ht := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp root_tends)).eventually_ge_atTop (max 1 (K/ε))
  filter_upwards [small_minor_eventually, ht, eventually_ge_atTop (16 : ℕ)] with X hsmall hlog hX
  intro F
  let Y := Nat.sqrt X
  let L := Real.log (2*(Y:ℝ))
  let T := 4096*(Y:ℝ)/L^10
  change max 1 (K/ε) ≤ Real.log ((2 * Nat.sqrt X : ℕ) : ℝ) at hlog
  push_cast at hlog
  change max 1 (K/ε) ≤ L at hlog
  have hL : 1 ≤ L := (le_max_left _ _).trans hlog
  have hLpos : 0 < L := by linarith
  have hke : K ≤ ε * L := by
    have hp := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hlog)
    linarith
  have hY : 4 ≤ Y := Nat.le_sqrt.mpr (by omega)
  have hy2 : (Y : ℝ)^2 ≤ (X : ℝ) := by exact_mod_cast Nat.sqrt_le' X
  have hy : X < (Y+1)^2 := Nat.lt_succ_sqrt' X
  have hlog2 : Real.log (2*X:ℕ) ≤ 3*L := by
    change Real.log ((2*X:ℕ):ℝ) ≤ ((3 : ℕ):ℝ) * Real.log (2*(Y:ℝ))
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    norm_cast
    nlinarith [show 0 ≤ Y^2*(Y-1) by positivity, Nat.mul_le_mul_left (Y^2) hY]
  have hlong : (∫ t in (0:ℝ)..1, ‖primeSum (2*X) t‖^2) ≤ 3*(X:ℝ)*(3*L)^2 := by
    apply (long_energy X).trans
    apply mul_le_mul _ (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog2 2)
      (sq_nonneg _) (by positivity)
    push_cast
    exact_mod_cast (show 2*X+1 ≤ 3*X by omega)
  have hscont : Continuous (shortSum X) := by
    unfold shortSum BulkCircle.S primeSum phase; fun_prop
  have hlcont : Continuous (primeSum (2*X)) := by unfold primeSum phase; fun_prop
  have hmeas : MeasurableSet (major X) := GoldbachEstermann.measurable_block_arcs _ _
  have hb := mixed_bessel (major X)ᶜ hmeas.compl (shortSum X) (primeSum (2*X))
    hscont hlcont F T (fun t hit hin => hsmall t hit hin)
  change (∑ n ∈ F, ‖minorCoefficient X n‖^2) ≤ _ at hb
  calc _ ≤ T^2 * (3*(X:ℝ)*(3*L)^2) :=
           hb.trans (mul_le_mul_of_nonneg_left hlong (sq_nonneg T))
       _ = (K/L^18) * ((Y:ℝ)^2 * X) := by
           dsimp [T, K]; field_simp; ring
       _ ≤ ε * (X:ℝ)^2 := by
           rw [sq (X:ℝ)]
           apply mul_le_mul _ (mul_le_mul_of_nonneg_right hy2 (by positivity)) (by positivity) hε.le
           apply (div_le_iff₀ (pow_pos hLpos _)).mpr
           exact hke.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hL (by decide : 18 ≠ 0)) hε.le)

theorem minor_energy_normalized {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ F : Finset ℕ, (∑ n ∈ F, ‖minorCoefficient X n‖^2) ≤
      ε * (X : ℝ) * (c * Real.sqrt X)^2 := by
  filter_upwards [minor_energy_tends (ε * c^2) (by positivity)] with X hX
  intro F
  apply (hX F).trans_eq
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg X)]
  ring

end
end ThinWindowMinor

end

-- ThinProduct
section

open Finset MeasureTheory Filter
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

namespace ThinWindowMinor
noncomputable section

def poly (I : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ I, (w i : ℂ) * phase ((i : ℝ) * t)

def coeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f (n : ℤ)

theorem coeff_integral (f : ℝ → ℂ) (n : ℕ) :
    coeff f n = ∫ t in (0 : ℝ)..1, f t * phase (-(n : ℝ)*t) := by
  rw [coeff, fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_eq_mul, fourier_coe_apply]
  rw [mul_comm]
  congr 2
  dsimp [phase]
  push_cast
  ring

/-- Character orthogonality on the unit interval; the computation follows the
registered mixed-coefficient lemma from the Goldbach project (Apache-2.0). -/
private theorem integral_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, phase]
  · let a : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha : a ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm)
      (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
    have hexp (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (a * (t : ℂ)) := by
      unfold phase a; push_cast; congr 1; ring
    have hend : Complex.exp a = 1 := Complex.exp_int_mul_two_pi_mul_I m
    simp_rw [hexp]
    rw [integral_exp_mul_complex ha]
    simp [hm, hend]

/-- The small support is independent of the target. The long polynomial has a
single fixed cutoff for every target n ≤ N. -/
theorem product_coefficient (I : Finset ℕ) (u v : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N) :
    coeff (fun t => poly I u t * poly (range (N+1)) v t) n =
      ((∑ i ∈ I.filter (fun i => i ≤ n), u i * v (n-i) : ℝ) : ℂ) := by
  rw [coeff_integral]
  let freq := fun i j : ℕ => (i : ℤ) + j - n
  let term := fun (i j : ℕ) (t : ℝ) => (u i : ℂ) * v j * phase ((freq i j : ℝ) * t)
  have expand (t : ℝ) :
      poly I u t * poly (range (N+1)) v t * phase (-(n:ℝ)*t) =
        ∑ i ∈ I, ∑ j ∈ range (N+1), term i j t := by
    unfold poly
    rw [sum_mul_sum, sum_mul]
    apply sum_congr rfl; intro i _
    rw [sum_mul]
    apply sum_congr rfl; intro j _
    have shift : (i:ℝ)*t+(j:ℝ)*t+(-(n:ℝ))*t = ((freq i j):ℝ)*t := by
      dsimp [freq]; push_cast; ring
    dsimp only [term]
    rw [← shift, BulkCircle.phase_add, BulkCircle.phase_add]
    ring
  have hc (i j : ℕ) : Continuous (term i j) := by dsimp [term, phase]; fun_prop
  have row (i : ℕ) :
      (∫ t in (0:ℝ)..1, ∑ j ∈ range (N+1), term i j t) =
        if i ≤ n then (u i : ℂ) * v (n-i) else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable 0 1)]
    by_cases hi : i ≤ n
    · have hm : n-i ∈ range (N+1) := mem_range.mpr (by omega)
      have hf (j : ℕ) : freq i j = 0 ↔ j = n-i := by dsimp [freq]; omega
      simp [hi, term, intervalIntegral.integral_const_mul, integral_mode, hf, mul_ite, hm]
    · have hf (j : ℕ) : freq i j ≠ 0 := by dsimp [freq]; omega
      simp only [term, intervalIntegral.integral_const_mul, integral_mode]
      simp [hi, hf]
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => hc i j)).intervalIntegrable 0 1)]
  simp_rw [row]
  rw [← sum_filter]
  push_cast
  rfl

theorem weighted_coefficient {X n : ℕ} (hY : 2 ≤ Nat.sqrt X) (hn : n ≤ 2*X) :
    coeff (fun t => shortSum X t * primeSum (2*X) t) n =
      ((∑ p ∈ ((Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ (n-p).Prime), Real.log (p:ℝ)*Real.log ((n-p:ℕ):ℝ) : ℝ) : ℂ) := by
  let P := (Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime
  have heq : shortSum X = poly P (fun p => Real.log p) := funext (shortSum_eq hY)
  rw [heq]
  change coeff (fun t => poly P (fun p => Real.log p) t * poly (range (2*X+1)) primeWeight t) n = _
  rw [product_coefficient _ _ _ hn]
  congr 1
  change (∑ p ∈ P.filter (fun p => p ≤ n), Real.log (p:ℝ)*primeWeight (n-p)) =
    ∑ p ∈ P.filter (fun p => p ≤ n ∧ (n-p).Prime), Real.log (p:ℝ)*Real.log ((n-p:ℕ):ℝ)
  simp only [sum_filter]
  apply sum_congr rfl; intro p _
  by_cases h : Nat.Prime (n-p) <;> by_cases hi : p ≤ n <;> simp [primeWeight, h, hi]

theorem long_energy_chebyshev (X : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖primeSum (2*X) t‖^2) ≤
      Real.log (2*X:ℕ) * (Real.log 4 * (2*X:ℕ)) := by
  have hParse := PEqualNP.Outside.L_goldbach_continuous_parseval (2*X) primeWeight
  change (∫ t in (0:ℝ)..1, ‖primeSum (2*X) t‖^2) = _ at hParse
  rw [hParse]
  calc _ ≤ ∑ k ∈ range (2*X+1), Real.log (2*X:ℕ) * primeWeight k := by
         apply sum_le_sum; intro k hk
         by_cases hp : k.Prime
         · simp only [primeWeight, ite_eq_left hp, sq]
           exact mul_le_mul_of_nonneg_right
             (Real.log_le_log (by exact_mod_cast hp.pos)
               (by exact_mod_cast (show k ≤ 2*X by simpa using hk))) (Real.log_natCast_nonneg k)
         · simp [primeWeight,hp]
       _ = Real.log (2*X:ℕ) * Chebyshev.theta (2*X:ℕ) := by
         rw [← mul_sum, Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
         rfl
       _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (by positivity))
           (Real.log_natCast_nonneg _)

/-- Uniform approximation of the short polynomial gives a mean-square bound
for the error after convolution with the long log-prime polynomial. -/
theorem uniform_model_error (X : ℕ) (model : ℝ → ℂ) (hmodel : Continuous model)
    (F : Finset ℕ) (δ : ℝ)
    (hδ : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖shortSum X t - model t‖ ≤ δ * Nat.sqrt X) :
    (∑ n ∈ F, ‖coeff (fun t => shortSum X t * primeSum (2*X) t) n -
      coeff (fun t => model t * primeSum (2*X) t) n‖^2) ≤
      (δ * Nat.sqrt X)^2 * (Real.log (2*X:ℕ) * (Real.log 4 * (2*X:ℕ))) := by
  have hs : Continuous (shortSum X) := by unfold shortSum BulkCircle.S primeSum phase; fun_prop
  have hl : Continuous (primeSum (2*X)) := by unfold primeSum phase; fun_prop
  have hb := mixed_bessel Set.univ MeasurableSet.univ (fun t => shortSum X t-model t)
    (primeSum (2*X)) (hs.sub hmodel) hl F (δ * Nat.sqrt X) (fun t ht _ => hδ t ht)
  simp only [Set.indicator_univ] at hb
  have hcoeff (n : ℕ) :
      coeff (fun t => (shortSum X t - model t)*primeSum (2*X) t) n =
      coeff (fun t => shortSum X t * primeSum (2*X) t) n -
        coeff (fun t => model t * primeSum (2*X) t) n := by
    rw [coeff_integral, coeff_integral, coeff_integral]
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub] <;>
      apply Continuous.intervalIntegrable <;> unfold phase <;> fun_prop
  change (∑ n ∈ F, ‖coeff (fun t => (shortSum X t-model t)*primeSum (2*X) t) n‖^2) ≤ _ at hb
  simp_rw [hcoeff] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (long_energy_chebyshev X) (sq_nonneg _))

def trueMass (X n : ℕ) : ℝ :=
  ∑ p ∈ ((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
    (fun p => p ≤ n ∧ (n-p).Prime), Real.log (p:ℝ)*Real.log ((n-p:ℕ):ℝ)

def modelMass (I : Finset ℕ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ I.filter (fun i => i ≤ n), u i * primeWeight (n-i)

/-- In physical space the Fourier comparison reads as a variance bound for
the two explicitly weighted representation counts on the same finite set. -/
theorem physical_error {X : ℕ} (hY : 2 ≤ Nat.sqrt X)
    (I F : Finset ℕ) (u : ℕ → ℝ) (hF : ∀ n ∈ F, n ≤ 2*X) (δ : ℝ)
    (ha : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖shortSum X t - poly I u t‖ ≤ δ * Nat.sqrt X) :
    (∑ n ∈ F, (trueMass X n - modelMass I u n)^2) ≤
      (δ * Nat.sqrt X)^2 * (Real.log (2*X:ℕ) * (Real.log 4 * (2*X:ℕ))) := by
  have hc : Continuous (poly I u) := by unfold poly phase; fun_prop
  apply le_trans _ (uniform_model_error X (poly I u) hc F δ ha)
  apply Finset.sum_le_sum
  intro n hn
  have hA := weighted_coefficient hY (hF n hn)
  change coeff (fun t => shortSum X t * primeSum (2*X) t) n = (trueMass X n : ℂ) at hA
  have hB := product_coefficient I u primeWeight (hF n hn)
  change coeff (fun t => poly I u t * primeSum (2*X) t) n = (modelMass I u n : ℂ) at hB
  rw [hA,hB, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]


end
end ThinWindowMinor

end

-- Overlap
section

namespace ThinBoundary
open MeasureTheory
open scoped Interval

theorem overlap {f : ℝ → ℂ} {g : ℝ → ℂ} {X δ : ℝ}
    (_hX : 0 < X) (hδ : 0 < δ) (hd : δ ≤ X/2)
    (hf : ContinuousOn f (Set.Icc (X/2) (2*X)))
    (hs : (∫ y in X..2*X, ‖g y‖^2) ≤ ∫ y in X-δ..2*X, ‖f y‖^2) :
    (∫ y in X..2*X, ‖g y‖^2) ≤
      (∫ y in X/2..X, ‖f y‖^2) + (∫ y in X..2*X, ‖f y‖^2) := by
  let w := fun y => ‖f y‖ ^ 2
  have hi : IntervalIntegrable w volume (X/2) (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hf.norm.pow 2)
  have hL : IntervalIntegrable w volume (X/2) X :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) ((hf.norm.pow 2).mono (Set.Icc_subset_Icc_right (by linarith)))
  have hR : IntervalIntegrable w volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) ((hf.norm.pow 2).mono (Set.Icc_subset_Icc_left (by linarith)))
  refine hs.trans ?_
  change (∫ y in X-δ..2*X, w y) ≤ (∫ y in X/2..X, w y) + ∫ y in X..2*X, w y
  rw [intervalIntegral.integral_add_adjacent_intervals hL hR]
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
    (Filter.Eventually.of_forall fun y => sq_nonneg _) hi

theorem overlap_budget {X h C : ℝ} (B : ℕ) (hX : 4 ≤ X) (hC : 0 ≤ C) :
    C*h^2*(X/2)/(Real.log (X/2))^B + C*h^2*X/(Real.log X)^B ≤
      ((2:ℝ)^B+1)*C*h^2*X/(Real.log X)^B := by
  have hXpos : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hH : 0 < Real.log (X/2) := Real.log_pos (by linarith)
  have he : Real.log X = Real.log (X/2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : X/2 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    congr 1; ring
  have hlog : Real.log X ≤ 2 * Real.log (X/2) := by
    have h₂ := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤X/2)
    linarith
  have hpow := pow_le_pow_left₀ hL.le hlog B
  rw [mul_pow] at hpow
  have hbal : (X/2)/(Real.log (X/2))^B ≤ (2:ℝ)^B * X/(Real.log X)^B := by
    apply (div_le_div_iff₀ (pow_pos hH _) (pow_pos hL _)).mpr
    calc (X/2) * (Real.log X)^B ≤ X * ((2:ℝ)^B * (Real.log (X/2))^B) :=
           mul_le_mul (by linarith) hpow (by positivity) hXpos.le
         _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hbal (show 0 ≤ C*h^2 by positivity)
  convert add_le_add_left hh (C*h^2*X/(Real.log X)^B) using 1 <;> ring

theorem scale_half {X h A : ℝ} (hX : 0 < X)
    (hs : A/(h/X) ≤ X^(5/9 : ℝ)) :
    A/(h/(X/2)) ≤ (X/2)^(5/9 : ℝ) := by
  have htwo : (2:ℝ)^(5/9 : ℝ) ≤ 2 := by
    calc (2:ℝ)^(5/9 : ℝ) ≤ 2^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ = _ := Real.rpow_one _
  calc A/(h/(X/2)) = (A/(h/X))/2 := by ring
       _ ≤ X^(5/9 : ℝ)/2 := by linarith
       _ ≤ X^(5/9 : ℝ)/(2:ℝ)^(5/9 : ℝ) :=
         div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
       _ = _ := (Real.div_rpow hX.le (by norm_num) _).symm

end ThinBoundary

end

-- BoundaryAdapters
section

namespace ThinBoundary

open Finset MeasureTheory OAI.Ostmann V1e V6i Vct Vg1 Vx

open scoped BigOperators Interval Classical

def characterRaw (B : ℕ) : Prop :=
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ),1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X → (Q : ℝ)≤2*(Real.log X)^24 →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      (∑ χ∈F,∫ y in X..2*X,
        ‖∑ i∈(V1 χ).V14 ((2 : ℝ)^(K+1)),
          Ve y h ((V1 χ).zeros i)‖^2)≤
        C*h^2*X/(Real.log X)^B

def principalRaw (B : ℕ) : Prop :=
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (K : ℕ) (X h : ℝ),X₀≤X → 0<h → h≤X →
      1/(h/X)≤X^(5/9 : ℝ) → Real.log ((2 : ℝ)^(K+1))≤2*Real.log X →
      (∫ y in X..2*X,‖∑ c∈V3b ((2 : ℝ)^(K+1)),
        Ve y h c.val.1‖^2)≤C*h^2*X/(Real.log X)^B

/-- The endpoint averages only cost one more dyadic mean square. -/
theorem average_budget (f : ℝ → ℂ) (X h δ C : ℝ) (B : ℕ)
    (hX : 4 ≤ X) (hδ : 0 < δ) (hd : δ ≤ X/2) (hC : 0 ≤ C)
    (hf : ContinuousOn f (Set.Icc (X/2) (2*X)))
    (hhalf : (∫ y in X/2..2*(X/2), ‖f y‖^2) ≤ C*h^2*(X/2)/(Real.log (X/2))^B)
    (hfull : (∫ y in X..2*X, ‖f y‖^2) ≤ C*h^2*X/(Real.log X)^B) :
    (∫ y in X..2*X, ‖V3q f δ y‖^2) ≤ ((2:ℝ)^B+1)*C*h^2*X/(Real.log X)^B := by
  have hwest := V6i.V1qh f X δ (by linarith) hδ
    (hf.mono (Set.Icc_subset_Icc_left (by linarith)))
  have h := overlap (f := f) (by linarith : 0<X) hδ hd hf hwest
  rw [show (2:ℝ)*(X/2)=X by ring] at hhalf
  exact h.trans ((add_le_add hhalf hfull).trans (overlap_budget B hX hC))

theorem smoothCharacter (B : ℕ) (raw : characterRaw B) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, ∀ (Q K : ℕ), 1≤Q → ∀ X h δ : ℝ,
    X₀≤X → 0<h → h≤X/2 → 0<δ → δ≤X/2 → (Q:ℝ)≤2*(Real.log (X/2))^24 →
    (Q:ℝ)^2/(h/X) ≤ X^(5/9:ℝ) → Real.log ((Q:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
    ∀ χ : PrimitiveComplexCharacter, χ.modulus≤Q →
    (∫ y in X..2*X, ‖V3q (fun u =>
      ∑ i∈(V1 χ).V14 ((2:ℝ)^(K+1)),Ve u h ((V1 χ).zeros i)) δ y‖^2) ≤
      C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,T,hm⟩ := raw
  refine ⟨((2:ℝ)^B+1)*C,by positivity,max (2*T) 4,?_⟩
  intro Q K hQ X h δ hX hh hupper hd hdX hq hscale height χ hχ
  have hX4 : 4≤X := (le_max_right _ _).trans hX
  have hT : 2*T≤X := (le_max_left _ _).trans hX
  have hlog := Real.log_le_log (by linarith : 0<X/2) (by linarith : X/2≤X)
  have hlog0 : 0≤Real.log (X/2) := Real.log_nonneg (by linarith)
  have hq' : (Q:ℝ) ≤ 2*(Real.log X)^24 := hq.trans (by gcongr)
  let f : ℝ → ℂ := fun u => ∑ i∈(V1 χ).V14 ((2:ℝ)^(K+1)),Ve u h ((V1 χ).zeros i)
  apply average_budget f X h δ C B hX4 hd hdX hC.le
    (Vab _ _ _ _ h (by linarith) hh.le)
  · have hc := hm Q hQ K (X/2) h (by linarith) hh hupper hq (scale_half (by linarith) hscale) height
      {χ} (by intro ξ hξ; simpa only [mem_singleton.mp hξ] using hχ)
    simpa only [sum_singleton] using hc
  · have hc := hm Q hQ K X h (by linarith) hh (by linarith) hq' hscale (by linarith)
      {χ} (by intro ξ hξ; simpa only [mem_singleton.mp hξ] using hχ)
    simpa only [sum_singleton] using hc

theorem smoothPrincipal (B : ℕ) (raw : principalRaw B) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, ∀ (K : ℕ) (X h δ : ℝ),
    X₀≤X → 0<h → h≤X/2 → 0<δ → δ≤X/2 →
    1/(h/X) ≤ X^(5/9:ℝ) → Real.log ((2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
    (∫ y in X..2*X, ‖V3q (fun u =>∑ c∈V3b ((2:ℝ)^(K+1)),Ve u h c.val.1) δ y‖^2) ≤
      C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,T,hm⟩ := raw
  refine ⟨((2:ℝ)^B+1)*C,by positivity,max (2*T) 4,?_⟩
  intro K X h δ hX hh hupper hd hdX hscale height
  have hX4 : 4≤X := (le_max_right _ _).trans hX
  have hT : 2*T≤X := (le_max_left _ _).trans hX
  have hlog := Real.log_le_log (by linarith : 0<X/2) (by linarith : X/2≤X)
  apply average_budget _ X h δ C B hX4 hd hdX hC.le
    (Vab _ _ _ _ h (by linarith) hh.le)
  · exact hm K (X/2) h (by linarith) hh hupper (scale_half (by linarith) hscale) height
  · exact hm K X h (by linarith) hh (by linarith) hscale (by linarith)

end ThinBoundary

end

-- Parameters
section

namespace ThinBoundary
open Filter
open scoped Topology

theorem eventual_log_power (k : ℕ) (e C : ℝ) (he : 0<e) :
    ∀ᶠ X : ℝ in atTop, C*(Real.log X)^k ≤ X^e := by
  have ht := (isLittleO_log_rpow_rpow_atTop (k:ℝ) he).tendsto_div_nhds_zero.const_mul C
  simp only [mul_zero] at ht
  have hh := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hh,eventually_ge_atTop (2:ℝ)] with X hsmall hX
  have hXp : 0<X := by linarith
  have hp : 0<X^e := Real.rpow_pos_of_pos hXp e
  have hs : C*(Real.log X)^k/X^e < 1 := by
    simpa only [Pi.div_apply, Real.rpow_natCast, mul_div_assoc] using hsmall
  linarith [(div_lt_one hp).mp hs]

theorem scale_from_lower {X Q h : ℝ} (hX : 0<X) (hh : 0<h)
    (hlower : Q^2*X^(4/9:ℝ) ≤ h) : Q^2/(h/X) ≤ X^(5/9:ℝ) := by
  have he : X^(5/9:ℝ)*X^(4/9:ℝ)=X := by
    rw [← Real.rpow_add hX]; norm_num
  apply (div_le_iff₀ (div_pos hh hX)).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hX).mpr
  calc _ = X^(5/9:ℝ)*(Q^2*X^(4/9:ℝ)) := by rw [mul_left_comm,he,mul_comm]
       _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

theorem residual_budget (B : ℕ) {X Q h U : ℝ}
    (hX : 4 ≤ X) (hQ : 1 ≤ Q) (hU : X^(3/2:ℝ) ≤ U)
    (hheight : Real.log (Q*U) ≤ 2*Real.log X)
    (hlower : Q^2*X^(4/9:ℝ) ≤ h)
    (habsorb : 16*(Real.log X)^(B+2) ≤ X^(1/18:ℝ)) :
    (X^(1/12:ℝ)*Real.log X + Real.sqrt X*Real.log X/X^(1/12:ℝ) +
      Q^2*X^2*Real.log (Q*U)/(X^(1/12:ℝ)*U))^2 * X ≤
      h^2*X/(Real.log X)^B := by
  have hpos : 0<X := by linarith
  have hone : 1≤X := by linarith
  have hlog : 0<Real.log X := Real.log_pos (by linarith)
  have huone : 1≤U := (Real.one_le_rpow hone (by norm_num : (0:ℝ) ≤ 3/2)).trans hU
  have hlogQU : 0≤Real.log (Q*U) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ huone)
  have hq : 1≤Q^2 := one_le_pow₀ hQ
  let d := X^(1/12:ℝ)
  let w := X^(5/12:ℝ)
  have hd : 0<d := Real.rpow_pos_of_pos hpos _
  have hw : 0<w := Real.rpow_pos_of_pos hpos _
  have hroot : d*w=Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]; dsimp [d,w]; rw [← Real.rpow_add hpos]; norm_num
  have hden : X^(3/2:ℝ)*(d*w)=X^2 := by
    dsimp [d,w]; rw [← Real.rpow_add hpos,← Real.rpow_add hpos]; norm_num
  have hdp : d ≤ w := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
  have ha : d*Real.log X ≤ Q^2*w*Real.log X := by
    gcongr; exact hdp.trans (le_mul_of_one_le_left hw.le hq)
  have hb : Real.sqrt X*Real.log X/d ≤ Q^2*w*Real.log X := by
    rw [← hroot, mul_assoc, mul_div_cancel_left₀ _ hd.ne']
    gcongr; exact le_mul_of_one_le_left hw.le hq
  have hc : Q^2*X^2*Real.log (Q*U)/(d*U) ≤ 2*Q^2*w*Real.log X := by
    apply (div_le_iff₀ (mul_pos hd (by linarith))).mpr
    calc Q^2*X^2*Real.log (Q*U) ≤ Q^2*X^2*(2*Real.log X) :=
           mul_le_mul_of_nonneg_left hheight (by positivity)
         _ = (2*Q^2*w*Real.log X)*(d*X^(3/2:ℝ)) := by rw [← hden]; ring
         _ ≤ _ := by gcongr
  have hr : d*Real.log X + Real.sqrt X*Real.log X/d +
      Q^2*X^2*Real.log (Q*U)/(d*U) ≤ 4*Q^2*w*Real.log X := by linarith
  have hs := pow_le_pow_left₀ (show 0≤ d*Real.log X + Real.sqrt X*Real.log X/d +
      Q^2*X^2*Real.log (Q*U)/(d*U) by positivity) hr 2
  have hw2 : w^2*X^(1/18:ℝ) = (X^(4/9:ℝ))^2 := by
    rw [← Real.rpow_natCast w 2, ← Real.rpow_natCast (X^(4/9:ℝ)) 2]
    dsimp [w]; rw [← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
    norm_num
  have hh := pow_le_pow_left₀ (by positivity : 0≤Q^2*X^(4/9:ℝ)) hlower 2
  apply (le_div_iff₀ (pow_pos hlog _)).mpr
  calc _ ≤ (4*Q^2*w*Real.log X)^2 * X * (Real.log X)^B := by gcongr
       _ = ((Q^2)^2 * X * w^2) * (16*(Real.log X)^(B+2)) := by rw [pow_add]; ring
       _ ≤ ((Q^2)^2 * X * w^2) * X^(1/18:ℝ) := by gcongr
       _ = (Q^2 * X^(4/9:ℝ))^2 * X := by rw [mul_pow,← hw2];ring
       _ ≤ _ := by gcongr

theorem eventually_half_cutoff :
    ∀ᶠ X : ℝ in atTop, (Real.log X)^23 ≤ 2*(Real.log (X/2))^24 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((2:ℝ)^24),
    eventually_ge_atTop (4:ℝ)] with X hL hX
  have hX0 : 0<X := by linarith
  have hH : 0≤Real.log (X/2) := Real.log_nonneg (by linarith)
  have he : Real.log X = Real.log (X/2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : X/2 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    congr 1; ring
  have hlog : Real.log X ≤ 2 * Real.log (X/2) := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤X/2)
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0≤Real.log X) hlog 24
  rw [mul_pow] at hpow
  have h1 := mul_le_mul_of_nonneg_left hL (show 0≤(Real.log X)^23 by positivity)
  calc (Real.log X)^23 ≤ (Real.log (X/2))^24 := by
         have h : (Real.log X)^23 * 2^24 ≤ 2^24*(Real.log (X/2))^24 := by
           refine h1.trans ?_; convert hpow using 1 <;> ring
         linarith only [h]
       _ ≤ _ := by linarith [pow_nonneg hH 24]

structure ThinPacket (B : ℕ) (X Q h : ℝ) (K : ℕ) : Prop where
  X_ge_four : 4 ≤ X
  delta_ge_one : 1 ≤ X^(1/12:ℝ)
  delta_le_half : X^(1/12:ℝ) ≤ X/2
  height_ge_two : 2 ≤ (2:ℝ)^(K+1)
  half_cutoff : Q ≤ 2*(Real.log (X/2))^24
  height_log : Real.log (Q*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2)
  scale : Q^2/(h/X) ≤ X^(5/9:ℝ)
  residual : (X^(1/12:ℝ)*Real.log X + Real.sqrt X*Real.log X/X^(1/12:ℝ) +
    Q^2*X^2*Real.log (Q*(2:ℝ)^(K+1))/(X^(1/12:ℝ)*(2:ℝ)^(K+1)))^2 * X ≤
    h^2*X/(Real.log X)^B

theorem eventually_parameters (B : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Q h : ℝ, 1≤Q → Q≤(Real.log X)^23 →
      0<h → Q^2*X^(4/9:ℝ)≤h → ∃ K : ℕ, ThinPacket B X Q h K := by
  filter_upwards [eventually_ge_atTop (4:ℝ),eventually_half_cutoff,
    eventual_log_power 23 (1/2) 8 (by norm_num),
    eventual_log_power (B+2) (1/18) 16 (by norm_num)]
    with X hX hcut hpoly habs
  intro Q h hQ hQx hh hlow
  have x0 : 0<X := by linarith
  have x1 : 1≤X := by linarith
  have hd : X^(1/12:ℝ) ≤ X/2 := by
    calc X^(1/12:ℝ) ≤ Real.sqrt X := by
           rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le x1 (by norm_num)
         _ ≤ _ := by
           apply Real.sqrt_le_iff.mpr
           exact ⟨by linarith,by nlinarith [mul_nonneg x0.le (by linarith : 0≤X-4)]⟩
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near
    (Real.one_le_rpow x1 (by norm_num : (0:ℝ)≤3/2)) (by norm_num : (1:ℝ)<2)
  let U : ℝ := 2^(K+1)
  have hunit : 2≤U := by
    dsimp [U];rw [pow_succ];nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=K)]
  have h2Q : 8*Q ≤ X^(1/2:ℝ) := by linarith
  have hprod : (8*Q) * X^(3/2:ℝ) ≤ X^2 := by
    calc _ ≤ X^(1/2:ℝ)*X^(3/2:ℝ) := mul_le_mul_of_nonneg_right h2Q (by positivity)
         _ = _ := by rw [← Real.rpow_add x0];norm_num
  have hup : U ≤ 2*X^(3/2:ℝ) := by dsimp [U];rw [pow_succ];linarith
  have hQU : Q*U ≤ (X/2)^2 := by
    have hhq := mul_le_mul_of_nonneg_left hup (by linarith : 0≤Q)
    linarith only [hhq,hprod] -- normalize products below if needed
  have hlog : Real.log (Q*U) ≤ 2*Real.log (X/2) := by
    have he := Real.log_le_log (by positivity : 0<Q*U) hQU
    simpa only [Real.log_pow,Nat.cast_ofNat] using he
  have hlogle := Real.log_le_log (by linarith : 0<X/2) (by linarith : X/2≤X)
  exact ⟨K, hX, Real.one_le_rpow x1 (by norm_num), hd, hunit, hQx.trans hcut,
    hlog, scale_from_lower x0 hh hlow, residual_budget B hX hQ hhi.le (by linarith) hlow habs⟩

end ThinBoundary

end

-- CharacterMean
section

namespace ThinBoundary
open Finset MeasureTheory OAI.Ostmann V7e Viu V86 V11r Vg1 Vct V6i V1e Vx
open scoped Topology BigOperators Interval Classical
def characterMean (B:ℕ) : Prop :=
  ∃C:ℝ,0<C ∧ ∃X₀:ℕ,∀X h:ℕ,
    X₀≤X → 2≤X → 0<h → (h:ℝ)≤(X:ℝ)/2 →
    (((X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V42 h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^B) ∧
    (∀χ:PrimitiveComplexCharacter,
      (χ.modulus:ℝ)≤(Real.log (X:ℝ))^23 →
      (χ.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V4q χ h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^B))
theorem characters_from_density (B : ℕ) (hnraw : characterRaw B) (hpraw : principalRaw B) : characterMean B := by
  obtain ⟨Cn,hCn,Xn,hn⟩ := smoothCharacter B hnraw
  obtain ⟨Cp,hCp,Xp,hp⟩ := smoothPrincipal B hpraw
  obtain ⟨Dn,hDn,hpn⟩ := V10t
  obtain ⟨Dp,hDp,hpp⟩ := V10s
  obtain ⟨Xa,ha⟩ := Filter.eventually_atTop.1 (eventually_parameters B)
  let C : ℝ := 2*Cp+2*Cn+24*Dp^2+24*Dn^2+1
  obtain ⟨N,hN⟩ := exists_nat_ge (max (max (max Xn Xp) Xa) 4)
  refine ⟨C,by dsimp [C]; positivity,N,?_⟩
  intro X h hNX hX2 hh hhX
  have hXlarge : max (max (max Xn Xp) Xa) 4≤(X : ℝ) :=
    hN.trans (by exact_mod_cast hNX)
  have hX4 : 4≤(X : ℝ) := (le_max_right _ _).trans hXlarge
  have hXpos : 0<(X : ℝ) := by linarith
  have hXa : Xa≤(X : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hXlarge)
  have hXnp : max Xn Xp≤(X : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hXlarge)
  have hXn : Xn≤(X : ℝ) := (le_max_left _ _).trans hXnp
  have hXp : Xp≤(X : ℝ) := (le_max_right _ _).trans hXnp
  have hhr : 0<(h : ℝ) := by exact_mod_cast hh
  have hhXr : (h : ℝ)≤X := by linarith
  have hLX : 1≤Real.log (X : ℝ) := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  let M : ℝ := (h : ℝ)^2*(X : ℝ)/(Real.log (X : ℝ))^B
  have hM : 0≤M := by dsimp [M]; positivity
  constructor
  · intro hlower
    have hQpoly : (1 : ℝ)≤(Real.log (X : ℝ))^23 := one_le_pow₀ hLX
    obtain ⟨K,p⟩ := ha (X : ℝ) hXa 1 (h : ℝ) (by norm_num) hQpoly hhr
      (by simpa only [one_pow,one_mul] using hlower)
    let δ : ℝ := (X : ℝ)^(1/12 : ℝ)
    let U : ℝ := (2 : ℝ)^(K+1)
    let S := V3b U
    let f : ℝ → ℂ := fun u => ∑ c∈S,Ve u (h : ℝ) c.val.1
    let g : ℝ → ℂ := V3q f δ
    let R : ℝ := δ*Real.log (X : ℝ)+Real.sqrt (X : ℝ)*Real.log (X : ℝ)/δ+
      (X : ℝ)^2*Real.log U/(δ*U)
    have hδp : 0<δ := by dsimp [δ]; linarith [p.delta_ge_one]
    have hlogU : 0≤Real.log U := Real.log_nonneg (by dsimp [U]; linarith [p.height_ge_two])
    have hR : 0≤R := by dsimp [R]; positivity
    have hcont : ContinuousOn f (Set.Icc ((X : ℝ)-δ) (2*(X : ℝ))) :=
      Vab S (fun c => c.val.1) ((X : ℝ)-δ) (2*(X : ℝ)) h
        (by dsimp [δ]; linarith [p.delta_le_half]) hhr.le
    have hg : ContinuousOn g (Set.Icc (X : ℝ) (2*(X : ℝ))) :=
      Vp7 f (X : ℝ) δ hXpos.le hδp.le hcont
    have hmain : (∫ y in (X : ℝ)..2*(X : ℝ),‖g y‖^2)≤Cp*M := by
      have he := hp K (X : ℝ) (h : ℝ) δ hXp hhr hhX hδp p.delta_le_half
        (by simpa only [one_pow] using p.scale)
        (by simpa only [one_mul] using p.height_log)
      apply he.trans_eq
      dsimp [M]
      ring
    have hres : R^2*(X : ℝ)≤12*M := by
      have he : R^2*(X:ℝ) ≤ M := by simpa only [one_pow,one_mul] using p.residual
      linarith
    have hpoint : ∀ y∈Set.Icc (X : ℝ) (2*(X : ℝ)),
        ‖V42 h y+g y‖≤Dp*R := by
      intro y hy
      exact hpp (X : ℝ) y δ U h hX4 hy hhXr p.delta_ge_one p.delta_le_half p.height_ge_two
    have he := V6h.Vmv (V42 h) g (X : ℝ) R M Cp Dp
      hXpos.le hR hDp.le hg hmain hres hpoint
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ (2*Cp+24*Dp^2)*M := he
      _ ≤ C*M := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg Dn]) hM
      _ = _ := by dsimp [M]; ring
  · intro χ hχpoly hlower
    have hQ1 : (1 : ℝ)≤χ.modulus := by exact_mod_cast χ.positive
    obtain ⟨K,p⟩ := ha (X : ℝ) hXa (χ.modulus : ℝ) (h : ℝ) hQ1 hχpoly hhr hlower
    let δ : ℝ := (X : ℝ)^(1/12 : ℝ)
    let U : ℝ := (2 : ℝ)^(K+1)
    let S := (V1 χ).V14 U
    let f : ℝ → ℂ := fun u => ∑ i∈S,Ve u (h : ℝ) ((V1 χ).zeros i)
    let g : ℝ → ℂ := V3q f δ
    let R : ℝ := δ*Real.log (X : ℝ)+Real.sqrt (X : ℝ)*Real.log (X : ℝ)/δ+
      (χ.modulus : ℝ)^2*(X : ℝ)^2*Real.log ((χ.modulus : ℝ)*U)/(δ*U)
    have hδp : 0<δ := by dsimp [δ]; linarith [p.delta_ge_one]
    have hU1 : 1≤U := by dsimp [U]; linarith [p.height_ge_two]
    have hlogU : 0≤Real.log ((χ.modulus : ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ1 hU1)
    have hR : 0≤R := by dsimp [R]; positivity
    have hcont : ContinuousOn f (Set.Icc ((X : ℝ)-δ) (2*(X : ℝ))) :=
      Vab S (V1 χ).zeros
        ((X : ℝ)-δ) (2*(X : ℝ)) h (by dsimp [δ]; linarith [p.delta_le_half]) hhr.le
    have hg : ContinuousOn g (Set.Icc (X : ℝ) (2*(X : ℝ))) :=
      Vp7 f (X : ℝ) δ hXpos.le hδp.le hcont
    have hmain : (∫ y in (X : ℝ)..2*(X : ℝ),‖g y‖^2)≤Cn*M := by
      have he := hn χ.modulus K χ.positive (X : ℝ) (h : ℝ) δ hXn hhr hhX hδp
        p.delta_le_half p.half_cutoff p.scale p.height_log χ le_rfl
      apply he.trans_eq
      dsimp [M]
      ring
    have hres : R^2*(X : ℝ)≤12*M := by linarith only [p.residual, hM]
    have hpoint : ∀ y∈Set.Icc (X : ℝ) (2*(X : ℝ)),
        ‖V4q χ h y+g y‖≤Dn*R := by
      intro y hy
      exact hpn χ.modulus χ.positive (X : ℝ) y δ U h hX4 hy hhXr p.delta_ge_one
        p.delta_le_half p.height_ge_two (by
          have hl : Real.log ((X:ℝ)/2) ≤ Real.log X := Real.log_le_log (by positivity) (by linarith)
          have hl0 : 0 ≤ Real.log ((X:ℝ)/2) := Real.log_nonneg (by linarith)
          exact p.half_cutoff.trans (by gcongr)) χ le_rfl
    have he := V6h.Vmv (V4q χ h) g (X : ℝ) R M Cn Dn
      hXpos.le hR hDn.le hg hmain hres hpoint
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ (2*Cn+24*Dn^2)*M := he
      _ ≤ C*M := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg Dp]) hM
      _ = _ := by dsimp [M]; ring
end ThinBoundary

end

-- ProgressionL1
section

namespace ThinBoundary
open Complex Filter Finset MeasureTheory OAI.Ostmann ArithmeticFunction Vel V7e
open V2h (V9a)
open V5d (Vaw)
open scoped Topology Interval BigOperators Classical
theorem primitive_L1 (A q:ℕ) [NeZero q] (X h:ℕ) (C:ℝ)
    (hC:0≤C) (hlog:1≤Real.log (X:ℝ))
    (hscale:(q:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ))
    (hsmall:(q:ℝ)≤(Real.log (X:ℝ))^23)
    (hprincipal:(∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V42 h y‖^2)≤
      C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^(2*A))
    (hprimitive:∀χ:PrimitiveComplexCharacter,
      (χ.modulus:ℝ)≤(Real.log (X:ℝ))^23 →
      (χ.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V4q χ h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^(2*A)) :
    (∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vbj q h y)≤
      (C+1)*(q.totient:ℝ)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
  have hsingle (χ:DirichletCharacter ℂ q) :
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),
        ‖V3n (V9a h y) (fun k=>(vonMangoldt k:ℂ)) χ.primitiveCharacter‖)≤
        (C+1)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
    by_cases hχ : χ=1
    · subst χ
      simp_rw [V1jt]
      exact V217 (fun r=>(∑k∈Ioc r (r+h),V1n k)-(h:ℂ)) X h A C _ hC (by linarith) hprincipal
    · let p := Vni χ hχ
      have hpq : (p.modulus:ℝ)≤(q:ℝ) := by exact_mod_cast V18g χ hχ
      have hpsmall : (p.modulus:ℝ)≤(Real.log (X:ℝ))^23 := hpq.trans hsmall
      have hpscale : (p.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) := by
        apply le_trans _ hscale
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hpq 2) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [V1ju χ hχ]
      exact V217 (fun r=>∑k∈Ioc r (r+h),Vl p k) X h A C _ hC (by linarith)
        (hprimitive p hpsmall hpscale)
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [V19x]
  apply (sum_le_sum (fun χ _=>hsingle χ)).trans_eq
  rw [sum_const,card_univ,nsmul_eq_mul,hcard]
  ring
set_option maxHeartbeats 1000000 in
theorem progression_L1 (A : ℕ) (H : characterMean (2*A)) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ (q : ℕ) [NeZero q] (X h : ℕ),
      X₀ ≤ X → 2 ≤ X → 0<h → (h:ℝ)≤(X:ℝ)/2 →
      (q:ℝ)^2*(X:ℝ)^(4/9:ℝ) ≤ (h:ℝ) → (q:ℝ) ≤ (Real.log (X:ℝ))^23 →
      (∑ r ∈ Ico X (2*X), V3z.V6v q (Ioc r (r+h))) ≤ C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
  obtain ⟨C,hC,X₀,hmean⟩ := H
  obtain ⟨N,hN⟩ := eventually_atTop.1 (Vw0 A 1 (by norm_num))
  obtain ⟨P,hP⟩ := eventually_atTop.1
    (V5d.Vqk A 1 (by norm_num))
  obtain ⟨M,hM⟩ := exists_nat_gt (Real.exp (1:ℝ))
  refine ⟨C+3,by positivity,X₀+N+P+M+3,?_⟩
  intro q inst X h hthreshold hX hh hhX hscale hsmall
  have hhXnat : h≤X := by exact_mod_cast (show (h:ℝ)≤(X:ℝ) by linarith)
  rw [V2h.Vdb q h (by omega : X≤2*X)]
  have hX₀ : X₀≤X := by omega
  have hNX : N≤X := by omega
  have hPX : P≤X := by omega
  have hMX : M≤X := by omega
  have hlog : 1≤Real.log (X:ℝ) := by
    have he : Real.exp (1:ℝ)≤(X:ℝ) := hM.le.trans (by exact_mod_cast hMX)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (1:ℝ)) he
  have hq1 : (1:ℝ)≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hx1 : (1:ℝ)≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hpow : 1≤(X:ℝ)^(4/9:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hqX : q≤X := by
    have hhR : (h:ℝ)≤(X:ℝ) := by exact_mod_cast hhXnat
    have hq2 : (q:ℝ)^2≤(h:ℝ) := (le_mul_of_one_le_right (sq_nonneg _) hpow).trans hscale
    exact_mod_cast (show (q:ℝ)≤(X:ℝ) by nlinarith)
  have hscale1 : (X:ℝ)^(4/9:ℝ)≤(h:ℝ) := by
    apply le_trans _ hscale
    exact le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (one_le_pow₀ hq1)
  have hboth := hmean X h hX₀ hX hh hhX
  have hprim := primitive_L1 A q X h C hC.le hlog hscale hsmall
    (hboth.1 hscale1) hboth.2
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hprimdiv := div_le_div_of_nonneg_right hprim hφ.le
  have he := hN X hNX q (NeZero.pos q) hqX
  have hp := hP X hPX
  simp only [one_mul] at he hp
  have heh := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) h)
  have hph := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) h)
  calc
    _ ≤ (∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vaw q h y)+
        2*(h:ℝ)*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ) :=
      V5d.V1cz q X h (by omega) hhXnat
    _ ≤ ((∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vbj q h y)/(q.totient:ℝ)+
        (h:ℝ)*(Real.log (q:ℝ)+2*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ)))+
        2*(h:ℝ)*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ) :=
      (add_le_add) (V17a X h (by omega) hhXnat) le_rfl
    _ ≤ (((C+1)*(q.totient:ℝ)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A)/(q.totient:ℝ)+
        (h:ℝ)*((X:ℝ)/(Real.log (X:ℝ))^A))+
        (h:ℝ)*((X:ℝ)/(Real.log (X:ℝ))^A) := by
      apply add_le_add (add_le_add hprimdiv heh)
      nlinarith only [hph]
    _ = (C+3)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by field_simp; ring
end ThinBoundary

end

-- Shifted
section

namespace ThinBoundary
open Finset Filter
open scoped BigOperators Topology Classical

noncomputable def primeClassMass (q b n Y : ℕ) : ℝ :=
  ∑ k ∈ (Ioc (n-2*Y) (n-Y)).filter (fun k => k % q = b),
    if k.Prime then Real.log (k:ℝ) else 0

theorem classError {q b n Y : ℕ} [NeZero q] (hb : b<q) (hc : b.Coprime q)
    (hn : 2*Y≤n) :
    |primeClassMass q b n Y - (Y:ℝ)/(q.totient:ℝ)| ≤
      V3z.V6v q (Ioc (n-2*Y) ((n-2*Y)+Y)) := by
  let I := Ioc (n-2*Y) ((n-2*Y)+Y)
  have hunit : IsUnit (b:ZMod q) := (ZMod.isUnit_iff_coprime b q).mpr hc
  have he := V3z.V114 I (b:ZMod q) hunit
  have hI : I.card = Y := by simp [I]
  have hfilter : I.filter (fun k : ℕ => (k:ZMod q) = (b:ZMod q)) =
      (Ioc (n-2*Y) (n-Y)).filter (fun k => k % q=b) := by
    have hw : n-2*Y+Y = n-Y := by omega
    ext k
    simp only [I,hw,mem_filter,ZMod.natCast_eq_natCast_iff,Nat.ModEq,Nat.mod_eq_of_lt hb]
  change ‖(∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q) = (b:ZMod q)), V54.V76 k) - (I.card:ℂ)/(q.totient:ℂ)‖ ≤ _ at he
  rw [hfilter, hI] at he
  simpa only [primeClassMass,V54.V76, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs] using he

theorem allClassError {q n Y : ℕ} [NeZero q] (hn : 2*Y≤n) :
    (q.totient:ℝ) * (∑ b ∈ (range q).filter (fun b => b.Coprime q),
        |primeClassMass q b n Y - (Y:ℝ)/(q.totient:ℝ)|) ≤
        (q:ℝ)^2 * V3z.V6v q (Ioc (n-2*Y) (n-2*Y+Y)) := by
  let I := Ioc (n-2*Y) (n-2*Y+Y)
  let U := (range q).filter (fun b => b.Coprime q)
  have hsum : (∑ b ∈ U, |primeClassMass q b n Y - (Y:ℝ)/(q.totient:ℝ)|) ≤
      (U.card:ℝ)*V3z.V6v q I := by
    calc _ ≤ ∑ _b ∈ U, V3z.V6v q I := sum_le_sum fun b hb =>
                  classError (mem_range.mp (mem_filter.mp hb).1) (mem_filter.mp hb).2 hn
         _ = _ := by simp
  have htot : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hcard : (U.card:ℝ) ≤ q := by exact_mod_cast (show U.card≤q by
    have := card_le_card (filter_subset (fun b : ℕ => b.Coprime q) (range q))
    simpa [U] using this)
  have hv := V3z.Vtd q I
  calc _ ≤ (q.totient:ℝ) * ((U.card:ℝ)*V3z.V6v q I) :=
             mul_le_mul_of_nonneg_left hsum (by positivity)
       _ ≤ (q:ℝ)*((q:ℝ)*V3z.V6v q I) := by gcongr
       _ = _ := by ring

theorem translated_dyadic {X Y Z : ℕ} (hY : 0<Y) (hlo : Z+2*Y≤X) (hhi : X≤2*Z)
    (F : ℕ→ℝ) (hnon : ∀ i,0≤F i) :
    ∑ n ∈ (Icc X (2*X)).filter Even, F (n-2*Y) ≤
      (∑ r ∈ Ico Z (2*Z), F r) + ∑ r ∈ Ico X (2*X), F r := by
  let E := (Icc X (2*X)).filter Even
  have inj : Set.InjOn (fun n => n-2*Y) (E:Set ℕ) := by
    intro n hn m hm he
    have hn' := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hm' := (mem_Icc.mp (mem_filter.mp hm).1).1
    change n-2*Y=m-2*Y at he
    omega
  have sub : E.image (fun n => n-2*Y) ⊆ Ico Z (2*Z) ∪ Ico X (2*X) := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
    have h := mem_Icc.mp (mem_filter.mp hn).1
    by_cases hcut : n-2*Y < 2*Z
    · exact mem_union_left _ (mem_Ico.mpr ⟨by omega,hcut⟩)
    · exact mem_union_right _ (mem_Ico.mpr ⟨by omega,by omega⟩)
  calc _ = ∑ r ∈ E.image (fun n => n-2*Y),F r := (sum_image inj).symm
       _ ≤ ∑ r ∈ Ico Z (2*Z) ∪ Ico X (2*X), F r :=
         sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => hnon i)
       _ ≤ _ := by
         rw [← sum_union_inter]
         linarith [sum_nonneg (s := Ico Z (2*Z) ∩ Ico X (2*X)) (fun i _ => hnon i)]

end ThinBoundary

end

-- ShiftShape
section

namespace ThinBoundary
open Filter
open scoped Topology

def windowCut (X : ℕ) := (Nat.log 2 (2*Nat.sqrt X + 2))^8

private theorem small_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n+2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ)^(Nat.log 2 (n+2)) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ)-2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2
    (Nat.cast_nonneg (Nat.log 2 (n+2)) : 0 ≤ (_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm,hraw,hlog]

theorem shift_shape (T : ℕ) :
    ∀ᶠ X : ℕ in atTop,
    let Y := Nat.sqrt X
    let Z := (X+1)/2
    T≤Z ∧ 4≤Z ∧ Z≤X ∧ X≤2*Z ∧ Z+2*Y≤X ∧ 0<Y ∧ 2*Y≤Z ∧
      (windowCut X:ℝ) ≤ (Real.log (Z:ℝ))^9 ∧
      1≤Real.log (Z:ℝ) ∧
      (windowCut X:ℝ)^2*(X:ℝ)^(4/9:ℝ) ≤ (Y:ℝ) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop
      ((4:ℝ)^8))
  have habs := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventual_log_power 18 (1/18) 2 (by norm_num))
  filter_upwards [eventually_ge_atTop (max 64 (2*(N+T))),habs] with X hX hlogabs
  dsimp only
  let Y := Nat.sqrt X
  let Z := (X+1)/2
  have h64 : 64≤X := (le_max_left _ _).trans hX
  have hh : 2*(N+T) ≤ X := (le_max_right _ _).trans hX
  have hy8 : 8≤Y := Nat.le_sqrt.mpr h64
  have hysq : Y*Y ≤ X := Nat.sqrt_le _
  have h8y : 8*Y ≤ X := (Nat.mul_le_mul_right _ hy8).trans hysq
  have hzx : Z≤X := by dsimp [Z];omega
  have hzl : 2*Y≤Z := by dsimp [Z];omega
  have hNZ : N≤Z := by dsimp [Z];omega
  have hZ0 : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hzlog : (4:ℝ)^8 ≤ Real.log (Z:ℝ) := hN _ hNZ
  have hzlog1 : 1≤Real.log (Z:ℝ) := by linarith
  have hL0 : 0≤Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))
  have hl := Real.log_le_log (by exact_mod_cast (show 0<2*Y by omega))
    (by exact_mod_cast hzl : ((2*Y:ℕ):ℝ) ≤ (Z:ℝ))
  have hNat : (Nat.log 2 (2*Y+2):ℝ) ≤ 4*Real.log (Z:ℝ) := by
    linarith [small_log (2*Y) (by omega)]
  have hcap : (windowCut X:ℝ) ≤ (Real.log (Z:ℝ))^9 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hNat 8
    rw [mul_pow] at h
    calc _ = ((Nat.log 2 (2*Y+2):ℝ))^8 := by simp [windowCut,Y]
         _ ≤ _ := h.trans (by rw [show (Real.log (Z:ℝ))^9 = Real.log (Z:ℝ)*(Real.log (Z:ℝ))^8 by ring]; exact mul_le_mul_of_nonneg_right hzlog (by positivity))
  refine ⟨by change T≤Z;omega,by change 4≤Z;omega,hzx,by omega,
    by omega,by change 0<Y;omega,hzl,hcap,hzlog1,?_⟩
  have hlogmon := Real.log_le_log hZ0 (by exact_mod_cast hzx : (Z:ℝ) ≤ (X:ℝ))
  have hc := hcap.trans (pow_le_pow_left₀ (by linarith) hlogmon 9)
  have hq2 : (windowCut X:ℝ)^2 ≤ (Real.log (X:ℝ))^18 := by
    calc _ ≤ ((Real.log (X:ℝ))^9)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
         _ = _ := by ring
  have hYroot : Real.sqrt (X:ℝ) ≤ 2*(Y:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    have ht := Nat.lt_succ_sqrt X
    change X < (Y+1)*(Y+1) at ht
    have ht' : (X:ℝ) < ((Y:ℝ)+1)*((Y:ℝ)+1) := by exact_mod_cast ht
    have hYreal : (8:ℝ)≤Y := by exact_mod_cast hy8
    constructor <;> nlinarith
  have hhalf : (X:ℝ)^(1/18:ℝ) * (X:ℝ)^(4/9:ℝ) = Real.sqrt (X:ℝ) := by
    rw [← Real.rpow_add (by exact_mod_cast (show 0<X by omega)),Real.sqrt_eq_rpow]
    norm_num
  have hlogabs' : (2:ℝ)*(Real.log (X:ℝ))^18 ≤ (X:ℝ)^(1/18:ℝ) := hlogabs
  have hs := mul_le_mul_of_nonneg_right hlogabs' (by positivity : (0:ℝ) ≤ (X:ℝ)^(4/9:ℝ))
  rw [hhalf] at hs
  exact (mul_le_mul_of_nonneg_right hq2 (by positivity)).trans (by nlinarith only [hs,hYroot])
end ThinBoundary

end

-- PhysicalRow
section

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped BigOperators
namespace ThinWindowModel

private theorem phase_nat (r : ℕ) : phase (r:ℝ) = 1 := by
  unfold phase
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I (r:ℤ) using 2 <;> push_cast <;> ring

private theorem phase_row_mod {q : ℕ} (hq : 0 < q) (n a k : ℕ) :
    phase ((((k % q:ℕ):ℝ)-n)*a/q) = phase (((k:ℝ)-n)*a/q) := by
  have hk : (k:ℝ) = ((k % q:ℕ):ℝ) + (q:ℝ)*((k/q:ℕ):ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have eqn : ((k:ℝ)-n)*a/q = (((k % q:ℕ):ℝ)-n)*a/q + ((k/q*a : ℕ):ℝ) := by
    conv_lhs => rw [hk]
    field_simp [show (q:ℝ) ≠ 0 by exact_mod_cast hq.ne']
    push_cast
    ring
  rw [eqn,BulkCircle.phase_add,phase_nat,mul_one]

private theorem row_mod {q : ℕ} (hq : 0 < q) (n k : ℕ) :
    rowWeight q n (k % q) = rowWeight q n k := by
  unfold rowWeight
  refine sum_congr rfl (fun a ha => ?_)
  rw [phase_row_mod hq]

private theorem row_at_difference {n k : ℕ} (hk : k ≤ n) (Q : ℕ) :
    (realWeight Q (n-k) : ℂ) = ∑ q ∈ Icc 1 Q, rowWeight q n k := by
  rw [realWeight_cast]
  apply sum_congr rfl
  intro q hq
  unfold rowWeight
  apply sum_congr rfl
  intro a ha
  rw [Nat.cast_sub hk]
  congr 2
  ring

private theorem sum_reflect {Y n : ℕ} (hn : 2*Y ≤ n) (f : ℕ → ℂ) :
    (∑ i ∈ Ico Y (2*Y), f i) = ∑ k ∈ Ioc (n-2*Y) (n-Y), f (n-k) := by
  apply sum_nbij' (fun i => n-i) (fun k => n-k)
  · intro i hi
    simp only [mem_Ico] at hi
    exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro k hk
    simp only [mem_Ioc] at hk
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i hi; simp only [mem_Ico] at hi; omega
  · intro k hk; simp only [mem_Ioc] at hk; omega
  · intro i hi
    have h := mem_Ico.mp hi
    rw [show n-(n-i)=i by omega]

private theorem partition_row {q n Y : ℕ} (hq : 0<q) (hQ : q ≤ n-2*Y) :
    (∑ k ∈ Ioc (n-2*Y) (n-Y), (primeWeight k:ℂ) * rowWeight q n k) =
      measuredRow q n (fun b => ThinBoundary.primeClassMass q b n Y) := by
  classical
  let J := Ioc (n-2*Y) (n-Y)
  have term (k : ℕ) (hk : k ∈ J) :
      (primeWeight k:ℂ)*rowWeight q n k =
      ∑ b ∈ units q, if k % q=b then (primeWeight k:ℂ)*rowWeight q n b else 0 := by
    by_cases hpr : k.Prime
    · have hlt := (mem_Ioc.mp hk).1
      have hc : k.Coprime q := hpr.coprime_iff_not_dvd.mpr
        (fun hd => by have := Nat.le_of_dvd hq hd; omega)
      have hu : k % q ∈ units q := by
        apply mem_filter.mpr
        exact ⟨mem_range.mpr (Nat.mod_lt _ hq), by
          change (k % q).gcd q = 1
          simpa [Nat.gcd_comm] using (Nat.gcd_rec q k).symm.trans (show q.gcd k = 1 from hc.symm)⟩
      rw [sum_eq_single (k % q)]
      · simp [row_mod hq]
      · intro b hb hne
        simp [Ne.symm hne]
      · exact fun h => False.elim (h hu)
    · simp [primeWeight,hpr]
  change (∑ k ∈ J, _) = _
  rw [sum_congr rfl term,sum_comm]
  unfold measuredRow
  apply sum_congr rfl
  intro b hb
  change _ = ((∑ k ∈ J.filter (fun k => k % q=b), primeWeight k : ℝ):ℂ) * rowWeight q n b
  rw [Complex.ofReal_sum, sum_mul, sum_filter]

theorem physical_row_identity {Y n Q : ℕ} (hn : 2*Y ≤ n) (hQ : Q ≤ n-2*Y) :
    ThinWindowMinor.modelMass (Ico Y (2*Y)) (realWeight Q) n =
      (∑ q ∈ Icc 1 Q, measuredRow q n (fun b => ThinBoundary.primeClassMass q b n Y)).re := by
  have hfilter : (Ico Y (2*Y)).filter (fun i => i ≤ n) = Ico Y (2*Y) :=
    filter_eq_self.mpr (fun i hi => by have := mem_Ico.mp hi; omega)
  have eqn : ((ThinWindowMinor.modelMass (Ico Y (2*Y)) (realWeight Q) n : ℝ):ℂ) =
      ∑ q ∈ Icc 1 Q, measuredRow q n (fun b => ThinBoundary.primeClassMass q b n Y) := by
    unfold ThinWindowMinor.modelMass
    rw [hfilter,Complex.ofReal_sum]
    simp_rw [Complex.ofReal_mul]
    rw [sum_reflect hn]
    calc
      _ = ∑ k ∈ Ioc (n-2*Y) (n-Y), ∑ q ∈ Icc 1 Q, (primeWeight k:ℂ)*rowWeight q n k := by
        apply sum_congr rfl
        intro k hk
        have h := mem_Ioc.mp hk
        rw [show n-(n-k)=k by omega,row_at_difference (by omega), sum_mul]
        apply sum_congr rfl
        intro q hq
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro q hq
        exact partition_row (mem_Icc.mp hq).1 ((mem_Icc.mp hq).2.trans hQ)
  exact congrArg Complex.re eqn
theorem eventual_physical_row :
    ∃ N : ℕ, ∀ X ≥ N, ∀ n ∈ (Icc X (2*X)).filter Even,
      let Y := Nat.sqrt X
      let Q := ThinBoundary.windowCut X
      ThinWindowMinor.modelMass (Ico Y (2*Y)) (realWeight Q) n =
        (∑ q ∈ Icc 1 Q, measuredRow q n (fun b => ThinBoundary.primeClassMass q b n Y)).re := by
  apply eventually_atTop.mp
  filter_upwards [ThinBoundary.shift_shape 0,eventually_ge_atTop (2:ℕ)] with X h hx
  rcases h with ⟨_,_,_,_,hz,hy,hz2,_,_,hp⟩
  intro n hn
  have hnX := (mem_Icc.mp (mem_filter.mp hn).1).1
  have hxpow : 1 ≤ (X:ℝ)^(4/9:ℝ) := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ X by omega)) (by norm_num)
  have hq : ThinBoundary.windowCut X ≤ X.sqrt := by
    have h1 := Nat.le_self_pow (by decide : 2 ≠ 0) (ThinBoundary.windowCut X)
    have hh : (ThinBoundary.windowCut X:ℝ) ≤ (X.sqrt:ℝ) := calc
      _ ≤ (ThinBoundary.windowCut X:ℝ)^2 := by exact_mod_cast h1
      _ ≤ _ := (le_mul_of_one_le_right (sq_nonneg _) hxpow).trans hp
    exact_mod_cast hh
  apply physical_row_identity <;> omega

end ThinWindowModel

end

-- RMS
section

open Filter Finset
open scoped Topology

namespace ThinWindowMinor

/-- A uniform log-square saving for the small-prime Fourier model gives a
vanishing relative variance on any subset of targets through 2X. -/
theorem physical_error_tends (I : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) {C : ℝ}
    (hsup : ∀ᶠ X : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖shortSum X t - poly (I X) (w X) t‖ ≤
        C * (Nat.sqrt X : ℝ) / (Real.log (2*(Nat.sqrt X : ℝ)))^2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, ∀ F : Finset ℕ, (∀ n ∈ F, n ≤ 2*X) →
      (∑ n ∈ F, (trueMass X n-modelMass (I X) (w X) n)^2) ≤ ε*(X:ℝ)^2 := by
  intro ε hε
  let K := 6 * C^2 * Real.log 4
  have ht := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp root_tends)).eventually_ge_atTop (max 1 (K / ε))
  filter_upwards [hsup, ht, eventually_ge_atTop (16 : ℕ)] with X hS hlog hX
  intro F hF
  let Y := Nat.sqrt X
  let L := Real.log (2*(Y:ℝ))
  change max 1 (K/ε) ≤ Real.log ((2*Y:ℕ):ℝ) at hlog
  push_cast at hlog
  change max 1 (K/ε) ≤ L at hlog
  have hL : 1 ≤ L := (le_max_left _ _).trans hlog
  have hLpos : 0 < L := by linarith
  have hY : 4 ≤ Y := Nat.le_sqrt.mpr (by omega)
  have hy2 : (Y:ℝ)^2 ≤ (X:ℝ) := by exact_mod_cast Nat.sqrt_le' X
  have hlast : K/L^3 ≤ ε := by
    apply (div_le_iff₀ (pow_pos hLpos _)).mpr
    have h := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hlog)
    calc K ≤ ε*L := by linarith
         _ ≤ ε*L^3 := mul_le_mul_of_nonneg_left (le_self_pow₀ hL (by decide : 3 ≠ 0)) hε.le
  have hlog2 : Real.log (2*X:ℕ) ≤ 3*L := by
    change Real.log ((2*X:ℕ):ℝ) ≤ ((3 : ℕ):ℝ) * Real.log (2*(Y:ℝ))
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    norm_cast
    have hy : X < (Y+1)^2 := Nat.lt_succ_sqrt' X
    nlinarith [Nat.mul_le_mul_left (Y^2) hY]
  have happrox (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖shortSum X t - poly (I X) (w X) t‖ ≤ (C / L^2) * Y := by
    apply (hS t ht).trans_eq
    change C*(Y:ℝ)/L^2 = (C/L^2)*Y
    ring
  have hphys := physical_error (X:=X) (by change 2 ≤ Y; omega) (I X) F (w X) hF (C/L^2) happrox
  calc _ ≤ ((C/L^2)*(Y:ℝ))^2 * (Real.log (2*X:ℕ) * (Real.log 4 * (2*X:ℕ))) := hphys
       _ ≤ ((C/L^2)*(Y:ℝ))^2 * ((3*L) * (Real.log 4 * (2*X:ℕ))) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog2 (by positivity)) (sq_nonneg _)
       _ = (K/L^3) * ((Y:ℝ)^2 * X) := by
         dsimp [K]
         push_cast
         field_simp
         ring
       _ ≤ ε*(X:ℝ)^2 := by
         rw [sq (X:ℝ)]
         exact mul_le_mul hlast (mul_le_mul_of_nonneg_right hy2 (by positivity)) (by positivity) hε.le

end ThinWindowMinor

end

-- RightPackets
section

/- Adapted from the formal proof of L-goldbach-frontier-skirt-polylog-moduli:
we retain the sharpened family density exponent 3 instead of rounding to 4,
which enlarges the allowed short-window inverse scale from X^(5/12) to X^(5/9).
The principal-character density proof is from LogTruSoul, goldbach-proofs PR #3746.
The source, original credits, and this adaptation are licensed Apache-2.0. -/

section
noncomputable section
open scoped BigOperators Classical
namespace V1eq
theorem Thin_family_three :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 1/2 ≤ σ → σ ≤ 1 →
      ∀ F : Finset OAI.Ostmann.PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((OAI.Ostmann.V1 χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ)^2*T)^(3*(1-σ)) * (Real.log ((Q : ℝ)*T))^13 := by
  obtain ⟨C,hC,hDensity⟩ := OAI.Ostmann.V1f0
  refine ⟨C,hC,?_⟩
  intro Q hQ T σ hT hσ hσ1 F hF
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQsq : (1 : ℝ) ≤ (Q : ℝ)^2 := by nlinarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hBase : (1 : ℝ) ≤ (Q : ℝ)^2*T := one_le_mul_of_one_le_of_one_le hQsq hT1
  have hLog : 0 ≤ Real.log ((Q : ℝ)*T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQR hT1)
  apply (hDensity Q hQ T σ hT hσ hσ1 F hF).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hLog 13)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le hBase ((div_le_iff₀ (by linarith : 0 < 2-σ)).mpr (by nlinarith [sq_nonneg (1-σ)]))
end V1eq
end
end

section
noncomputable section
open Finset MeasureTheory Set
open scoped BigOperators Interval Classical
namespace Vmm
theorem Thin_power_decay {X A δ σ : ℝ} (hX : 1 ≤ X) (hA : 0 ≤ A)
    (hscale : A ≤ X ^ (5/9 : ℝ)) (hδ : 0 ≤ δ)
    (hσ : σ ≤ 1 - δ) :
    X ^ (2 * σ - 2) * A ^ (3 * (1 - σ)) ≤ X ^ (-δ / 3) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  calc
    _ ≤ X ^ (2 * σ - 2) * (X ^ (5/9 : ℝ)) ^ (3 * (1 - σ)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hA hscale (by linarith)) (Real.rpow_nonneg hXpos.le _)
    _ = X ^ ((σ - 1) / 3) := by
      rw [← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos]
      congr 1
      ring
    _ ≤ X ^ (-δ / 3) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
end Vmm
end
end

section
noncomputable section
open Finset MeasureTheory Set
open scoped BigOperators Interval Classical
namespace Vmm
set_option maxHeartbeats 1500000 in
theorem Thin_weighted_sum {α : Type*} (F : Finset α) (β : α → ℝ)
    {X A C L δ : ℝ} (hX : 1 ≤ X) (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hscale : A ≤ X ^ (5/9 : ℝ))
    (hβ : ∀ i ∈ F, 1/2 ≤ β i ∧ β i ≤ 1-δ)
    (hdensity : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1-δ →
      ((F.filter (fun i => σ ≤ β i)).card : ℝ) ≤
        C * A ^ (3 * (1-σ)) * L^13) :
    (∑ i ∈ F, X ^ (2 * β i - 2)) ≤
      C * L^13 * (1 + Real.log X) * X ^ (-δ/3) := by
  have hsc : A ^ (3/4:ℝ) ≤ X ^ (5/12:ℝ) := calc
    _ ≤ (X^(5/9:ℝ))^(3/4:ℝ) := Real.rpow_le_rpow hA hscale (by norm_num)
    _ = _ := by rw [← Real.rpow_mul (by linarith : 0≤X)]; norm_num
  apply Vry F β hX (Real.rpow_nonneg hA _) hC hL hδ hδhalf hsc hβ
  intro σ hσ hs
  rw [← Real.rpow_mul hA, show (3/4:ℝ)*(4*(1-σ))=3*(1-σ) by ring]
  exact hdensity σ hσ hs

end Vmm
end
end

section
noncomputable section
open Finset
open scoped BigOperators Classical
namespace Vmn
theorem Thin_Vwf :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ X T η δ : ℝ,
      1 ≤ X → 2 ≤ T → 0 < η → 0 ≤ δ → δ ≤ 1/2 →
      (Q : ℝ)^2/η ≤ X^(5/9 : ℝ) →
      ∀ F : Finset OAI.Ostmann.PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∑ i ∈ ((OAI.Ostmann.V1 χ).V14 T).filter
          (fun i => 1/2 ≤ ((OAI.Ostmann.V1 χ).zeros i).re ∧
            ((OAI.Ostmann.V1 χ).zeros i).re ≤ 1-δ),
          X ^ (2*((OAI.Ostmann.V1 χ).zeros i).re-2)) ≤
        C * (Real.log ((Q : ℝ)*T))^13 * (1 + Real.log X) *
          (max 1 (η*T))^2 * X^(-δ/3) := by
  obtain ⟨C,hC,hDensity⟩ := V1eq.Thin_family_three
  refine ⟨C,hC,?_⟩
  intro Q hQ X T η δ hX hT hη hδ hδhalf hscale F hF
  let Z := OAI.Ostmann.V1
  let S : Finset (Σ _ : OAI.Ostmann.PrimitiveComplexCharacter, ℕ) :=
    F.sigma (fun χ => ((Z χ).V14 T).filter
      (fun i => 1/2 ≤ ((Z χ).zeros i).re ∧ ((Z χ).zeros i).re ≤ 1-δ))
  let β : (Σ _ : OAI.Ostmann.PrimitiveComplexCharacter, ℕ) → ℝ :=
    fun i => ((Z i.1).zeros i.2).re
  let B := max 1 (η*T)
  have hB : 1 ≤ B := le_max_left _ _
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hpow : 0 ≤ X^(5/9 : ℝ) := Real.rpow_nonneg hXpos.le _
  have hscaleB : (Q : ℝ)^2*T ≤ X^(5/9 : ℝ)*B := by
    have hs := (div_le_iff₀ hη).mp hscale
    calc
      _ ≤ (X^(5/9 : ℝ)*η)*T :=
        mul_le_mul_of_nonneg_right hs (by linarith)
      _ = X^(5/9 : ℝ)*(η*T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hpow
  have hβ : ∀ i ∈ S, (1/2 : ℝ) ≤ β i ∧ β i ≤ 1-δ := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hi).2).2
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hL : 0 ≤ Real.log ((Q : ℝ)*T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQR (by linarith))
  have hd (σ : ℝ) (hσ : 1/2 ≤ σ) (hσδ : σ ≤ 1-δ) :
      ((S.filter (fun i => σ ≤ β i)).card : ℝ) ≤
        (C*B^2) * (X^(5/9 : ℝ))^(3*(1-σ)) * (Real.log ((Q : ℝ)*T))^13 := by
    have hsub : S.filter (fun i => σ ≤ β i) ⊆
        F.sigma (fun χ => ((Z χ).V14 T).filter
          (fun i => σ ≤ ((Z χ).zeros i).re)) := by
      intro i hi
      obtain ⟨hiS,hiσ⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiF,hiZ⟩ := Finset.mem_sigma.mp hiS
      exact Finset.mem_sigma.mpr ⟨hiF,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiZ).1,hiσ⟩⟩
    have hf := V18s
      (show 0 ≤ (Q : ℝ)^2*T by positivity) hB hpow hscaleB
      (show 0 ≤ 3*(1-σ) by linarith) (show 3*(1-σ) ≤ 2 by linarith)
    calc
      _ ≤ ((F.sigma (fun χ => ((Z χ).V14 T).filter
          (fun i => σ ≤ ((Z χ).zeros i).re))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = ∑ χ ∈ F, ((Z χ).count σ T : ℝ) := by
        simp only [Finset.card_sigma, Nat.cast_sum, OAI.Ostmann.ComplexZeroEnumeration.count]
      _ ≤ C * ((Q : ℝ)^2*T)^(3*(1-σ)) * (Real.log ((Q : ℝ)*T))^13 :=
        hDensity Q hQ T σ hT hσ (by linarith) F hF
      _ ≤ C * (B^2 * (X^(5/9 : ℝ))^(3*(1-σ))) *
          (Real.log ((Q : ℝ)*T))^13 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hf hC.le) (pow_nonneg hL _)
      _ = _ := by ring
  have hb := Vmm.Thin_weighted_sum S β hX hpow
    (show 0 ≤ C*B^2 by positivity) hL hδ hδhalf le_rfl hβ hd
  have hbr : (C*B^2) * (Real.log ((Q : ℝ)*T))^13 *
      (1+Real.log X) * X^(-δ/3) =
      C * (Real.log ((Q : ℝ)*T))^13 * (1+Real.log X) * B^2 * X^(-δ/3) := by ring
  rw [hbr] at hb
  simpa only [S,β,Z,B,Finset.sum_sigma] using hb
end Vmn
end
end

section
noncomputable section
open Filter Finset
open scoped Topology BigOperators Classical
namespace V1l
theorem Thin_V1gm (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1 ≤ Q → ∀ X T η : ℝ,
      X₀ ≤ X → 2 ≤ T → 0 < η →
      (Q : ℝ)^2/η ≤ X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T) ≤ 2*Real.log X →
      ∀ F : Finset OAI.Ostmann.PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∑ i ∈ ((OAI.Ostmann.V1 χ).V14 T).filter
          (fun i => 1/2 ≤ ((OAI.Ostmann.V1 χ).zeros i).re ∧
            ((OAI.Ostmann.V1 χ).zeros i).re ≤ 1-V2j A X),
          X ^ (2*((OAI.Ostmann.V1 χ).zeros i).re-2)) ≤
        C * (max 1 (η*T))^2 / (Real.log X)^A := by
  obtain ⟨C,hC,hband⟩ := Vmn.Thin_Vwf
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.1 (Vgn A)
  refine ⟨16384*C,by positivity,X₀,?_⟩
  intro Q hQ X T η hXX Tge hη hscale hlogs F hF
  obtain ⟨hX,hlogX,hδ,hδhalf⟩ := hX₀ X hXX
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hL : 0 ≤ Real.log ((Q : ℝ)*T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQR (by linarith))
  have hb := hband Q hQ X T η (V2j A X) hX.le Tge hη hδ hδhalf hscale F hF
  apply hb.trans
  calc
    _ = (C*(max 1 (η*T))^2) *
        ((Real.log ((Q : ℝ)*T))^13 * (1+Real.log X) * X^(-V2j A X/3)) := by ring
    _ ≤ (C*(max 1 (η*T))^2) * (16384/(Real.log X)^A) :=
      mul_le_mul_of_nonneg_left (V1r8 A hX hlogX hL hlogs) (by positivity)
    _ = _ := by ring
end V1l
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1l (V2j)
namespace Vda
theorem Thin_V1gn (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X T η K : ℝ,
      X₀≤X → 2≤T → 0<η → 0≤K →
      (Q : ℝ)^2/η≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ a : PrimitiveComplexCharacter → ℕ → ℂ,
      (∀ χ∈F, ∀ i∈((V1 χ).V14 T).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        ‖a χ i‖≤K*min η (1/T)*Real.log X) →
      (∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈((V1 χ).V14 T).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        a χ i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
          C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C₀,hC₀,X₀,hDensity⟩ :=
    V1l.Thin_V1gm (B+4)
  let D : ℝ := 20800/Real.log (14/13)
  have hD : 0<D := by
    dsimp [D]
    exact div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ)<14/13))
  refine ⟨4*D*C₀, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X T η K hX₀ hT hη hK hscale hlog F hF a ha
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL1 : 1≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hh
  have hL : 0<Real.log X := by linarith
  have hTp : 0<T := by linarith
  have hQT : 0≤Real.log ((Q : ℝ)*T) := by
    apply Real.log_nonneg
    have hQR : (1 : ℝ)≤(Q : ℝ) := by exact_mod_cast hQ
    nlinarith
  have hw := hDensity Q hQ X T η hXX hT hη hscale hlog F hF
  have he := Vtb.V18h Q hQ X T
    (K*min η (1/T)*Real.log X) (V2j (B+4) X) hXp hT F hF a ha
  change _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log ((Q : ℝ)*T))^2 * _ at he
  apply he.trans
  calc
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log ((Q : ℝ)*T))^2 *
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(2*Real.log X)^2 *
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by
      gcongr
    _ = (D*C₀*X^3)*
        ((K*min η (1/T)*Real.log X)^2*(2*Real.log X)^2*(max 1 (η*T))^2/
          (Real.log X)^(B+4)) := by ring
    _ = (D*C₀*X^3)*(4*K^2*η^2/(Real.log X)^B) := by
      rw [Vjp B K (Real.log X) η T hL hTp]
    _ = (4*D*C₀)*K^2*η^2*X^3/(Real.log X)^B := by ring
end Vda
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1l (V2j)
namespace Vda
theorem Thin_Vjq (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X T η K : ℝ,
      X₀≤X → 2≤T → 0<η → 0≤K →
      (Q : ℝ)^2/η≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 T).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X)) →
      ∀ a : PrimitiveComplexCharacter → ℕ → ℂ,
      (∀ χ∈F, ∀ i∈S χ, ‖a χ i‖≤K*min η (1/T)*Real.log X) →
      (∑ χ∈F, ∫ y in X..4*X,
        ‖∑ i∈S χ, a χ i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
          C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ := Thin_V1gn B
  refine ⟨C,hC,max X₀ (Real.exp 1),?_⟩
  intro Q hQ X T η K hX₀ hT hη hK hscale hlog F hF S hS a ha
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hL : 0≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hXe
    rw [Real.log_exp] at hh
    linarith
  have hTp : 0<T := by linarith
  have hA : 0≤K*min η (1/T)*Real.log X := by positivity
  let b (χ : PrimitiveComplexCharacter) (i : ℕ) : ℂ := if i∈S χ then a χ i else 0
  have hb : ∀ χ∈F, ∀ i∈((V1 χ).V14 T).filter
      (fun i => 1/2≤((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re≤1-V2j (B+4) X),
      ‖b χ i‖≤K*min η (1/T)*Real.log X := by
    intro χ hχ i _
    by_cases hi : i∈S χ
    · simpa only [b, ite_eq_left hi] using ha χ hχ i hi
    · simpa only [b, ite_eq_right hi, norm_zero] using hA
  have hseries (χ : PrimitiveComplexCharacter) (hχ : χ∈F) (y : ℝ) :
      (∑ i∈((V1 χ).V14 T).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        b χ i*(y : ℂ)^((V1 χ).zeros i)) =
      ∑ i∈S χ, a χ i*(y : ℂ)^((V1 χ).zeros i) := by
    calc
      _ = ∑ i∈S χ, b χ i*(y : ℂ)^((V1 χ).zeros i) := by
        exact (sum_subset (hS χ hχ) (by intro i _ hi; simp [b,hi])).symm
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        simp only [b, ite_eq_left hi]
  calc
    _ = ∑ χ∈F, ∫ y in X..4*X,
        ‖∑ i∈((V1 χ).V14 T).filter
          (fun i => 1/2≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-V2j (B+4) X),
          b χ i*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
      apply sum_congr rfl
      intro χ hχ
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [hseries χ hχ y]
    _ ≤ _ := hMean Q hQ X T η K hXX hT hη hK hscale hlog F hF b hb
end Vda
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1e
open Vg2 (Vy2)
open V1l (V2j)
namespace V93
theorem Thin_Vz7 (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h T : ℝ,
      X₀≤X → 2≤T → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ Vy2 B X T χ) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ := Vda.Thin_Vjq B
  refine ⟨16*C, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X h T hX₀ hT hh hhX hscale hlog F hF S hsub
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp : 0<Real.log X := by linarith
  have hTp : 0<T := by linarith
  let η : ℝ := h/X
  have hη : 0<η := div_pos hh hXp
  have htarget : (16*C)*h^2*X/(Real.log X)^B =
      (16*C)*η^2*X^3/(Real.log X)^B := by
    dsimp only [η]
    field_simp
  rw [htarget]
  have hS : ∀ χ∈F, S χ ⊆
      ((V1 χ).V14 T).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X) := by
    intro χ hχ i hi
    have hi := hsub χ hχ hi
    obtain ⟨hiT,hiR,hiB,hiH⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hiT,hiR,hiB⟩
  by_cases hlow : η≤1/T
  · have ha : ∀ χ∈F, ∀ i∈S χ,
        ‖(η : ℂ)‖≤1*min η (1/T)*Real.log X := by
      intro χ hχ i hi
      rw [Complex.norm_real, Real.norm_of_nonneg hη.le, min_eq_left hlow, one_mul]
      exact le_mul_of_one_le_right hη.le hL
    have hm := hMean Q hQ X T η 1 hXX hT hη (by norm_num) hscale hlog F hF
      S hS (fun _ _ => (η : ℂ)) ha
    have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
      ∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
        (η : ℂ)*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
      apply sum_le_sum
      intro χ hχ
      rw [Vp0 _ _ X η hη.le]
      exact V1dq _ _ (by
        intro i hi
        have hr := (mem_filter.mp (hsub χ hχ hi)).2.1
        linarith) X h hXp hh.le hhX
    apply he.trans (hm.trans ?_)
    norm_num only [one_pow, mul_one]
    have hp : 0≤C*η^2*X^3/(Real.log X)^B := by positivity
    calc
      _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
      _ = _ := by ring
  · have hhigh : 1/T≤η := le_of_not_ge hlow
    have ha : ∀ χ∈F, ∀ i∈S χ,
        ‖(1 : ℂ)/((V1 χ).zeros i)‖≤2*min η (1/T)*Real.log X := by
      intro χ hχ i hi
      have hhgt := (mem_filter.mp (hsub χ hχ hi)).2.2.2
      have hc := Vhl _ T hTp hhgt
      rw [min_eq_right hhigh]
      apply hc.trans
      have heq : 2/T=2*(1/T) := by ring
      rw [heq]
      exact le_mul_of_one_le_right (by positivity) hL
    have hm := hMean Q hQ X T η 2 hXX hT hη (by norm_num) hscale hlog F hF
      S hS
      (fun χ i => (1 : ℂ)/((V1 χ).zeros i)) ha
    have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
      4*(∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
        (1/((V1 χ).zeros i))*(y : ℂ)^((V1 χ).zeros i)‖^2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro χ hχ
      exact V1p0 _ _ X h hXp hh.le hhX
    apply he.trans ((mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ)≤4)).trans_eq ?_)
    ring
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e
open V1l (V2j)
namespace V93
theorem Thin_V1ep (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h : ℝ,
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*2)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 2).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ :=
    Vda.Thin_Vjq B
  refine ⟨4*C, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X h hX₀ hh hhX hscale hlog F hF S hS
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  let η : ℝ := h/X
  have hη : 0<η := div_pos hh hXp
  have hη1 : η≤1 := (div_le_one hXp).2 hhX
  have hmin : η≤2*min η (1/2) := by
    by_cases he : η≤1/2
    · rw [min_eq_left he]
      linarith
    · rw [min_eq_right (le_of_not_ge he)]
      linarith
  have ha : ∀ χ∈F, ∀ i∈S χ,
      ‖(η : ℂ)‖≤2*min η (1/2)*Real.log X := by
    intro χ hχ i hi
    rw [Complex.norm_real, Real.norm_of_nonneg hη.le]
    exact hmin.trans (le_mul_of_one_le_right (by positivity) hL)
  have hm := hMean Q hQ X 2 η 2 hXX (by norm_num) hη (by norm_num)
    hscale hlog F hF S hS (fun _ _ => (η : ℂ)) ha
  have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
      Ve y h ((V1 χ).zeros i)‖^2) ≤
    ∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
      (η : ℂ)*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
    apply sum_le_sum
    intro χ hχ
    rw [Vp0 _ _ X η hη.le]
    exact V1dq _ _ (by
      intro i hi
      have hr := (mem_filter.mp (hS χ hχ hi)).2.1
      linarith) X h hXp hh.le hhX
  apply he.trans (hm.trans_eq ?_)
  dsimp only [η]
  field_simp
  norm_num
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e V6b
open Vg2 (Vy2)
open V1l (V2j)
namespace V93
theorem Thin_V16g (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 ((2 : ℝ)^(K+1))).filter
        (fun i => 1/2≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+6) X)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨Cl,hCl,Xl,hlow⟩ := Thin_V1ep (B+2)
  obtain ⟨Cd,hCd,Xd,hdyad⟩ := Thin_Vz7 (B+2)
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Cl+Cd)*(2/Real.log 2)^2,by positivity,
    max (max Xl Xd) (Real.exp 1),?_⟩
  intro Q hQ K X h hX₀ hh hhX hscale hlog F hF S hS
  have hXl : Xl≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX₀)
  have hXd : Xd≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX₀)
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp : 0<Real.log X := by linarith
  have hQR : (1 : ℝ)≤Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ)<Q := by linarith
  let ρ (χ : PrimitiveComplexCharacter) := (V1 χ).zeros
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => (ρ χ i).im) k
  have hlogk (k : ℕ) (hk : k∈range (K+1)) :
      Real.log ((Q : ℝ)*(2 : ℝ)^(k+1))≤2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ hQp.le
    exact pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hk)))
  have hPk (k : ℕ) (χ : PrimitiveComplexCharacter) (hχ : χ∈F)
      (i : ℕ) (hi : i∈P k χ) :
      i∈S χ ∧ |(ρ χ i).im|≤(2 : ℝ)^(k+1) ∧
      (k=0 ∨ (2 : ℝ)^k < |(ρ χ i).im|) := by
    exact mem_filter.mp hi
  have hband (χ : PrimitiveComplexCharacter) (hχ : χ∈F)
      (i : ℕ) (hi : i∈S χ) :
      1/2≤(ρ χ i).re ∧ (ρ χ i).re≤1-V2j ((B+2)+4) X := by
    simpa only [Nat.add_assoc] using (mem_filter.mp (hS χ hχ hi)).2
  have hm (k : ℕ) (hk : k∈range (K+1)) :
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈P k χ,
        Ve y h (ρ χ i)‖^2) ≤ (Cl+Cd)*h^2*X/(Real.log X)^(B+2) := by
    by_cases hk0 : k=0
    · subst k
      have hs : ∀ χ∈F, P 0 χ⊆((V1 χ).V14 2).filter
          (fun i => 1/2≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-V2j ((B+2)+4) X) := by
        intro χ hχ i hi
        obtain ⟨hiS,hiT,hiL⟩ := hPk 0 χ hχ i hi
        apply mem_filter.mpr
        refine ⟨?_,hband χ hχ i hiS⟩
        exact ((V1 χ).V2r 2 i).mpr (by simpa using hiT)
      have hb := hlow Q hQ X h hXl hh hhX hscale (by simpa using hlogk 0 hk) F hF (P 0) hs
      apply hb.trans
      gcongr
      linarith
    · have hs : ∀ χ∈F, P k χ⊆Vy2 (B+2) X ((2 : ℝ)^(k+1)) χ := by
        intro χ hχ i hi
        obtain ⟨hiS,hiT,hiL⟩ := hPk k χ hχ i hi
        apply mem_filter.mpr
        refine ⟨((V1 χ).V2r _ i).mpr hiT,
          (hband χ hχ i hiS).1,(hband χ hχ i hiS).2,?_⟩
        have hl := hiL.resolve_left hk0
        rw [pow_succ]
        linarith
      have hT : (2 : ℝ)≤(2 : ℝ)^(k+1) := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
          (show 1≤k+1 by omega)
      have hb := hdyad Q hQ X h ((2 : ℝ)^(k+1)) hXd hT hh hhX hscale
        (hlogk k hk) F hF (P k) hs
      apply hb.trans
      gcongr
      linarith
  have hid (χ : PrimitiveComplexCharacter) (hχ : χ∈F) (y : ℝ) :
      (∑ i∈S χ, Ve y h (ρ χ i)) =
        ∑ k∈range (K+1), ∑ i∈P k χ, Ve y h (ρ χ i) := by
    apply V9u
    intro i hi
    exact ((V1 χ).V2r _ i).mp
      (mem_filter.mp (hS χ hχ hi)).1
  have hi (χ : PrimitiveComplexCharacter) (k : ℕ) :
      IntervalIntegrable (fun y => ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2)
        volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      ((V6e (P k χ) (ρ χ) X h hXp hh.le hhX).norm.pow 2)
  have hen (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖∑ i∈S χ, Ve y h (ρ χ i)‖^2) ≤
        ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := by
    have hg := V1dr (range (K+1))
      (fun k y => ∑ i∈P k χ, Ve y h (ρ χ i)) X hXp.le
      (fun k _ => hi χ k)
    simpa only [← hid χ hχ,card_range] using hg
  have hcount := Vhn Q K hQ X hlog
  calc
    _ ≤ ∑ χ∈F, ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := sum_le_sum hen
    _ = ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∑ χ∈F, ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := by
      rw [← mul_sum,sum_comm]
    _ ≤ ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), (Cl+Cd)*h^2*X/(Real.log X)^(B+2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hm) (by positivity)
    _ = ((K+1 : ℕ) : ℝ)^2*((Cl+Cd)*h^2*X/(Real.log X)^(B+2)) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ ((2/Real.log 2)*Real.log X)^2*((Cl+Cd)*h^2*X/(Real.log X)^(B+2)) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hcount
    _ = ((Cl+Cd)*(2/Real.log 2)^2)*h^2*X/(Real.log X)^B := by
      rw [pow_add]
      field_simp
      <;> ring
end V93
end
end

section
noncomputable section
namespace GoldbachPrincipalDensityThree
open scoped BigOperators Classical
open OAI.Ostmann Vx Vam
open Vl0 Vio

theorem high_log_gap_three (H σ:ℝ) (hH:4096≤H) (hσ:2/3≤σ) :
    1/Real.log H≤σ-1/2 := by
  have hl12:Real.log 4096=12*Real.log 2 := by
    have h:=Real.log_pow (2:ℝ) 12
    norm_num at h
    exact h
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<4096) hH
  rw [hl12] at hlog
  have h6:6≤Real.log H := by linarith [V1v8]
  have hb : 1/Real.log H≤(1/6:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0<Real.log H)).mpr
    linarith
  linarith

theorem target_exponent_le_three (σ:ℝ) (hσ:1/2≤σ) (hσ1:σ≤1) :
    Vy σ≤3*(1-σ) := by
  unfold Vy
  apply (div_le_iff₀ (by linarith : 0<2-σ)).mpr
  have hp := mul_nonneg (by linarith : 0≤1-σ) (by linarith : 0≤1-3*(σ-1))
  nlinarith [sq_nonneg (1-σ)]

theorem shell_power_three (H T σ:ℝ) (hH:1≤H) (hHT:H≤2*T)
    (hT:2≤T) (hσ:2/3≤σ) (hσ1:σ≤1) :
    H^Vy σ≤2*T^(3*(1-σ)) := by
  have he0:0≤3*(1-σ) := by linarith
  have he1:3*(1-σ)≤1 := by linarith
  calc
    _ ≤ H^(3*(1-σ)) := Real.rpow_le_rpow_of_exponent_le hH
      (target_exponent_le_three σ (by linarith) hσ1)
    _ ≤ (2*T)^(3*(1-σ)) := Real.rpow_le_rpow (by linarith) hHT he0
    _ = (2:ℝ)^(3*(1-σ))*T^(3*(1-σ)) := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2*T^(3*(1-σ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) he1
      simpa using h

theorem constant_to_thirteen_three (T σ:ℝ) (hT:2≤T) (hσ1:σ≤1) :
    1≤(Real.log 2)⁻¹^13*(T^(3*(1-σ))*(Real.log T)^13) := by
  have hl:0<Real.log 2 := Real.log_pos (by norm_num)
  have hL:Real.log 2≤Real.log T := Real.log_le_log (by norm_num) hT
  have hL0:0≤Real.log T := hl.le.trans hL
  have hp : 1≤T^(3*(1-σ)) := Real.one_le_rpow (by linarith) (by linarith)
  have hlog : (Real.log 2)^13≤(Real.log T)^13 := pow_le_pow_left₀ hl.le hL 13
  have hmul : (Real.log 2)^13≤T^(3*(1-σ))*(Real.log T)^13 :=
    hlog.trans (le_mul_of_one_le_left (by positivity) hp)
  have hh := mul_le_mul_of_nonneg_left hmul (show 0≤(Real.log 2)⁻¹^13 by positivity)
  simpa only [←mul_pow,inv_mul_cancel₀ hl.ne',one_pow] using hh

theorem principal_high_sigma_count_three :
    ∃C:ℝ,0<C ∧ ∀T σ:ℝ,2≤T → 2/3≤σ → σ≤1 →
      ∀S:Finset V1o,
      (∀c∈S,σ≤c.val.1.re) → (∀c∈S,|c.val.1.im|≤T) →
      (S.card:ℝ)≤C*T^(3*(1-σ))*(Real.log T)^13 := by
  obtain ⟨C,hC,hb⟩ := V1kk
  let D := (39/Real.log (14/13))*4096*Real.log 4096
  let E := 2*2^10*C
  have hD:0<D := by dsimp [D]; positivity
  have hE:0<E := by dsimp [E]; positivity
  refine ⟨D*(Real.log 2)⁻¹^13+4*E*(Real.log 2)⁻¹^2,by positivity,?_⟩
  intro T σ hT hσ hσ1 S hr ht
  have hlog:0≤Real.log T := Real.log_nonneg (by linarith)
  have htarget:0≤T^(3*(1-σ)) := by positivity
  obtain ⟨J,hJlo,hJhi,hJlog⟩ := V1vr T hT
  let L := S.filter (fun c => |c.val.1.im|≤4096)
  let U : ℕ→Finset V1o := fun j => S.filter (fun c =>
    4096< |c.val.1.im| ∧ (2:ℝ)^j≤|c.val.1.im| ∧ |c.val.1.im|≤(2:ℝ)^(j+1))
  have hcover : S ⊆ L ∪ (Finset.range (J+1)).biUnion U := by
    intro c hc
    by_cases hlow:|c.val.1.im|≤4096
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc,hlow⟩)
    · have hhigh:4096< |c.val.1.im| := lt_of_not_ge hlow
      obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near
        (by linarith : (1:ℝ)≤|c.val.1.im|) (by norm_num : (1:ℝ)<2)
      have hj:j<J+1 := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
        (hlo.trans (ht c hc) |>.trans_lt hJhi)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_range.mpr hj,Finset.mem_filter.mpr ⟨hc,hhigh,hlo,hhi.le⟩⟩)
  have hcard : (S.card:ℝ)≤(L.card:ℝ)+∑j∈Finset.range (J+1),((U j).card:ℝ) := by
    have hn := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
    exact_mod_cast hn
  have hlow : (L.card:ℝ)≤D := Vdt 4096 (by norm_num) L
    (fun c hc => (show (1/2:ℝ)≤σ by linarith).trans (hr c (Finset.mem_filter.mp hc).1))
    (fun c hc => (Finset.mem_filter.mp hc).2)
  have hblock (j:ℕ) (hj:j∈Finset.range (J+1)) :
      ((U j).card:ℝ)≤E*T^(3*(1-σ))*(Real.log T)^10 := by
    have hjle:j≤J := by have := Finset.mem_range.mp hj; omega
    let H := (2:ℝ)^(j+1)
    have hHT:H≤2*T := by
      have hh : (2:ℝ)^j≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hjle
      dsimp [H]
      rw [pow_succ]
      nlinarith
    by_cases hH:4096≤H
    · have hh := hb H σ hH (by linarith) hσ1 (high_log_gap_three H σ hH hσ) (U j)
        (fun c hc => hr c (Finset.mem_filter.mp hc).1)
        (fun c hc => (Finset.mem_filter.mp hc).2.2.2)
        (fun c hc => by
          have hp : H/2=(2:ℝ)^j := by dsimp [H]; rw [pow_succ]; ring
          rw [hp]
          exact (Finset.mem_filter.mp hc).2.2.1)
      have hp := shell_power_three H T σ (by linarith) hHT hT hσ hσ1
      have hl := V208 H T (by positivity) hHT hT
      have hl0:0≤Real.log H := Real.log_nonneg (by linarith)
      calc
        _ ≤ C*H^Vy σ*(Real.log H)^10 := hh
        _ ≤ C*(2*T^(3*(1-σ)))*(2*Real.log T)^10 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le)
            (pow_le_pow_left₀ hl0 hl 10) (by positivity) (by positivity)
        _ = _ := by dsimp [E]; ring
    · have hu:U j=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        have hc' := (Finset.mem_filter.mp hc).2
        have hh : |c.val.1.im|≤H := hc'.2.2
        linarith
      rw [hu,Finset.card_empty,Nat.cast_zero]
      positivity
  have hsum : (∑j∈Finset.range (J+1),((U j).card:ℝ))≤
      4*E*T^(3*(1-σ))*(Real.log T)^11 := by
    calc
      _ ≤ ∑_j∈Finset.range (J+1),E*T^(3*(1-σ))*(Real.log T)^10 :=
        Finset.sum_le_sum hblock
      _ = (J+1:ℝ)*(E*T^(3*(1-σ))*(Real.log T)^10) := by simp
      _ ≤ (4*Real.log T)*(E*T^(3*(1-σ))*(Real.log T)^10) :=
        mul_le_mul_of_nonneg_right hJlog (by positivity)
      _ = _ := by ring
  have hL2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hT
  have hconst := mul_le_mul_of_nonneg_left (constant_to_thirteen_three T σ hT hσ1) hD.le
  have hraise := mul_le_mul_of_nonneg_left (V1r9 (Real.log T) hL2)
    (show 0≤4*E*T^(3*(1-σ)) by positivity)
  have hh := hcard.trans (add_le_add hlow hsum)
  apply hh.trans
  have hf := add_le_add hconst hraise
  convert hf using 1 <;> ring

theorem principal_density_three :
    ∃C:ℝ,0<C ∧ ∀T σ:ℝ,2≤T → 1/2≤σ → σ≤1 →
      ∀S:Finset V1o,
      (∀c∈S,σ≤c.val.1.re) → (∀c∈S,|c.val.1.im|≤T) →
      (S.card:ℝ)≤C*T^(3*(1-σ))*(Real.log T)^13 := by
  obtain ⟨C,hC,hb⟩ := principal_high_sigma_count_three
  let D := (39/Real.log (14/13))*(Real.log 2)⁻¹^12
  have hD:0<D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro T σ hT hσ hσ1 S hr ht
  have hL2:=Real.log_le_log (by norm_num : (0:ℝ)<2) hT
  have hL:0≤Real.log T := Real.log_nonneg (by linarith)
  have hpow:0≤T^(3*(1-σ)) := by positivity
  by_cases hσ3:2/3≤σ
  · exact (hb T σ hT hσ3 hσ1 S hr ht).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C≤C+D) hpow) (by positivity))
  · have hcount := Vdt T hT S
      (fun c hc=>hσ.trans (hr c hc)) ht
    have hpower:T≤T^(3*(1-σ)) := by
      have h:=Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤T)
        (show (1:ℝ)≤3*(1-σ) by linarith)
      simpa using h
    have hlogs:=Vka (Real.log T) hL2
    calc
      _ ≤ (39/Real.log (14/13))*T*Real.log T := hcount
      _ ≤ (39/Real.log (14/13))*T^(3*(1-σ))*((Real.log 2)⁻¹^12*(Real.log T)^13) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpower (by positivity)) hlogs hL (by positivity)
      _ = D*T^(3*(1-σ))*(Real.log T)^13 := by dsimp [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : D≤C+D) hpow) (by positivity)

theorem principal_density_three_literal :
    ∃C:ℝ,0<C ∧ ∀T σ:ℝ,2≤T → 1/2≤σ → σ≤1 →
      (((V3b T).filter (fun c=>σ≤c.val.1.re)).card:ℝ)≤
        C*T^(3*(1-σ))*(Real.log T)^13 := by
  obtain ⟨C,hC,hb⟩ := principal_density_three
  refine ⟨C,hC,?_⟩
  intro T σ hT hσ hσ1
  exact hb T σ hT hσ hσ1 _
    (fun c hc=>(Finset.mem_filter.mp hc).2)
    (fun c hc=>(V5l T c).mp (Finset.mem_filter.mp hc).1)

end GoldbachPrincipalDensityThree
end
end

section
noncomputable section
open Finset Filter
open scoped BigOperators Classical
open Vx Vm0
open Vmm Vmn V1l
namespace Vno
theorem Thin_Vzi :
    ∃C:ℝ,0<C ∧ ∀ X T η δ:ℝ,
      1≤X → 2≤T → 0<η → 0≤δ → δ≤1/2 →
      1/η≤X^(5/9:ℝ) →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,1/2≤c.val.1.re ∧ c.val.1.re≤1-δ) →
      (∑c∈S,X^(2*c.val.1.re-2))≤
        C*(Real.log T)^13*(1+Real.log X)*(max 1 (η*T))^2*X^(-δ/3) := by
  obtain ⟨C,hC,hDensity⟩ := GoldbachPrincipalDensityThree.principal_density_three
  refine ⟨C,hC,?_⟩
  intro X T η δ hX hT hη hδ hδhalf hscale S ht hr
  let B:=max 1 (η*T)
  have hB:1≤B := le_max_left _ _
  have hXp:0<X := by linarith
  have hp:0≤X^(5/9:ℝ) := by positivity
  have hscaleB:T≤X^(5/9:ℝ)*B := by
    have hs:1≤X^(5/9:ℝ)*η := (div_le_iff₀ hη).mp hscale
    calc
      T=1*T := by ring
      _ ≤ (X^(5/9:ℝ)*η)*T := mul_le_mul_of_nonneg_right hs (by linarith)
      _ = X^(5/9:ℝ)*(η*T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hp
  have hL:0≤Real.log T := Real.log_nonneg (by linarith)
  have hd (σ:ℝ) (hσ:1/2≤σ) (hσδ:σ≤1-δ) :
      ((S.filter fun c=>σ≤c.val.1.re).card:ℝ)≤
        (C*B^2)*(X^(5/9:ℝ))^(3*(1-σ))*(Real.log T)^13 := by
    have hf:=V18s (show 0≤T by linarith) hB hp hscaleB
      (show 0≤3*(1-σ) by linarith) (show 3*(1-σ)≤2 by linarith)
    have hh:=hDensity T σ hT hσ (by linarith) (S.filter fun c=>σ≤c.val.1.re)
      (fun c hc=>(mem_filter.mp hc).2)
      (fun c hc=>ht c (mem_filter.mp hc).1)
    calc
      _ ≤ C*T^(3*(1-σ))*(Real.log T)^13 := hh
      _ ≤ C*(B^2*(X^(5/9:ℝ))^(3*(1-σ)))*(Real.log T)^13 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hC.le) (by positivity)
      _ = _ := by ring
  have hb:=Vmm.Thin_weighted_sum S (fun c=>c.val.1.re) hX hp
    (show 0≤C*B^2 by positivity) hL hδ hδhalf le_rfl hr hd
  exact hb.trans_eq (by dsimp [B]; ring)
end Vno
end
end

section
noncomputable section
open Finset Filter
open scoped BigOperators Classical
open Vx Vm0
open Vmm Vmn V1l
namespace Vno
theorem Thin_V1ki (A:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀X T η:ℝ,X₀≤X → 2≤T → 0<η →
      1/η≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,1/2≤c.val.1.re ∧ c.val.1.re≤1-V2j A X) →
      (∑c∈S,X^(2*c.val.1.re-2))≤C*(max 1 (η*T))^2/(Real.log X)^A := by
  obtain ⟨C,hC,hband⟩:=Thin_Vzi
  obtain ⟨X₀,hX₀⟩:=eventually_atTop.1 (Vgn A)
  refine ⟨16384*C,by positivity,X₀,?_⟩
  intro X T η hXX hT hη hscale hlogs S ht hr
  obtain ⟨hX,hlogX,hδ,hδhalf⟩:=hX₀ X hXX
  have hL:0≤Real.log T := Real.log_nonneg (by linarith)
  have hb:=hband X T η (V2j A X) hX.le hT hη hδ hδhalf hscale S ht hr
  apply hb.trans
  calc
    _ = (C*(max 1 (η*T))^2)*((Real.log T)^13*(1+Real.log X)*X^(-V2j A X/3)) := by ring
    _ ≤ (C*(max 1 (η*T))^2)*(16384/(Real.log X)^A) :=
      mul_le_mul_of_nonneg_left (V1r8 A hX hlogX hL hlogs) (by positivity)
    _ = _ := by ring
end Vno
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vno
open V1l Vid Vda
namespace Vqu
theorem Thin_Vvi (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀X T η K:ℝ,X₀≤X → 2≤T → 0<η → 0≤K →
      1/η≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,1/2≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+4) X) →
      ∀a:V1o→ℂ,(∀c∈S,‖a c‖≤K*min η (1/T)*Real.log X) →
      (∫y in X..4*X,‖∑c∈S,a c*(y:ℂ)^c.val.1‖^2)≤
        C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C₀,hC₀,X₀,hDensity⟩:=Thin_V1ki (B+4)
  let D:ℝ:=33800/Real.log (14/13)
  have hD:0<D := by dsimp [D]; positivity
  refine ⟨4*D*C₀,by positivity,max X₀ (Real.exp 1),?_⟩
  intro X T η K hX₀ hT hη hK hscale hlog S ht hr a ha
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL1:1≤Real.log X := by
    have hh:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hh
  have hL:0<Real.log X := by linarith
  have hTp:0<T := by linarith
  have hTL:0≤Real.log T := Real.log_nonneg (by linarith)
  have hw:=hDensity X T η hXX hT hη hscale hlog S ht hr
  have he:=V1c8 X T (K*min η (1/T)*Real.log X) hXp hT
    S ht (fun c hc=>(hr c hc).1) a ha
  change _≤D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log T)^2*_ at he
  apply he.trans
  calc
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log T)^2*
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(2*Real.log X)^2*
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by gcongr
    _ = (D*C₀*X^3)*
        ((K*min η (1/T)*Real.log X)^2*(2*Real.log X)^2*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by ring
    _ = (D*C₀*X^3)*(4*K^2*η^2/(Real.log X)^B) := by
      rw [Vjp B K (Real.log X) η T hL hTp]
    _ = _ := by ring
end Vqu
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vqu V1e
open V1l (V2j)
namespace Vzb
theorem Thin_V1f2 (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀X h T:ℝ,X₀≤X → 2≤T → 0<h → h≤X →
      1/(h/X)≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,1/2≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+4) X) →
      (T=2 ∨ ∀c∈S,T/2≤|c.val.1.im|) →
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩:=Thin_Vvi B
  refine ⟨16*C,by positivity,max X₀ (Real.exp 1),?_⟩
  intro X h T hX₀ hT hh hhX hscale hlog S ht hr hheight
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL:1≤Real.log X := by
    have hl:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hTp:0<T := by linarith
  let η:=h/X
  have hη:0<η := div_pos hh hXp
  have hη1:η≤1 := (div_le_one hXp).mpr hhX
  have htarget:(16*C)*h^2*X/(Real.log X)^B=(16*C)*η^2*X^3/(Real.log X)^B := by
    dsimp [η]; field_simp
  rw [htarget]
  have hlowenergy :
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        (∫y in X..4*X,‖∑c∈S,(η:ℂ)*(y:ℂ)^c.val.1‖^2) := by
    rw [Vp0 _ _ X η hη.le]
    exact V1dq S (fun c=>c.val.1)
      (fun c hc=>by linarith [(hr c hc).1]) X h hXp hh.le hhX
  by_cases hsmall:η≤1/T
  · have ha:∀c∈S,‖(η:ℂ)‖≤1*min η (1/T)*Real.log X := by
      intro c hc
      rw [Complex.norm_real,Real.norm_of_nonneg hη.le,min_eq_left hsmall,one_mul]
      exact le_mul_of_one_le_right hη.le hL
    have hm:=hMean X T η 1 hXX hT hη (by norm_num) hscale hlog S ht hr (fun _=>(η:ℂ)) ha
    apply hlowenergy.trans (hm.trans ?_)
    norm_num only [one_pow,mul_one]
    have hp:0≤C*η^2*X^3/(Real.log X)^B := by positivity
    calc
      _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
      _ = _ := by ring
  · have hhigh:1/T≤η := le_of_not_ge hsmall
    rcases hheight with hbottom | hheight
    · have ha:∀c∈S,‖(η:ℂ)‖≤2*min η (1/T)*Real.log X := by
        intro c hc
        rw [Complex.norm_real,Real.norm_of_nonneg hη.le,min_eq_right hhigh,hbottom]
        norm_num
        exact hη1.trans hL
      have hm:=hMean X T η 2 hXX hT hη (by norm_num) hscale hlog S ht hr (fun _=>(η:ℂ)) ha
      apply hlowenergy.trans (hm.trans ?_)
      have hp:0≤C*η^2*X^3/(Real.log X)^B := by positivity
      calc
        _ = 4*(C*η^2*X^3/(Real.log X)^B) := by ring
        _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
        _ = _ := by ring
    · have ha:∀c∈S,‖(1:ℂ)/c.val.1‖≤2*min η (1/T)*Real.log X := by
        intro c hc
        have hinv:=Vhl c.val.1 T hTp (hheight c hc)
        rw [min_eq_right hhigh]
        apply hinv.trans
        have heq:2/T=2*(1/T) := by ring
        rw [heq]
        exact le_mul_of_one_le_right (by positivity) hL
      have hm:=hMean X T η 2 hXX hT hη (by norm_num) hscale hlog S ht hr
        (fun c=>(1:ℂ)/c.val.1) ha
      apply (V1p0 S (fun c=>c.val.1) X h hXp hh.le hhX).trans
      exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4)).trans_eq (by ring)
end Vzb
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vzb V1e
open V6b V1l
namespace Vpd
theorem Thin_Vx2 (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀(K:ℕ)(X h:ℝ),X₀≤X → 0<h → h≤X →
      1/(h/X)≤X^(5/9:ℝ) →
      Real.log ((2:ℝ)^(K+1))≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤(2:ℝ)^(K+1)) →
      (∀c∈S,1/2≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+6) X) →
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hpacket⟩:=Thin_V1f2 (B+2)
  have hl2:0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C*(2/Real.log 2)^2,by positivity,max X₀ (Real.exp 1),?_⟩
  intro K X h hX₀ hh hhX hscale hlog S ht hr
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL:1≤Real.log X := by
    have hl:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp:0<Real.log X := by linarith
  let P:ℕ→Finset V1o := fun k=>Vpt S (fun c=>c.val.1.im) k
  have hlogk (k:ℕ) (hk:k∈range (K+1)) :
      Real.log ((2:ℝ)^(k+1))≤2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hk)))
  have hPk (k:ℕ) (c:V1o) (hc:c∈P k) :
      c∈S ∧ |c.val.1.im|≤(2:ℝ)^(k+1) ∧
        (k=0 ∨ (2:ℝ)^k< |c.val.1.im|) := mem_filter.mp hc
  have hm (k:ℕ) (hk:k∈range (K+1)) :
      (∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^(B+2) := by
    have hT:(2:ℝ)≤(2:ℝ)^(k+1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1≤k+1 by omega)
    apply hpacket X h ((2:ℝ)^(k+1)) hXX hT hh hhX hscale (hlogk k hk) (P k)
      (fun c hc=>(hPk k c hc).2.1)
      (fun c hc=>by simpa only [Nat.add_assoc] using hr c (hPk k c hc).1)
    by_cases hk0:k=0
    · left; simp [hk0]
    · right
      intro c hc
      have hl: (2:ℝ)^k< |c.val.1.im| := (hPk k c hc).2.2.resolve_left hk0
      rw [pow_succ]
      linarith
  have hid (y:ℝ) : (∑c∈S,Ve y h c.val.1)=
      ∑k∈range (K+1),∑c∈P k,Ve y h c.val.1 :=
    V9u S (fun c=>c.val.1.im)
      (fun c=>Ve y h c.val.1) K ht
  have hi (k:ℕ) : IntervalIntegrable
      (fun y=>‖∑c∈P k,Ve y h c.val.1‖^2) volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      ((V6e (P k) (fun c=>c.val.1) X h hXp hh.le hhX).norm.pow 2)
  have hen :
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
      ((K+1:ℕ):ℝ)*(∑k∈range (K+1),∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2) := by
    have hg:=V1dr (range (K+1))
      (fun k y=>∑c∈P k,Ve y h c.val.1) X hXp.le (fun k _=>hi k)
    simpa only [←hid,card_range] using hg
  have hcount := Vhn 1 K le_rfl X (by simpa using hlog)
  calc
    _ ≤ ((K+1:ℕ):ℝ)*(∑k∈range (K+1),∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2) := hen
    _ ≤ ((K+1:ℕ):ℝ)*(∑_k∈range (K+1),C*h^2*X/(Real.log X)^(B+2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hm) (by positivity)
    _ = ((K+1:ℕ):ℝ)^2*(C*h^2*X/(Real.log X)^(B+2)) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ ((2/Real.log 2)*Real.log X)^2*(C*h^2*X/(Real.log X)^(B+2)) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hcount
    _ = _ := by
      rw [pow_add]
      field_simp
      <;> ring
end Vpd
end
end

end

-- FullWeights
section

noncomputable section
open Filter Finset
open scoped Classical Topology BigOperators
namespace ThinWeights
open OAI.Ostmann Vx V5s V1l

theorem split_card_bound {ι : Type*} (s : Finset ι) (β : ι → ℝ) (a X : ℝ) (hx : 1≤X) :
    (∑ i∈s.filter (fun i => 0≤β i ∧ β i≤a), X^(2*β i-2)) ≤
      (∑ i∈s.filter (fun i => 1/2≤β i ∧ β i≤a), X^(2*β i-2)) + (s.card:ℝ)/X := by
  let S := s.filter (fun i => 0≤β i ∧ β i≤a)
  let P := fun i => 1/2≤β i
  have eq : S.filter P = s.filter (fun i => 1/2≤β i ∧ β i≤a) := by
    ext i; simp only [S,P,mem_filter]; constructor <;> intro h
    · exact ⟨h.1.1,h.2,h.1.2.2⟩
    · exact ⟨⟨h.1,by linarith [h.2.1],h.2.2⟩,h.2.1⟩
  have low : (∑ i∈S.filter (fun i=>¬P i), X^(2*β i-2)) ≤ (s.card:ℝ)/X := calc
    _ ≤ ∑ _i∈S.filter (fun i=>¬P i), X^(-1:ℝ) := by
      apply sum_le_sum; intro i hi
      have hh := lt_of_not_ge ((mem_filter.mp hi).2 : ¬ P i)
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hh])
    _ = ((S.filter (fun i=>¬P i)).card:ℝ)/X := by simp [div_eq_mul_inv,Real.rpow_neg_one]
    _ ≤ _ := by
      have hsub : S.filter (fun i=>¬P i) ⊆ s := (filter_subset ..).trans (filter_subset ..)
      exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by linarith)
  change (∑ i∈S, _) ≤ _
  rw [← sum_filter_add_sum_filter_not S P, eq]
  linarith only [low]

theorem eventually_left_budget (A:ℕ) : ∃ X₀:ℝ, ∀ X:ℝ,X₀≤X → 1≤X ∧ 1≤Real.log X ∧ (Real.log X)^(A+1)≤X^(4/9:ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop ((A+1:ℕ):ℝ) (by norm_num : (0:ℝ)<4/9)).bound (by norm_num:(0:ℝ)<1)
  apply eventually_atTop.mp
  filter_upwards [hh,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with X hh hx hL
  refine ⟨hx,hL,?_⟩
  simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg (by linarith : 0≤Real.log X) _), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0≤X) _), one_mul] using hh

theorem left_budget (A:ℕ) {X Q T η N C : ℝ}
    (hx : 1≤X) (hlog : 1≤Real.log X) (hsave : (Real.log X)^(A+1)≤X^(4/9:ℝ))
    (hQ:1≤Q) (hT:2≤T) (hη:0<η) (hC:0≤C)
    (hscale:Q^2/η≤X^(5/9:ℝ)) (hlogs:Real.log (Q*T) ≤ 2*Real.log X)
    (hN:N≤C*(Q^2*T)*Real.log (Q*T)) : N/X ≤ (2*C)*(max 1 (η*T))^2/(Real.log X)^A := by
  let B := max 1 (η*T)
  have hB : 1≤B := le_max_left _ _
  have hX : 0<X := by linarith
  have hL : 0 < Real.log X := by linarith
  have hQT : 0≤Real.log (Q*T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ (by linarith))
  have hb : Q^2*T ≤ X^(5/9:ℝ)*B := calc
    _ ≤ (X^(5/9:ℝ)*η)*T := mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hscale) (by linarith)
    _ = X^(5/9:ℝ)*(η*T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hp : X^(5/9:ℝ) * X^(4/9:ℝ) = X := by rw [←Real.rpow_add hX]; norm_num
  have hnum : N*(Real.log X)^A ≤ 2*C*B^2*X := calc
    _ ≤ (C*(X^(5/9:ℝ)*B)*(2*Real.log X))*(Real.log X)^A :=
      mul_le_mul_of_nonneg_right (hN.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb hC) hlogs hQT (by positivity))) (by positivity)
    _ = 2*C*B*(X^(5/9:ℝ)*(Real.log X)^(A+1)) := by rw [pow_succ]; ring
    _ ≤ 2*C*B*(X^(5/9:ℝ)*X^(4/9:ℝ)) := by gcongr
    _ = 2*C*B*X := by rw [hp]
    _ ≤ _ := by gcongr; nlinarith [sq_nonneg (B-1)]
  apply (div_le_div_iff₀ hX (pow_pos hL A)).mpr hnum

theorem full_char_weight (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ (Q : ℕ), 1 ≤ Q → ∀ X T η : ℝ,
      X₀ ≤ X → 2 ≤ T → 0 < η → (Q:ℝ)^2/η ≤ X^(5/9:ℝ) → Real.log ((Q:ℝ)*T) ≤ 2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F, χ.modulus≤Q) →
      (∑ χ∈F, ∑ i∈((V1 χ).V14 T).filter (fun i => 0≤((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re≤1-V2j A X), X^(2*((V1 χ).zeros i).re-2)) ≤ C*(max 1 (η*T))^2/(Real.log X)^A := by
  obtain ⟨C,hC,Xr,hr⟩ := Thin_V1gm A
  obtain ⟨Xl,hl⟩ := eventually_left_budget A
  let D : ℝ := 32/Real.log (14/13)
  have hD : 0 < D := by dsimp [D]; exact div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨C+8*D,by positivity,max Xr Xl,?_⟩
  intro Q hQ X T η hX hT hη hscale hlogs F hF
  have hx := (le_max_left _ _).trans hX
  obtain ⟨hx1,hL,hsave⟩ := hl X ((le_max_right _ _).trans hX)
  have right := hr Q hQ X T η hx hT hη hscale hlogs F hF
  let N : ℝ := ∑ χ∈F, (((V1 χ).V14 T).card:ℝ)
  have hQt : 1 ≤ (Q:ℝ) := by exact_mod_cast hQ
  have ht1 : 1≤(Q:ℝ)*T := one_le_mul_of_one_le_of_one_le hQt (by linarith)
  have hQt2 : 2 ≤ (Q:ℝ)*T := hT.trans (le_mul_of_one_le_left (by linarith) hQt)
  have hlogT : Real.log ((Q:ℝ)*(T+2)) ≤ 2*Real.log ((Q:ℝ)*T) := calc
    _ ≤ Real.log (2*((Q:ℝ)*T)) := Real.log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hT (show 0≤(Q:ℝ) by positivity)])
    _ = Real.log 2 + Real.log ((Q:ℝ)*T) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hQt2]
  have ordinary := Vn5 Q hQ T (by linarith) 0 F hF
  have hs : N ≤ D*(Q:ℝ)^2*(T+1)*Real.log ((Q:ℝ)*(T+2)) := by
    simpa only [N,ComplexZeroEnumeration.Vgd] using ordinary
  have count : N ≤ (4*D)*((Q:ℝ)^2*T)*Real.log ((Q:ℝ)*T) := calc
    _ ≤ D*(Q:ℝ)^2*(T+1)*Real.log ((Q:ℝ)*(T+2)) := hs
    _ ≤ D*(Q:ℝ)^2*(2*T)*(2*Real.log ((Q:ℝ)*T)) := mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hlogT
      (Real.log_nonneg (by nlinarith [hQt2])) (by positivity)
    _ = _ := by ring
  have rem := left_budget A hx1 hL hsave hQt hT hη (by positivity : 0≤4*D) hscale hlogs count
  have sub := sum_le_sum (s:=F) (fun χ _ => split_card_bound ((V1 χ).V14 T)
    (fun i => ((V1 χ).zeros i).re) (1 - V2j A X) X hx1)
  rw [sum_add_distrib,← Finset.sum_div] at sub
  apply sub.trans
  exact (add_le_add right rem).trans_eq (by ring)

theorem full_principal_weight (T X η δ:ℝ) (hT:2≤T) (hx:1≤X) (hη:0<η)
    (hδ:0≤δ) (hδmax:δ≤1/2) (hscale:1/η≤X^(5/9:ℝ))
    (S : Finset V1o) (ht:∀ c∈S,|c.val.1.im|≤T)
    (hr:∀ c∈S, 0≤c.val.1.re ∧ c.val.1.re≤1-δ) (A:ℕ) (hL:1≤Real.log X)
    (hsave:(Real.log X)^(A+1)≤X^(4/9:ℝ)) (hlogs:Real.log T≤2*Real.log X) :
    (∑c∈S.filter (fun c=>c.val.1.re<1/2),X^(2*c.val.1.re-2)) ≤
      (156/Real.log (14/13))*(max 1 (η*T))^2/(Real.log X)^A := by
  let D := 78/Real.log (14/13:ℝ)
  have hD : 0 < D := by dsimp [D]; exact div_pos (by norm_num) (Real.log_pos (by norm_num))
  have count : (S.card:ℝ) ≤ D*((1:ℝ)^2*T)*Real.log (1*T) := by simpa [D] using Vhe T hT S ht
  have rem := left_budget A (Q:=1) hx hL hsave le_rfl hT hη hD.le (by simpa using hscale) (by simpa using hlogs) count
  calc
    _ ≤ ∑ _c∈S.filter (fun c=>c.val.1.re<1/2),X^(-1:ℝ) := by
      apply sum_le_sum; intro i hi; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith [(mem_filter.mp hi).2])
    _ = ((S.filter (fun c=>c.val.1.re<1/2)).card:ℝ)/X := by simp [div_eq_mul_inv,Real.rpow_neg_one]
    _ ≤ (S.card:ℝ)/X := div_le_div_of_nonneg_right (by exact_mod_cast card_filter_le ..) (by linarith)
    _ ≤ _ := rem.trans_eq (by dsimp [D]; ring)

theorem full_principal_log_weight (A:ℕ) :
    ∃ C:ℝ,0<C ∧ ∃ X₀:ℝ, ∀ X T η:ℝ,X₀≤X → 2≤T → 0<η →
      1/η≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀ S:Finset V1o,(∀ c∈S,|c.val.1.im|≤T) →
      (∀ c∈S,0≤c.val.1.re ∧ c.val.1.re≤1-V2j A X) →
      (∑c∈S,X^(2*c.val.1.re-2)) ≤ C*(max 1 (η*T))^2/(Real.log X)^A := by
  obtain ⟨C,hC,X₁,hR⟩ := Vno.Thin_V1ki A
  obtain ⟨X₂,hL⟩ := eventually_left_budget A
  obtain ⟨X₃,hcut⟩ := eventually_atTop.mp (Vgn A)
  have hpos : 0 < Real.log (14/13:ℝ) := Real.log_pos (by norm_num)
  refine ⟨C + 156/Real.log (14/13), by positivity,max X₁ (max X₂ X₃),?_⟩
  intro X T η hX hT hη hs hl S ht hr
  have h₁ := (le_max_left _ _).trans hX
  have h₂ := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have h₃ := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  obtain ⟨hx,hLX,hsv⟩ := hL X h₂
  obtain ⟨_,_,hδ,hδmax⟩ := hcut X h₃
  let P (c : V1o) := 1/2≤c.val.1.re
  have hb := hR X T η h₁ hT hη hs hl (S.filter P)
    (fun i hi => ht i (mem_filter.mp hi).1) (fun i hi=>⟨(mem_filter.mp hi).2,(hr i (mem_filter.mp hi).1).2⟩)
  have ha := full_principal_weight T X η (V2j A X) hT hx hη hδ hδmax hs S ht hr A hLX hsv hl
  have heq : S.filter (fun c=>¬P c) = S.filter (fun c => c.val.1.re<1/2) := by
    ext c; simp [P,not_le]
  rw [←sum_filter_add_sum_filter_not S P,heq]
  exact (add_le_add hb ha).trans_eq (by ring)

end ThinWeights
end

end

-- AllRows
section

noncomputable section
open Finset MeasureTheory
open scoped Classical BigOperators ComplexConjugate Interval
namespace ThinRows
open OAI.Ostmann Vjr Vx V5s

theorem char_right (Q : ℕ) (hQ : 1≤Q) (T : ℝ) (hT : 2≤T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus≤Q)
    (S : Finset ℕ) (hS : S⊆(V1 χ).V14 T)
    (hr : ∀ i∈S, 1/2≤((V1 χ).zeros i).re) (u : ℝ) (hu : |u|≤T) :
    (∑ j∈S, 1/(1+|u-((V1 χ).zeros j).im|)) ≤
        (160/Real.log (14/13))*(Real.log ((Q : ℝ)*T))^2 := by
  let Z := V1 χ
  have hL : 0≤Real.log ((Q : ℝ)*T) := by
    apply Real.log_nonneg
    have hq : (1 : ℝ)≤Q := by exact_mod_cast hQ
    nlinarith
  have hd : 0<Real.log (14/13 : ℝ) := Real.log_pos (by norm_num)
  have hb := V15d S (fun j => (Z.zeros j).im) u T ((8/Real.log (14/13))*Real.log ((Q : ℝ)*T))
    (by linarith) hu (by positivity) (fun j hj => (Z.V2r T j).mp (hS hj))
    (V1u1 Q hQ T hT χ hχ S hS hr)
  exact hb.trans <| (mul_le_mul_of_nonneg_left (V18v Q hQ T hT) (by positivity)).trans_eq (by ring)

theorem char_row (Q : ℕ) (hQ : 1≤Q) (T : ℝ) (hT : 2≤T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus≤Q)
    (S : Finset ℕ) (hS : S⊆(V1 χ).V14 T) (u : ℝ) (hu : |u|≤T) :
    (∑ j∈S, 1/(1+|u-((V1 χ).zeros j).im|)) ≤
        (320/Real.log (14/13))*(Real.log ((Q : ℝ)*T))^2 := by
  let P (j:ℕ) := 1/2 ≤ ((V1 χ).zeros j).re
  let L := S.filter (fun j => ¬ P j)
  let R := L.image (V7z χ)
  have hr := char_right Q hQ T hT χ hχ (S.filter P) ((filter_subset ..).trans hS)
    (fun _ hs => (mem_filter.mp hs).2) u hu
  have hb : R ⊆ (V1 χ).V14 T := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    apply ((V1 χ).V2r T _).mpr
    simpa [Vrj] using ((V1 χ).V2r T j).mp (hS (mem_filter.mp hj).1)
  have hR : ∀ j∈R, 1/2 ≤ ((V1 χ).zeros j).re := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have h := lt_of_not_ge ((mem_filter.mp hi).2 : ¬P i)
    rw [Vrj]; simp; linarith
  have hl := char_right Q hQ T hT χ hχ R hb hR u hu
  rw [show R=L.image (V7z χ) from rfl, sum_image (fun i _ j _ hij => (V7z χ).injective hij)] at hl
  simp only [Vrj, Complex.sub_im, Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] at hl
  rw [← sum_filter_add_sum_filter_not S P]
  change (∑ j∈S.filter P, _) + (∑ j∈L, _) ≤ _
  exact (add_le_add hr hl).trans_eq (by ring)

theorem principal_right (T:ℝ) (hT:2≤T) (S:Finset V1o) (hS:S⊆V3b T)
    (hr:∀ c∈S,1/2≤c.val.1.re) (u:ℝ) (hu:|u|≤T) :
    (∑ d∈S,1/(1+|u-d.val.1.im|))≤(260/Real.log (14/13))*(Real.log T)^2 := by
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hd : 0 < Real.log (14/13:ℝ) := Real.log_pos (by norm_num)
  have hb := V15d S (fun d=>d.val.1.im) u T ((13/Real.log (14/13))*Real.log T)
    (by linarith) hu (by positivity) (fun d hd => (V5l T d).mp (hS hd)) (V1sq T hT S hS hr)
  have hlog : 1+Real.log ((⌈2*T+2⌉₊+1:ℕ):ℝ)≤5*Real.log T := by
    simpa using V18v 1 (by norm_num) T hT
  exact hb.trans <| (mul_le_mul_of_nonneg_left hlog (by positivity)).trans_eq (by ring)

theorem principal_row (T:ℝ) (hT:2≤T) (S:Finset V1o) (hS:S⊆V3b T) (u:ℝ) (hu:|u|≤T) :
    (∑ d∈S,1/(1+|u-d.val.1.im|))≤(520/Real.log (14/13))*(Real.log T)^2 := by
  let P (j:V1o) := 1/2 ≤ j.val.1.re
  let L := S.filter (fun j => ¬P j)
  let R := L.image V1sj
  have hp := principal_right T hT (S.filter P) ((filter_subset ..).trans hS)
    (fun _ hs=> (mem_filter.mp hs).2) u hu
  have hb : R⊆V3b T := by
    intro j hj
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
    apply (V5l T _).mpr
    simpa [V16m] using (V5l T i).mp (hS (mem_filter.mp hi).1)
  have hr : ∀ j∈R, 1/2≤j.val.1.re := by
    intro j hj
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
    have h:=lt_of_not_ge ((mem_filter.mp hi).2 : ¬P i)
    rw [V16m]; simp; linarith
  have hl:=principal_right T hT R hb hr (-u) (by simpa using hu)
  rw [show R=L.image V1sj from rfl, sum_image (fun i _ j _ hij => V1qm.injective hij)] at hl
  simp only [V16m,Complex.sub_im,Complex.one_im,zero_sub,neg_sub_neg,abs_sub_comm _ u] at hl
  rw [← sum_filter_add_sum_filter_not S P]
  change (∑ j∈S.filter P, _) + (∑ j∈L, _) ≤ _
  exact (add_le_add hp hl).trans_eq (by ring)
end ThinRows
end

end

-- FullPackets
section

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
namespace Vtb
theorem Full_V1mc (Q : ℕ) (hQ : 1≤Q)
    (X T A : ℝ) (hX : 0<X) (hT : 2≤T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus≤Q)
    (S : Finset ℕ) (hS : S⊆(V1 χ).V14 T)
    (hr : ∀ i∈S, 0≤((V1 χ).zeros i).re)
    (a : ℕ → ℂ) (ha : ∀ i∈S, ‖a i‖≤A) :
    (∫ y in X..4*X, ‖∑ i∈S, a i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
      (41600/Real.log (14/13))*A^2*X^3*(Real.log ((Q : ℝ)*T))^2 *
        ∑ i∈S, X^(2*((V1 χ).zeros i).re-2) := by
  have hd : 0<Real.log (14/13 : ℝ) := Real.log_pos (by norm_num)
  have hb := Vid.V1r0 S a
    (V1 χ).zeros X
    ((320/Real.log (14/13))*(Real.log ((Q : ℝ)*T))^2) A hX (by positivity)
    (fun i hi => by linarith [hr i hi])
    (fun i _ => ((V1 χ).in_strip i).2.le) ha
    (fun i hi => ThinRows.char_row Q hQ T hT χ hχ S hS _ (((V1 χ).V2r T i).mp (hS hi)))
  apply hb.trans_eq
  ring
end Vtb
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
namespace Vtb
theorem Full_V18i (Q : ℕ) (hQ : 1≤Q)
    (X T A δ : ℝ) (hX : 0<X) (hT : 2≤T)
    (χ : PrimitiveComplexCharacter) (hχ : χ.modulus≤Q)
    (a : ℕ → ℂ)
    (ha : ∀ i∈((V1 χ).V14 T).filter
      (fun i => 0≤((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re≤1-δ), ‖a i‖≤A) :
    (∫ y in X..4*X, ‖∑ i∈((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-δ),
        a i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
      (41600/Real.log (14/13))*A^2*X^3*(Real.log ((Q : ℝ)*T))^2 *
        ∑ i∈((V1 χ).V14 T).filter
          (fun i => 0≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-δ),
          X^(2*((V1 χ).zeros i).re-2) := by
  exact Full_V1mc Q hQ X T A hX hT χ hχ _ (filter_subset _ _)
    (fun i hi => (mem_filter.mp hi).2.1) a ha
end Vtb
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
namespace Vtb
theorem Full_V18h (Q : ℕ) (hQ : 1≤Q)
    (X T A δ : ℝ) (hX : 0<X) (hT : 2≤T)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ∈F, χ.modulus≤Q)
    (a : PrimitiveComplexCharacter → ℕ → ℂ)
    (ha : ∀ χ∈F, ∀ i∈((V1 χ).V14 T).filter
      (fun i => 0≤((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re≤1-δ), ‖a χ i‖≤A) :
    (∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-δ),
        a χ i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
      (41600/Real.log (14/13))*A^2*X^3*(Real.log ((Q : ℝ)*T))^2 *
        ∑ χ∈F, ∑ i∈((V1 χ).V14 T).filter
          (fun i => 0≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-δ),
          X^(2*((V1 χ).zeros i).re-2) := by
  rw [mul_sum]
  apply sum_le_sum
  intro χ hχ
  exact Full_V18i Q hQ X T A δ hX hT χ (hF χ hχ) (a χ) (ha χ hχ)
end Vtb
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1l (V2j)
namespace Vda
theorem Full_V1gn (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X T η K : ℝ,
      X₀≤X → 2≤T → 0<η → 0≤K →
      (Q : ℝ)^2/η≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ a : PrimitiveComplexCharacter → ℕ → ℂ,
      (∀ χ∈F, ∀ i∈((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        ‖a χ i‖≤K*min η (1/T)*Real.log X) →
      (∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        a χ i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
          C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C₀,hC₀,X₀,hDensity⟩ :=
    ThinWeights.full_char_weight (B+4)
  let D : ℝ := 41600/Real.log (14/13)
  have hD : 0<D := by
    dsimp [D]
    exact div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ)<14/13))
  refine ⟨4*D*C₀, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X T η K hX₀ hT hη hK hscale hlog F hF a ha
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL1 : 1≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hh
  have hL : 0<Real.log X := by linarith
  have hTp : 0<T := by linarith
  have hQT : 0≤Real.log ((Q : ℝ)*T) := by
    apply Real.log_nonneg
    have hQR : (1 : ℝ)≤(Q : ℝ) := by exact_mod_cast hQ
    nlinarith
  have hw := hDensity Q hQ X T η hXX hT hη hscale hlog F hF
  have he := Vtb.Full_V18h Q hQ X T
    (K*min η (1/T)*Real.log X) (V2j (B+4) X) hXp hT F hF a ha
  change _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log ((Q : ℝ)*T))^2 * _ at he
  apply he.trans
  calc
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log ((Q : ℝ)*T))^2 *
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(2*Real.log X)^2 *
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by
      gcongr
    _ = (D*C₀*X^3)*
        ((K*min η (1/T)*Real.log X)^2*(2*Real.log X)^2*(max 1 (η*T))^2/
          (Real.log X)^(B+4)) := by ring
    _ = (D*C₀*X^3)*(4*K^2*η^2/(Real.log X)^B) := by
      rw [Vjp B K (Real.log X) η T hL hTp]
    _ = (4*D*C₀)*K^2*η^2*X^3/(Real.log X)^B := by ring
end Vda
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1l (V2j)
namespace Vda
theorem Full_Vjq (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X T η K : ℝ,
      X₀≤X → 2≤T → 0<η → 0≤K →
      (Q : ℝ)^2/η≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X)) →
      ∀ a : PrimitiveComplexCharacter → ℕ → ℂ,
      (∀ χ∈F, ∀ i∈S χ, ‖a χ i‖≤K*min η (1/T)*Real.log X) →
      (∑ χ∈F, ∫ y in X..4*X,
        ‖∑ i∈S χ, a χ i*(y : ℂ)^((V1 χ).zeros i)‖^2) ≤
          C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ := Full_V1gn B
  refine ⟨C,hC,max X₀ (Real.exp 1),?_⟩
  intro Q hQ X T η K hX₀ hT hη hK hscale hlog F hF S hS a ha
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hL : 0≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hXe
    rw [Real.log_exp] at hh
    linarith
  have hTp : 0<T := by linarith
  have hA : 0≤K*min η (1/T)*Real.log X := by positivity
  let b (χ : PrimitiveComplexCharacter) (i : ℕ) : ℂ := if i∈S χ then a χ i else 0
  have hb : ∀ χ∈F, ∀ i∈((V1 χ).V14 T).filter
      (fun i => 0≤((V1 χ).zeros i).re ∧
        ((V1 χ).zeros i).re≤1-V2j (B+4) X),
      ‖b χ i‖≤K*min η (1/T)*Real.log X := by
    intro χ hχ i _
    by_cases hi : i∈S χ
    · simpa only [b, ite_eq_left hi] using ha χ hχ i hi
    · simpa only [b, ite_eq_right hi, norm_zero] using hA
  have hseries (χ : PrimitiveComplexCharacter) (hχ : χ∈F) (y : ℝ) :
      (∑ i∈((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X),
        b χ i*(y : ℂ)^((V1 χ).zeros i)) =
      ∑ i∈S χ, a χ i*(y : ℂ)^((V1 χ).zeros i) := by
    calc
      _ = ∑ i∈S χ, b χ i*(y : ℂ)^((V1 χ).zeros i) := by
        exact (sum_subset (hS χ hχ) (by intro i _ hi; simp [b,hi])).symm
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        simp only [b, ite_eq_left hi]
  calc
    _ = ∑ χ∈F, ∫ y in X..4*X,
        ‖∑ i∈((V1 χ).V14 T).filter
          (fun i => 0≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-V2j (B+4) X),
          b χ i*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
      apply sum_congr rfl
      intro χ hχ
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [hseries χ hχ y]
    _ ≤ _ := hMean Q hQ X T η K hXX hT hη hK hscale hlog F hF b hb
end Vda
end
end

section
noncomputable section
open Finset MeasureTheory Complex
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1l (V2j)
namespace Vg2
noncomputable def Full_Vy2 (B : ℕ) (X T : ℝ)
    (χ : PrimitiveComplexCharacter) : Finset ℕ :=
  ((V1 χ).V14 T).filter
    (fun i => 0≤((V1 χ).zeros i).re ∧
      ((V1 χ).zeros i).re≤1-V2j (B+4) X ∧
        T/2≤|((V1 χ).zeros i).im|)
end Vg2
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann
open V1e
open Vg2 (Vy2)
open V1l (V2j)
namespace V93
theorem Full_Vz7 (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h T : ℝ,
      X₀≤X → 2≤T → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ Vg2.Full_Vy2 B X T χ) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ := Vda.Full_Vjq B
  refine ⟨16*C, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X h T hX₀ hT hh hhX hscale hlog F hF S hsub
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp : 0<Real.log X := by linarith
  have hTp : 0<T := by linarith
  let η : ℝ := h/X
  have hη : 0<η := div_pos hh hXp
  have htarget : (16*C)*h^2*X/(Real.log X)^B =
      (16*C)*η^2*X^3/(Real.log X)^B := by
    dsimp only [η]
    field_simp
  rw [htarget]
  have hS : ∀ χ∈F, S χ ⊆
      ((V1 χ).V14 T).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X) := by
    intro χ hχ i hi
    have hi := hsub χ hχ hi
    obtain ⟨hiT,hiR,hiB,hiH⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hiT,hiR,hiB⟩
  by_cases hlow : η≤1/T
  · have ha : ∀ χ∈F, ∀ i∈S χ,
        ‖(η : ℂ)‖≤1*min η (1/T)*Real.log X := by
      intro χ hχ i hi
      rw [Complex.norm_real, Real.norm_of_nonneg hη.le, min_eq_left hlow, one_mul]
      exact le_mul_of_one_le_right hη.le hL
    have hm := hMean Q hQ X T η 1 hXX hT hη (by norm_num) hscale hlog F hF
      S hS (fun _ _ => (η : ℂ)) ha
    have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
      ∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
        (η : ℂ)*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
      apply sum_le_sum
      intro χ hχ
      rw [Vp0 _ _ X η hη.le]
      exact V1dq _ _ (by
        intro i hi
        exact ((V1 χ).in_strip i).1) X h hXp hh.le hhX
    apply he.trans (hm.trans ?_)
    norm_num only [one_pow, mul_one]
    have hp : 0≤C*η^2*X^3/(Real.log X)^B := by positivity
    calc
      _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
      _ = _ := by ring
  · have hhigh : 1/T≤η := le_of_not_ge hlow
    have ha : ∀ χ∈F, ∀ i∈S χ,
        ‖(1 : ℂ)/((V1 χ).zeros i)‖≤2*min η (1/T)*Real.log X := by
      intro χ hχ i hi
      have hhgt := (mem_filter.mp (hsub χ hχ hi)).2.2.2
      have hc := Vhl _ T hTp hhgt
      rw [min_eq_right hhigh]
      apply hc.trans
      have heq : 2/T=2*(1/T) := by ring
      rw [heq]
      exact le_mul_of_one_le_right (by positivity) hL
    have hm := hMean Q hQ X T η 2 hXX hT hη (by norm_num) hscale hlog F hF
      S hS
      (fun χ i => (1 : ℂ)/((V1 χ).zeros i)) ha
    have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
      4*(∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
        (1/((V1 χ).zeros i))*(y : ℂ)^((V1 χ).zeros i)‖^2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro χ hχ
      exact V1p0 _ _ X h hXp hh.le hhX
    apply he.trans ((mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ)≤4)).trans_eq ?_)
    ring
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e
open V1l (V2j)
namespace V93
theorem Full_V1ep (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h : ℝ,
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*2)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 2).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+4) X)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩ :=
    Vda.Full_Vjq B
  refine ⟨4*C, by positivity, max X₀ (Real.exp 1), ?_⟩
  intro Q hQ X h hX₀ hh hhX hscale hlog F hF S hS
  have hXX : X₀≤X := (le_max_left _ _).trans hX₀
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  let η : ℝ := h/X
  have hη : 0<η := div_pos hh hXp
  have hη1 : η≤1 := (div_le_one hXp).2 hhX
  have hmin : η≤2*min η (1/2) := by
    by_cases he : η≤1/2
    · rw [min_eq_left he]
      linarith
    · rw [min_eq_right (le_of_not_ge he)]
      linarith
  have ha : ∀ χ∈F, ∀ i∈S χ,
      ‖(η : ℂ)‖≤2*min η (1/2)*Real.log X := by
    intro χ hχ i hi
    rw [Complex.norm_real, Real.norm_of_nonneg hη.le]
    exact hmin.trans (le_mul_of_one_le_right (by positivity) hL)
  have hm := hMean Q hQ X 2 η 2 hXX (by norm_num) hη (by norm_num)
    hscale hlog F hF S hS (fun _ _ => (η : ℂ)) ha
  have he : (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
      Ve y h ((V1 χ).zeros i)‖^2) ≤
    ∑ χ∈F, ∫ y in X..4*X, ‖∑ i∈S χ,
      (η : ℂ)*(y : ℂ)^((V1 χ).zeros i)‖^2 := by
    apply sum_le_sum
    intro χ hχ
    rw [Vp0 _ _ X η hη.le]
    exact V1dq _ _ (by
      intro i hi
      exact ((V1 χ).in_strip i).1) X h hXp hh.le hhX
  apply he.trans (hm.trans_eq ?_)
  dsimp only [η]
  field_simp
  norm_num
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e V6b
open Vg2 (Vy2)
open V1l (V2j)
namespace V93
theorem Full_V16g (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆((V1 χ).V14 ((2 : ℝ)^(K+1))).filter
        (fun i => 0≤((V1 χ).zeros i).re ∧
          ((V1 χ).zeros i).re≤1-V2j (B+6) X)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨Cl,hCl,Xl,hlow⟩ := Full_V1ep (B+2)
  obtain ⟨Cd,hCd,Xd,hdyad⟩ := Full_Vz7 (B+2)
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Cl+Cd)*(2/Real.log 2)^2,by positivity,
    max (max Xl Xd) (Real.exp 1),?_⟩
  intro Q hQ K X h hX₀ hh hhX hscale hlog F hF S hS
  have hXl : Xl≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX₀)
  have hXd : Xd≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX₀)
  have hXe : Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp : 0<X := (Real.exp_pos 1).trans_le hXe
  have hL : 1≤Real.log X := by
    have hl := Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp : 0<Real.log X := by linarith
  have hQR : (1 : ℝ)≤Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ)<Q := by linarith
  let ρ (χ : PrimitiveComplexCharacter) := (V1 χ).zeros
  let P (k : ℕ) (χ : PrimitiveComplexCharacter) :=
    Vpt (S χ) (fun i => (ρ χ i).im) k
  have hlogk (k : ℕ) (hk : k∈range (K+1)) :
      Real.log ((Q : ℝ)*(2 : ℝ)^(k+1))≤2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ hQp.le
    exact pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hk)))
  have hPk (k : ℕ) (χ : PrimitiveComplexCharacter) (hχ : χ∈F)
      (i : ℕ) (hi : i∈P k χ) :
      i∈S χ ∧ |(ρ χ i).im|≤(2 : ℝ)^(k+1) ∧
      (k=0 ∨ (2 : ℝ)^k < |(ρ χ i).im|) := by
    exact mem_filter.mp hi
  have hband (χ : PrimitiveComplexCharacter) (hχ : χ∈F)
      (i : ℕ) (hi : i∈S χ) :
      0≤(ρ χ i).re ∧ (ρ χ i).re≤1-V2j ((B+2)+4) X := by
    simpa only [Nat.add_assoc] using (mem_filter.mp (hS χ hχ hi)).2
  have hm (k : ℕ) (hk : k∈range (K+1)) :
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈P k χ,
        Ve y h (ρ χ i)‖^2) ≤ (Cl+Cd)*h^2*X/(Real.log X)^(B+2) := by
    by_cases hk0 : k=0
    · subst k
      have hs : ∀ χ∈F, P 0 χ⊆((V1 χ).V14 2).filter
          (fun i => 0≤((V1 χ).zeros i).re ∧
            ((V1 χ).zeros i).re≤1-V2j ((B+2)+4) X) := by
        intro χ hχ i hi
        obtain ⟨hiS,hiT,hiL⟩ := hPk 0 χ hχ i hi
        apply mem_filter.mpr
        refine ⟨?_,hband χ hχ i hiS⟩
        exact ((V1 χ).V2r 2 i).mpr (by simpa using hiT)
      have hb := hlow Q hQ X h hXl hh hhX hscale (by simpa using hlogk 0 hk) F hF (P 0) hs
      apply hb.trans
      gcongr
      linarith
    · have hs : ∀ χ∈F, P k χ⊆Vg2.Full_Vy2 (B+2) X ((2 : ℝ)^(k+1)) χ := by
        intro χ hχ i hi
        obtain ⟨hiS,hiT,hiL⟩ := hPk k χ hχ i hi
        apply mem_filter.mpr
        refine ⟨((V1 χ).V2r _ i).mpr hiT,
          (hband χ hχ i hiS).1,(hband χ hχ i hiS).2,?_⟩
        have hl := hiL.resolve_left hk0
        rw [pow_succ]
        linarith
      have hT : (2 : ℝ)≤(2 : ℝ)^(k+1) := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
          (show 1≤k+1 by omega)
      have hb := hdyad Q hQ X h ((2 : ℝ)^(k+1)) hXd hT hh hhX hscale
        (hlogk k hk) F hF (P k) hs
      apply hb.trans
      gcongr
      linarith
  have hid (χ : PrimitiveComplexCharacter) (hχ : χ∈F) (y : ℝ) :
      (∑ i∈S χ, Ve y h (ρ χ i)) =
        ∑ k∈range (K+1), ∑ i∈P k χ, Ve y h (ρ χ i) := by
    apply V9u
    intro i hi
    exact ((V1 χ).V2r _ i).mp
      (mem_filter.mp (hS χ hχ hi)).1
  have hi (χ : PrimitiveComplexCharacter) (k : ℕ) :
      IntervalIntegrable (fun y => ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2)
        volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      ((V6e (P k χ) (ρ χ) X h hXp hh.le hhX).norm.pow 2)
  have hen (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖∑ i∈S χ, Ve y h (ρ χ i)‖^2) ≤
        ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := by
    have hg := V1dr (range (K+1))
      (fun k y => ∑ i∈P k χ, Ve y h (ρ χ i)) X hXp.le
      (fun k _ => hi χ k)
    simpa only [← hid χ hχ,card_range] using hg
  have hcount := Vhn Q K hQ X hlog
  calc
    _ ≤ ∑ χ∈F, ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := sum_le_sum hen
    _ = ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), ∑ χ∈F, ∫ y in X..2*X,
          ‖∑ i∈P k χ, Ve y h (ρ χ i)‖^2) := by
      rw [← mul_sum,sum_comm]
    _ ≤ ((K+1 : ℕ) : ℝ)*(∑ k∈range (K+1), (Cl+Cd)*h^2*X/(Real.log X)^(B+2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hm) (by positivity)
    _ = ((K+1 : ℕ) : ℝ)^2*((Cl+Cd)*h^2*X/(Real.log X)^(B+2)) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ ((2/Real.log 2)*Real.log X)^2*((Cl+Cd)*h^2*X/(Real.log X)^(B+2)) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hcount
    _ = ((Cl+Cd)*(2/Real.log 2)^2)*h^2*X/(Real.log X)^B := by
      rw [pow_add]
      field_simp
      <;> ring
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e V6b V9h
open V1l (V2j)
namespace V93
theorem Full_Vp9 (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ⊆(V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∀ χ∈F, ∀ i∈S χ,
        ((V1 χ).zeros i).re≤1-V2j (B+6) X) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hc⟩ := Full_V16g B
  refine ⟨C,hC,X₀,?_⟩
  intro Q hQ K X h hX hh hhX hs hl F hF S hS hcut
  exact hc Q hQ K X h hX hh hhX hs hl F hF S (fun χ hχ i hi =>
    Finset.mem_filter.mpr ⟨hS χ hχ hi,((V1 χ).in_strip i).1.le,hcut χ hχ i hi⟩)
end V93
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e V93
namespace Vbg
theorem Full_Vz6 (B : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ),1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X → (Q : ℝ)≤2*(Real.log X)^24 →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F,S χ⊆(V1 χ).V14 ((2 : ℝ)^(K+1))) →
      (∑ χ∈F,∫ y in X..2*X,‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,Xm,hm⟩ := V93.Full_Vp9 B
  obtain ⟨Xz,hz⟩ := Vro (B+6)
  refine ⟨C,hC,max (max Xm Xz) 2,?_⟩
  intro Q hQ K X h hX hh hhX hQX hscale hlog F hF S hS
  have hXm : Xm≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXz : Xz≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hXp : 0<X := by linarith
  have hQr : 1≤(Q : ℝ) := by exact_mod_cast hQ
  have hQp : 0<(Q : ℝ) := by linarith
  have hheight : (2 : ℝ)^(K+1)≤X^2 := by
    have hprod : (Q : ℝ)*(2 : ℝ)^(K+1)≤X^2 := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).1
      simpa only [Real.log_pow,Nat.cast_ofNat] using hlog
    have hm := mul_le_mul_of_nonneg_right hQr
      (by positivity : 0≤(2 : ℝ)^(K+1))
    nlinarith
  apply hm Q hQ K X h hXm hh hhX hscale hlog F hF S hS
  intro χ hχ i hi
  have hχQ : (χ.modulus : ℝ)≤Q := by exact_mod_cast hF χ hχ
  have hγ := ((V1 χ).V2r ((2 : ℝ)^(K+1)) i).mp
    (hS χ hχ hi)
  exact hz X hXz χ (hχQ.trans hQX) i (hγ.trans hheight)
end Vbg
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open OAI.Ostmann V1e V93
namespace Vbg
theorem Full_Vpb (B : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ),1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X → (Q : ℝ)≤2*(Real.log X)^24 →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      (∑ χ∈F,∫ y in X..2*X,
        ‖∑ i∈(V1 χ).V14 ((2 : ℝ)^(K+1)),
          Ve y h ((V1 χ).zeros i)‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hm⟩ := Full_Vz6 B
  refine ⟨C,hC,X₀,?_⟩
  intro Q hQ K X h hX hh hhX hQX hscale hlog F hF
  exact hm Q hQ K X h hX hh hhX hQX hscale hlog F hF _
    (fun χ _ => Finset.Subset.refl _)
end Vbg
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vno
open V1l Vid Vda
namespace Vqu
theorem Full_V1c8 (X T A:ℝ) (hX:0<X) (hT:2≤T)
    (S:Finset V1o) (ht:∀c∈S,|c.val.1.im|≤T)
    (hr:∀c∈S,0≤c.val.1.re) (a:V1o→ℂ) (ha:∀c∈S,‖a c‖≤A) :
    (∫y in X..4*X,‖∑c∈S,a c*(y:ℂ)^c.val.1‖^2)≤
      (67600/Real.log (14/13))*A^2*X^3*(Real.log T)^2*
        ∑c∈S,X^(2*c.val.1.re-2) := by
  have hsub:S⊆V3b T := fun c hc=>(V5l T c).mpr (ht c hc)
  have hb:=V1r0 S a (fun c=>c.val.1) X
    ((520/Real.log (14/13))*(Real.log T)^2) A hX (by positivity)
    (fun c hc=>(by linarith [hr c hc])) (fun c hc=>c.property.1.2.1.le) ha
    (fun c hc=>ThinRows.principal_row T hT S hsub _ (ht c hc))
  exact hb.trans_eq (by ring)
end Vqu
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vno
open V1l Vid Vda
namespace Vqu
theorem Full_Vvi (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀X T η K:ℝ,X₀≤X → 2≤T → 0<η → 0≤K →
      1/η≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,0≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+4) X) →
      ∀a:V1o→ℂ,(∀c∈S,‖a c‖≤K*min η (1/T)*Real.log X) →
      (∫y in X..4*X,‖∑c∈S,a c*(y:ℂ)^c.val.1‖^2)≤
        C*K^2*η^2*X^3/(Real.log X)^B := by
  obtain ⟨C₀,hC₀,X₀,hDensity⟩:=ThinWeights.full_principal_log_weight (B+4)
  let D:ℝ:=67600/Real.log (14/13)
  have hD:0<D := by dsimp [D]; positivity
  refine ⟨4*D*C₀,by positivity,max X₀ (Real.exp 1),?_⟩
  intro X T η K hX₀ hT hη hK hscale hlog S ht hr a ha
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL1:1≤Real.log X := by
    have hh:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hh
  have hL:0<Real.log X := by linarith
  have hTp:0<T := by linarith
  have hTL:0≤Real.log T := Real.log_nonneg (by linarith)
  have hw:=hDensity X T η hXX hT hη hscale hlog S ht hr
  have he:=Full_V1c8 X T (K*min η (1/T)*Real.log X) hXp hT
    S ht (fun c hc=>(hr c hc).1) a ha
  change _≤D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log T)^2*_ at he
  apply he.trans
  calc
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(Real.log T)^2*
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ D*(K*min η (1/T)*Real.log X)^2*X^3*(2*Real.log X)^2*
        (C₀*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by gcongr
    _ = (D*C₀*X^3)*
        ((K*min η (1/T)*Real.log X)^2*(2*Real.log X)^2*(max 1 (η*T))^2/(Real.log X)^(B+4)) := by ring
    _ = (D*C₀*X^3)*(4*K^2*η^2/(Real.log X)^B) := by
      rw [Vjp B K (Real.log X) η T hL hTp]
    _ = _ := by ring
end Vqu
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vqu V1e
open V1l (V2j)
namespace Vzb
theorem Full_V1f2 (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀X h T:ℝ,X₀≤X → 2≤T → 0<h → h≤X →
      1/(h/X)≤X^(5/9:ℝ) → Real.log T≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤T) →
      (∀c∈S,0≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+4) X) →
      (T=2 ∨ ∀c∈S,T/2≤|c.val.1.im|) →
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hMean⟩:=Vqu.Full_Vvi B
  refine ⟨16*C,by positivity,max X₀ (Real.exp 1),?_⟩
  intro X h T hX₀ hT hh hhX hscale hlog S ht hr hheight
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL:1≤Real.log X := by
    have hl:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hTp:0<T := by linarith
  let η:=h/X
  have hη:0<η := div_pos hh hXp
  have hη1:η≤1 := (div_le_one hXp).mpr hhX
  have htarget:(16*C)*h^2*X/(Real.log X)^B=(16*C)*η^2*X^3/(Real.log X)^B := by
    dsimp [η]; field_simp
  rw [htarget]
  have hlowenergy :
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        (∫y in X..4*X,‖∑c∈S,(η:ℂ)*(y:ℂ)^c.val.1‖^2) := by
    rw [Vp0 _ _ X η hη.le]
    exact V1dq S (fun c=>c.val.1)
      (fun c _=>c.property.1.1) X h hXp hh.le hhX
  by_cases hsmall:η≤1/T
  · have ha:∀c∈S,‖(η:ℂ)‖≤1*min η (1/T)*Real.log X := by
      intro c hc
      rw [Complex.norm_real,Real.norm_of_nonneg hη.le,min_eq_left hsmall,one_mul]
      exact le_mul_of_one_le_right hη.le hL
    have hm:=hMean X T η 1 hXX hT hη (by norm_num) hscale hlog S ht hr (fun _=>(η:ℂ)) ha
    apply hlowenergy.trans (hm.trans ?_)
    norm_num only [one_pow,mul_one]
    have hp:0≤C*η^2*X^3/(Real.log X)^B := by positivity
    calc
      _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
      _ = _ := by ring
  · have hhigh:1/T≤η := le_of_not_ge hsmall
    rcases hheight with hbottom | hheight
    · have ha:∀c∈S,‖(η:ℂ)‖≤2*min η (1/T)*Real.log X := by
        intro c hc
        rw [Complex.norm_real,Real.norm_of_nonneg hη.le,min_eq_right hhigh,hbottom]
        norm_num
        exact hη1.trans hL
      have hm:=hMean X T η 2 hXX hT hη (by norm_num) hscale hlog S ht hr (fun _=>(η:ℂ)) ha
      apply hlowenergy.trans (hm.trans ?_)
      have hp:0≤C*η^2*X^3/(Real.log X)^B := by positivity
      calc
        _ = 4*(C*η^2*X^3/(Real.log X)^B) := by ring
        _ ≤ 16*(C*η^2*X^3/(Real.log X)^B) := by linarith only [hp]
        _ = _ := by ring
    · have ha:∀c∈S,‖(1:ℂ)/c.val.1‖≤2*min η (1/T)*Real.log X := by
        intro c hc
        have hinv:=Vhl c.val.1 T hTp (hheight c hc)
        rw [min_eq_right hhigh]
        apply hinv.trans
        have heq:2/T=2*(1/T) := by ring
        rw [heq]
        exact le_mul_of_one_le_right (by positivity) hL
      have hm:=hMean X T η 2 hXX hT hη (by norm_num) hscale hlog S ht hr
        (fun c=>(1:ℂ)/c.val.1) ha
      apply (V1p0 S (fun c=>c.val.1) X h hXp hh.le hhX).trans
      exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4)).trans_eq (by ring)
end Vzb
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vzb V1e
open V6b V1l
namespace Vpd
theorem Full_Vx2 (B:ℕ) :
    ∃C:ℝ,0<C ∧ ∃X₀:ℝ,
      ∀(K:ℕ)(X h:ℝ),X₀≤X → 0<h → h≤X →
      1/(h/X)≤X^(5/9:ℝ) →
      Real.log ((2:ℝ)^(K+1))≤2*Real.log X →
      ∀S:Finset V1o,
      (∀c∈S,|c.val.1.im|≤(2:ℝ)^(K+1)) →
      (∀c∈S,0≤c.val.1.re ∧ c.val.1.re≤1-V2j (B+6) X) →
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hpacket⟩:=Vzb.Full_V1f2 (B+2)
  have hl2:0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C*(2/Real.log 2)^2,by positivity,max X₀ (Real.exp 1),?_⟩
  intro K X h hX₀ hh hhX hscale hlog S ht hr
  have hXX:X₀≤X := (le_max_left _ _).trans hX₀
  have hXe:Real.exp 1≤X := (le_max_right _ _).trans hX₀
  have hXp:0<X := (Real.exp_pos 1).trans_le hXe
  have hL:1≤Real.log X := by
    have hl:=Real.log_le_log (Real.exp_pos 1) hXe
    simpa only [Real.log_exp] using hl
  have hLp:0<Real.log X := by linarith
  let P:ℕ→Finset V1o := fun k=>Vpt S (fun c=>c.val.1.im) k
  have hlogk (k:ℕ) (hk:k∈range (K+1)) :
      Real.log ((2:ℝ)^(k+1))≤2*Real.log X := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    exact pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hk)))
  have hPk (k:ℕ) (c:V1o) (hc:c∈P k) :
      c∈S ∧ |c.val.1.im|≤(2:ℝ)^(k+1) ∧
        (k=0 ∨ (2:ℝ)^k< |c.val.1.im|) := mem_filter.mp hc
  have hm (k:ℕ) (hk:k∈range (K+1)) :
      (∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^(B+2) := by
    have hT:(2:ℝ)≤(2:ℝ)^(k+1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1≤k+1 by omega)
    apply hpacket X h ((2:ℝ)^(k+1)) hXX hT hh hhX hscale (hlogk k hk) (P k)
      (fun c hc=>(hPk k c hc).2.1)
      (fun c hc=>by simpa only [Nat.add_assoc] using hr c (hPk k c hc).1)
    by_cases hk0:k=0
    · left; simp [hk0]
    · right
      intro c hc
      have hl: (2:ℝ)^k< |c.val.1.im| := (hPk k c hc).2.2.resolve_left hk0
      rw [pow_succ]
      linarith
  have hid (y:ℝ) : (∑c∈S,Ve y h c.val.1)=
      ∑k∈range (K+1),∑c∈P k,Ve y h c.val.1 :=
    V9u S (fun c=>c.val.1.im)
      (fun c=>Ve y h c.val.1) K ht
  have hi (k:ℕ) : IntervalIntegrable
      (fun y=>‖∑c∈P k,Ve y h c.val.1‖^2) volume X (2*X) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      ((V6e (P k) (fun c=>c.val.1) X h hXp hh.le hhX).norm.pow 2)
  have hen :
      (∫y in X..2*X,‖∑c∈S,Ve y h c.val.1‖^2)≤
      ((K+1:ℕ):ℝ)*(∑k∈range (K+1),∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2) := by
    have hg:=V1dr (range (K+1))
      (fun k y=>∑c∈P k,Ve y h c.val.1) X hXp.le (fun k _=>hi k)
    simpa only [←hid,card_range] using hg
  have hcount := Vhn 1 K le_rfl X (by simpa using hlog)
  calc
    _ ≤ ((K+1:ℕ):ℝ)*(∑k∈range (K+1),∫y in X..2*X,‖∑c∈P k,Ve y h c.val.1‖^2) := hen
    _ ≤ ((K+1:ℕ):ℝ)*(∑_k∈range (K+1),C*h^2*X/(Real.log X)^(B+2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hm) (by positivity)
    _ = ((K+1:ℕ):ℝ)^2*(C*h^2*X/(Real.log X)^(B+2)) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ ((2/Real.log 2)*Real.log X)^2*(C*h^2*X/(Real.log X)^(B+2)) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hcount
    _ = _ := by
      rw [pow_add]
      field_simp
      <;> ring
end Vpd
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vpf
open V1l V1e Vt7
namespace Vqx
theorem Full_V16f (B : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (K : ℕ) (X h : ℝ),X₀≤X → 0<h → h≤X →
      1/(h/X)≤X^(5/9 : ℝ) → Real.log ((2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ S : Finset V1o,
      (∀ c∈S,|c.val.1.im|≤(2 : ℝ)^(K+1)) →
      (∫ y in X..2*X,‖∑ c∈S,Ve y h c.val.1‖^2)≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,Xm,hm⟩ := Vpd.Full_Vx2 B
  obtain ⟨Xz,hz⟩ := Vwg (B+6)
  refine ⟨C,hC,max (max Xm Xz) 2,?_⟩
  intro K X h hX hh hhX hscale hlog S hS
  have hXm : Xm≤X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXz : Xz≤X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hXp : 0<X := by linarith
  have hheight : (2 : ℝ)^(K+1)≤X^2 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).1
    simpa only [Real.log_pow,Nat.cast_ofNat] using hlog
  exact hm K X h hXm hh hhX hscale hlog S hS
    (fun c hc => ⟨c.property.1.1.le,hz X hXz c ((hS c hc).trans hheight)⟩)
end Vqx
end
end

section
noncomputable section
open Finset MeasureTheory
open scoped BigOperators Interval Classical
open Vx Vpf
open V1l V1e Vt7
namespace Vqx
theorem Full_Vt4 (B : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (K : ℕ) (X h : ℝ),X₀≤X → 0<h → h≤X →
      1/(h/X)≤X^(5/9 : ℝ) → Real.log ((2 : ℝ)^(K+1))≤2*Real.log X →
      (∫ y in X..2*X,‖∑ c∈V3b ((2 : ℝ)^(K+1)),
        Ve y h c.val.1‖^2)≤C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₀,hm⟩ := Full_V16f B
  refine ⟨C,hC,X₀,?_⟩
  intro K X h hX hh hhX hscale hlog
  exact hm K X h hX hh hhX hscale hlog _
    (fun c hc => (V5l _ c).mp hc)
end Vqx
end
end

end

-- ThinWindowAP
section

namespace ThinBoundary
open Filter Finset
open scoped Topology BigOperators Classical

theorem prime_window_AP (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ X≥N,
      let Y := Nat.sqrt X
      let Q := (Nat.log 2 (2*Y+2))^8
      (∑ n ∈ (Icc X (2*X)).filter Even,
        ∑ q ∈ Icc 1 Q, (q.totient:ℝ) *
          ∑ b ∈ (range q).filter (fun j => j.Coprime q),
            |primeClassMass q b n Y - (Y:ℝ)/(q.totient:ℝ)|) ≤ ε*(X:ℝ)*(Y:ℝ) := by
  let A := 50
  obtain ⟨C,hC,T,hap⟩ := progression_L1 A
    (characters_from_density (2*A) (Vbg.Full_Vpb (2*A)) (Vqx.Full_Vt4 (2*A)))
  let D : ℝ := ((2:ℝ)^A+1)*C
  have hD : 0<D := by dsimp [D];positivity
  apply eventually_atTop.1
  have hg := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (D/ε)
  filter_upwards [shift_shape T, hg] with X hs hlog
  let Y := Nat.sqrt X
  let Q := windowCut X
  let Z := (X+1)/2
  let L := Real.log (X:ℝ)
  let Lz := Real.log (Z:ℝ)
  obtain ⟨ht,hZ4,hZX,hXZ,hwest,hY,hYsmall,hQz,hLz,hscale⟩ := hs
  have hzpos : 0<(Z:ℝ) := by exact_mod_cast (show 0<Z by omega)
  have hxpos : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hzx : (Z:ℝ) ≤ X := by exact_mod_cast hZX
  have hhalf : (X:ℝ)/2 ≤ Z := by
    have : (X:ℝ)≤2*(Z:ℝ) := by exact_mod_cast hXZ
    linarith
  change (Q:ℝ) ≤ Lz^9 at hQz
  change 1≤Lz at hLz
  have hlogmon : Lz≤L := Real.log_le_log hzpos hzx
  have hL : 1≤L := hLz.trans hlogmon
  have hL0 : 0<L := by linarith
  have hLz0 : 0<Lz := by linarith
  have hcut : (Q:ℝ) ≤ L^9 := hQz.trans (pow_le_pow_left₀ hLz0.le hlogmon 9)
  have hx4 : (4:ℝ)≤X := by exact_mod_cast (show 4≤X by omega)
  have hLratio : L≤2*Lz := by
    have h : (X:ℝ) ≤ (Z:ℝ)^2 := by nlinarith [show (4:ℝ)≤Z by exact_mod_cast hZ4]
    simpa only [L,Lz,Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hxpos h
  have hzbudget : (Z:ℝ)/Lz^A ≤ (2:ℝ)^A*(X:ℝ)/L^A := by
    have hpow := pow_le_pow_left₀ hL0.le hLratio A
    rw [mul_pow] at hpow
    apply (div_le_div_iff₀ (pow_pos hLz0 _) (pow_pos hL0 _)).mpr
    calc _ ≤ (X:ℝ)*((2:ℝ)^A*Lz^A) := mul_le_mul hzx hpow (by positivity) hxpos.le
         _ = _ := by ring
  let E := (Icc X (2*X)).filter Even
  let err := fun q n : ℕ => (q.totient:ℝ) *
        ∑ b ∈ (range q).filter (fun b => b.Coprime q),
          |primeClassMass q b n Y - (Y:ℝ)/(q.totient:ℝ)|
  let M : ℝ := D*(Y:ℝ)*(X:ℝ)/L^A
  have hM : 0≤M := by dsimp [M];positivity
  have hrow (q : ℕ) (hq : q ∈ Icc 1 Q) :
      ∑ n ∈ E, err q n ≤ (Q:ℝ)^2 * M := by
    have ⟨hq1,hqQ⟩ := mem_Icc.mp hq
    letI : NeZero q := ⟨by omega⟩
    have hqbound : (q:ℝ)≤Q := by exact_mod_cast hqQ
    have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg q) hqbound 2
    have hqscale : (q:ℝ)^2*(X:ℝ)^(4/9:ℝ) ≤ Y :=
      (mul_le_mul_of_nonneg_right hq2 (by positivity)).trans hscale
    have hscaleZ : (q:ℝ)^2*(Z:ℝ)^(4/9:ℝ) ≤ Y :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hzpos.le hzx (by norm_num)) (sq_nonneg _)).trans hqscale
    have hqz23 : (q:ℝ) ≤ Lz^23 := hqbound.trans (hQz.trans (pow_le_pow_right₀ hLz (by decide)))
    have hq23 : (q:ℝ) ≤ L^23 := hqz23.trans (pow_le_pow_left₀ hLz0.le hlogmon 23)
    have hhalfy : (Y:ℝ) ≤ (Z:ℝ)/2 := by
      have : 2*(Y:ℝ)≤Z := by exact_mod_cast hYsmall
      linarith
    have hwz := hap q Z Y ht (by omega) hY hhalfy hscaleZ hqz23
    have hwx := hap q X Y (by omega) (by omega) hY (by linarith) hqscale hq23
    let F := fun r => V3z.V6v q (Ioc r (r+Y))
    have hFn (r : ℕ) : 0≤F r := V3z.Vtd q _
    have hshift := translated_dyadic hY hwest hXZ F hFn
    have hbound : (∑ n ∈ E, F (n-2*Y)) ≤ M := by
      refine hshift.trans ((add_le_add hwz hwx).trans ?_)
      have h := mul_le_mul_of_nonneg_left hzbudget (show 0≤C*(Y:ℝ) by positivity)
      change C*(Y:ℝ)*(Z:ℝ)/Lz^A + C*(Y:ℝ)*(X:ℝ)/L^A ≤ D*(Y:ℝ)*(X:ℝ)/L^A
      unfold D
      convert add_le_add_left h (C*(Y:ℝ)*(X:ℝ)/L^A) using 1 <;> ring
    calc _ ≤ ∑ n ∈ E, (q:ℝ)^2*F (n-2*Y) := sum_le_sum fun n hn => by
            apply allClassError
            have h := (mem_Icc.mp (mem_filter.mp hn).1).1
            omega
         _ = (q:ℝ)^2*∑ n ∈ E,F (n-2*Y) := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul hq2 hbound (sum_nonneg fun r _ => hFn _) (sq_nonneg _)
  have htot : (∑ n ∈ E, ∑ q ∈ Icc 1 Q, err q n) ≤ (Q:ℝ)^3 * M := by
    rw [sum_comm]
    calc _ ≤ ∑ _q ∈ Icc 1 Q, (Q:ℝ)^2*M := sum_le_sum hrow
         _ = _ := by simp [Nat.card_Icc]; ring
  change (∑ n ∈ E, ∑ q ∈ Icc 1 Q, err q n) ≤ ε*(X:ℝ)*(Y:ℝ)
  refine htot.trans ?_
  have hqcu : (Q:ℝ)^3 ≤ L^27 := by
    calc _ ≤ (L^9)^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcut 3
         _ = _ := by ring
  have hDe : D ≤ ε*L := by
    change D/ε ≤ L at hlog
    linarith [(div_le_iff₀ hε).mp hlog]
  have he : (Q:ℝ)^3 * D ≤ ε*L^A := by
    calc _ ≤ L^27*(ε*L) := mul_le_mul hqcu hDe hD.le (by positivity)
         _ = ε * L^28 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 28≤50)) hε.le
  unfold M
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hL0 _)).mpr
  convert mul_le_mul_of_nonneg_right he (show 0 ≤ (X:ℝ)*(Y:ℝ) by positivity) using 1 <;> ring

end ThinBoundary

end

-- Finish
section

namespace ThinFinish
open Finset ThinBoundary ThinWindowModel ThinWindowMinor
open scoped BigOperators Classical

abbrev targets (X : ℕ) := (Icc X (2*X)).filter Even
noncomputable def physical (X n : ℕ) : ℝ :=
  modelMass (Ico (Nat.sqrt X) (2*Nat.sqrt X)) (realWeight (windowCut X)) n
noncomputable def rowError (X n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (windowCut X), (q.totient:ℝ) * ∑ b ∈ units q,
    |primeClassMass q b n (Nat.sqrt X) - (Nat.sqrt X:ℝ)/(q.totient:ℝ)|

def RowIdentification : Prop :=
  ∃ N : ℕ, ∀ X≥N, ∀ n∈targets X, physical X n =
    (∑ q ∈ Icc 1 (windowCut X), measuredRow q n (fun b => primeClassMass q b n (Nat.sqrt X))).re

def FourierComparison : Prop :=
  ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ X≥N, (∑ n∈targets X, (trueMass X n - physical X n)^2)
    ≤ η*(X:ℝ)^2

private theorem row_nonneg (X n : ℕ) : 0 ≤ rowError X n := by
  unfold rowError; positivity

private theorem one_miss {y r d : ℝ} (hy : 0≤y) (hfloor : y/3-d≤r) :
    y^2 ≤ 6*y*d+9*(0-r)^2 := by
  have hh := mul_le_mul_of_nonneg_left hfloor hy
  nlinarith only [hh,sq_nonneg (y-3*r)]

theorem density (hID : RowIdentification) (hFourier : FourierComparison) :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n);
    let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime;
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card;
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (((E X).filter (fun n => H X n=0)).card:ℝ) ≤ ε*(X:ℝ) := by
  dsimp only
  intro ε hε
  let η : ℝ := ε/42
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨I,hI⟩ := hID
  obtain ⟨F,hF⟩ := hFourier η hη
  obtain ⟨A,hA⟩ := prime_window_AP η hη
  refine ⟨max 4 (max I (max F A)),?_⟩
  intro X hX
  let Y := Nat.sqrt X
  let miss := (targets X).filter fun n =>
    ((((Icc Y (2*Y)).filter Nat.Prime).filter (fun p => p≤n ∧ Nat.Prime (n-p))).card = 0)
  change (miss.card : ℝ) ≤ ε*(X:ℝ)
  have hy : 2≤Y := Nat.le_sqrt.mpr (by omega)
  have hy' : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hq : 1≤windowCut X := by
    have hp : 2≤2*Y+2 := by omega
    have hx : 0<Nat.log 2 (2*Y+2) := Nat.log_pos (by decide) hp
    exact Nat.one_le_pow _ _ hx
  have hinc : miss ⊆ targets X := filter_subset _ _
  have hpoint (n : ℕ) (hn : n∈miss) :
      (Y:ℝ)^2 ≤ 6*(Y:ℝ)*rowError X n + 9*(trueMass X n - physical X n)^2 := by
    have hE := hinc hn
    have heven : Even n := (mem_filter.mp hE).2
    have hzero : trueMass X n = 0 := by
      have hm := (mem_filter.mp hn).2
      have hempty := Finset.card_eq_zero.mp hm
      dsimp only [Y] at hempty
      simp only [trueMass,hempty,sum_empty]
    have hfloor := model_floor_with_errors hq heven (Y:ℝ) (by positivity)
      (fun q b => primeClassMass q b n Y)
    rw [← hI X (by omega) n hE] at hfloor
    rw [hzero]
    exact one_miss hy'.le hfloor
  have hcost : (miss.card:ℝ)*(Y:ℝ)^2 ≤
      6*(Y:ℝ)*(∑ n∈targets X,rowError X n) +
      9*(∑ n∈targets X,(trueMass X n - physical X n)^2) := by
    calc _ = ∑ _n ∈ miss,(Y:ℝ)^2 := by simp
         _ ≤ ∑ n ∈ miss,(6*(Y:ℝ)*rowError X n + 9*(trueMass X n - physical X n)^2) :=
              sum_le_sum hpoint
         _ ≤ ∑ n ∈ targets X,(6*(Y:ℝ)*rowError X n + 9*(trueMass X n - physical X n)^2) :=
              sum_le_sum_of_subset_of_nonneg hinc (fun n _ _ => by have := row_nonneg X n; positivity)
         _ = _ := by rw [sum_add_distrib,mul_sum,mul_sum]
  have hrow : ∑ n∈targets X,rowError X n ≤ η*(X:ℝ)*(Y:ℝ) := hA X (by omega)
  have hfour := hF X (by omega)
  have hupper : (X:ℝ) ≤ 4*(Y:ℝ)^2 := by
    have hh := Nat.lt_succ_sqrt X
    change X < (Y+1)*(Y+1) at hh
    have hh' : (X:ℝ) < ((Y:ℝ)+1)*((Y:ℝ)+1) := by exact_mod_cast hh
    have : (2:ℝ) ≤ Y := by exact_mod_cast hy
    nlinarith
  have hx2 : (X:ℝ)^2 ≤ 4*(X:ℝ)*(Y:ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg X)]
  have hmain : (miss.card:ℝ)*(Y:ℝ)^2 ≤ 42*η*(X:ℝ)*(Y:ℝ)^2 := by
    nlinarith only [hcost,mul_le_mul_of_nonneg_left hrow (show 0≤6*(Y:ℝ) by positivity),
      hfour,mul_le_mul_of_nonneg_left hx2 hη.le]
  apply le_of_mul_le_mul_right (a := (Y:ℝ)^2) _ (sq_pos_of_pos hy')
  dsimp [η] at hmain
  linarith
end ThinFinish

end

-- NearArc
section

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped BigOperators Topology
namespace ThinWindowModel

theorem near_uniform :
    ∀ᶠ x : ℕ in atTop, ∀ L D q a : ℕ, ∀ β : ℝ,
      x ≤ 64*D → 0 < L → L+D+1 ≤ x → 0 < q → q ≤ Polylog.cutoff 36 x →
      |β| ≤ blockWidth D (Polylog.cutoff 36 x) q →
      ‖BulkCircle.S L D ((a:ℝ)/q+β) - unitMean q a * BulkCircle.U L D β‖
        ≤ (x:ℝ)/(Real.log (x:ℝ))^4 := by
  obtain ⟨M,hM,hpre⟩ := Polylog.uniform_prefix_error 36 40 (by decide)
  let C : ℝ := 1000*4^36
  have hcon : 0 < C := by norm_num [C]
  have hlim := (Polylog.envelope_saving 36 40 M).eventually_lt_const (show 0 < 1/C by positivity)
  filter_upwards [hpre,hlim,eventually_ge_atTop (2:ℕ)] with x hpre hlim hx
  intro L D q a β hgeom hL hux hq hqmax hβ
  let E := Polylog.errorEnvelope 36 40 M x
  have hE : 0 ≤ E := by dsimp [E,Polylog.errorEnvelope]; positivity
  have hsmall (u : ℕ) (hu : 0<u) (hu' : u≤x) :=
    BulkCircle.point_approx (a:=a) hgeom hu hu' hq hqmax hβ hE (hpre q a hq hqmax)
  have herr :
      ‖BulkCircle.S L D ((a:ℝ)/q+β) - unitMean q a * BulkCircle.U L D β‖ ≤
      1000*(Polylog.cutoff 36 x:ℝ)*E := by
    rw [show BulkCircle.S L D ((a:ℝ)/q+β) - unitMean q a * BulkCircle.U L D β =
      (primeSum (L+D+1) ((a:ℝ)/q+β) - unitMean q a * kernel (L+D+1) β) -
      (primeSum L ((a:ℝ)/q+β) - unitMean q a * kernel L β) by
        unfold BulkCircle.S BulkCircle.U; ring]
    apply (norm_sub_le ..).trans
    linarith only [hsmall (L+D+1) (by omega) hux, hsmall L hL (by omega)]
  have hlog : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (show 1<x by omega))
  have hx' : (0:ℝ)<x := by exact_mod_cast (show 0<x by omega)
  apply herr.trans
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    1000*(Polylog.cutoff 36 x:ℝ)*E*(Real.log x)^4
        ≤ 1000*(4*Real.log x)^36*E*(Real.log x)^4 := by gcongr; exact Polylog.cutoff_le_log 36 hx
    _ = C*((Real.log x)^40*E) := by dsimp [C]; ring
    _ ≤ _ := by
      change (Real.log (x:ℝ))^40 * E / (x:ℝ) < 1/C at hlim
      apply (le_div_iff₀' hcon).mp
      have hh := (div_lt_div_iff₀ hx' hcon).mp hlim
      apply (le_div_iff₀ hcon).mpr
      linarith
end ThinWindowModel

end

-- RamanujanSize
section

open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped ComplexConjugate BigOperators
namespace ThinRamanujan

theorem ram_one_norm_le (q : ℕ) : ‖ram q 1‖ ≤ 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hn (j : ℕ) : ¬ p^(j+1) ∣ 1 := by
        intro hd
        have h := Nat.le_of_dvd (by decide : 0<1) hd
        exact (not_le_of_gt (Nat.one_lt_pow (by omega) hp.one_lt)) h
      rw [ram_primePower p k 1 hp, ite_eq_right (hn k)]
      cases k with
      | zero => norm_num
      | succ k => simp only [ite_eq_right (hn k),sub_self,norm_zero]; norm_num
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, norm_mul]
    simpa using mul_le_mul iq ir (norm_nonneg _) (show (0:ℝ)≤1 by norm_num)

theorem ram_conj (q k : ℕ) : conj (ram q k) = ram q k := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j => rw [ram_primePower p j k hp]; split_ifs <;> simp
  | coprime q r hq hr hqr iq ir => rw [ram_mul (by omega) (by omega) hqr, map_mul, iq, ir]

private theorem totient_square_aux (q : ℕ) : q ≤ 2 * q.totient^2 ∧ (¬2∣q → q ≤ q.totient^2) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p j hp =>
    cases j with
    | zero => simp
    | succ j =>
      rw [Nat.totient_prime_pow_succ hp, pow_succ p j, mul_pow]
      have pos := pow_pos hp.pos j
      by_cases he : p=2
      · subst p
        constructor
        · simp only [Nat.reduceSub,one_pow,mul_one]; nlinarith only [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt pos),sq_nonneg (((2:ℕ)^j)-1), Nat.mul_le_mul_left (2^j) pos]
        · intro h; exact (h (dvd_mul_left ..)).elim
      · have h3 : 3 ≤ p := by have := hp.two_le; omega
        have hloc : p ≤ (p-1)^2 := by
          have h2 : 2 ≤ p-1 := by omega
          nlinarith only [Nat.mul_le_mul_left (p-1) h2, show p ≤ 2*(p-1) by omega]
        have hmain : p^j*p ≤ (p^j)^2*(p-1)^2 := by
          apply Nat.mul_le_mul _ hloc
          nlinarith only [Nat.mul_le_mul_left (p^j) pos]
        exact ⟨by omega,fun _=>hmain⟩
  | coprime q r hq hr hqr iq ir =>
    rw [Nat.totient_mul hqr,mul_pow]
    constructor
    · by_cases hd : 2∣q
      · have hnd : ¬2∣r := by
          intro hr2
          have h := Nat.dvd_gcd hd hr2
          rw [hqr.gcd_eq_one] at h
          omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul iq.1 (ir.2 hnd)
      · calc
          q*r ≤ q.totient^2*(2*r.totient^2) := Nat.mul_le_mul (iq.2 hd) ir.1
          _ = _ := by ring
    · intro h
      exact Nat.mul_le_mul (iq.2 fun hd => h (dvd_mul_of_dvd_left hd _))
        (ir.2 fun hd => h (dvd_mul_of_dvd_right hd _))

theorem sqrt_le_twice_totient (q : ℕ) : Real.sqrt (q:ℝ) ≤ 2*q.totient := by
  have h : (q:ℝ) ≤ 2*(q.totient:ℝ)^2 := by exact_mod_cast (totient_square_aux q).1
  exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith only [h,sq_nonneg (q.totient:ℝ)]⟩

theorem unitMean_one_le (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := BulkCircle.unitMean_norm q a hq

theorem unitMean_sqrt (q a : ℕ) (hq : 0 < q) (hc : a.Coprime q) : ‖unitMean q a‖ ≤ 2/Real.sqrt (q:ℝ) := by
  have ht : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hroot := Real.sqrt_pos.mpr (by exact_mod_cast hq : 0<(q:ℝ))
  rw [unitMean_eq_ram hc,norm_div,Complex.norm_natCast]
  apply (div_le_div_iff₀ ht hroot).mpr
  calc
    _ ≤ 1*Real.sqrt (q:ℝ) := mul_le_mul_of_nonneg_right (ram_one_norm_le q) hroot.le
    _ ≤ _ := by simpa only [one_mul] using sqrt_le_twice_totient q

theorem sum_unitMean_norm_le (q : ℕ) (hq : 0<q) :
    ∑ a∈(range q).filter (fun a=>a.Coprime q), ‖unitMean q a‖ ≤ 1 := by
  have ht : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  calc
    _ = ∑ _a∈(range q).filter (fun a=>a.Coprime q), ‖ram q 1‖/(q.totient:ℝ) := by
      apply sum_congr rfl; intro a ha; rw [unitMean_eq_ram (mem_filter.mp ha).2,norm_div,Complex.norm_natCast]
    _ = ‖ram q 1‖ := by
      have hc : ((range q).filter (fun a=>a.Coprime q)).card = q.totient := by
        rw [Nat.totient_eq_card_coprime]; congr 1; ext i; simp [Nat.coprime_comm]
      simp only [sum_const,nsmul_eq_mul,hc]
      field_simp
    _ ≤ _ := ram_one_norm_le q

theorem closed_numerators_norm_le {q : ℕ} (hq : 1<q) :
    (∑ a ∈ GoldbachBlockGeometry.numerators q, ‖unitMean q a‖) ≤ 1 := by
  have hs : GoldbachBlockGeometry.numerators q = (range q).filter (fun a=>a.Coprime q) := by
    ext a
    simp only [GoldbachBlockGeometry.numerators,mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      have ne : a ≠ q := by intro he; subst a; have h := hc.gcd_eq_one; rw [Nat.gcd_self] at h; omega
      exact ⟨by omega,hc⟩
    · exact fun h => ⟨by omega,h.2⟩
  rw [hs]
  exact sum_unitMean_norm_le q (by omega)

end ThinRamanujan

end

-- KernelSeparation
section

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

namespace ThinKernel

def units (q : ℕ) := (range q).filter (fun a => a.Coprime q)

def centers (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (range Q)).filter (fun p => p.2 < p.1 ∧ p.2.Coprime p.1)

theorem mem_centers {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ centers Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ p.2.Coprime p.1 := by
  simp only [centers, mem_filter, mem_product, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨⟨hq,hQ⟩,_⟩,ha,hc⟩; exact ⟨hq,hQ,ha,hc⟩
  · rintro ⟨hq,hQ,ha,hc⟩; exact ⟨⟨⟨hq,hQ⟩,by omega⟩,ha,hc⟩

noncomputable def center (p : ℕ × ℕ) : ℝ := p.2 / (p.1 : ℝ)
noncomputable def dist (t : ℝ) (p : ℕ × ℕ) : ℝ :=
  OAI.Problem337.RealPhase.integerDistance (t - center p)

theorem center_bounds {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ centers Q) : 0 ≤ center p ∧ center p < 1 := by
  obtain ⟨hq, _, ha, _⟩ := mem_centers.mp hp
  have hq' : (0:ℝ) < p.1 := by exact_mod_cast hq
  constructor
  · unfold center; positivity
  · rw [center, div_lt_one hq']; exact_mod_cast ha

theorem farey_separation {Q : ℕ} {p s : ℕ × ℕ} (hp : p ∈ centers Q)
    (hs : s ∈ centers Q) (hne : p ≠ s) (k : ℤ) :
    1 / (Q : ℝ)^2 ≤ |center p - center s - k| := by
  rcases p with ⟨q,a⟩; rcases s with ⟨r,b⟩
  obtain ⟨hq, hqQ, ha, hcop⟩ := mem_centers.mp hp
  obtain ⟨hr, hrQ, hb, hcop'⟩ := mem_centers.mp hs
  obtain ⟨ha₀,ha₁⟩ := center_bounds hp
  obtain ⟨hb₀,hb₁⟩ := center_bounds hs
  dsimp at hq hqQ ha hcop hr hrQ hb hcop'
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast (show 0<Q by omega)
  let m : ℤ := (a:ℤ)*r - (b:ℤ)*q - k*q*r
  have he : (m:ℝ) = (center (q,a) - center (r,b) - k)*((q:ℝ)*r) := by
    unfold m center; dsimp; push_cast; field_simp
  have hm : m ≠ 0 := by
    intro hz
    have he' : (center (q,a) - center (r,b) - k)*((q:ℝ)*r) = 0 := by rw [← he,hz]; norm_num
    have hdiff := (mul_eq_zero.mp he').resolve_right (mul_ne_zero hq'.ne' hr'.ne')
    have hk₀ : (-1:ℝ) < k := by linarith
    have hk₁ : (k:ℝ) < 1 := by linarith
    have hk : k=0 := by
      exact_mod_cast (show k=0 by have : (-1:ℤ)<k := by exact_mod_cast hk₀
                                  have : k<(1:ℤ) := by exact_mod_cast hk₁
                                  omega)
    have hh : (a:ℤ)*r = (b:ℤ)*q := by simpa [m,hk,sub_eq_zero] using hz
    have eq : a*r=b*q := by exact_mod_cast hh
    have hqr : q ∣ r := hcop.symm.dvd_of_dvd_mul_left (eq ▸ dvd_mul_left q b)
    have hrq : r ∣ q := hcop'.symm.dvd_of_dvd_mul_left (eq.symm ▸ dvd_mul_left r a)
    obtain rfl := Nat.dvd_antisymm hqr hrq
    exact hne (Prod.ext rfl (Nat.eq_of_mul_eq_mul_right hq eq))
  have hm' : 1 ≤ ‖(m : ℝ)‖ := by rw [Real.norm_eq_abs]; exact_mod_cast (Int.one_le_abs hm)
  rw [Real.norm_eq_abs, he, abs_mul, abs_of_pos (mul_pos hq' hr')] at hm'
  calc 1 / (Q:ℝ)^2 ≤ 1 / ((q:ℝ)*r) := by
         apply one_div_le_one_div_of_le (mul_pos hq' hr')
         rw [sq]; gcongr
       _ ≤ _ := (div_le_iff₀ (mul_pos hq' hr')).mpr hm'

theorem separation_sum {Q : ℕ} {p s : ℕ × ℕ} (hp : p∈centers Q)
    (hs : s∈centers Q) (hsp : s≠p) (t : ℝ) :
    1/(Q:ℝ)^2 ≤ dist t s + dist t p := by
  let k := round (t-center s) - round (t-center p)
  have hsep := farey_separation hp hs hsp.symm k
  have hid : center p - center s - (k:ℝ) =
      ((t-center s) - round (t-center s)) - ((t-center p) - round (t-center p)) := by
    dsimp [k]; push_cast; ring
  rw [hid] at hsep
  exact hsep.trans (abs_sub _ _)

theorem exists_nearest {Q : ℕ} (hQ : 1 ≤ Q) (t : ℝ) :
    ∃ p ∈ centers Q, (∀ s ∈ centers Q, dist t p ≤ dist t s) ∧
      (∀ s ∈ centers Q, s ≠ p → 1 / (2 * (Q:ℝ)^2) ≤ dist t s) := by
  have hmem : (1,0) ∈ centers Q := mem_centers.mpr ⟨by decide,hQ,by decide,by decide⟩
  obtain ⟨p,hp,hmin⟩ := (centers Q).exists_min_image (dist t) ⟨_,hmem⟩
  refine ⟨p,hp,hmin,?_⟩
  intro s hs hsp
  have hh := separation_sum hp hs hsp t
  have hi := hmin s hs
  have hid' : 1/(2*(Q:ℝ)^2) = (1/(Q:ℝ)^2)/2 := by ring
  linarith

theorem kernel_times_distance (L D : ℕ) (x : ℝ) :
    ‖BulkCircle.U L D x‖ * OAI.Problem337.RealPhase.integerDistance x ≤ 1 := by
  let d := OAI.Problem337.RealPhase.integerDistance x
  have hn := OAI.Problem337.RealPhase.integerDistance_nonneg x
  change ‖BulkCircle.U L D x‖ * d ≤ 1
  by_cases hd : d=0
  · simp [hd]
  have hdp : 0<d := lt_of_le_of_ne hn (Ne.symm hd)
  have hj := OAI.Problem337.RealPhase.two_integerDistance_le_abs_sin x
  change 2*d ≤ _ at hj
  have hsi : Real.sin (Real.pi*x) ≠ 0 := by intro h; rw [h,abs_zero] at hj; linarith
  have hK := OAI.Problem337.norm_geometric_phase_sum_le hsi (D+1)
  have hpow (k : ℕ) : phase ((k:ℝ)*x) = (Complex.exp (Complex.I * (2*Real.pi*x:ℝ)))^k := by
    rw [← Complex.exp_nat_mul]; unfold phase
    congr 1; push_cast; ring
  have hh : ‖kernel D x‖ ≤ 1/|Real.sin (Real.pi*x)| := by simpa only [kernel,hpow] using hK
  rw [BulkCircle.shifted_kernel, norm_mul, BulkCircle.norm_phase, one_mul]
  apply (le_div_iff₀ hdp).mp
  exact hh.trans (one_div_le_one_div_of_le hdp (by linarith))

theorem kernel_off_arcs {Q B D : ℕ} (hQB : Q≤B) (hD : 0<D) {p : ℕ × ℕ}
    (hp : p∈centers Q) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hout : t∉GoldbachBlockGeometry.arcs B D) (L : ℕ) :
    ‖BulkCircle.U L D (t - center p)‖ ≤ D * (p.1 : ℝ) / B := by
  obtain ⟨hq,hqQ,ha,hcop⟩ := mem_centers.mp hp
  have hq' : 0 < (p.1:ℝ) := by exact_mod_cast hq
  have hB : 1 ≤ B := by omega
  have hB' : 0 < (B:ℝ) := by exact_mod_cast hB
  have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
  have hbd := center_bounds hp
  have outside (a q : ℕ) (h1 : 1≤q) (h2 : q≤B) (h3 : a≤q) (h4 : a.Coprime q) :
      (B:ℝ)/((q:ℝ)*D) < |t-(a:ℝ)/q| := by
    by_contra! h
    exact hout ⟨q,a,h1,h2,h3,h4,h⟩
  have h0 := outside 0 1 (by decide) hB (by decide) (by decide)
  have h1 := outside 1 1 (by decide) hB (by decide) (by decide)
  have hx := outside p.2 p.1 hq (hqQ.trans hQB) ha.le hcop
  change (B:ℝ) / ((p.1:ℝ)*D) < |t - center p| at hx
  norm_num only [Nat.cast_zero,Nat.cast_one,one_mul,div_one,sub_zero] at h0 h1
  rw [abs_of_nonneg ht.1] at h0
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2),neg_sub] at h1
  have hle : (B:ℝ) / ((p.1:ℝ)*D) ≤ (B:ℝ)/D := by
    apply div_le_div_of_nonneg_left hB'.le hD' _
    exact le_mul_of_one_le_left hD'.le (by exact_mod_cast hq)
  let k := round (t - center p)
  have dd : (B:ℝ) / ((p.1:ℝ)*D) ≤ dist t p := by
    change _ ≤ |t - center p - (k:ℝ)|
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      exact le_abs_self _ |> le_trans (by linarith [ht.1,hbd.2,hle.trans h0.le])
    · simpa [hk] using hx.le
    · have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      exact (neg_le_abs _).trans' (by linarith [hbd.1,hle.trans h1.le])
  have hh := kernel_times_distance L D (t-center p)
  change ‖BulkCircle.U L D (t-center p)‖ * dist t p ≤ 1 at hh
  have hv := (mul_le_mul_of_nonneg_left dd (norm_nonneg (BulkCircle.U L D (t-center p)))).trans hh
  have hi : ((D:ℝ) * p.1 / B) * ((B:ℝ) / ((p.1:ℝ)*D)) = 1 := by field_simp
  exact le_of_mul_le_mul_right (hv.trans_eq hi.symm) (by positivity : 0 < (B:ℝ)/((p.1:ℝ)*D))

theorem sum_centers {M : Type*} [AddCommMonoid M] (Q : ℕ) (f : ℕ → ℕ → M) :
    (∑ p ∈ centers Q, f p.1 p.2) = ∑ q ∈ Icc 1 Q, ∑ a ∈ units q, f q a := by
  rw [centers, sum_filter, sum_product]
  apply sum_congr rfl; intro q hq
  rw [← sum_filter]
  congr 1
  ext a
  simp only [units, mem_filter, mem_range]
  have hqQ := (mem_Icc.mp hq).2
  constructor
  · rintro ⟨_,ha,hc⟩; exact ⟨ha,hc⟩
  · rintro ⟨ha,hc⟩; exact ⟨by omega,ha,hc⟩

theorem weight_sum_le (Q : ℕ)
    (hweights : ∀ q ∈ Icc 1 Q, ∑ a ∈ units q, ‖unitMean q a‖ ≤ 1) :
    (∑ p ∈ centers Q, ‖unitMean p.1 p.2‖) ≤ (Q : ℝ) := by
  rw [sum_centers Q (fun q a => ‖unitMean q a‖)]
  calc _ ≤ ∑ _q ∈ Icc 1 Q, (1 : ℝ) := sum_le_sum hweights
       _ = _ := by simp

theorem kernel_of_dist {T : ℝ} (hT : 0 < T) (L D : ℕ) (t : ℝ) (s : ℕ × ℕ)
    (hfar : 1/T ≤ dist t s) : ‖BulkCircle.U L D (t-center s)‖ ≤ T := by
  have hu := kernel_times_distance L D (t-center s)
  change ‖BulkCircle.U L D (t-center s)‖ * dist t s ≤ 1 at hu
  have hh := (mul_le_mul_of_nonneg_left hfar (norm_nonneg _)).trans hu
  have hdiv : ‖BulkCircle.U L D (t-center s)‖ / T ≤ 1 := by simpa only [mul_one_div] using hh
  have hh' := (div_le_iff₀ hT).mp hdiv
  linarith

noncomputable def modelTerm (L D : ℕ) (t : ℝ) (s : ℕ × ℕ) : ℂ :=
  unitMean s.1 s.2 * BulkCircle.U L D (t-center s)

/-- Among any list of model centers, all terms at circular distance at least 1/T
have total norm at most T times the sum of numerator weights. -/
theorem tail_of_far {Q L D : ℕ} (t : ℝ) (T : ℝ) (hT : 0<T) (p : ℕ × ℕ)
    (hweights : ∀ q ∈ Icc 1 Q, ∑ a ∈ units q, ‖unitMean q a‖ ≤ 1)
    (hfar : ∀ s∈(centers Q).erase p, 1/T ≤ dist t s) :
    (∑ s ∈ (centers Q).erase p, ‖modelTerm L D t s‖) ≤ (Q:ℝ)*T := by
  calc _ ≤ ∑ s ∈ (centers Q).erase p, ‖unitMean s.1 s.2‖*T := by
         apply sum_le_sum
         intro s hs
         unfold modelTerm
         rw [norm_mul]
         exact mul_le_mul_of_nonneg_left (kernel_of_dist hT L D t s (hfar s hs)) (norm_nonneg _)
       _ = (∑ s ∈ (centers Q).erase p, ‖unitMean s.1 s.2‖)*T := (sum_mul ..).symm
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ hT.le
         exact (sum_le_sum_of_subset_of_nonneg (erase_subset p _) (fun s _ _ => norm_nonneg _)).trans
           (weight_sum_le Q hweights)

theorem other_model_bound {Q L D : ℕ} (hQ : 1≤Q) (t : ℝ) {p : ℕ × ℕ}
    (hp : p∈centers Q) (hmin : ∀ s∈centers Q, dist t p ≤ dist t s)
    (hweights : ∀ q ∈ Icc 1 Q, ∑ a ∈ units q, ‖unitMean q a‖ ≤ 1) :
    (∑ s ∈ (centers Q).erase p, ‖modelTerm L D t s‖) ≤ 2*(Q:ℝ)^3 := by
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hfar (s) (hs : s ∈ (centers Q).erase p) : 1/(2*(Q:ℝ)^2) ≤ dist t s := by
    obtain ⟨hn,hs⟩ := mem_erase.mp hs
    have hh := separation_sum hp hs hn t
    have hi := hmin s hs
    rw [show 1/(2*(Q:ℝ)^2) = (1/(Q:ℝ)^2)/2 by ring]
    linarith
  convert tail_of_far (L:=L) (D:=D) t (2*(Q:ℝ)^2) (by positivity) p hweights hfar using 1
  ring

theorem model_off_arcs {Q B D : ℕ} (hQ : 1≤Q) (hQB : Q≤B) (hD : 0<D)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hout : t ∉ GoldbachBlockGeometry.arcs B D)
    (hweights : ∀ q ∈ Icc 1 Q, ∑ a ∈ units q, ‖unitMean q a‖ ≤ 1) (L : ℕ) :
    ‖∑ s ∈ centers Q, modelTerm L D t s‖ ≤ 2*(Q:ℝ)^3 + D*(Q:ℝ)/B := by
  obtain ⟨p,hp,hmin,_⟩ := exists_nearest hQ t
  obtain ⟨hq,hqQ,_,_⟩ := mem_centers.mp hp
  have hB : 0 ≤ (B:ℝ) := by positivity
  have hs : ‖modelTerm L D t p‖ ≤ D*(Q:ℝ)/B := by
    unfold modelTerm
    rw [norm_mul]
    calc _ ≤ 1 * ((D:ℝ)*p.1/B) := mul_le_mul (BulkCircle.unitMean_norm _ _ hq)
           (kernel_off_arcs hQB hD hp ht hout L) (norm_nonneg _) zero_le_one
         _ ≤ _ := by rw [one_mul]; gcongr
  apply (norm_sum_le _ _).trans
  rw [← add_sum_erase _ _ hp]
  linarith [other_model_bound (L:=L) (D:=D) hQ t hp hmin hweights]

theorem row_weight (Q q : ℕ) (hq : q∈Icc 1 Q) : ∑ a∈units q, ‖unitMean q a‖ ≤ 1 :=
  ThinRamanujan.sum_unitMean_norm_le q (mem_Icc.mp hq).1

theorem tail_nearest {Q L D : ℕ} (hQ : 1≤Q) (t : ℝ) {p : ℕ × ℕ}
    (hp : p∈centers Q) (hmin : ∀ s∈centers Q, dist t p ≤ dist t s) :
    (∑ s ∈ (centers Q).erase p, ‖modelTerm L D t s‖) ≤ 2*(Q:ℝ)^3 :=
  other_model_bound hQ t hp hmin (row_weight Q)

theorem model_off_arcs_unconditional {Q B D : ℕ} (hQ : 1≤Q) (hQB : Q≤B) (hD : 0<D)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hout : t ∉ GoldbachBlockGeometry.arcs B D) (L : ℕ) :
    ‖∑ s ∈ centers Q, modelTerm L D t s‖ ≤ 2*(Q:ℝ)^3 + D*(Q:ℝ)/B :=
  model_off_arcs hQ hQB hD ht hout (row_weight Q) L

/-- The distinguished rational center can come from a larger list. When its
denominator exceeds the model cutoff this controls the entire model. -/
theorem tail_near_large_center {Q B L D : ℕ} (hQB : Q≤B) {p : ℕ × ℕ}
    (hp : p∈centers B) {t : ℝ} (hnear : dist t p ≤ 1/(2*(B:ℝ)^2)) :
    (∑ s ∈ (centers Q).erase p, ‖modelTerm L D t s‖) ≤ (Q:ℝ)*(2*(B:ℝ)^2) := by
  have hB : 0 < B := by have h := mem_centers.mp hp; omega
  have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
  apply tail_of_far t _ (by positivity) p (row_weight Q)
  intro s hs
  obtain ⟨hn, hs⟩ := mem_erase.mp hs
  obtain ⟨hq,hqQ,ha,hcop⟩ := mem_centers.mp hs
  have hs' := mem_centers.mpr ⟨hq,hqQ.trans hQB,ha,hcop⟩
  have hsep := separation_sum hp hs' hn t
  have he : 1/(2*(B:ℝ)^2) = (1/(B:ℝ)^2)/2 := by ring
  linarith

private theorem U_sub_one (L D : ℕ) (t : ℝ) :
    BulkCircle.U L D (t-1) = BulkCircle.U L D t := by
  have hi (m : ℤ) : phase (m:ℝ) = 1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I m using 2
    push_cast; ring
  have hp (k : ℕ) : phase ((k:ℝ)*(t-1)) = phase ((k:ℝ)*t) := by
    rw [mul_sub,mul_one,sub_eq_add_neg,BulkCircle.phase_add]
    have h1 := hi (-(k:ℤ))
    push_cast at h1
    rw [h1,mul_one]
  unfold BulkCircle.U kernel
  simp only [hp]

/-- Convert a numerator at either end of the closed rational arc list to
the half-open center convention, preserving its complete shifted kernel. -/
theorem normalized_center {B q a : ℕ} (hq : 1≤q) (hB : q≤B) (ha : a≤q)
    (hc : a.Coprime q) (t : ℝ) (L D : ℕ) :
    ∃ p∈centers B, p.1=q ∧ dist t p ≤ |t-(a:ℝ)/q| ∧
      unitMean q a * BulkCircle.U L D (t-(a:ℝ)/q) = modelTerm L D t p := by
  rcases lt_or_eq_of_le ha with hlt | rfl
  · refine ⟨(q,a), mem_centers.mpr ⟨hq,hB,hlt,hc⟩,rfl,?_,rfl⟩
    simpa only [dist,OAI.Problem337.RealPhase.integerDistance,center,Int.cast_zero,sub_zero]
      using round_le (t-(a:ℝ)/q) (0:ℤ)
  · have he : a=1 := by simpa using hc
    subst a
    refine ⟨(1,0),mem_centers.mpr ⟨by decide,hB,by decide,by decide⟩,rfl,?_,?_⟩
    · simpa [dist,OAI.Problem337.RealPhase.integerDistance,center] using round_le t (1:ℤ)
    · simp only [modelTerm,center,Nat.cast_zero,Nat.cast_one,div_one,sub_zero,
        U_sub_one,unitMean_eq_ram (by decide : (1:ℕ).Coprime 1),
        unitMean_eq_ram (by decide : (0:ℕ).Coprime 1)]

end ThinKernel

end

-- UniformNumbers
section

open Filter Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped Topology BigOperators
namespace ThinUniform

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem cutoff_parameters : ∀ᶠ Y : ℕ in atTop,
    2≤Y ∧ 1≤Real.log (2*(Y:ℝ)) ∧
    let g := Nat.log 2 (2*Y+2)
    1≤g ∧ Real.log (2*(Y:ℝ))≤2*(g:ℝ) ∧ 16*(g:ℝ)^110 ≤ (Y:ℝ) := by
  let C : ℝ := 32*4^110
  have hC : 0<C := by norm_num [C]
  have hh := (isLittleO_log_rpow_rpow_atTop (110:ℝ) (by norm_num : (0:ℝ)<1)).bound (show 0<1/C by positivity)
  have tending : Tendsto (fun y:ℕ => 2*(y:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [tending.eventually hh,tending.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1),
    eventually_ge_atTop (2:ℕ)] with Y hy hL hY
  let g := Nat.log 2 (2*Y+2)
  have hg : 1≤g := Nat.le_log_of_pow_le (by decide) (by dsimp [g]; norm_num)
  have hx : 0<2*(Y:ℝ) := by positivity
  have hlt := Nat.lt_pow_succ_log_self (by decide : 1<2) (2*Y+2)
  have hcast : 2*(Y:ℝ) ≤ (2:ℝ)^(g+1) := by
    have h : 2*Y ≤ 2^(g+1) := (show 2*Y ≤ 2*Y+2 by omega).trans (Nat.le_of_lt hlt)
    exact_mod_cast h
  have hlog := Real.log_le_log hx hcast
  rw [Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
  have hgu : (g:ℝ) ≤ 4*Real.log (2*(Y:ℝ)) := by
    have hu := Polylog.cutoff_le_log 1 (n:=2*Y) (by omega)
    simpa [Polylog.cutoff,g] using hu
  have hbound : (Real.log (2*(Y:ℝ)))^110 ≤ (1/C) * (2*(Y:ℝ)) := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,abs_of_pos hx] using hy
  refine ⟨hY,hL,hg,?_,?_⟩
  · push_cast at hlog
    have hga : (1:ℝ)≤g := by exact_mod_cast hg
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hl2 (show (0:ℝ)≤g+1 by positivity),hga]
  · have hgpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) g) hgu 110
    rw [mul_pow] at hgpow
    have he : C*(Real.log (2*(Y:ℝ)))^110 ≤ 2*(Y:ℝ) := by
      calc _ ≤ C*((1/C)*(2*(Y:ℝ))) := mul_le_mul_of_nonneg_left hbound hC.le
           _ = _ := by field_simp
    dsimp only [C] at he
    linarith only [hgpow,he]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Budgets for the minor arcs, the separated model kernels and the central large-denominator kernel. -/
theorem error_budgets {g l Y:ℝ} (hg:1≤g) (hl:1≤l) (hlg:l≤2*g) (hY:16*g^110≤Y) :
    2*g^80 ≤ Y/l^2 ∧ 2*g^24 ≤ Y/l^2 ∧ Y*g^8/g^36 ≤ 4*Y/l^2 ∧
    2*Y/g^4 ≤ 8*Y/l^2 ∧ 2*Y/l^4 ≤ 2*Y/l^2 ∧ 4096*Y/l^10 ≤ 4096*Y/l^2 := by
  have gp : 0<g := by linarith
  have lp : 0<l := by linarith
  have yp : 0≤Y := le_trans (by positivity) hY
  have ls : l^2≤4*g^2 := by nlinarith only [pow_le_pow_left₀ lp.le hlg 2]
  have poly (k:ℕ) (hk:k+2≤110) : 2*g^k ≤ Y/l^2 := by
    apply (le_div_iff₀ (by positivity)).2
    calc _ ≤ (2*g^k)*(4*g^2) := mul_le_mul_of_nonneg_left ls (by positivity)
         _ = 8*g^(k+2) := by rw [pow_add]; ring
         _ ≤ 8*g^110 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg hk) (by norm_num)
         _ ≤ Y := by linarith only [hY, pow_nonneg gp.le 110]
  refine ⟨poly 80 (by decide),poly 24 (by decide),?_,?_,?_,?_⟩
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc _ ≤ (Y*g^8)*(4*g^2) := mul_le_mul_of_nonneg_left ls (by positivity)
         _ = (4*Y)*g^10 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg (show 10≤36 by decide)) (by positivity)
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc _ ≤ (2*Y)*(4*g^2) := mul_le_mul_of_nonneg_left ls (by positivity)
         _ = (8*Y)*g^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg (by decide)) (by positivity)
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hl (by decide))
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hl (by decide))

end ThinUniform

end

-- UniformApprox
section

open Filter Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc ThinWindowModel ThinWindowMinor
open scoped Topology BigOperators
namespace ThinUniform
noncomputable section

set_option maxHeartbeats 700000 in
set_option maxRecDepth 4096 in
private theorem model_window (Y : ℕ) (hY : 1≤Y) (u : ℝ) :
    dirichletWindow (Ico Y (2*Y)) u = BulkCircle.U (Y-1) (Y-1) u := by
  rw [BulkCircle.shifted_kernel]
  have h₁ : ((Y-1:ℕ):ℝ) + 1 = Y := by exact_mod_cast (by omega : Y-1+1=Y)
  have h₂ : (Y-1)+1 = Y := by omega
  rw [h₁]
  unfold dirichletWindow kernel
  rw [Finset.sum_Ico_eq_sum_range,h₂,show 2*Y-Y=Y by omega, mul_sum]
  apply sum_congr rfl; intro k hk
  rw [← BulkCircle.phase_add]; push_cast; congr 1; ring

set_option maxHeartbeats 700000 in
set_option maxRecDepth 4096 in
private theorem model_sum (Y Q : ℕ) (hY : 1≤Y) (t : ℝ) :
    poly (Ico Y (2*Y)) (realWeight Q) t =
      ∑ s∈ThinKernel.centers Q, ThinKernel.modelTerm (Y-1) (Y-1) t s := by
  change transform _ _ _ = _
  rw [transform_weight,ThinKernel.sum_centers Q (fun q a => ThinKernel.modelTerm (Y-1) (Y-1) t (q,a))]
  apply sum_congr rfl; intro q hq
  apply sum_congr rfl; intro a ha
  rw [model_window Y hY]; rfl

set_option maxHeartbeats 700000 in
set_option maxRecDepth 4096 in
private theorem upper_kernel (Y:ℕ) (hY:1≤Y) (β:ℝ) :
    ‖BulkCircle.U (Y-1) (Y-1) β‖ ≤ (Y:ℝ) := by
  rw [BulkCircle.shifted_kernel,norm_mul,BulkCircle.norm_phase,one_mul]
  exact (BulkCircle.norm_kernel_le (Y-1) β).trans (by exact_mod_cast (by omega : Y-1+1≤Y))

set_option maxHeartbeats 700000 in
set_option maxRecDepth 4096 in
theorem approximation : ∀ᶠ X : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
    let Y := Nat.sqrt X
    ‖shortSum X t - poly (Ico Y (2*Y)) (realWeight (Polylog.cutoff 8 (2*Y))) t‖ ≤
      (4200/(Real.log (2*(Y:ℝ)))^2) * Y := by
  have hn := root_tends.eventually near_uniform
  have hs : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.2; intro b; filter_upwards [eventually_ge_atTop (b^2)] with n hn
    exact Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  filter_upwards [hn,hs.eventually cutoff_parameters,small_minor_eventually] with X hn hp hminor
  let Y := X.sqrt
  let D := Y-1
  let g := Nat.log 2 (2*Y+2)
  let B := Polylog.cutoff 36 (2*Y)
  let Q := Polylog.cutoff 8 (2*Y)
  let l := Real.log (2*(Y:ℝ))
  obtain ⟨hY,hl,hg,hlg,hbig⟩ := hp
  change 2≤Y at hY
  change 1≤l at hl
  change 1≤g at hg
  change l ≤ 2*(g:ℝ) at hlg
  change 16*(g:ℝ)^110 ≤ Y at hbig
  have hgr : (1:ℝ)≤g := by exact_mod_cast hg
  have gd : 0<D := by dsimp [D]; omega
  have qpos : 1≤Q := one_le_pow₀ hg
  have qb : Q≤B := pow_le_pow_right₀ hg (by decide : 8≤36)
  have bpos : 0<(B:ℝ) := by exact_mod_cast (by omega : 0<B)
  have bval : (B:ℝ)=(g:ℝ)^36 := by dsimp [B,g,Polylog.cutoff]; push_cast; rfl
  have qval : (Q:ℝ)=(g:ℝ)^8 := by dsimp [Q,g,Polylog.cutoff]; push_cast; rfl
  have sep : 2*(B:ℝ)^3 ≤ (D:ℝ) := by
    have hgp := pow_le_pow_right₀ hgr (show 108≤110 by decide)
    have hbase : 1 ≤ (g:ℝ)^110 := one_le_pow₀ hgr
    have hd : (D:ℝ) + 1 = Y := by exact_mod_cast (by dsimp [D]; omega : D+1=Y)
    rw [bval, ←pow_mul]; norm_num; linarith only [hbig,hgp,hbase,hd]
  have budget := error_budgets hgr hl hlg hbig
  obtain ⟨htail,htail',hsmall,hpeak,hprimary,houter⟩ := budget
  have htailNear : (Q:ℝ)*(2*(B:ℝ)^2) ≤ (Y:ℝ)/l^2 := by
    rw [bval,qval]; convert htail using 1 <;> ring
  have htailOff : 2*(Q:ℝ)^3 ≤ (Y:ℝ)/l^2 := by rw [qval,←pow_mul]; exact htail'
  have hoff : (D:ℝ)*Q/B ≤ 4*(Y:ℝ)/l^2 := by
    apply le_trans _ hsmall
    rw [bval,qval]; gcongr; exact_mod_cast (by dsimp [D]; omega : D≤Y)
  intro t ht
  dsimp only
  change ‖shortSum X t - poly (Ico Y (2*Y)) (realWeight Q) t‖ ≤ 4200/l^2*Y
  rw [model_sum Y Q (by omega)]
  let M := ∑ s∈ThinKernel.centers Q, ThinKernel.modelTerm D D t s
  change ‖shortSum X t - M‖ ≤ _
  let Z := (Y:ℝ)/l^2
  have scale (c:ℝ) : c*Y/l^2 = c*Z := by dsimp [Z]; ring
  rw [scale 2] at hprimary
  rw [scale 4] at hoff
  rw [scale 8] at hpeak
  rw [scale 4096] at houter
  have nonneg : 0≤(Y:ℝ)/l^2 := by positivity
  have conclusion : (Y:ℝ)/l^2 * 4200 = 4200/l^2*Y := by ring
  rw [←conclusion]
  change ‖shortSum X t-M‖ ≤ Z*4200
  change 0≤Z at nonneg
  by_cases htarc : t∈major X
  · obtain ⟨q,a,hq,hqB,ha,hc,hw⟩ := htarc
    change q≤B at hqB
    change |t-(a:ℝ)/q| ≤ (B:ℝ)/((q:ℝ)*D) at hw
    have hnear := hn D D q a (t-(a:ℝ)/q) (by dsimp [D]; omega) gd (by dsimp [D]; omega) hq hqB hw
    rw [add_sub_cancel] at hnear
    change ‖shortSum X t - unitMean q a * BulkCircle.U D D (t-(a:ℝ)/q)‖ ≤ ((2*Y:ℕ):ℝ)/(Real.log ((2*Y:ℕ):ℝ))^4 at hnear
    push_cast at hnear
    change ‖shortSum X t - unitMean q a * BulkCircle.U D D (t-(a:ℝ)/q)‖ ≤ 2*Y/l^4 at hnear
    obtain ⟨p,hp,heq,hd,hm⟩ := ThinKernel.normalized_center hq hqB ha hc t D D
    have hclose : ThinKernel.dist t p ≤ 1/(2*(B:ℝ)^2) := by
      apply (hd.trans hw).trans
      have dq : 0<(q:ℝ) := by exact_mod_cast hq
      have dD : 0<(D:ℝ) := by exact_mod_cast gd
      apply (div_le_div_iff₀ (mul_pos dq dD) (by positivity)).mpr
      have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
      have := le_mul_of_one_le_left dD.le hq1
      nlinarith only [sep,this]
    have hrest := ThinKernel.tail_near_large_center (L:=D) (D:=D) qb hp hclose
    have hrest' := (norm_sum_le (ThinKernel.centers Q |>.erase p) _).trans hrest
    have hrest2 := hrest'.trans htailNear
    change _ ≤ Z at hrest2
    have hmain : ‖shortSum X t - unitMean q a * BulkCircle.U D D (t-(a:ℝ)/q)‖ ≤ 2*Z := hnear.trans hprimary
    rw [hm] at hmain
    by_cases hqQ : q≤Q
    · have hpc : p∈ThinKernel.centers Q := by
        obtain ⟨h₁,h₂,h₃,h₄⟩ := ThinKernel.mem_centers.mp hp
        exact ThinKernel.mem_centers.mpr ⟨h₁,heq ▸ hqQ,h₃,h₄⟩
      have hsum : M = ThinKernel.modelTerm D D t p + ∑ s∈(ThinKernel.centers Q).erase p,ThinKernel.modelTerm D D t s := (add_sum_erase _ _ hpc).symm
      rw [hsum,←sub_sub]
      exact (norm_sub_le _ _).trans (by linarith only [hmain,hrest2,nonneg])
    · have hpc : p∉ThinKernel.centers Q := fun h => hqQ (heq ▸ (ThinKernel.mem_centers.mp h).2.1)
      rw [erase_eq_of_notMem hpc] at hrest2
      change ‖M‖ ≤ Z at hrest2
      have hqr : (Q:ℝ) ≤ q := by exact_mod_cast (by omega : Q≤q)
      have hroot : (g:ℝ)^4 ≤ Real.sqrt q := by
        apply (Real.le_sqrt (by positivity) (by positivity)).mpr
        rw [qval] at hqr; convert hqr using 1 <;> ring
      have hterm : ‖ThinKernel.modelTerm D D t p‖ ≤ 2*(Y:ℝ)/(g:ℝ)^4 := by
        rw [←hm,norm_mul]
        have hφ := ThinRamanujan.unitMean_sqrt q a hq hc
        have hle := hφ.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hroot)
        have h := mul_le_mul hle (upper_kernel Y (by omega) (t-(a:ℝ)/q)) (norm_nonneg _) (by positivity)
        exact h.trans_eq (by ring)
      have tri := norm_add_le (shortSum X t-ThinKernel.modelTerm D D t p) (ThinKernel.modelTerm D D t p)
      rw [sub_add_cancel] at tri
      exact (norm_sub_le _ _).trans (by linarith only [hmain,hrest2,nonneg,tri,hterm,hpeak])
  · have hreal := hminor t ht htarc
    change ‖shortSum X t‖ ≤ 4096*Y/l^10 at hreal
    have hmodel := ThinKernel.model_off_arcs_unconditional qpos qb gd ht htarc D
    change ‖M‖ ≤ _ at hmodel
    change _ ≤ Z at htailOff
    exact (norm_sub_le _ _).trans (by linarith only [hreal.trans houter,hmodel,htailOff,hoff,nonneg])
end
end ThinUniform

end

-- FinalThin
section

open Filter Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped BigOperators Topology

theorem Conjectures.Goldbach.DynThinWindowExceptions :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, (((E X).filter (fun n => H X n=0)).card:ℝ) ≤ ε*(X:ℝ) := by
  apply ThinFinish.density ThinWindowModel.eventual_physical_row
  intro ε hε
  let I := fun X : ℕ => Ico (Nat.sqrt X) (2*Nat.sqrt X)
  let w := fun X : ℕ => ThinWindowModel.realWeight (ThinBoundary.windowCut X)
  have hs : ∀ᶠ X : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖ThinWindowMinor.shortSum X t - ThinWindowMinor.poly (I X) (w X) t‖ ≤
        (4200:ℝ) * (Nat.sqrt X:ℝ) / Real.log (2*(Nat.sqrt X:ℝ))^2 := by
    filter_upwards [ThinUniform.approximation] with X h
    intro t ht
    have h' := h t ht
    change _ ≤ (4200 / Real.log (2*(Nat.sqrt X:ℝ))^2)*(Nat.sqrt X:ℝ) at h'
    apply h'.trans_eq
    ring
  have he := ThinWindowMinor.physical_error_tends I w hs ε hε
  apply eventually_atTop.mp
  filter_upwards [he] with X h
  exact h (ThinFinish.targets X) (fun n hn => (mem_Icc.mp (mem_filter.mp hn).1).2)

end
