import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space


open Filter MeasureTheory
open scoped Topology

open scoped BigOperators ComplexConjugate

-- Finite Parseval construction adapted from Clrs17 in Goldbach PR 138.
private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem frontierDeepParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _



open MeasureTheory Filter
open scoped Topology

private def frontierArc (n bound width : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ bound ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / q| ≤ (width : ℝ) / ((q : ℝ) * n)}

private theorem frontierArc_measurable (n bound width : ℕ) :
    MeasurableSet (frontierArc n bound width) := by
  classical
  let piece (q a : ℕ) : Set ℝ :=
    if 1 ≤ q ∧ q ≤ bound ∧ a ≤ q ∧ Nat.Coprime a q then
      {t | |t - (a : ℝ) / q| ≤ (width : ℝ) / ((q : ℝ) * n)}
    else ∅
  have hpieces : frontierArc n bound width = ⋃ q : ℕ, ⋃ a : ℕ, piece q a := by
    ext t
    simp only [frontierArc, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, hq, hB, ha, hc, ht⟩
      have hp : 1 ≤ q ∧ q ≤ bound ∧ a ≤ q ∧ Nat.Coprime a q := ⟨hq, hB, ha, hc⟩
      exact ⟨q, a, by simpa only [piece, ite_eq_left hp,
        Set.mem_ofPred_eq] using ht⟩
    · rintro ⟨q, a, ht⟩
      by_cases hp : 1 ≤ q ∧ q ≤ bound ∧ a ≤ q ∧ Nat.Coprime a q
      · exact ⟨q, a, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
          by simpa only [piece, ite_eq_left hp, Set.mem_ofPred_eq] using ht⟩
      · simp [piece, hp] at ht
  rw [hpieces]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases hp : 1 ≤ q ∧ q ≤ bound ∧ a ≤ q ∧ Nat.Coprime a q
  · simp only [piece, ite_eq_left hp]
    exact (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  · simp [piece, hp]



open scoped BigOperators

theorem goldbach_geometric_sum_le_inv_twice_round_distance (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]


open MeasureTheory

theorem goldbach_periodic_integral_mul_nat
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]


open Set

noncomputable def goldbach_round_tail (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0

theorem goldbach_round_tail_periodic (δ : ℝ) : Function.Periodic (goldbach_round_tail δ) 1 := by
  intro x
  simp only [goldbach_round_tail, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]

theorem goldbach_round_tail_integral (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (goldbach_round_tail δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, goldbach_round_tail δ x) = 2 / δ - 4 := by
  let g := goldbach_round_tail δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, goldbach_round_tail, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := goldbach_round_tail_periodic δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring

theorem goldbach_sum_Icc_one_eq_shifted_range {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, f j) = ∑ j ∈ Finset.range K, f (j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro j hj
    obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
    exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

theorem goldbach_exponential_shifted_range_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * ((j+1 : ℕ) : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  have hshift (j : ℕ) : e (j+1) = e 1 * e j := by
    dsimp [e]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit : ‖e 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs : (∑ j ∈ Finset.range K, e (j+1)) = e 1 * (∑ j ∈ Finset.range K, e j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hshift j)
  change ‖∑ j ∈ Finset.range K, e (j+1)‖ = ‖∑ j ∈ Finset.range K, e j‖
  rw [hs, norm_mul, hunit, one_mul]

theorem goldbach_positive_exponential_prefix_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  rw [goldbach_sum_Icc_one_eq_shifted_range]
  exact goldbach_exponential_shifted_range_norm θ K

theorem goldbach_norm_weighted_prefix_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Monotone w) (hw₀ : ∀ j, 0 ≤ w j) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K, ‖∑ j ∈ Finset.range n, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, w j • a j‖ ≤ 2 * w (K-1) * B := by
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hlead :
      ‖w (K-1) • (∑ j ∈ Finset.range K, a j)‖ ≤ w (K-1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ _)]
    exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (hw₀ _)
  have hrest :
      ‖∑ j ∈ Finset.range (K-1), (w (j+1) - w j) • (∑ i ∈ Finset.range (j+1), a i)‖
        ≤ (w (K-1)-w 0) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1),
          ‖(w (j+1)-w j) • (∑ i ∈ Finset.range (j+1), a i)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1)-w j)*B := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        have hdiff : 0 ≤ w (j+1)-w j := sub_nonneg.mpr (hw (Nat.le_succ j))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (hprefix (j+1) hj') hdiff
      _ = _ := by rw [← Finset.sum_mul, htel]
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ w (K-1)*B + (w (K-1)-w 0)*B := by exact add_le_add hlead hrest
    _ = (2*w (K-1)-w 0)*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (hw₀ 0)) hB

theorem goldbach_log_exponential_prefix_bound (θ B : ℝ) (K : ℕ) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K,
      ‖∑ j ∈ Finset.range n, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ j ∈ Finset.Icc 1 K,
      (Real.log (j : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 * Real.log (K : ℝ) * B := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  let w : ℕ → ℝ := fun j => Real.log ((j+1 : ℕ) : ℝ)
  have hw : Monotone w := by
    intro i j hij
    dsimp [w]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hw₀ (j : ℕ) : 0 ≤ w j :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 1))
  have hshifted (n : ℕ) (hn : n ≤ K) :
      ‖∑ j ∈ Finset.range n, e (j+1)‖ ≤ B := by
    calc
      _ = ‖∑ j ∈ Finset.range n, e j‖ := goldbach_exponential_shifted_range_norm θ n
      _ ≤ _ := hprefix n hn
  have hreindex :
      (∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j) =
        ∑ j ∈ Finset.range K, w j • e (j+1) := by
    simpa only [w, Complex.real_smul] using
      goldbach_sum_Icc_one_eq_shifted_range (fun j => (Real.log (j : ℝ) : ℂ) * e j) K
  change ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j‖ ≤ _
  rw [hreindex]
  by_cases hK : K = 0
  · simp [hK]
  · have hterm : w (K-1) = Real.log (K : ℝ) := by
      dsimp [w]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    simpa only [hterm] using
      goldbach_norm_weighted_prefix_le (fun j => e (j+1)) w K B hw hw₀ hB hshifted

theorem goldbach_truncated_square_comparison (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := goldbach_round_tail δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := goldbach_round_tail_integral δ hδ hd
  have hp := goldbach_round_tail_periodic δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, goldbach_round_tail]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [goldbach_round_tail, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        goldbach_periodic_integral_mul_nat g hp hiUnit m hm, hvalue]

theorem goldbach_geometric_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]

theorem goldbach_positive_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  simp_rw [goldbach_positive_exponential_prefix_norm]
  exact goldbach_geometric_tail_l2 K m hm δ hδ hd s hs hcut

theorem goldbach_log_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 2 * Real.log (K : ℝ)^2 / δ := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  let A : ℝ := Real.log (K : ℝ)^2
  have hA : 0 ≤ A := sq_nonneg _
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF A hA m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    have hgeo := goldbach_log_exponential_prefix_bound ((m : ℝ)*t) (1/(2*d)) K
      (by positivity) (fun n _ => goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) n hpos)
    have hEq : 2 * Real.log (K : ℝ) * (1/(2*d)) = Real.log (K : ℝ)/d := by
      field_simp [hn.ne']
    rw [hEq] at hgeo
    calc
      _ ≤ (Real.log (K : ℝ)/d)^2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = A * (1/d^2) := by dsimp [A]; rw [div_pow,one_div,div_eq_mul_inv]
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  calc
    _ ≤ A * (2/δ - 4) := hI
    _ ≤ A * (2/δ) := mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hA
    _ = _ := by dsimp [A]; ring

section

open scoped BigOperators

namespace GoldbachVaughan

theorem truncated_dirichlet_sum_reindex {R : Type*} [CommSemiring R]
    (n : ℕ) (a b h : ℕ → R) :
    (∑ k ∈ Finset.range (n+1), (∑ p ∈ k.divisorsAntidiagonal, a p.1 * b p.2) * h k) =
      ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d), a d * b j * h (d * j) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma' (Finset.range (n+1)) Nat.divisorsAntidiagonal
    (fun k p => a p.1 * b p.2 * h k)]
  rw [Finset.sum_sigma' (Finset.Icc 1 n) (fun d => Finset.Icc 1 (n / d))
    (fun d j => a d * b j * h (d * j))]
  refine Finset.sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩)
    (fun y _ => ⟨y.1 * y.2, (y.1, y.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, ⟨d, j⟩⟩ hx
    obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp hx
    change k ∈ Finset.range (n+1) at hk
    change (d, j) ∈ k.divisorsAntidiagonal at hp
    obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hle : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hd : 0 < d := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
    have hj : 0 < j := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
    have hdle : d ≤ n := (Nat.le_mul_of_pos_right d hj).trans (hprod ▸ hle)
    have hjle : j ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by simpa [Nat.mul_comm, hprod] using hle)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdle⟩, Finset.mem_Icc.mpr ⟨hj, hjle⟩⟩
  · rintro ⟨d, j⟩ hy
    obtain ⟨hd, hj⟩ := Finset.mem_sigma.mp hy
    change d ∈ Finset.Icc 1 n at hd
    change j ∈ Finset.Icc 1 (n/d) at hj
    obtain ⟨hdpos, _⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hj
    have hle : d * j ≤ n := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).1 hjle
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (show d*j < n+1 by omega),
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hdpos hjpos).ne'⟩⟩
  · rintro ⟨k, ⟨d, j⟩⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change d*j = k at hprod
    subst k
    rfl
  · rintro ⟨d, j⟩ _
    rfl
  · rintro ⟨k, ⟨d, j⟩⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    simp [hprod]

end GoldbachVaughan

open ArithmeticFunction

namespace GoldbachVaughan

theorem finite_dirichlet_exponential (n U : ℕ) (a b : ArithmeticFunction ℝ)
    (t : ℝ) (E : ℝ → ℂ) (ha : ∀ d > U, a d = 0) :
    (∑ k ∈ Finset.range (n+1), ((a*b) k : ℂ) * E ((k : ℝ)*t)) =
      ∑ d ∈ Finset.Icc 1 U, (a d : ℂ) *
        ∑ j ∈ Finset.Icc 1 (n/d), (b j : ℂ) * E ((j : ℝ)*((d : ℝ)*t)) := by
  let F := fun d : ℕ => (a d : ℂ) *
    ∑ j ∈ Finset.Icc 1 (n/d), (b j : ℂ) * E ((j : ℝ)*((d : ℝ)*t))
  calc
    _ = ∑ d ∈ Finset.Icc 1 n, F d := by
      simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
      rw [truncated_dirichlet_sum_reindex n (fun d => (a d : ℂ)) (fun j => (b j : ℂ))
        (fun k => E ((k : ℝ)*t))]
      apply Finset.sum_congr rfl
      intro d _
      dsimp [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      rw [show (d : ℝ) * (j : ℝ) * t = (j : ℝ) * ((d : ℝ)*t) by ring]
      ring
    _ = ∑ d ∈ Finset.Icc 1 (max n U), F d := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _))
      intro d hd hdn
      have hd₀ := (Finset.mem_Icc.mp hd).1
      have hd₁ : n < d := by
        by_contra! hp
        exact hdn (Finset.mem_Icc.mpr ⟨hd₀, hp⟩)
      simp [F, Nat.div_eq_of_lt hd₁]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_right _ _))
      intro d hd hdU
      have hd₀ := (Finset.mem_Icc.mp hd).1
      have hd₁ : U < d := by
        by_contra! hp
        exact hdU (Finset.mem_Icc.mpr ⟨hd₀, hp⟩)
      simp [ha d hd₁]

end GoldbachVaughan
end

section

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction zeta Moebius

namespace GoldbachVaughan

noncomputable def low (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ U then f m else 0, by simp⟩

noncomputable def high (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if U < m then f m else 0, by simp⟩

private theorem low_add_high (U : ℕ) (f : ArithmeticFunction ℝ) :
    low U f + high U f = f := by
  ext m
  change (if m ≤ U then f m else 0) + (if U < m then f m else 0) = f m
  by_cases h : m ≤ U
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

theorem vaughan_identity (U : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ := by
  have hμ : (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
      (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [low_add_high, coe_moebius_mul_coe_zeta]
  have hlog : (ζ : ArithmeticFunction ℝ) * (low U Λ + high U Λ) =
      ArithmeticFunction.log := by
    rw [low_add_high, zeta_mul_vonMangoldt]
  calc
    _ = low U Λ + high U Λ := (low_add_high U Λ).symm
    _ = low U Λ + (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
        (ζ : ArithmeticFunction ℝ) * high U Λ := by rw [hμ, one_mul]
    _ = _ := by rw [← hlog]; ring

theorem typeII_coefficient (U m : ℕ) :
    (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) m =
      ∑ a ∈ m.divisors.filter (fun a => U < a ∧ U < m / a),
        (∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ)) * Λ (m / a) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) a * high U Λ b),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hcoef : (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) a =
      ∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ) := by
    simp only [coe_mul_zeta_apply, Finset.sum_filter]
    rfl
  rw [hcoef]
  by_cases hlarge : U < m / a
  · by_cases haLarge : U < a
    · simp [high, hlarge, haLarge]
    · have hzero : (∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        obtain ⟨hdv, hdU⟩ := Finset.mem_filter.mp hd
        have hdA : d ≤ a := Nat.divisor_le hdv
        omega
      simp [hzero, haLarge]
  · simp [high, hlarge]


theorem typeI_coeff_zero_above_square (U m : ℕ) (hm : U^2 < m) :
    (low U (μ : ArithmeticFunction ℝ) * low U Λ) m = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
  by_cases hleft : x.1 ≤ U
  · have hright : ¬ x.2 ≤ U := by
      intro hright
      have hmul := Nat.mul_le_mul hleft hright
      rw [hprod, ← pow_two] at hmul
      exact (not_le_of_gt hm) hmul
    simp [low, hright]
  · simp [low, hleft]

theorem typeI_coeff_abs_le_log (U m : ℕ) :
    |(low U (μ : ArithmeticFunction ℝ) * low U Λ) m| ≤ Real.log (m : ℝ) := by
  rw [mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      low U Λ a * low U (μ : ArithmeticFunction ℝ) b), ← vonMangoldt_sum]
  calc
    _ ≤ ∑ a ∈ m.divisors, |low U Λ a * low U (μ : ArithmeticFunction ℝ) (m / a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      have hΛ : |low U Λ a| ≤ Λ a := by
        by_cases h : a ≤ U
        · simp [low, h, abs_of_nonneg vonMangoldt_nonneg]
        · simp [low, h, vonMangoldt_nonneg]
      have hμ : |low U (μ : ArithmeticFunction ℝ) (m / a)| ≤ 1 := by
        by_cases h : m / a ≤ U
        · have hh : |((μ (m / a) : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast abs_moebius_le_one (n := m / a)
          simpa [low, h] using hh
        · simp [low, h]
      rw [abs_mul]
      simpa only [mul_one] using
        mul_le_mul hΛ hμ (abs_nonneg _) vonMangoldt_nonneg

end GoldbachVaughan

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction zeta Moebius

namespace GoldbachVaughan

noncomputable def exponentialSum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (w k : ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)

theorem exponentialSum_continuous (n : ℕ) (w : ℕ → ℝ) : Continuous (exponentialSum n w) := by
  unfold exponentialSum
  fun_prop

theorem exponential_vaughan_difference (n U : ℕ) (t : ℝ) :
    exponentialSum n Λ t -
      exponentialSum n (fun m =>
        ∑ a ∈ m.divisors.filter (fun a => U < a ∧ U < m / a),
          (∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ)) * Λ (m / a)) t =
      exponentialSum n (low U Λ) t +
        exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k) t -
        exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) k) t := by
  simp only [exponentialSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrArg (fun f : ArithmeticFunction ℝ => f k) (vaughan_identity U)
  change Λ k = low U Λ k + (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k -
    (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) k +
    (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) k at hk
  rw [typeII_coefficient] at hk
  rw [hk]
  push_cast
  ring

end GoldbachVaughan
end


open MeasureTheory

private theorem frontierRestrictedL2Sum {ι : Type*} (t : Finset ι) (s : Set ℝ)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ t, Continuous (f i)) :
    (∫ x in s ∩ Set.Ioc (0 : ℝ) 1, ‖∑ i ∈ t, f i x‖ ^ 2) ≤
      (t.card : ℝ) * ∑ i ∈ t, ∫ x in s ∩ Set.Ioc (0 : ℝ) 1, ‖f i x‖ ^ 2 := by
  let ν := volume.restrict (s ∩ Set.Ioc (0 : ℝ) 1)
  have integrableEach (i : ι) (hi : i ∈ t) : Integrable (fun x => ‖f i x‖ ^ 2) ν :=
    (((hf i hi).norm.pow 2).intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  have continuousSum : Continuous (fun x => ∑ i ∈ t, f i x) := continuous_finsetSum _ hf
  have integrableSum : Integrable (fun x => ‖∑ i ∈ t, f i x‖ ^ 2) ν :=
    ((continuousSum.norm.pow 2).intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  have integrableMajorant :
      Integrable (fun x => (t.card : ℝ) * ∑ i ∈ t, ‖f i x‖ ^ 2) ν :=
    (integrable_finsetSum t integrableEach).const_mul _
  have pointwise (x : ℝ) :
      ‖∑ i ∈ t, f i x‖ ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, ‖f i x‖ ^ 2 := by
    calc
      _ ≤ (∑ i ∈ t, ‖f i x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          Finset.sum_mul_sq_le_sq_mul_sq t (fun _ : ι => (1 : ℝ)) (fun i => ‖f i x‖)
  change (∫ x, ‖∑ i ∈ t, f i x‖ ^ 2 ∂ν) ≤ (t.card : ℝ) * ∑ i ∈ t, ∫ x, ‖f i x‖ ^ 2 ∂ν
  calc
    _ ≤ ∫ x, (t.card : ℝ) * ∑ i ∈ t, ‖f i x‖ ^ 2 ∂ν :=
      integral_mono integrableSum integrableMajorant pointwise
    _ = _ := by rw [integral_const_mul, integral_finsetSum t integrableEach]

private theorem frontierRestrictedL2SumOfUniform {ι : Type*} (t : Finset ι) (s : Set ℝ)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ t, Continuous (f i)) (K : ℝ)
    (hK : ∀ i ∈ t, (∫ x in s ∩ Set.Ioc (0 : ℝ) 1, ‖f i x‖ ^ 2) ≤ K) :
    (∫ x in s ∩ Set.Ioc (0 : ℝ) 1, ‖∑ i ∈ t, f i x‖ ^ 2) ≤ (t.card : ℝ) ^ 2 * K := by
  refine (frontierRestrictedL2Sum t s f hf).trans ?_
  calc
    _ ≤ (t.card : ℝ) * ∑ i ∈ t, K :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK) (Nat.cast_nonneg _)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc]

namespace GoldbachVaughan

theorem weighted_restricted_energy
    (U : ℕ) (s : Set ℝ) (w : ℕ → ℝ) (g : ℕ → ℝ → ℂ) (A B : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ d ∈ Finset.Icc 1 U, |w d| ≤ A)
    (hg : ∀ d ∈ Finset.Icc 1 U, Continuous (g d))
    (hbound : ∀ d ∈ Finset.Icc 1 U,
      (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖g d t‖ ^ 2) ≤ B) :
    (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖∑ d ∈ Finset.Icc 1 U, (w d : ℂ) * g d t‖ ^ 2)
      ≤ (U : ℝ)^2 * (A^2*B) := by
  have hcard : (Finset.Icc 1 U).card = U := by
    simp
  have hsbound : ∀ d ∈ Finset.Icc 1 U, (∫ t in s ∩ Set.Ioc (0 : ℝ) 1,
      ‖(w d : ℂ) * g d t‖^2) ≤ A^2*B := by
    intro d hd
    have heq : (fun t => ‖(w d : ℂ) * g d t‖ ^ 2) =
        fun t => |w d|^2 * ‖g d t‖^2 := by
      ext t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    rw [heq, integral_const_mul]
    calc
      _ ≤ |w d|^2 * B := mul_le_mul_of_nonneg_left (hbound d hd) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hw d hd) 2) hB
  simpa only [hcard] using frontierRestrictedL2SumOfUniform (Finset.Icc 1 U) s
    (fun d t => (w d : ℂ) * g d t) (fun d hd => continuous_const.mul (hg d hd))
    (A^2*B) hsbound

theorem restricted_energy_sub_three (s : Set ℝ) (a b c : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖a t + b t - c t‖^2) ≤
      3 * ((∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖a t‖^2) +
           (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖b t‖^2) +
           (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖c t‖^2)) := by
  let ν := volume.restrict (s ∩ Set.Ioc (0 : ℝ) 1)
  have hi (f : ℝ → ℂ) (hf : Continuous f) : Integrable (fun x => ‖f x‖^2) ν :=
    ((hf.norm.pow 2).intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  calc
    _ ≤ ∫ t, (3:ℝ) * (‖a t‖^2 + ‖b t‖^2 + ‖c t‖^2) ∂ν := by
      refine integral_mono (hi _ ((ha.add hb).sub hc)) (((hi a ha).add (hi b hb)).add (hi c hc) |>.const_mul 3) ?_
      intro t
      have ht := (norm_sub_le (a t + b t) (c t)).trans
        (add_le_add (norm_add_le (a t) (b t)) le_rfl)
      refine (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans ?_
      nlinarith only [sq_nonneg (‖a t‖ - ‖b t‖), sq_nonneg (‖a t‖ - ‖c t‖),
        sq_nonneg (‖b t‖ - ‖c t‖)]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_add ((hi a ha).add (hi b hb)) (hi c hc)).trans (by
        exact congrArg (fun z : ℝ => z + ∫ t, ‖c t‖^2 ∂ν) (integral_add (hi a ha) (hi b hb)))

theorem type1_cutoff_energy_scale {x : ℝ} {U : ℕ} (hx : 0 < x)
    (hU : (U : ℝ)^2 ≤ x^(1/8 : ℝ)) :
    (((U^2 : ℕ) : ℝ)^2) * x^(2/3 : ℝ) ≤ x^(11/12 : ℝ) := by
  push_cast
  calc
    _ ≤ (x^(1/8 : ℝ))^2 * x^(2/3 : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hU 2) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      norm_num

end GoldbachVaughan

section
open MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace GoldbachVaughan

theorem type1_convolution_energies (n U : ℕ) (hn : 1 ≤ n) (hUn : U^2 ≤ n)
    (s : Set ℝ) (hs : MeasurableSet s) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hcut : ∀ d ∈ Finset.Icc 1 (U^2), ∀ t ∈ Set.Icc (0:ℝ) 1, t ∈ s →
      δ ≤ |(d : ℝ)*t - (round ((d : ℝ)*t) : ℝ)|)
    (hδInv : 1/(2*δ) = (n : ℝ)^(2/3 : ℝ))
    (hscale : (((U^2 : ℕ) : ℝ)^2) * (n : ℝ)^(2/3 : ℝ) ≤ (n : ℝ)^(11/12 : ℝ)) :
    let B := (n : ℝ)^(11/12 : ℝ) * (Real.log (n : ℝ))^2
    (∫ t in s ∩ Set.Ioc (0:ℝ) 1,
        ‖exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k) t‖^2)
      ≤ 4 * B ∧
    (∫ t in s ∩ Set.Ioc (0:ℝ) 1,
        ‖exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * low U Λ *
          (ζ : ArithmeticFunction ℝ)) k) t‖^2) ≤ B := by
  intro B
  let P := fun d j : ℕ => fun t : ℝ =>
    Complex.exp (((2 * Real.pi * (j : ℝ) * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)
  let M := fun d t => ∑ j ∈ Finset.Icc 1 (n/d), (Real.log (j : ℝ) : ℂ) * P d j t
  let Z := fun d t => ∑ j ∈ Finset.Icc 1 (n/d), P d j t
  have hmCont (d : ℕ) : Continuous (M d) := by dsimp [M,P]; fun_prop
  have hzCont (d : ℕ) : Continuous (Z d) := by dsimp [Z,P]; fun_prop
  have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnn
  have logTrunc (d : ℕ) : 0 ≤ Real.log ((n/d : ℕ) : ℝ) ∧
      Real.log ((n/d : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    by_cases hh : n/d = 0
    · simp [hh, hnlog]
    · have hp : 1 ≤ n/d := Nat.pos_of_ne_zero hh
      have hp' : (1 : ℝ) ≤ ((n/d : ℕ) : ℝ) := by exact_mod_cast hp
      exact ⟨Real.log_nonneg hp', Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self n d)⟩
  have hM (d : ℕ) (hd : d ∈ Finset.Icc 1 (U^2)) :
      (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖M d t‖^2) ≤
        4 * (Real.log (n : ℝ))^2 * (n : ℝ)^(2/3 : ℝ) := by
    have h := goldbach_log_exponential_tail_l2 (n/d) d (Finset.mem_Icc.mp hd).1
      δ hδ hδhalf s hs (hcut d hd)
    rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator hs, Set.inter_comm] at h
    refine h.trans ?_
    calc
      _ ≤ 2 * (Real.log (n : ℝ))^2 / δ :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (logTrunc d).1 (logTrunc d).2 2)
            (by norm_num)) hδ.le
      _ = _ := by rw [← hδInv]; field_simp; ring
  have hZ (d : ℕ) (hd : d ∈ Finset.Icc 1 (U^2)) :
      (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖Z d t‖^2) ≤ (n : ℝ)^(2/3 : ℝ) := by
    have h := goldbach_positive_exponential_tail_l2 (n/d) d (Finset.mem_Icc.mp hd).1
      δ hδ hδhalf s hs (hcut d hd)
    rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator hs, Set.inter_comm, hδInv] at h
    exact h
  have hUle : U ≤ U^2 := by nlinarith
  have hMoeZero (d : ℕ) (hd : U^2 < d) : low U (μ : ArithmeticFunction ℝ) d = 0 := by
    simp [low, not_le_of_gt (hUle.trans_lt hd)]
  have hMoeAbs (d : ℕ) : |low U (μ : ArithmeticFunction ℝ) d| ≤ 1 := by
    by_cases hd : d ≤ U
    · have h : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      simpa [low, hd] using h
    · simp [low, hd]
  have hEqM : exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) k) =
      fun t => ∑ d ∈ Finset.Icc 1 (U^2), (low U (μ : ArithmeticFunction ℝ) d : ℂ) * M d t := by
    funext t
    simpa only [exponentialSum, M, P, ArithmeticFunction.log_apply, mul_assoc] using
      finite_dirichlet_exponential n (U^2) (low U (μ : ArithmeticFunction ℝ))
        ArithmeticFunction.log t
        (fun x => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) hMoeZero
  have hEqZ : exponentialSum n (fun k => (low U (μ : ArithmeticFunction ℝ) * low U Λ *
      (ζ : ArithmeticFunction ℝ)) k) = fun t => ∑ d ∈ Finset.Icc 1 (U^2),
        ((low U (μ : ArithmeticFunction ℝ) * low U Λ) d : ℂ) * Z d t := by
    funext t
    unfold exponentialSum
    rw [finite_dirichlet_exponential n (U^2) (low U (μ : ArithmeticFunction ℝ) * low U Λ)
      (ζ : ArithmeticFunction ℝ) t
      (fun x => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) (typeI_coeff_zero_above_square U)]
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj₀ : j ≠ 0 := (show 0 < j from (Finset.mem_Icc.mp hj).1).ne'
    simp [P, mul_assoc, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hj₀]
  constructor
  · have h := weighted_restricted_energy (U^2) s (low U (μ : ArithmeticFunction ℝ)) M
      1 (4 * (Real.log (n : ℝ))^2 * (n : ℝ)^(2/3 : ℝ)) (by norm_num) (by positivity)
      (fun d _ => hMoeAbs d) (fun d _ => hmCont d) hM
    rw [hEqM]
    refine h.trans ?_
    dsimp [B]
    calc
      _ = (4 * (Real.log (n : ℝ))^2) * ((((U^2 : ℕ) : ℝ)^2) * (n : ℝ)^(2/3 : ℝ)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 4 * (Real.log (n : ℝ))^2)
  · have hcoeff (d : ℕ) (hd : d ∈ Finset.Icc 1 (U^2)) :
          |(low U (μ : ArithmeticFunction ℝ) * low U Λ) d| ≤ Real.log (n : ℝ) := by
      have hd₀ : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hdn : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2.trans hUn
      exact (typeI_coeff_abs_le_log U d).trans (Real.log_le_log hd₀ hdn)
    have h := weighted_restricted_energy (U^2) s
      (fun k => (low U (μ : ArithmeticFunction ℝ) * low U Λ) k) Z
      (Real.log (n : ℝ)) ((n : ℝ)^(2/3 : ℝ)) hnlog (by positivity)
      hcoeff (fun d _ => hzCont d) hZ
    rw [hEqZ]
    refine h.trans ?_
    dsimp [B]
    calc
      _ = (((U^2 : ℕ) : ℝ)^2 * (n : ℝ)^(2/3 : ℝ)) * (Real.log (n : ℝ))^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (sq_nonneg _)

end GoldbachVaughan
end


namespace GoldbachVaughan

theorem deep_arc_nearest_integer_distance
    (n H Q₁ m : ℕ) (t : ℝ) (hn : 0 < n) (hm : 0 < m) (hlimit : m ≤ Q₁)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hdeep : ¬ ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (H : ℝ) / ((q : ℝ) * (n : ℝ))) :
    (H : ℝ) / n < |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| := by
  let x : ℝ := (m : ℝ) * t
  let z : ℤ := round x
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx₀ : 0 ≤ x := mul_nonneg hmR.le ht.1
  have hx₁ : x ≤ (m : ℝ) := by
    simpa [x] using mul_le_mul_of_nonneg_left ht.2 hmR.le
  have hz₀ : 0 ≤ z := by
    have hz₀' : -(1 : ℝ) < (z : ℝ) := by
      have h := sub_half_lt_round x
      change x - 1 / 2 < (z : ℝ) at h
      linarith
    have : -(1 : ℤ) < z := by exact_mod_cast hz₀'
    omega
  have hz₁ : z ≤ m := by
    have hz₁' : (z : ℝ) < (m : ℝ) + 1 := by
      have h := round_le_add_half x
      change (z : ℝ) ≤ x + 1 / 2 at h
      linarith
    have : z < (m : ℤ) + 1 := by exact_mod_cast hz₁'
    omega
  let b := z.toNat
  have hbZ : (b : ℤ) = z := Int.toNat_of_nonneg hz₀
  have hbR : (b : ℝ) = (z : ℝ) := by exact_mod_cast hbZ
  have hbm : b ≤ m := by omega
  let d := b.gcd m
  let a := b / d
  let q := m / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hm
  have hda : d ∣ b := Nat.gcd_dvd_left b m
  have hdq : d ∣ m := Nat.gcd_dvd_right b m
  have hq₀ : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hdq) hd
  have hqm : q ≤ m := Nat.div_le_self m d
  have haq : a ≤ q := Nat.div_le_div_right hbm
  have hcoprime : Nat.Coprime a q := Nat.coprime_div_gcd_div_gcd hd
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq₀
  have hr : (a : ℝ) / (q : ℝ) = (b : ℝ) / (m : ℝ) := by
    exact Nat.cast_div_div_div_cancel_right hdq hda
  have hout : (H : ℝ) / ((q : ℝ) * n) < |t - (a : ℝ) / q| :=
    lt_of_not_ge (fun h => hdeep ⟨q, a, hq₀, hqm.trans hlimit, haq, hcoprime, h⟩)
  have hdist : (m : ℝ) * |t - (a : ℝ) / q| = |x - (z : ℝ)| := by
    rw [hr, ← hbR]
    calc
      (m : ℝ) * |t - (b : ℝ) / m| = |(m : ℝ) * (t - (b : ℝ) / m)| := by
        rw [abs_mul, abs_of_pos hmR]
      _ = |x - (b : ℝ)| := by
        congr 1
        dsimp [x]
        field_simp

  have hbase : (H : ℝ) / n ≤ (m : ℝ) * ((H : ℝ) / ((q : ℝ) * n)) := by
    have hqmR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
    rw [div_mul_eq_div_div, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hnR.le
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hqR).2
    nlinarith [mul_le_mul_of_nonneg_right hqmR (Nat.cast_nonneg H : 0 ≤ (H : ℝ))]
  change (H : ℝ) / n < |x - (z : ℝ)|
  rw [← hdist]
  exact hbase.trans_lt (mul_lt_mul_of_pos_left hout hmR)

end GoldbachVaughan


open Filter

namespace GoldbachVaughan

theorem type1_cut_parameters (n : ℕ) (hn : 1 ≤ n) :
    let x := (n : ℝ)
    let U := ⌊x ^ (1/16 : ℝ)⌋₊
    let Q₁ := ⌊x ^ (1/3 : ℝ)⌋₊
    let H : ℕ := 256 * Q₁ * (Nat.log 2 (n+2))^2
    let δ := 1 / (2*x ^ (2/3 : ℝ))
    U^2 ≤ Q₁ ∧ (U : ℝ)^2 ≤ x ^ (1/8 : ℝ) ∧
      0 < δ ∧ δ ≤ 1/2 ∧ δ ≤ (H : ℝ) / x ∧ 1 / (2*δ) = x ^ (2/3 : ℝ) := by
  intro x U Q₁ H δ
  have hx₁ : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx : 0 < x := zero_lt_one.trans_le hx₁
  have hp : 0 < x ^ (2/3 : ℝ) := Real.rpow_pos_of_pos hx _
  have hu : (U : ℝ) ≤ x ^ (1/16 : ℝ) := Nat.floor_le (by positivity)
  have husq : (U : ℝ)^2 ≤ x ^ (1/8 : ℝ) := calc
    _ ≤ (x ^ (1/16 : ℝ))^2 := by gcongr
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
  have hUQ : U^2 ≤ Q₁ := Nat.le_floor (by
    push_cast
    exact husq.trans (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)))
  have hq₁ : 1 ≤ Q₁ := Nat.le_floor (by
    push_cast
    exact Real.one_le_rpow hx₁ (by norm_num))
  have hq₁R : 1 ≤ (Q₁ : ℝ) := by exact_mod_cast hq₁
  have hq : x ^ (1/3 : ℝ) ≤ 2 * (Q₁ : ℝ) := by
    have hf : x ^ (1/3 : ℝ) < (Q₁ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hlogH : Q₁ ≤ H := by
    dsimp [H]
    calc
      Q₁ = 1 * Q₁ * 1 := by simp
      _ ≤ 256 * Q₁ * (Nat.log 2 (n+2))^2 := by
        exact mul_le_mul' (mul_le_mul' (by decide : (1 : ℕ) ≤ 256) le_rfl)
          (by simpa using pow_le_pow_left' hlog 2)
  have hlogHR : (Q₁ : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlogH
  have hδn : δ * x = x ^ (1/3 : ℝ) / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_eq_div_iff (show 2*x ^ (2/3 : ℝ) ≠ 0 by positivity) (by norm_num)).2
    rw [show x ^ (1/3 : ℝ) * (2 * x ^ (2/3 : ℝ)) =
      2 * (x ^ (2/3 : ℝ) * x ^ (1/3 : ℝ)) by ring,
      ← Real.rpow_add hx]
    norm_num [mul_comm]
  refine ⟨hUQ, husq, by dsimp [δ]; positivity, ?_, ?_, ?_⟩
  · dsimp [δ]
    have hxp : 1 ≤ x ^ (2/3 : ℝ) := Real.one_le_rpow hx₁ (by norm_num)
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  · apply (le_div_iff₀ hx).2
    rw [hδn]
    linarith
  · dsimp [δ]
    field_simp

theorem eventually_type1_power_budget (C e : ℝ) (hC : 0 < C) (he : 0 < e) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ)^ (23/24 : ℝ) * Real.log (n : ℝ)^2 ≤ e * (n : ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := 1/24) 2 (by norm_num)).bound
    (div_pos he hC)
  have hbound : ∀ᶠ x : ℝ in atTop, C*x^(23/24 : ℝ) * Real.log x^2 ≤ e*x := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hl hx₁
    have hx : 0 < x := zero_lt_one.trans_le hx₁
    have hpow : 0 ≤ x^(1/24 : ℝ) := by positivity
    have hlog : Real.log x^2 ≤ (e/C)*x^(1/24 : ℝ) := by
      have hrealPow : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
      apply (le_abs_self _).trans
      simpa only [hrealPow, Real.norm_eq_abs,
        abs_of_nonneg hpow] using hl
    calc
      _ ≤ C*x^(23/24 : ℝ) * ((e/C)*x^(1/24 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = e * (x^(23/24 : ℝ) * x^(1/24 : ℝ)) := by field_simp
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  refine ⟨⌈X⌉₊, fun n hn => hX _ ((Nat.le_ceil X).trans ?_)⟩
  exact_mod_cast hn

end GoldbachVaughan


open Filter
open scoped Topology

private theorem frontierTypeIPowerScalars (x L : ℝ) (hx : 1 ≤ x) :
    0 ≤ x ^ (11 / 12 : ℝ) * L ^ 2 ∧
    x ^ (11 / 12 : ℝ) * L ^ 2 ≤ x * L ^ 2 ∧
    0 ≤ x ^ (23 / 24 : ℝ) * L ^ 2 ∧
    (x ^ (23 / 24 : ℝ) * L ^ 2) ^ 2 = (x * L ^ 2) * (x ^ (11 / 12 : ℝ) * L ^ 2) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hle : x ^ (11 / 12 : ℝ) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (11 / 12 : ℝ) ≤ 1)
  have hmul : (x ^ (23 / 24 : ℝ)) ^ 2 = x ^ (11 / 12 : ℝ) * x := by
    calc
      _ = (x ^ (23 / 24 : ℝ)) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ ((23 / 24 : ℝ) * ((2 : ℕ) : ℝ)) := (Real.rpow_mul hxp.le _ _).symm
      _ = x ^ ((11 / 12 : ℝ) + 1) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hxp, Real.rpow_one]
  refine ⟨by positivity, mul_le_mul_of_nonneg_right hle (sq_nonneg _), by positivity, ?_⟩
  rw [mul_pow, hmul]
  ring

private theorem frontierTypeIAsymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      60 * (n : ℝ) ^ (23 / 24 : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ ε * (n : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 24 : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 24)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_natCast] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := hlim.eventually_lt_const (by positivity : 0 < ε / 60)
  apply eventually_atTop.1
  filter_upwards [he, eventually_ge_atTop 1] with n hsmall hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n : ℝ) ^ 2 ≤ (ε / 60) * (n : ℝ) ^ (1 / 24 : ℝ) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hn' _)).mp hsmall.le
  have hpow : (n : ℝ) ^ (23 / 24 : ℝ) * (n : ℝ) ^ (1 / 24 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hn']
    norm_num
  calc
    _ ≤ 60 * (n : ℝ) ^ (23 / 24 : ℝ) * ((ε / 60) * (n : ℝ) ^ (1 / 24 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = ε * ((n : ℝ) ^ (23 / 24 : ℝ) * (n : ℝ) ^ (1 / 24 : ℝ)) := by ring
    _ = _ := by rw [hpow]



open MeasureTheory

private theorem frontierRestrictedProductHolder (s : Set ℝ) (hs : MeasurableSet s)
    (a b p : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hpNorm : ∀ t, ‖p t‖ = 1) :
    ‖∫ t in (0 : ℝ)..1, s.indicator (fun x => a x * b x * p x) t‖ ≤
      Real.sqrt (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖a t‖ ^ 2) *
      Real.sqrt (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖b t‖ ^ 2) := by
  let ν := volume.restrict (s ∩ Set.Ioc (0 : ℝ) 1)
  let A := fun x => a x * b x * p x
  let u := fun t => ‖a t‖
  let v := fun t => ‖b t‖
  have hu : Continuous u := ha.norm
  have hv : Continuous v := hb.norm
  have huLp : MemLp u (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
      (((hu.pow 2).intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right)
  have hvLp : MemLp v (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mpr
      (((hv.pow 2).intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => norm_nonneg (a t))
    (Filter.Eventually.of_forall fun t => norm_nonneg (b t)) huLp hvLp
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_indicator hs, Measure.restrict_restrict hs]
  change ‖∫ t, A t ∂ν‖ ≤
    Real.sqrt (∫ t, u t ^ 2 ∂ν) * Real.sqrt (∫ t, v t ^ 2 ∂ν)
  calc
    _ ≤ ∫ t, ‖A t‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ t, u t * v t ∂ν := by
      apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp [A, u, v, hpNorm]
    _ ≤ _ := by simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hHolder


private theorem frontierMaskedSquareBudget (s : Set ℝ) (hs : MeasurableSet s)
    (a b p : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (hp : Continuous p)
    (hpNorm : ∀ t, ‖p t‖ = 1) (X Y Z : ℝ)
    (hY : 0 ≤ Y) (hYX : Y ≤ X) (hZ : 0 ≤ Z) (hZsq : Z ^ 2 = X * Y)
    (hErr : (∫ t in s ∩ Set.Ioc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) ≤ 21 * Y)
    (hFull : (∫ t in (0 : ℝ)..1, ‖a t‖ ^ 2) ≤ 2 * X) :
    ‖(∫ t in (0 : ℝ)..1, s.indicator (fun u => a u ^ 2 * p u) t) -
      (∫ t in (0 : ℝ)..1, s.indicator (fun u => b u ^ 2 * p u) t)‖ ≤ 60 * Z := by
  let ν := volume.restrict (s ∩ Set.Ioc (0 : ℝ) 1)
  let u := fun t => ‖a t‖ ^ 2
  let v := fun t => ‖a t - b t‖ ^ 2
  let w := fun t => ‖a t + b t‖ ^ 2
  let A := ∫ t, v t ∂ν
  let B := ∫ t, w t ∂ν
  let U := ∫ t, u t ∂ν
  have hu : Continuous u := ha.norm.pow 2
  have hv : Continuous v := (ha.sub hb).norm.pow 2
  have hw : Continuous w := (ha.add hb).norm.pow 2
  have hUi : Integrable u ν := (hu.intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  have hAi : Integrable v ν := (hv.intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  have hBi : Integrable w ν := (hw.intervalIntegrable (0 : ℝ) 1).1.mono_set Set.inter_subset_right
  have hUm : U ≤ 2 * X := by
    refine le_trans ?_ hFull
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_mono_set (hu.intervalIntegrable (0 : ℝ) 1).1
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖a t‖))
      (Filter.Eventually.of_forall fun t ht => ht.2)
  have hB : B ≤ 58 * X := by
    have hPt (t : ℝ) : w t ≤ 8 * u t + 2 * v t := by
      have ht : ‖a t + b t‖ ≤ 2 * ‖a t‖ + ‖a t - b t‖ := by
        calc
          _ = ‖(2 : ℂ) * a t - (a t - b t)‖ := congrArg norm (by ring)
          _ ≤ ‖(2 : ℂ) * a t‖ + ‖a t - b t‖ := norm_sub_le _ _
          _ = _ := by norm_num [norm_mul]
      change ‖a t + b t‖ ^ 2 ≤ 8 * ‖a t‖ ^ 2 + 2 * ‖a t - b t‖ ^ 2
      calc
        _ ≤ (2 * ‖a t‖ + ‖a t - b t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
        _ ≤ _ := by nlinarith only [sq_nonneg (2 * ‖a t‖ - ‖a t - b t‖)]
    have hInt : B ≤ 8 * U + 2 * A := by
      have hm := integral_mono hBi ((hUi.const_mul 8).add (hAi.const_mul 2)) hPt
      change B ≤ (∫ t, 8 * u t + 2 * v t ∂ν) at hm
      rw [integral_add (hUi.const_mul 8) (hAi.const_mul 2), integral_const_mul,
        integral_const_mul] at hm
      exact hm
    have hAm : A ≤ 21 * Y := hErr
    linarith only [hInt, hUm, hAm, hYX]
  have hA₀ : 0 ≤ A := integral_nonneg (fun t => sq_nonneg ‖a t - b t‖)
  have hB₀ : 0 ≤ B := integral_nonneg (fun t => sq_nonneg ‖a t + b t‖)
  have hP : A * B ≤ (60 * Z) ^ 2 := by
    calc
      _ ≤ (21 * Y) * (58 * X) := mul_le_mul hErr hB hB₀ (by positivity)
      _ = 1218 * Z ^ 2 := by rw [hZsq]; ring
      _ ≤ _ := by nlinarith only [sq_nonneg Z]
  have factor :
      (∫ t in (0 : ℝ)..1, s.indicator (fun x => a x ^ 2 * p x) t) -
        (∫ t in (0 : ℝ)..1, s.indicator (fun x => b x ^ 2 * p x) t) =
        ∫ t in (0 : ℝ)..1, s.indicator (fun x => (a x - b x) * (a x + b x) * p x) t := by
    have hIA : IntervalIntegrable (fun t => a t ^ 2 * p t) volume (0 : ℝ) 1 :=
      ((ha.pow 2).mul hp).intervalIntegrable (0 : ℝ) 1
    have hIB : IntervalIntegrable (fun t => b t ^ 2 * p t) volume (0 : ℝ) 1 :=
      ((hb.pow 2).mul hp).intervalIntegrable (0 : ℝ) 1
    have hIA' : IntervalIntegrable (s.indicator (fun x => a x ^ 2 * p x)) volume (0 : ℝ) 1 :=
      ⟨hIA.1.indicator hs, hIA.2.indicator hs⟩
    have hIB' : IntervalIntegrable (s.indicator (fun x => b x ^ 2 * p x)) volume (0 : ℝ) 1 :=
      ⟨hIB.1.indicator hs, hIB.2.indicator hs⟩
    rw [← intervalIntegral.integral_sub hIA' hIB']
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases hts : t ∈ s
    · simp only [Set.indicator_of_mem hts]
      ring
    · simp only [Set.indicator_of_notMem hts, sub_zero]
  rw [factor]
  calc
    _ ≤ Real.sqrt A * Real.sqrt B :=
      frontierRestrictedProductHolder s hs (fun t => a t - b t) (fun t => a t + b t) p
        (ha.sub hb) (ha.add hb) hpNorm
    _ = Real.sqrt (A * B) := (Real.sqrt_mul hA₀ B).symm
    _ ≤ Real.sqrt ((60 * Z) ^ 2) := Real.sqrt_le_sqrt hP
    _ = _ := Real.sqrt_sq (by positivity)


private noncomputable def frontierTypeIExpSum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * parsevalPhase ((k : ℝ) * t)

private noncomputable def frontierTypeIShortMangoldt (U k : ℕ) : ℝ :=
  if k ≤ U then ArithmeticFunction.vonMangoldt k else 0

private theorem frontierTypeIMangoldtSqLe {n k : ℕ} (hk : k ≤ n) :
    (ArithmeticFunction.vonMangoldt k) ^ 2 ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) := by
    by_cases hk0 : k = 0
    · simpa [hk0] using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)
  exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
    (ArithmeticFunction.vonMangoldt_le_log.trans hlog) _

private theorem frontierTypeIMangoldtEnergy (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (0 : ℝ)..1, ‖frontierTypeIExpSum n ArithmeticFunction.vonMangoldt t‖ ^ 2) ≤
      2 * (n : ℝ) * Real.log (n : ℝ) ^ 2 := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k ^ 2 :=
      frontierDeepParseval n ArithmeticFunction.vonMangoldt
    _ ≤ ∑ _k ∈ Finset.range (n + 1), Real.log (n : ℝ) ^ 2 :=
      Finset.sum_le_sum fun k hk =>
        frontierTypeIMangoldtSqLe (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = ((n : ℝ) + 1) * Real.log (n : ℝ) ^ 2 := by simp
    _ ≤ _ := by
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact mul_le_mul_of_nonneg_right (by linarith only [hnR]) (sq_nonneg _)

private theorem frontierTypeIMaskedEnergyLe (s : Set ℝ) (hs : MeasurableSet s)
    (n : ℕ) (w : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun x => ‖frontierTypeIExpSum n w x‖ ^ 2) t) ≤
      ∫ t in (0 : ℝ)..1, ‖frontierTypeIExpSum n w t‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖frontierTypeIExpSum n w t‖ ^ 2
  have hf : Continuous f := by
    dsimp only [f, frontierTypeIExpSum, parsevalPhase]
    fun_prop
  have hi : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hf.intervalIntegrable (0 : ℝ) 1).1
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ t, s.indicator f t ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤
    ∫ t, f t ∂volume.restrict (Set.Ioc (0 : ℝ) 1)
  refine integral_mono (hi.indicator hs) hi fun t => ?_
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    exact sq_nonneg _

private theorem frontierTypeIMaskedTruncatedBound (s : Set ℝ) (hs : MeasurableSet s)
    (n U : ℕ) :
    (∫ t in (0 : ℝ)..1,
      s.indicator (fun x => ‖frontierTypeIExpSum n (frontierTypeIShortMangoldt U) x‖ ^ 2) t) ≤
      ((U : ℝ) + 1) * Real.log (n : ℝ) ^ 2 := by
  let T := (Finset.range (n + 1)).filter (· ≤ U)
  have hT : T ⊆ Finset.range (U + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  have hsum :
      (∑ k ∈ Finset.range (n + 1), frontierTypeIShortMangoldt U k ^ 2) =
        ∑ k ∈ T, ArithmeticFunction.vonMangoldt k ^ 2 := by
    dsimp only [T]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ≤ U <;> simp [frontierTypeIShortMangoldt, hk]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖frontierTypeIExpSum n (frontierTypeIShortMangoldt U) t‖ ^ 2 :=
      frontierTypeIMaskedEnergyLe s hs n (frontierTypeIShortMangoldt U)
    _ = ∑ k ∈ Finset.range (n + 1), frontierTypeIShortMangoldt U k ^ 2 :=
      frontierDeepParseval n (frontierTypeIShortMangoldt U)
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k ^ 2 := hsum
    _ ≤ ∑ _k ∈ T, Real.log (n : ℝ) ^ 2 :=
      Finset.sum_le_sum fun k hk =>
        frontierTypeIMangoldtSqLe (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
    _ ≤ ∑ _k ∈ Finset.range (U + 1), Real.log (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp

private theorem frontierTypeIMaskedShortEnergy (s : Set ℝ) (hs : MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n) :
    let U := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊
    (∫ t in (0 : ℝ)..1,
      s.indicator (fun x => ‖frontierTypeIExpSum n (frontierTypeIShortMangoldt U) x‖ ^ 2) t) ≤
      2 * (n : ℝ) ^ (11 / 12 : ℝ) * Real.log (n : ℝ) ^ 2 := by
  intro U
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hU : (U : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hOne : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hPow : (n : ℝ) ^ (1 / 16 : ℝ) ≤ (n : ℝ) ^ (11 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  exact (frontierTypeIMaskedTruncatedBound s hs n U).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hU, hOne, hPow]) (sq_nonneg _))


theorem PEqualNP.Outside.L_goldbach_frontier_vaughan_type1_elimination :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let typeII := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Jdeep n Λ Λ - Jdeep n (typeII n) (typeII n)‖ ≤ e * (n : ℝ) := by
  intro E S Q Q₁ H wideArcs Λ μ U typeII Jdeep e he
  obtain ⟨N, hN⟩ := GoldbachVaughan.eventually_type1_power_budget 60 e (by norm_num) he
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  let s := (wideArcs n)ᶜ
  have hs : MeasurableSet s := (frontierArc_measurable n (Q₁ n) (H n)).compl
  let δ : ℝ := 1 / (2 * (n : ℝ)^(2/3 : ℝ))
  obtain ⟨hUQ, hUsq, hδ, hδhalf, hδle, hδInv⟩ := GoldbachVaughan.type1_cut_parameters n hn1
  have hUn : (U n)^2 ≤ n := by
    have hp : ((U n : ℝ)^2) ≤ (n : ℝ) :=
      hUsq.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1/8:ℝ) ≤ 1))
    exact_mod_cast hp
  have hcut (d : ℕ) (hd : d ∈ Finset.Icc 1 ((U n)^2))
      (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hts : t ∈ s) :
      δ ≤ |(d:ℝ)*t - (round ((d:ℝ)*t) : ℝ)| := by
    have hd₀ := (Finset.mem_Icc.mp hd).1
    have hdQ := (Finset.mem_Icc.mp hd).2.trans hUQ
    exact hδle.trans (GoldbachVaughan.deep_arc_nearest_integer_distance
      n (H n) (Q₁ n) d t hn0 hd₀ hdQ ht hts).le
  have hscl := GoldbachVaughan.type1_cutoff_energy_scale (U := U n)
    (zero_lt_one.trans_le hnR) hUsq
  obtain ⟨hM, hZ⟩ := GoldbachVaughan.type1_convolution_energies n (U n) hn1 hUn
    s hs δ hδ hδhalf hcut hδInv hscl
  let a₀ := GoldbachVaughan.exponentialSum n (GoldbachVaughan.low (U n) ArithmeticFunction.vonMangoldt)
  let b₀ := GoldbachVaughan.exponentialSum n (fun k => (GoldbachVaughan.low (U n)
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * ArithmeticFunction.log) k)
  let c₀ := GoldbachVaughan.exponentialSum n (fun k => (GoldbachVaughan.low (U n)
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
    GoldbachVaughan.low (U n) ArithmeticFunction.vonMangoldt *
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) k)
  have hshort := frontierTypeIMaskedShortEnergy s hs n hn1
  dsimp only at hshort
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator hs, Set.inter_comm] at hshort
  change (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖a₀ t‖^2) ≤
    2 * (n : ℝ)^(11/12 : ℝ) * (Real.log (n : ℝ))^2 at hshort
  have hshort' : (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖a₀ t‖^2) ≤
      2 * (n : ℝ)^(11/12 : ℝ)*(Real.log (n : ℝ))^2 := by
    simpa only [mul_assoc] using hshort
  have hFull := frontierTypeIMangoldtEnergy n hn1
  change (∫ t in (0 : ℝ)..1, ‖S n Λ t‖^2) ≤
    2 * (n : ℝ) * (Real.log (n : ℝ))^2 at hFull
  let X := (n : ℝ) * (Real.log (n : ℝ))^2
  let Y := (n : ℝ)^(11/12 : ℝ) * (Real.log (n : ℝ))^2
  let Z := (n : ℝ)^(23/24 : ℝ) * (Real.log (n : ℝ))^2
  have hErr : (∫ t in s ∩ Set.Ioc (0:ℝ) 1,
      ‖S n Λ t - S n (typeII n) t‖^2) ≤ 21*Y := by
    simp_rw [show ∀ t, S n Λ t - S n (typeII n) t = a₀ t + b₀ t - c₀ t from
      fun t => GoldbachVaughan.exponential_vaughan_difference n (U n) t]
    refine (GoldbachVaughan.restricted_energy_sub_three s a₀ b₀ c₀
      (GoldbachVaughan.exponentialSum_continuous ..)
      (GoldbachVaughan.exponentialSum_continuous ..)
      (GoldbachVaughan.exponentialSum_continuous ..)).trans ?_
    change (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖b₀ t‖^2) ≤ 4*Y at hM
    change (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖c₀ t‖^2) ≤ Y at hZ
    have hs' : (∫ t in s ∩ Set.Ioc (0:ℝ) 1, ‖a₀ t‖^2) ≤ 2*Y := by
      simpa only [Y, mul_assoc] using hshort'
    linarith only [hs', hM, hZ]
  obtain ⟨hY, hYX, hZnonneg, hZsq⟩ := frontierTypeIPowerScalars (n : ℝ) (Real.log (n : ℝ)) hnR
  let p := fun t : ℝ => E (-(n:ℝ)*t)
  have hp : Continuous p := by dsimp [p, E]; fun_prop
  have hpnorm (t : ℝ) : ‖p t‖ = 1 := by
    dsimp [p, E]
    simp [Complex.norm_exp, Complex.mul_re]
  have henergyFull : (∫ t in (0 : ℝ)..1, ‖S n Λ t‖^2) ≤ 2*X := by
    dsimp [X]
    simpa only [mul_assoc] using hFull
  have hfinal := frontierMaskedSquareBudget s hs (S n Λ) (S n (typeII n)) p
    (GoldbachVaughan.exponentialSum_continuous ..)
    (GoldbachVaughan.exponentialSum_continuous ..) hp hpnorm
    X Y Z hY hYX hZnonneg hZsq hErr henergyFull
  apply (show ‖Jdeep n Λ Λ - Jdeep n (typeII n) (typeII n)‖ ≤ 60*Z from by
    simpa only [Jdeep, s, p, pow_two] using hfinal).trans
  simpa only [Z, mul_assoc] using hN n ((le_max_left _ _).trans hn)
