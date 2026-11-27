import Mathlib

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Conjectures.Goldbach.TernaryCirclePositivity_aux

noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma phase_cont : Continuous phase := by
  change Continuous (fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I))
  fun_prop

theorem finiteParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t))
    ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1
      MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * phase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1
    MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, phase (x + y) = phase x * phase y := by
    intro x y
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous phase := by
    unfold phase
    fun_prop
  have hphase_exp : ∀ m : ℤ,
      Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, phase (m : ℝ) = 1 := by
    intro m
    unfold phase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (phase x) = phase (-x) := by
    intro x
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ,
      intervalIntegral (fun t : ℝ => phase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => phase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1,
          Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold phase
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
        simpa only [phase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * phase (a * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
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
    have hmul : phase (-((k : ℝ) * t)) * phase ((j : ℝ) * t) =
        phase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * phase (-((k : ℝ) * t))) *
          ((w j : ℂ) * phase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (phase (-((k : ℝ) * t)) * phase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum T (fun k _ => continuous_finsetSum T
      (fun j _ => continuous_const.mul (hphase_cont.comp
        (continuous_const.mul continuous_id))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) *
          (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
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
          ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) :=
        Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1
      MeasureTheory.volume = (intervalIntegral z (0 : ℝ) 1
      MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1
        MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1
          MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by
      rw [hmain]
      exact Complex.ofReal_re _


theorem phase_add (u v : ℝ) : phase (u + v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]


theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume =
        intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]


end Conjectures.Goldbach.TernaryCirclePositivity_aux

namespace Conjectures.Goldbach.TernaryCirclePositivity_aux

theorem zero_from_triples (w : ℕ → ℝ) (n Y : ℕ)
    (hn : ∀ p q r : ℕ, p + q + r = n → w p * w q * w r = 0) :
    (∫ t in (0 : ℝ)..1,
      (∑ k ∈ Finset.range (Y + 1), (w k : ℂ) * phase ((k : ℝ) * t)) ^ 3 *
        phase (-(n : ℝ) * t)) = 0 := by
  let I := Finset.range (Y + 1)
  let term := fun (p q r : ℕ) (t : ℝ) =>
    ((w p : ℂ) * (w q : ℂ) * (w r : ℂ)) *
      phase (((((p : ℤ) + q + r - n : ℤ) : ℝ)) * t)
  have hcont (p q r : ℕ) : Continuous (term p q r) := by
    dsimp [term, phase]
    fun_prop
  have hpoint (t : ℝ) :
      (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) ^ 3 *
          phase (-(n : ℝ) * t) =
        ∑ p ∈ I, ∑ q ∈ I, ∑ r ∈ I, term p q r t := by
    rw [show (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) ^ 3 =
        ((∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) *
          (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t))) *
          (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) by ring]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ =>
        Finset.sum_congr rfl (fun r _ => ?_)))
    dsimp [term]
    have hE : phase ((p : ℝ) * t) * phase ((q : ℝ) * t) *
        phase ((r : ℝ) * t) * phase (-(n : ℝ) * t) =
        phase (((((p : ℤ) + q + r - n : ℤ) : ℝ)) * t) := by
      rw [← phase_add, ← phase_add, ← phase_add]
      congr 1
      push_cast
      ring
    calc
      (w r : ℂ) * phase ((r : ℝ) * t) *
          ((w q : ℂ) * phase ((q : ℝ) * t)) *
          ((w p : ℂ) * phase ((p : ℝ) * t)) *
          phase (-(n : ℝ) * t)
          = ((w p : ℂ) * (w q : ℂ) * (w r : ℂ)) *
              (phase ((p : ℝ) * t) * phase ((q : ℝ) * t) *
                phase ((r : ℝ) * t) * phase (-(n : ℝ) * t)) := by ring
      _ = ((w p : ℂ) * (w q : ℂ) * (w r : ℂ)) *
            phase (((((p : ℤ) + q + r - n : ℤ) : ℝ)) * t) := by rw [hE]
  change (∫ t in (0 : ℝ)..1,
    (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) ^ 3 *
      phase (-(n : ℝ) * t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun p _ =>
    (continuous_finsetSum I (fun q _ =>
      (continuous_finsetSum I (fun r _ => hcont p q r)))).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro p hp
  rw [intervalIntegral.integral_finsetSum (fun q _ =>
    (continuous_finsetSum I (fun r _ => hcont p q r)).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro q hq
  rw [intervalIntegral.integral_finsetSum (fun r _ => (hcont p q r).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro r hr
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases hsum : (p : ℤ) + q + r - n = 0
  · have hnat : p + q + r = n := by omega
    have hz : w p * w q * w r = 0 := hn p q r hnat
    simp only [hsum, ite_true, mul_one]
    exact_mod_cast hz
  · simp [hsum]

end Conjectures.Goldbach.TernaryCirclePositivity_aux

namespace Conjectures.Goldbach

open Conjectures.Goldbach.TernaryCirclePositivity_aux

theorem TernaryCirclePositivity :
    (let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0;
     let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
     let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t);
     ∀ (n : ℕ) (A : Set ℝ) (U : ℝ), MeasurableSet A → 0 ≤ U →
       (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S n t‖ ≤ U) →
       U * (∑ k ∈ Finset.range (n + 1), (w k)^2) <
         (intervalIntegral (A.indicator (fun t => (S n t)^3 * E (-(n : ℝ) * t)))
           (0 : ℝ) 1 MeasureTheory.volume).re →
       ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n) := by
  dsimp only
  intro n A U hA hU hsup hfloor
  classical
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  let S : ℕ → ℝ → ℂ := fun n t =>
    ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * phase ((k : ℝ) * t)
  have hsup' : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S n t‖ ≤ U := by
    simpa [S, phase, w] using hsup
  have hfloor' : U * (∑ k ∈ Finset.range (n + 1), (w k)^2) <
      (intervalIntegral (A.indicator (fun t => (S n t)^3 * phase (-(n : ℝ) * t)))
        (0 : ℝ) 1 MeasureTheory.volume).re := by
    simpa [S, phase, w] using hfloor
  by_contra hno
  have hno_prod : ∀ p q r : ℕ, p + q + r = n → w p * w q * w r = 0 := by
    intro p q r hsum
    by_contra hprod
    have hp : Nat.Prime p := by
      by_contra hp
      have : w p = 0 := by simp [w, hp]
      simp [this] at hprod
    have hq : Nat.Prime q := by
      by_contra hq
      have : w q = 0 := by simp [w, hq]
      simp [this] at hprod
    have hr : Nat.Prime r := by
      by_contra hr
      have : w r = 0 := by simp [w, hr]
      simp [this] at hprod
    exact hno ⟨p, q, r, hp, hq, hr, hsum⟩
  let F : ℝ → ℂ := fun t => (S n t)^3 * phase (-(n : ℝ) * t)
  have hcontS : Continuous (S n) := by
    dsimp [S]
    exact continuous_finsetSum (Finset.range (n + 1)) (fun k _ =>
      continuous_const.mul (phase_cont.comp (by fun_prop)))
  have hcontF : Continuous F := by
    dsimp [F]
    exact (hcontS.pow 3).mul (phase_cont.comp (by fun_prop))
  have hintF : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) 1 :=
    hcontF.intervalIntegrable _ _
  have hfull : intervalIntegral F (0 : ℝ) 1 MeasureTheory.volume = 0 := by
    simpa [F, S] using zero_from_triples w n n hno_prod
  have hsplit : intervalIntegral (A.indicator F) (0 : ℝ) 1 MeasureTheory.volume +
      intervalIntegral (Aᶜ.indicator F) (0 : ℝ) 1 MeasureTheory.volume = 0 := by
    rw [indicator_integral_split (f := F) (s := A) hA (a := (0 : ℝ)) (b := (1 : ℝ)) hintF, hfull]
  have hAcomp : (intervalIntegral (A.indicator F) (0 : ℝ) 1 MeasureTheory.volume).re =
      -(intervalIntegral (Aᶜ.indicator F) (0 : ℝ) 1 MeasureTheory.volume).re := by
    have := congrArg Complex.re hsplit
    simp only [Complex.add_re, Complex.zero_re] at this
    linarith
  have hcomp_three_int : IntervalIntegrable
      (Aᶜ.indicator (fun t => ‖F t‖)) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨(hcontF.norm.intervalIntegrable _ _).1.indicator hA.compl,
      (hcontF.norm.intervalIntegrable _ _).2.indicator hA.compl⟩
  have hcomp_rhs_int : IntervalIntegrable
      (Aᶜ.indicator (fun t => U * ‖S n t‖ ^ 2)) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨((continuous_const.mul (hcontS.norm.pow 2)).intervalIntegrable _ _).1.indicator hA.compl,
      ((continuous_const.mul (hcontS.norm.pow 2)).intervalIntegrable _ _).2.indicator hA.compl⟩
  have hsq_full_int : IntervalIntegrable (fun t => ‖S n t‖ ^ 2)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (hcontS.norm.pow 2).intervalIntegrable _ _
  have hsq_comp_int : IntervalIntegrable
      (Aᶜ.indicator (fun t => ‖S n t‖ ^ 2)) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨(hsq_full_int.1.indicator hA.compl), (hsq_full_int.2.indicator hA.compl)⟩
  have hcomp_le : intervalIntegral (Aᶜ.indicator (fun t => ‖F t‖))
      (0 : ℝ) 1 MeasureTheory.volume ≤
      intervalIntegral (Aᶜ.indicator (fun t => U * ‖S n t‖ ^ 2))
        (0 : ℝ) 1 MeasureTheory.volume := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hcomp_three_int hcomp_rhs_int
    intro t ht
    by_cases hta : t ∈ Aᶜ
    · rw [Set.indicator_of_mem hta, Set.indicator_of_mem hta]
      have hnormF : ‖F t‖ = ‖S n t‖ ^ 3 := by
        dsimp [F]
        rw [norm_mul, norm_pow]
        have hphase : ‖phase (-(n : ℝ) * t)‖ = 1 := by
          simpa [phase, mul_assoc] using Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * (n : ℝ) * t))
        rw [hphase, mul_one]
      rw [hnormF]
      have hle : ‖S n t‖ ≤ U := hsup' t ht hta
      calc
        ‖S n t‖ ^ 3 = ‖S n t‖ ^ 2 * ‖S n t‖ := by ring
        _ ≤ ‖S n t‖ ^ 2 * U := by gcongr
        _ = U * ‖S n t‖ ^ 2 := by ring
    · rw [Set.indicator_of_notMem hta, Set.indicator_of_notMem hta]
  have hcomp_sq_le : intervalIntegral (Aᶜ.indicator (fun t => U * ‖S n t‖ ^ 2))
      (0 : ℝ) 1 MeasureTheory.volume ≤ U * (∑ k ∈ Finset.range (n + 1), (w k)^2) := by
    have hconst : (Aᶜ.indicator (fun t => U * ‖S n t‖ ^ 2)) =
        fun t => U * (Aᶜ.indicator (fun t => ‖S n t‖ ^ 2) t) := by
      funext t
      by_cases ht : t ∈ Aᶜ <;> simp [ht]
    rw [hconst, intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hU
    calc
      intervalIntegral (Aᶜ.indicator (fun t => ‖S n t‖ ^ 2))
          (0 : ℝ) 1 MeasureTheory.volume ≤
          intervalIntegral (fun t => ‖S n t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          hsq_comp_int hsq_full_int
        intro t ht
        by_cases hta : t ∈ Aᶜ
        · rw [Set.indicator_of_mem hta]
        · rw [Set.indicator_of_notMem hta]
          positivity
      _ = ∑ k ∈ Finset.range (n + 1), (w k)^2 := finiteParseval n w
  have hcomp_norm : ‖intervalIntegral (Aᶜ.indicator F) (0 : ℝ) 1 MeasureTheory.volume‖ ≤
      U * (∑ k ∈ Finset.range (n + 1), (w k)^2) := by
    calc
      ‖intervalIntegral (Aᶜ.indicator F) (0 : ℝ) 1 MeasureTheory.volume‖ ≤
          intervalIntegral (fun t => ‖Aᶜ.indicator F t‖) (0 : ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
      _ = intervalIntegral (Aᶜ.indicator (fun t => ‖F t‖)) (0 : ℝ) 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        by_cases hta : t ∈ Aᶜ <;> simp [hta]
      _ ≤ intervalIntegral (Aᶜ.indicator (fun t => U * ‖S n t‖ ^ 2))
          (0 : ℝ) 1 MeasureTheory.volume := hcomp_le
      _ ≤ U * (∑ k ∈ Finset.range (n + 1), (w k)^2) := hcomp_sq_le
  have hbound : (intervalIntegral (A.indicator F) (0 : ℝ) 1 MeasureTheory.volume).re ≤
      U * (∑ k ∈ Finset.range (n + 1), (w k)^2) := by
    rw [hAcomp]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans hcomp_norm
  linarith

end Conjectures.Goldbach
