import Mathlib

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.MinorSupFourthMoment_aux

noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem finiteParseval :
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

private theorem maskedBessel :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t); ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ), MeasurableSet A → (∑ m ∈ Finset.range M, ‖intervalIntegral (A.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤ intervalIntegral (A.indicator (fun t => ‖S X u t‖^4)) (0 : ℝ) 1 MeasureTheory.volume := by
  intro E S X M u A hA
  let f := A.indicator (fun t => (S X u t)^2)
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hc : Continuous (fun t => (S X u t)^2) := by dsimp [S,E]; fun_prop
  have hmem : MemLp f 2 μ := by
    apply MemLp.indicator hA.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have hcoeff (m : ℕ) : fourierCoeffOn zero_lt_one f (m:ℤ) =
      ∫ t in (0:ℝ)..1, A.indicator (fun t => (S X u t)^2 * E (-(m:ℝ)*t)) t := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases h : t ∈ A
    · simp only [f, Set.indicator_of_mem h, smul_eq_mul, fourier_coe_apply]
      rw [mul_comm]
      congr 2
      dsimp [E]
      push_cast
      ring
    · simp [f,h]
  let s : Finset ℤ := (Finset.range M).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hParse := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hbound := sum_le_hasSum s (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖) hParse
  have hpoint (t : ℝ) : ‖f t‖^2 = A.indicator (fun t => ‖S X u t‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · simp only [f,Set.indicator_of_mem ht,norm_pow]; ring
    · simp [f, ht]
  simp only [s, Finset.sum_map, sub_zero, inv_one, one_smul, hpoint] at hbound
  change (∑ m ∈ Finset.range M, ‖fourierCoeffOn zero_lt_one f (m : ℤ)‖^2) ≤ _ at hbound
  simp_rw [hcoeff] at hbound
  exact hbound

end Conjectures.Goldbach.MinorSupFourthMoment_aux

open Conjectures.Goldbach.MinorSupFourthMoment_aux

theorem Conjectures.Goldbach.MinorSupFourthMoment :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t); ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ) (U : ℝ), MeasurableSet A → 0 ≤ U → (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S X u t‖ ≤ U) → (∑ m ∈ Finset.range M, ‖intervalIntegral (Aᶜ.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤ U^2 * ∑ k ∈ Finset.range (X+1), (u k)^2 := by
  intro E S X M u A U hA hU hsup
  have hc : Continuous (S X u) := by dsimp [S,E]; fun_prop
  have hfour : IntervalIntegrable (Aᶜ.indicator (fun t => ‖S X u t‖^4)) volume 0 1 :=
    ⟨((hc.norm.pow 4).intervalIntegrable _ _).1.indicator hA.compl,
      ((hc.norm.pow 4).intervalIntegrable _ _).2.indicator hA.compl⟩
  calc
    _ ≤ ∫ t in (0:ℝ)..1, Aᶜ.indicator (fun t => ‖S X u t‖^4) t :=
      maskedBessel X M u Aᶜ hA.compl
    _ ≤ ∫ t in (0:ℝ)..1, U^2 * ‖S X u t‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one hfour
        ((continuous_const.mul (hc.norm.pow 2)).intervalIntegrable _ _)
      intro t ht
      by_cases h : t ∈ Aᶜ
      · rw [Set.indicator_of_mem h]
        calc
          ‖S X u t‖ ^ 4 = ‖S X u t‖ ^ 2 * ‖S X u t‖ ^ 2 := by ring
          _ ≤ U^2 * ‖S X u t‖^2 := by gcongr; exact hsup t ht h
      · rw [Set.indicator_of_notMem h]
        exact mul_nonneg (sq_nonneg U) (sq_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, finiteParseval X u]
