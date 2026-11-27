import Mathlib

open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.AlmostAllExceptionDensity_aux

private noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem finiteParseval :
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

open MeasureTheory Filter

private theorem maskedBessel :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) :=
      ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t)
    ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ), MeasurableSet A →
      (∑ m ∈ Finset.range M,
        ‖intervalIntegral
          (A.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t)))
          (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤
      intervalIntegral (A.indicator (fun t => ‖S X u t‖^4))
        (0 : ℝ) 1 MeasureTheory.volume := by
  intro E S X M u A hA
  let f := A.indicator (fun t => (S X u t)^2)
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hc : Continuous (fun t => (S X u t)^2) := by
    dsimp [S, E]
    fun_prop
  have hmem : MemLp f 2 μ := by
    apply MemLp.indicator hA.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have hcoeff (m : ℕ) : fourierCoeffOn zero_lt_one f (m:ℤ) =
      ∫ t in (0:ℝ)..1,
        A.indicator (fun t => (S X u t)^2 * E (-(m:ℝ)*t)) t := by
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
    · simp [f, h]
  let s : Finset ℤ :=
    (Finset.range M).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hParse := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hbound := sum_le_hasSum s
    (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖) hParse
  have hpoint (t : ℝ) : ‖f t‖^2 =
      A.indicator (fun t => ‖S X u t‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · simp only [f, Set.indicator_of_mem ht, norm_pow]
      ring
    · simp [f, ht]
  simp only [s, Finset.sum_map, sub_zero, inv_one, one_smul, hpoint] at hbound
  change (∑ m ∈ Finset.range M,
    ‖fourierCoeffOn zero_lt_one f (m : ℤ)‖^2) ≤ _ at hbound
  simp_rw [hcoeff] at hbound
  exact hbound

open MeasureTheory Filter

private theorem minorFourthMoment :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) :=
      ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t)
    ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ) (U : ℝ), MeasurableSet A →
      0 ≤ U →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S X u t‖ ≤ U) →
      (∑ m ∈ Finset.range M,
        ‖intervalIntegral
          (Aᶜ.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t)))
          (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤
      U^2 * ∑ k ∈ Finset.range (X+1), (u k)^2 := by
  intro E S X M u A U hA hU hsup
  have hc : Continuous (S X u) := by
    dsimp [S, E]
    fun_prop
  have hfour : IntervalIntegrable
      (Aᶜ.indicator (fun t => ‖S X u t‖^4)) volume 0 1 :=
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
          _ ≤ U^2 * ‖S X u t‖^2 := by
            gcongr
            exact hsup t ht h
      · rw [Set.indicator_of_notMem h]
        exact mul_nonneg (sq_nonneg U) (sq_nonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, finiteParseval X u]

open MeasureTheory

private theorem phase_add (u v : ℝ) : phase (u + v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourier_mode (m : ℤ) :
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

private theorem zero_from_pairs (w : ℕ → ℝ) (n Y : ℕ)
    (hn : ∀ k j : ℕ, k + j = n → w k * w j = 0) :
    (∫ t in (0 : ℝ)..1,
      (∑ k ∈ Finset.range (Y+1), (w k : ℂ) * phase ((k : ℝ) * t))^2 *
        phase (-(n:ℝ)*t)) = 0 := by
  let I := Finset.range (Y+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) *
      phase (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by
    dsimp [term, phase]
    fun_prop
  have hpoint (t : ℝ) :
      (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) ^ 2 *
          phase (-(n : ℝ) * t) =
        ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t =
        ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  change (∫ t in (0:ℝ)..1,
    (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t))^2 *
      phase (-(n:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro k _
  rw [intervalIntegral.integral_finsetSum
    (fun j _ => (hcont k j).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro j _
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases heq : (k : ℤ) + j - n = 0
  · have hz : w k * w j = 0 := hn k j (by omega)
    simp only [heq, if_true, mul_one]
    exact_mod_cast hz
  · simp [heq]

private theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ}
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

end Conjectures.Goldbach.AlmostAllExceptionDensity_aux

theorem Conjectures.Goldbach.AlmostAllExceptionDensity :
    let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S (Y : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (Y+1),
      (w k : ℂ) * E ((k : ℝ)*t);
    let D (X : ℕ) := (Finset.Ico X (2*X)).filter
      (fun n => 4 ≤ n ∧ Even n);
    let G (n : ℕ) := ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p + q = n;
    let bad (X : ℕ) := @Finset.filter ℕ (fun n => ¬ G n)
      (Classical.decPred _) (D X);
    ∀ (X : ℕ) (A : Set ℝ) (c U : ℝ), MeasurableSet A → 0 < c → 0 ≤ U →
      (∀ n ∈ D X,
        c * (X : ℝ) ≤
          (intervalIntegral
            (A.indicator (fun t =>
              (S (2*X) t)^2 * E (-(n : ℝ)*t)))
            (0 : ℝ) 1 MeasureTheory.volume).re) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A →
        ‖S (2*X) t‖ ≤ U) →
      ((bad X).card : ℝ) * (c * (X : ℝ))^2 ≤
        U^2 * ∑ k ∈ Finset.range (2*X+1), (w k)^2 := by
  classical
  dsimp only
  intro X A c U hA hc hU hmajor hminor
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  let E : ℝ → ℂ := fun x =>
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let S : ℕ → ℝ → ℂ := fun Y t =>
    ∑ k ∈ Finset.range (Y+1), (w k : ℂ) * E ((k : ℝ) * t)
  let D : ℕ → Finset ℕ := fun X₀ =>
    (Finset.Ico X₀ (2*X₀)).filter (fun n => 4 ≤ n ∧ Even n)
  let G : ℕ → Prop := fun n => ∃ p q : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ p + q = n
  let bad : ℕ → Finset ℕ := fun X₀ =>
    @Finset.filter ℕ (fun n => ¬ G n) (Classical.decPred _) (D X₀)
  let major (n : ℕ) : ℂ := ∫ t in (0 : ℝ)..1,
    A.indicator (fun t => (S (2*X) t)^2 * E (-(n : ℝ) * t)) t
  let minor (n : ℕ) : ℂ := ∫ t in (0 : ℝ)..1,
    Aᶜ.indicator (fun t => (S (2*X) t)^2 * E (-(n : ℝ) * t)) t
  have hbad_sub_D : bad X ⊆ D X := by
    exact @Finset.filter_subset ℕ (fun n => ¬ G n)
      (Classical.decPred _) (D X)
  have hbad_sub_range : bad X ⊆ Finset.range (2*X+1) := by
    intro n hn
    have hnD : n ∈ D X := hbad_sub_D hn
    have hnIco : n ∈ Finset.Ico X (2*X) :=
      (Finset.mem_filter.mp hnD).1
    have hnlt : n < 2*X := (Finset.mem_Ico.mp hnIco).2
    exact Finset.mem_range.mpr (by omega)
  have hnotG (n : ℕ) (hn : n ∈ bad X) : ¬ G n := by
    exact ((@Finset.mem_filter ℕ (fun n => ¬ G n)
      (Classical.decPred _) (D X) n).mp hn).2
  have hzero_pairs (n : ℕ) (hn : n ∈ bad X) (k j : ℕ)
      (hkj : k + j = n) : w k * w j = 0 := by
    by_cases hpk : Nat.Prime k
    · by_cases hpj : Nat.Prime j
      · have hg : G n := ⟨k, j, hpk, hpj, hkj⟩
        exact False.elim (hnotG n hn hg)
      · simp [w, hpj]
    · simp [w, hpk]
  have hfloor (n : ℕ) (hn : n ∈ bad X) :
      (c * (X : ℝ))^2 ≤ ‖minor n‖^2 := by
    have hfull :
        (∫ t in (0 : ℝ)..1,
          (S (2*X) t)^2 * E (-(n : ℝ) * t)) = 0 := by
      dsimp only [S, E]
      exact
        Conjectures.Goldbach.AlmostAllExceptionDensity_aux.zero_from_pairs
          w n (2*X) (hzero_pairs n hn)
    have hcont : Continuous (fun t =>
        (S (2*X) t)^2 * E (-(n : ℝ) * t)) := by
      dsimp [S, E]
      fun_prop
    have hsplit :=
      (Conjectures.Goldbach.AlmostAllExceptionDensity_aux.indicator_integral_split
        hA (hcont.intervalIntegrable 0 1)).trans hfull
    have hRe := congrArg Complex.re hsplit
    rw [Complex.add_re, Complex.zero_re] at hRe
    change (major n).re + (minor n).re = 0 at hRe
    have hmajor_n : c * (X : ℝ) ≤ (major n).re :=
      hmajor n (hbad_sub_D hn)
    have hneg : (minor n).re ≤ -(c * (X : ℝ)) := by
      linarith
    have habs : c * (X : ℝ) ≤ |(minor n).re| := by
      rw [abs_of_nonpos (hneg.trans (by
        exact neg_nonpos.mpr (mul_nonneg hc.le (Nat.cast_nonneg X))))]
      linarith
    have hnorm : |(minor n).re| ≤ ‖minor n‖ :=
      Complex.abs_re_le_norm (minor n)
    exact pow_le_pow_left₀
      (mul_nonneg hc.le (Nat.cast_nonneg X))
      (habs.trans hnorm) 2
  have hsum_bad :
      ∑ n ∈ bad X, (c * (X : ℝ))^2 ≤
        ∑ n ∈ bad X, ‖minor n‖^2 :=
    Finset.sum_le_sum (fun n hn => hfloor n hn)
  have hsum_range :
      ∑ n ∈ bad X, ‖minor n‖^2 ≤
        ∑ n ∈ Finset.range (2*X+1), ‖minor n‖^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hbad_sub_range
      (fun _ _ _ => sq_nonneg _)
  have hmoment :
      (∑ n ∈ Finset.range (2*X+1), ‖minor n‖^2) ≤
        U^2 * ∑ k ∈ Finset.range (2*X+1), (w k)^2 := by
    unfold minor
    dsimp only [S, E]
    exact
      Conjectures.Goldbach.AlmostAllExceptionDensity_aux.minorFourthMoment
        (2*X) (2*X+1) w A U hA hU (by
          intro t ht hnot
          exact hminor t ht hnot)
  calc
    ((bad X).card : ℝ) * (c * (X : ℝ))^2 =
        ∑ _n ∈ bad X, (c * (X : ℝ))^2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ bad X, ‖minor n‖^2 := hsum_bad
    _ ≤ ∑ n ∈ Finset.range (2*X+1), ‖minor n‖^2 := hsum_range
    _ ≤ U^2 * ∑ k ∈ Finset.range (2*X+1), (w k)^2 := hmoment
