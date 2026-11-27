import Mathlib

noncomputable def goldbachPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private lemma continuous_goldbachPhase : Continuous goldbachPhase := by
  unfold goldbachPhase
  continuity

private lemma integral_goldbachPhase_int (m : ℤ) :
    ∫ t in (0 : ℝ)..1, goldbachPhase ((m : ℝ) * t) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [goldbachPhase]
  · have hc : ((m : ℂ) * (2 * Real.pi * Complex.I)) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast hm
      · apply mul_ne_zero
        · norm_num
        · exact Complex.I_ne_zero
    have heq : (fun t : ℝ => goldbachPhase ((m : ℝ) * t)) =
        fun t : ℝ => Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (t : ℂ)) := by
      funext t
      simp [goldbachPhase]
      ring_nf
    rw [heq, integral_exp_mul_complex hc]
    have h1 : Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * ((1 : ℝ) : ℂ)) = 1 := by
      simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I m
    have h0 : Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [h1, h0]
    simp [hm]

private lemma goldbachPhase_add (a b : ℝ) :
    goldbachPhase (a + b) = goldbachPhase a * goldbachPhase b := by
  simp [goldbachPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma integral_goldbachPhase_pair (n k l : ℕ) :
    ∫ t in (0 : ℝ)..1,
        goldbachPhase ((k : ℝ) * t) * goldbachPhase ((l : ℝ) * t) *
          goldbachPhase (-(n : ℝ) * t) =
      if k + l = n then 1 else 0 := by
  let m : ℤ := (k : ℤ) + (l : ℤ) - (n : ℤ)
  have hprod : (fun t : ℝ =>
        goldbachPhase ((k : ℝ) * t) * goldbachPhase ((l : ℝ) * t) *
          goldbachPhase (-(n : ℝ) * t)) =
      fun t : ℝ => goldbachPhase ((m : ℝ) * t) := by
    funext t
    rw [← goldbachPhase_add, ← goldbachPhase_add]
    congr 1
    simp [m]
    push_cast
    ring
  rw [hprod, integral_goldbachPhase_int]
  by_cases hkn : k + l = n
  · have hm : m = 0 := by
      dsimp [m]
      omega
    simp [hkn, hm]
  · have hm : m ≠ 0 := by
      intro h
      apply hkn
      have : (k : ℤ) + (l : ℤ) - (n : ℤ) = 0 := by simpa [m] using h
      omega
    simp [hkn, hm]

private lemma circle_coefficient (n : ℕ) (w : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1,
        (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * goldbachPhase ((k : ℝ) * t)) ^ 2 *
          goldbachPhase (-(n : ℝ) * t) =
      ((∑ p ∈ Finset.range (n + 1), w p * w (n - p) : ℝ) : ℂ) := by
  classical
  let T := Finset.range (n + 1)
  have hfun : (fun t : ℝ =>
        (∑ k ∈ T, (w k : ℂ) * goldbachPhase ((k : ℝ) * t)) ^ 2 *
          goldbachPhase (-(n : ℝ) * t)) =
      fun t : ℝ => ∑ k ∈ T, ∑ l ∈ T,
        (w k : ℂ) * (w l : ℂ) *
          (goldbachPhase ((k : ℝ) * t) * goldbachPhase ((l : ℝ) * t) *
            goldbachPhase (-(n : ℝ) * t)) := by
    funext t
    rw [pow_two, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hfun, Complex.ofReal_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk_le : k ≤ n := by simpa using (Finset.mem_range.mp hk)
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, integral_goldbachPhase_pair]
      rw [Finset.sum_eq_single (n - k)]
      · rw [if_pos (by omega : k + (n - k) = n)]
        norm_num
      · intro l hl hne
        rw [if_neg (by
          intro h
          exact hne (by omega))]
        simp
      · intro hnk
        exfalso
        apply hnk
        exact Finset.mem_range.mpr (by omega)
    · intro l hl
      exact (by
        dsimp [goldbachPhase]
        fun_prop :
        Continuous (fun t : ℝ =>
          (w k : ℂ) * (w l : ℂ) *
            (goldbachPhase ((k : ℝ) * t) * goldbachPhase ((l : ℝ) * t) *
              goldbachPhase (-(n : ℝ) * t)))).intervalIntegrable _ _
  · intro k hk
    exact (by
      dsimp [goldbachPhase]
      fun_prop :
      Continuous (fun t : ℝ =>
        ∑ l ∈ T, (w k : ℂ) * (w l : ℂ) *
          (goldbachPhase ((k : ℝ) * t) * goldbachPhase ((l : ℝ) * t) *
            goldbachPhase (-(n : ℝ) * t)))).intervalIntegrable _ _

theorem PEqualNP.Outside.L_goldbach_smooth_arc_margin :
    ∀ (n : ℕ) (u : ℝ → ℝ), Continuous u →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
      let phase : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
      let S : ℝ → ℂ := fun t => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * phase ((k : ℝ) * t))
      let f : ℝ → ℂ := fun t => (S t) ^ 2 * phase (-(n : ℝ) * t)
      let A : ℂ := intervalIntegral (fun t => ((u t : ℝ) : ℂ) * f t) (0 : ℝ) 1 MeasureTheory.volume
      let B : ℂ := intervalIntegral (fun t => (((1 - u t : ℝ) : ℂ)) * f t) (0 : ℝ) 1 MeasureTheory.volume
      ‖B‖ < A.re → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n u hu
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  let phase : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  let S : ℝ → ℂ := fun t => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * phase ((k : ℝ) * t))
  let f : ℝ → ℂ := fun t => (S t) ^ 2 * phase (-(n : ℝ) * t)
  let A : ℂ := intervalIntegral (fun t => ((u t : ℝ) : ℂ) * f t) (0 : ℝ) 1 MeasureTheory.volume
  let B : ℂ := intervalIntegral (fun t => (((1 - u t : ℝ) : ℂ)) * f t) (0 : ℝ) 1 MeasureTheory.volume
  dsimp only
  intro h
  let C : ℝ := ∑ p ∈ Finset.range (n + 1), w p * w (n - p)
  have hf_cont : Continuous f := by
    dsimp [f, S, phase]
    fun_prop
  have hA_int : IntervalIntegrable (fun t : ℝ => ((u t : ℝ) : ℂ) * f t) MeasureTheory.volume 0 1 := by
    exact ((Complex.continuous_ofReal.comp hu).mul hf_cont).intervalIntegrable _ _
  have hB_int : IntervalIntegrable (fun t : ℝ => (((1 - u t : ℝ) : ℂ)) * f t) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp (continuous_const.sub hu) |>.mul hf_cont
  have hAB : A + B = (C : ℂ) := by
    calc
      A + B = ∫ t in (0 : ℝ)..1, (((u t : ℝ) : ℂ) * f t + (((1 - u t : ℝ) : ℂ)) * f t) := by
        dsimp [A, B]
        rw [intervalIntegral.integral_add hA_int hB_int]
      _ = ∫ t in (0 : ℝ)..1, f t := by
        apply intervalIntegral.integral_congr
        intro t ht
        push_cast
        ring
      _ = (C : ℂ) := by
        simpa [C, f, S, phase, goldbachPhase] using circle_coefficient n w
  have hCpos : 0 < C := by
    have hre : 0 < (A + B).re := by
      have hbre : -‖B‖ ≤ B.re := by
        have := Complex.abs_re_le_norm B
        linarith [neg_abs_le B.re]
      rw [Complex.add_re]
      linarith
    rw [hAB] at hre
    simpa using hre
  have hsumpos : 0 < ∑ p ∈ Finset.range (n + 1), w p * w (n - p) := by
    simpa [C] using hCpos
  have hnonneg : ∀ p ∈ Finset.range (n + 1), 0 ≤ w p * w (n - p) := by
    intro p hp
    apply mul_nonneg
    · by_cases hpp : Nat.Prime p
      · simp [w, hpp]
        positivity
      · simp [w, hpp]
    · by_cases hq : Nat.Prime (n - p)
      · simp [w, hq]
        positivity
      · simp [w, hq]
  obtain ⟨p, hpT, hppos⟩ := Finset.sum_pos_iff_of_nonneg hnonneg |>.mp hsumpos
  have hp_le : p ≤ n := by simpa using (Finset.mem_range.mp hpT)
  have hwp_nonneg : 0 ≤ w p := by
    by_cases hpp : Nat.Prime p
    · simp [w, hpp]
      exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    · simp [w, hpp]
  have hwq_nonneg : 0 ≤ w (n - p) := by
    by_cases hq : Nat.Prime (n - p)
    · simp [w, hq]
      exact Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
    · simp [w, hq]
  have hwp : 0 < w p := by
    by_contra hle
    push Not at hle
    nlinarith [hppos, hwp_nonneg, hwq_nonneg]
  have hwq : 0 < w (n - p) := by
    by_contra hle
    push Not at hle
    nlinarith [hppos, hwp_nonneg, hwq_nonneg]
  have hp : Nat.Prime p := by
    by_contra h
    simp [w, h] at hwp
  have hq : Nat.Prime (n - p) := by
    by_contra h
    simp [w, h] at hwq
  exact ⟨p, n - p, hp, hq, Nat.add_sub_of_le hp_le⟩
