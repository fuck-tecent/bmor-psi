import Mathlib

open MeasureTheory Set Filter
open scoped Topology

theorem PEqualNP.Outside.L_goldbach_mellin_low_frequency_floor :
    let Adm := fun φ : ℝ → ℝ => (∀ j : ℕ, ContDiff ℝ j φ) ∧ (∀ u, 0≤φ u ∧ φ u≤1) ∧ (∀ u, φ (1-u)=φ u) ∧ (∀ u, u < 1/3 ∨ 2/3 < u → φ u=0) ∧ (∀ u, 5/12≤u → u≤7/12 → φ u=1); let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let W := fun (f : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (f x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ φ : ℝ → ℝ, Adm φ → ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, |t|≤δ → (1:ℝ)/12 ≤ (W (F φ) t).re := by
  dsimp only
  intro φ ⟨hsmooth, hrange, _, hsupport, hplateau⟩
  let f := fun x : ℝ => Real.exp (x / 2) * φ (Real.exp x)
  let K := Icc (Real.log (1/3)) (Real.log (2/3))
  let P := Icc (Real.log (5/12)) (Real.log (7/12))
  let g := fun t x : ℝ => (f x : ℂ) * Complex.exp (((t*x : ℝ) : ℂ) * Complex.I)
  let H := fun t : ℝ => ∫ x in K, g t x
  have hφ : Continuous φ := (hsmooth 1).continuous
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g.uncurry := by dsimp [g, Function.uncurry]; fun_prop
  have hH : Continuous H := continuous_parametric_integral_of_continuous hg isCompact_Icc
  have htotal (t : ℝ) : H t = ∫ x, g t x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have he : Real.exp x < 1 / 3 ∨ 2 / 3 < Real.exp x := by
      by_contra! h
      exact hx ⟨(Real.log_le_iff_le_exp (by norm_num)).2 h.1,
        (Real.le_log_iff_exp_le (by norm_num)).2 h.2⟩
    simp [g, f, hsupport _ he]
  have hsub : P ⊆ K := Icc_subset_Icc
    (Real.log_le_log (by norm_num) (by norm_num))
    (Real.log_le_log (by norm_num) (by norm_num))
  have hab : Real.log (5/12) ≤ Real.log (7/12) := Real.log_le_log (by norm_num) (by norm_num)
  have hzero : (1 : ℝ) / 6 ≤ (H 0).re := by
    calc
      (1 : ℝ) / 6 = ∫ x in P, Real.exp x := by
        dsimp [P]
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          integral_exp, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
        norm_num
      _ ≤ ∫ x in P, f x := by
        apply setIntegral_mono_on Real.continuous_exp.integrableOn_Icc hf.integrableOn_Icc
          measurableSet_Icc
        intro x hx
        have hl := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5/12)).1 hx.1
        have hu := (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 7/12)).1 hx.2
        have hneg : x ≤ 0 := hx.2.trans (Real.log_nonpos (by norm_num) (by norm_num))
        simp only [f, hplateau _ hl hu, mul_one, Real.exp_le_exp]
        linarith
      _ ≤ ∫ x in K, f x := setIntegral_mono_set hf.integrableOn_Icc
        (Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le (hrange _).1))
        (Eventually.of_forall hsub)
      _ = (H 0).re := by
        simp only [H, g, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
        rw [integral_complex_ofReal, Complex.ofReal_re]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (1 : ℝ) / 12 < (H t).re :=
    (Complex.continuous_re.comp hH).continuousAt.eventually_const_lt
      (show (1 : ℝ) / 12 < (H 0).re by linarith)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε / 2, by positivity, ?_⟩
  intro t ht
  change (1 : ℝ) / 12 ≤ (∫ x, g t x).re
  rw [← htotal t]
  refine le_of_lt (hball (show t ∈ Metric.ball 0 ε from ?_))
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  linarith
