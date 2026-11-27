import Mathlib

open MeasureTheory
open scoped SchwartzMap FourierTransform

private theorem weightedIntegrable (g : 𝓢(ℝ, ℂ)) {J : ℝ → ℝ} (hJ : Continuous J)
    {K : ℝ} (hK : ∀ t, |J t| ≤ K * (1 + Real.log (2 + |t|))) :
    Integrable (fun t : ℝ => ‖g t‖^2 * J t) := by
  let A := SchwartzMap.seminorm ℝ 0 0 g
  let B := SchwartzMap.seminorm ℝ 1 0 g
  let C := |K| * (2*A + B)
  have hC : 0 ≤ C := by
    dsimp [C, A, B]
    positivity
  have hint : Integrable (fun t : ℝ => C * ‖g t‖) := g.integrable.norm.const_mul C
  apply hint.mono (by exact ((g.continuous.norm.pow 2).mul hJ).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2+|t|)
  have hg0 : ‖g t‖ ≤ A := g.norm_le_seminorm ℝ t
  have hg1 : |t| *‖g t‖ ≤ B := by
    simpa [Real.norm_eq_abs, B] using g.norm_pow_mul_le_seminorm ℝ 1 t
  have hj : |J t| ≤ |K| * (2+|t|) := calc
    _ ≤ K * (1+Real.log (2+|t|)) := hK t
    _ ≤ |K| * (1+Real.log (2+|t|)) := by
      apply mul_le_mul_of_nonneg_right (le_abs_self _)
      have := Real.log_nonneg (by linarith [abs_nonneg t] : 1 ≤ 2+|t|)
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
  calc
    ‖g t‖^2 * |J t| ≤ ‖g t‖^2 * (|K| * (2+|t|)) :=
      mul_le_mul_of_nonneg_left hj (sq_nonneg _)
    _ = (|K| * (2*‖g t‖ + |t| *‖g t‖))*‖g t‖ := by ring
    _ ≤ C * ‖g t‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

theorem PEqualNP.Outside.L_goldbach_mellin_archimedean_budget :
    let W := fun (f : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (f x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ (f J : ℝ → ℝ), (∀ j : ℕ, ContDiff ℝ j f) → HasCompactSupport f → Continuous J → (∃ K : ℝ, ∀ t, |J t| ≤ K*(1+Real.log (2+|t|))) → MeasureTheory.Integrable (fun t : ℝ => ‖W f t‖^2*J t) MeasureTheory.volume := by
  intro W f J hf hc hJ hbound
  obtain ⟨K,hK⟩ := hbound
  let F : 𝓢(ℝ, ℂ) := (hc.toSchwartzMap (contDiff_infty.mpr hf)).postcompCLM Complex.ofRealCLM
  let scale : ℝˣ := Units.mk0 (-(2 * Real.pi)⁻¹)
    (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfUnit (M := ℝ) scale).toContinuousLinearEquiv
  let G : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (𝓕 F)
  have hG (t : ℝ) : G t = W f t := by
    change 𝓕 (F : ℝ → ℂ) ((-(2 * Real.pi)⁻¹) * t) = _
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    have he : -2 * Real.pi * x * (-(2 * Real.pi)⁻¹ * t) = t*x := by
      field_simp [Real.pi_ne_zero]
    change Complex.exp _ * (f x : ℂ) = (f x : ℂ) * Complex.exp _
    rw [he, mul_comm]
  simpa only [← hG] using weightedIntegrable G hJ hK
