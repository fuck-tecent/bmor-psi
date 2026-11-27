import Mathlib

open MeasureTheory Set Real
open scoped FourierTransform SchwartzMap ContDiff

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_goldbach_mellin_parseval_constant :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let W := fun (f : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (f x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ φ : ℝ → ℝ, Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → (∫ t : ℝ, ‖W (F φ) t‖^2) = 2*Real.pi*(intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume) := by
  dsimp only
  intro φ hφ hsupport
  let f : ℝ → ℂ := fun x => (Real.exp (x / 2) * φ (Real.exp x) : ℝ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := Real.log (1 / 3)) (b := Real.log (2 / 3)))
    intro x hx
    by_contra hx'
    have hout : Real.exp x < 1 / 3 ∨ 2 / 3 < Real.exp x := by
      by_contra! hin
      exact hx' ⟨(Real.log_le_iff_le_exp (by norm_num)).2 hin.1,
        (Real.le_log_iff_exp_le (by norm_num)).2 hin.2⟩
    exact hx (by simp [f, hsupport _ hout])
  have hf1 : Integrable f := hf.integrable_of_hasCompactSupport hfs
  have hf2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hfs
  let f₂ : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f
  let fHat₂ : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 f₂
  have hff : Continuous (𝓕 f) := by
    have hf1' := memLp_one_iff_integrable.mpr hf1
    rw [← Real.fourierTransform_toLp hf1']
    exact (Lp.fourierTransform (hf1'.toLp f)).continuous
  have hform : (fHat₂ : ℝ → ℂ) =ᵐ[volume] (𝓕 f) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp fHat₂).locallyIntegrable (by norm_num)) hff.locallyIntegrable
    intro g hg hgs
    let g₀ := Complex.ofRealCLM ∘ g
    have hg₀ : HasCompactSupport g₀ := hgs.comp_left rfl
    have hgc : ContDiff ℝ ∞ g₀ := by dsimp [g₀]; fun_prop
    let ψ : 𝓢(ℝ, ℂ) := hg₀.toSchwartzMap hgc
    calc
      _ = (fHat₂ : 𝓢'(ℝ, ℂ)) ψ := by
        rw [Lp.toTemperedDistribution_apply]
        rfl
      _ = ∫ x, (𝓕 ψ) x • f₂ x := by
        rw [show fHat₂ = 𝓕 f₂ from rfl, ← Lp.fourier_toTemperedDistribution_eq,
          TemperedDistribution.fourier_apply,
          Lp.toTemperedDistribution_apply]
      _ = ∫ x, (𝓕 ψ) x • f x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        change f₂ x = f x at hx
        rw [hx]
      _ = _ := by
        have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
            (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
            (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
            continuous_fourierChar continuous_inner ψ.integrable hf1
        simp only [flip_innerₗ, ContinuousLinearMap.mul_apply'] at h
        change (∫ x, 𝓕 (ψ : ℝ → ℂ) x * f x) = ∫ x, (g x : ℂ) * 𝓕 f x at h
        simpa only [SchwartzMap.fourier_coe, smul_eq_mul] using! h
  have hpl : (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
    have hinner (v : Lp ℂ 2 (volume : Measure ℝ)) :
        inner ℂ v v = ((∫ x, ‖v x‖ ^ 2 : ℝ) : ℂ) := by
      change (∫ x, inner ℂ (v x) (v x)) = _
      rw [← integral_complex_ofReal (f := fun x => ‖v x‖ ^ 2)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [inner_self_eq_norm_sq_to_K]
      exact (Complex.ofReal_pow ‖v x‖ 2).symm
    have h := Lp.inner_fourier_eq f₂ f₂
    change inner ℂ fHat₂ fHat₂ = inner ℂ f₂ f₂ at h
    rw [hinner, hinner] at h
    have h' := Complex.ofReal_injective h
    calc
      _ = ∫ x, ‖fHat₂ x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hform] with x hx
        rw [hx]
      _ = ∫ x, ‖f₂ x‖ ^ 2 := h'
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        change f₂ x = f x at hx
        rw [hx]
  have hspace : (∫ x, ‖f x‖ ^ 2) = ∫ u in (0 : ℝ)..1, (φ u) ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have htrim (s : Set ℝ) (hs : Ioc (0 : ℝ) 1 ⊆ s) :
        (∫ u in s, (φ u) ^ 2) = ∫ u : ℝ, (φ u) ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hzero : φ u = 0 := by
        apply hsupport
        by_cases hpos : 0 < u
        · right
          have hgt : 1 < u := lt_of_not_ge (fun hle => hu (hs ⟨hpos, hle⟩))
          linarith
        · left
          have hle := le_of_not_gt hpos
          linarith
      simp [hzero]
    calc
      _ = ∫ x : ℝ, Real.exp x • (φ (Real.exp x)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with x
        change ‖((Real.exp (x / 2) * φ (Real.exp x) : ℝ) : ℂ)‖ ^ 2 =
          Real.exp x * φ (Real.exp x) ^ 2
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, pow_two (Real.exp (x / 2)),
          ← Real.exp_add, add_halves]
      _ = ∫ u in Ioi (0 : ℝ), (φ u) ^ 2 := integral_comp_exp (fun u => (φ u) ^ 2)
      _ = ∫ u in Ioc (0 : ℝ) 1, (φ u) ^ 2 := by
        rw [htrim _ (fun _ hu => hu.1), htrim _ (fun _ hu => hu)]
  let a : ℝ := -(2 * Real.pi)
  have ha : a ≠ 0 := neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hsign (t : ℝ) :
      (∫ x : ℝ, f x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
        𝓕 f (a⁻¹ * t) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [] with x
    have hx : -2 * Real.pi * inner ℝ x (a⁻¹ * t) = t * x := by
      rw [Real.inner_apply, show -2 * Real.pi = a by simp [a]]
      calc
        a * (x * (a⁻¹ * t)) = (a * a⁻¹) * (t * x) := by ring
        _ = _ := by rw [mul_inv_cancel₀ ha, one_mul]
    rw [hx, smul_eq_mul, mul_comm]
  change (∫ t : ℝ, ‖∫ x : ℝ, f x * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
    2 * Real.pi * ∫ u in (0 : ℝ)..1, (φ u) ^ 2
  simp_rw [hsign]
  rw [Measure.integral_comp_inv_mul_left (fun t => ‖𝓕 f t‖ ^ 2) a, hpl, hspace]
  simp [a, abs_of_pos Real.pi_pos, abs_mul]
