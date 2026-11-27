import Mathlib

open MeasureTheory Real Complex Set Filter
open scoped FourierTransform Convolution Topology RealInnerProductSpace

noncomputable section

namespace Conjectures.Goldbach.FiniteMajorSincMass_aux

set_option maxHeartbeats 1600000 in
def hset : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)

set_option maxHeartbeats 1600000 in
lemma hset_mem_iff {t : ℝ} : t ∈ hset ↔ -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 := Iff.rfl

set_option maxHeartbeats 1600000 in
lemma hset_meas : MeasurableSet hset := measurableSet_Icc

set_option maxHeartbeats 1600000 in
lemma hset_neg_mem {t : ℝ} : -t ∈ hset ↔ t ∈ hset := by
  rw [hset_mem_iff, hset_mem_iff]
  constructor
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

set_option maxHeartbeats 1600000 in
def hind : ℝ → ℂ := hset.indicator (fun _ => 1)

set_option maxHeartbeats 1600000 in
lemma hind_of_mem {t : ℝ} (ht : t ∈ hset) : hind t = 1 := by
  simp only [hind, Set.indicator_of_mem ht]

set_option maxHeartbeats 1600000 in
lemma hind_of_notMem {t : ℝ} (ht : t ∉ hset) : hind t = 0 := by
  simp only [hind, Set.indicator_of_notMem ht]

set_option maxHeartbeats 1600000 in
lemma hind_even (t : ℝ) : hind (-t) = hind t := by
  by_cases ht : t ∈ hset
  · rw [hind_of_mem (hset_neg_mem.mpr ht), hind_of_mem ht]
  · rw [hind_of_notMem (fun h => ht (hset_neg_mem.mp h)), hind_of_notMem ht]

set_option maxHeartbeats 1600000 in
lemma hind_mul_self (t : ℝ) : hind t * hind t = hind t := by
  by_cases ht : t ∈ hset
  · rw [hind_of_mem ht, one_mul]
  · rw [hind_of_notMem ht, mul_zero]

set_option maxHeartbeats 1600000 in
lemma hset_measure_ne_top : volume hset ≠ ⊤ := by
  have h : volume hset < ⊤ := isCompact_Icc.measure_lt_top
  exact h.ne

set_option maxHeartbeats 1600000 in
lemma hind_integrable : Integrable hind := by
  rw [hind, integrable_indicator_iff hset_meas]
  exact integrableOn_const hset_measure_ne_top

set_option maxHeartbeats 1600000 in
lemma integral_hind : ∫ t : ℝ, hind t = 1 := by
  have h1 : (∫ t : ℝ, hind t) = volume.real hset • (1 : ℂ) := by
    rw [hind, integral_indicator_const (1 : ℂ) hset_meas]
  rw [h1]
  have h2 : volume.real hset = 1 := by
    show volume.real (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) = 1
    rw [Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  rw [h2]
  simp

set_option maxHeartbeats 1600000 in
lemma hind_ft (w : ℝ) : 𝓕 hind w = ((Real.sinc (Real.pi * w) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  have hpt : ∀ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I) • hind v
      = hset.indicator
          (fun v : ℝ => Complex.exp ((↑(-2 * Real.pi * (v * w)) : ℂ) * Complex.I)) v := by
    intro v
    by_cases hv : v ∈ hset
    · rw [hind_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul, mul_one]
    · rw [hind_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator hset_meas]
  simp only [hset]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hrw : ∀ x : ℝ, (-2 * Real.pi * (x * w)) = ((-2 * Real.pi * w) * x) := by
    intro x
    ring
  have hrw' : ∀ x : ℝ, (↑(-2 * Real.pi * (x * w)) : ℂ) = ↑((-2 * Real.pi * w) * x) := by
    intro x
    rw [hrw x]
  simp_rw [hrw']
  by_cases hw : w = 0
  · subst hw
    have hc0 : (fun x : ℝ => Complex.exp ((↑((-2 * Real.pi * 0) * x) : ℂ) * Complex.I))
        = fun _ => (1 : ℂ) := by
      funext x
      simp
    rw [hc0, intervalIntegral.integral_const]
    simp [Real.sinc_zero]
    norm_num
  · have hne : (-2 * Real.pi * w) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_ne_zero) hw
    have hstep : (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          Complex.exp ((↑((-2 * Real.pi * w) * x) : ℂ) * Complex.I))
        = (-2 * Real.pi * w)⁻¹ • ∫ t in ((-2 * Real.pi * w) * (-(1 / 2 : ℝ)))..((-2 * Real.pi * w) * (1 / 2)),
            Complex.exp ((↑t : ℂ) * Complex.I) :=
      intervalIntegral.integral_comp_mul_left
        (fun t : ℝ => Complex.exp ((↑t : ℂ) * Complex.I)) hne
    rw [hstep]
    have e1 : (-2 * Real.pi * w) * (-(1 / 2 : ℝ)) = Real.pi * w := by ring
    have e2 : (-2 * Real.pi * w) * (1 / 2 : ℝ) = -(Real.pi * w) := by ring
    rw [e1, e2, intervalIntegral.integral_symm, integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul]
    have hkey : ((-2 * Real.pi * w)⁻¹ * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w)) : ℝ)
        = Real.sinc (Real.pi * w) := by
      field_simp [hne] <;> ring
    calc _ = ((↑((-2 * Real.pi * w)⁻¹
            * -(2 * (Real.pi * w) * Real.sinc (Real.pi * w))) : ℂ)) := by
          push_cast <;> ring
      _ = _ := by rw [hkey]

set_option maxHeartbeats 1600000 in
lemma hind_eventuallyEq (s : ℝ) (h1 : s ≠ -(1 / 2 : ℝ)) (h2 : s ≠ (1 / 2 : ℝ)) :
    ∀ᶠ y in 𝓝 s, hind y = hind s := by
  by_cases hs1 : (-(1 / 2 : ℝ)) < s
  · by_cases hs2 : s < (1 / 2 : ℝ)
    · have hm : s ∈ hset := hset_mem_iff.mpr ⟨le_of_lt hs1, le_of_lt hs2⟩
      filter_upwards [Ioo_mem_nhds hs1 hs2] with y hy
      have hy' := Set.mem_Ioo.mp hy
      rw [hind_of_mem (hset_mem_iff.mpr ⟨le_of_lt hy'.1, le_of_lt hy'.2⟩), hind_of_mem hm]
    · have hs2' : (1 / 2 : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hs2) (fun hcon => h2 hcon.symm)
      have hm : s ∉ hset :=
        fun hx => absurd (hset_mem_iff.mp hx).2 (by linarith : ¬ (s ≤ 1 / 2))
      filter_upwards [Ioi_mem_nhds hs2'] with y hy
      have hy' := Set.mem_Ioi.mp hy
      rw [hind_of_notMem
          (fun hx => absurd (hset_mem_iff.mp hx).2 (by linarith : ¬ (y ≤ 1 / 2))),
        hind_of_notMem hm]
  · have hs1' : s < -(1 / 2 : ℝ) := lt_of_le_of_ne (le_of_not_gt hs1) h1
    have hm : s ∉ hset :=
      fun hx => absurd (hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ s))
    filter_upwards [Iio_mem_nhds hs1'] with y hy
    have hy' := Set.mem_Iio.mp hy
    rw [hind_of_notMem
        (fun hx => absurd (hset_mem_iff.mp hx).1 (by linarith : ¬ (-(1 / 2 : ℝ) ≤ y))),
      hind_of_notMem hm]

set_option maxHeartbeats 1600000 in
lemma convolution_hind_continuousAt_zero :
    ContinuousAt (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) 0 := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun t => hind t * hind (x - t)) volume := by
    intro x
    simpa using (hind_integrable.aestronglyMeasurable.convolution_integrand_snd
      (ContinuousLinearMap.mul ℂ ℂ) hind_integrable.aestronglyMeasurable x)
  have hbound : ∀ x t : ℝ, ‖hind t * hind (x - t)‖ ≤ ‖hind t‖ := by
    intro x t
    have h3 : ‖hind (x - t)‖ ≤ 1 := by
      by_cases hmem : (x - t) ∈ hset
      · rw [hind_of_mem hmem]
        simp
      · rw [hind_of_notMem hmem]
        simp
    rw [norm_mul]
    calc ‖hind t‖ * ‖hind (x - t)‖ ≤ ‖hind t‖ * 1 :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ‖hind t‖ := mul_one _
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun x => hind t * hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (hind t * hind (-t))) := by
    filter_upwards [MeasureTheory.volume.ae_ne (-(1 / 2 : ℝ)),
      MeasureTheory.volume.ae_ne (1 / 2 : ℝ)] with t h1 h2
    have hsub : Tendsto (fun x : ℝ => x - t) (𝓝 (0 : ℝ)) (𝓝 (-t)) := by
      have hc : ContinuousAt (fun x : ℝ => x - t) 0 := by fun_prop
      simpa using hc.tendsto
    have hkey : ∀ᶠ y in 𝓝 (-t), hind y = hind (-t) :=
      hind_eventuallyEq (-t) (fun hcon => h2 (by linarith)) (fun hcon => h1 (by linarith))
    have hconv : Tendsto (fun x : ℝ => hind (x - t)) (𝓝 (0 : ℝ)) (𝓝 (hind (-t))) := by
      refine (tendsto_const_nhds.congr' ?_)
      filter_upwards [hsub.eventually hkey] with x hx
      exact hx.symm
    exact tendsto_const_nhds.mul hconv
  have hmain : Tendsto (fun x : ℝ => ∫ t, hind t * hind (x - t)) (𝓝 (0 : ℝ))
      (𝓝 (∫ t, hind t * hind (-t))) :=
    tendsto_integral_filter_of_dominated_convergence (fun t => ‖hind t‖)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (hbound x))
      hind_integrable.norm hlim
  have hout : Tendsto (fun x : ℝ => (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) x) (𝓝 (0 : ℝ))
      (𝓝 ((hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) 0)) := by
    simpa only [convolution_mul, zero_sub] using hmain
  exact hout

set_option maxHeartbeats 1600000 in
lemma sinc_sq_nonneg (t : ℝ) : 0 ≤ Real.sinc (Real.pi * t) ^ 2 := sq_nonneg _

set_option maxHeartbeats 1600000 in
lemma sinc_sq_le_one (t : ℝ) : Real.sinc (Real.pi * t) ^ 2 ≤ 1 := by
  have hA := Real.sinc_le_one (Real.pi * t)
  have hB := Real.neg_one_le_sinc (Real.pi * t)
  nlinarith

set_option maxHeartbeats 1600000 in
lemma sinc_sq_even (t : ℝ) :
    Real.sinc (Real.pi * (-t)) ^ 2 = Real.sinc (Real.pi * t) ^ 2 := by
  rw [mul_neg, Real.sinc_neg]

set_option maxHeartbeats 1600000 in
lemma sinc_sq_le (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := by
  have hpi : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  rw [Real.sinc_of_ne_zero hpi]
  have h1 : Real.sin (Real.pi * t) ^ 2 ≤ 1 := by
    have hA := Real.sin_le_one (Real.pi * t)
    have hB := Real.neg_one_le_sin (Real.pi * t)
    nlinarith
  have h2 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
  have h3 : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  calc (Real.sin (Real.pi * t) / (Real.pi * t)) ^ 2
      = Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) := by rw [div_pow, h3]
    _ ≤ 1 / (Real.pi ^ 2 * t ^ 2) := div_le_div_of_nonneg_right h1 h2.le

set_option maxHeartbeats 1600000 in
lemma sinc_sq_le_inv (t : ℝ) (ht : t ≠ 0) :
    Real.sinc (Real.pi * t) ^ 2 ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
  calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := sinc_sq_le t ht
    _ = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by rw [div_eq_mul_inv, one_mul, mul_inv_rev]; ring

set_option maxHeartbeats 1600000 in
lemma sinc_sq_le_two (t : ℝ) :
    Real.sinc (Real.pi * t) ^ 2 ≤ 2 / (1 + (Real.pi * t) ^ 2) := by
  have hrw : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
  have hden : (0 : ℝ) < 1 + Real.pi ^ 2 * t ^ 2 := by positivity
  by_cases ht : t = 0
  · subst ht
    norm_num [Real.sinc_zero]
  · have hu0 : (0 : ℝ) < Real.pi ^ 2 * t ^ 2 := by positivity
    rcases le_or_gt (Real.pi ^ 2 * t ^ 2) 1 with h | h
    · have h2 : (1 : ℝ) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 := sinc_sq_le_one t
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h2
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]
    · have h3 : 1 / (Real.pi ^ 2 * t ^ 2) ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := by
        rw [div_le_div_iff₀ hu0 hden]
        nlinarith
      calc Real.sinc (Real.pi * t) ^ 2 ≤ 1 / (Real.pi ^ 2 * t ^ 2) := sinc_sq_le t ht
        _ ≤ 2 / (1 + Real.pi ^ 2 * t ^ 2) := h3
        _ = 2 / (1 + (Real.pi * t) ^ 2) := by rw [hrw]

set_option maxHeartbeats 1600000 in
lemma sinc_sq_integrable : Integrable (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) := by
    fun_prop
  have hG : Integrable (fun t : ℝ => 2 / (1 + (Real.pi * t) ^ 2)) := by
    have h2 : Integrable (fun x : ℝ => 2 * (1 + x ^ 2) ⁻¹) :=
      integrable_inv_one_add_sq.const_mul 2
    have h3 : Integrable (fun t : ℝ => 2 * (1 + (Real.pi * t) ^ 2) ⁻¹) :=
      h2.comp_mul_left' Real.pi_ne_zero
    refine h3.congr (ae_of_all _ fun t => ?_)
    simp only [div_eq_mul_inv]
  refine Integrable.mono' hG hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sinc_sq_nonneg t)]
  exact sinc_sq_le_two t

set_option maxHeartbeats 1600000 in
lemma sinc_sq_total : ∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 = 1 := by
  have hT_int : Integrable (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) :=
    hind_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hind_integrable
  have hFT : ∀ ξ : ℝ, 𝓕 (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) ξ
      = ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ) := by
    intro ξ
    rw [Real.fourier_mul_convolution_eq hind_integrable hind_integrable ξ, hind_ft ξ]
    push_cast
    ring
  have hFT_int : Integrable (𝓕 (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind)) := by
    have h1 : Integrable (fun ξ : ℝ => ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ)) :=
      Integrable.iff_ofReal.mp sinc_sq_integrable
    exact h1.congr (ae_of_all _ fun ξ => (hFT ξ).symm)
  have hinv : 𝓕⁻ (𝓕 (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind)) 0
      = (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) 0 :=
    hT_int.fourierInv_fourier_eq hFT_int convolution_hind_continuousAt_zero
  have hT0 : (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind) 0 = 1 := by
    rw [convolution_mul]
    simp only [zero_sub]
    have hself : ∀ t : ℝ, hind t * hind (-t) = hind t := by
      intro t
      rw [hind_even t]
      exact hind_mul_self t
    simp_rw [hself]
    exact integral_hind
  have hF0 : 𝓕⁻ (𝓕 (hind ⋆[ContinuousLinearMap.mul ℂ ℂ] hind)) 0
      = ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    rw [integral_congr_ae (ae_of_all _ fun v => hFT v)]
    first
      | exact integral_ofReal
      | norm_cast
  have hfin : ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hF0, hinv, hT0]
  exact Complex.ofReal_inj.mp hfin

set_option maxHeartbeats 1600000 in
lemma trunc_bound (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_even : ∀ t, f (-t) = f t)
    (hf_bound : ∀ t, t ≠ 0 → f t ≤ (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹)
    (hf_int : Integrable f) (hf_tot : ∫ t : ℝ, f t = 1) (h : ℝ) (hh : 0 < h) :
    let k := intervalIntegral (fun t : ℝ => f t) (-h) h MeasureTheory.volume
    0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k := by
  dsimp only
  have hle : -h ≤ h := by linarith
  have hk : intervalIntegral (fun t : ℝ => f t) (-h) h volume
      = ∫ t in Ioc (-h) h, f t ∂volume := intervalIntegral.integral_of_le hle
  have hbound_int : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹) (Ioi h) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi h) :=
      integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := h) (by norm_num) hh
    have hmul : IntegrableOn (fun t : ℝ => (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)) (Ioi h) :=
      hbase.const_mul _
    refine hmul.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have htpos : 0 < t := hh.trans ht
    show (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) = (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
  have htail : ∫ t in Ioi h, f t ∂volume ≤ (Real.pi ^ 2)⁻¹ * h⁻¹ := by
    have hA : ∫ t in Ioi h, f t ∂volume ≤ ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume :=
      setIntegral_mono_on hf_int.integrableOn hbound_int measurableSet_Ioi
        (fun t ht => hf_bound t (ne_of_gt (lt_of_lt_of_le hh ht.le)))
    have hB : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume = (Real.pi ^ 2)⁻¹ * h⁻¹ := by
      have hc : ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ ∂volume
          = ∫ t in Ioi h, (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ) ∂volume := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have htpos : 0 < t := hh.trans ht
        show (Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ = (Real.pi ^ 2)⁻¹ * t ^ (-2 : ℝ)
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg htpos.le, Real.rpow_two]
      rw [hc, integral_const_mul, integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hh]
      have h3 : (-h ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) = h⁻¹ := by
        rw [show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one]
        simp
      rw [h3]
    linarith [hA, hB]
  have hleft : ∫ t in Iic (-h), f t ∂volume = ∫ t in Ioi h, f t ∂volume := by
    have h1 : ∫ t in Iic (-h), f t ∂volume = ∫ t in Iic (-h), f (-t) ∂volume :=
      setIntegral_congr_fun measurableSet_Iic (fun x _ => (hf_even x).symm)
    rw [h1, integral_comp_neg_Iic (-h) f]
    simp
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by
    have h4 := Real.pi_gt_three
    nlinarith
  have hinv : (Real.pi ^ 2)⁻¹ ≤ (9 : ℝ)⁻¹ := by
    have h5 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hpi.le
    simpa using h5
  have htail' : ∫ t in Ioi h, f t ∂volume ≤ (9 : ℝ)⁻¹ * h⁻¹ := by
    have h6 := mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hh.le)
    linarith [htail, h6]
  have hcomp : ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume
      = ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume := by
    rw [compl_Ioc]
    exact setIntegral_union (Iic_disjoint_Ioi hle) measurableSet_Ioi hf_int.integrableOn
      hf_int.integrableOn
  have htotal : (∫ t in Ioc (-h) h, f t ∂volume) + ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume = 1 := by
    rw [integral_add_compl measurableSet_Ioc hf_int]
    exact hf_tot
  have hnn : 0 ≤ ∫ t in (Ioc (-h) h)ᶜ, f t ∂volume :=
    setIntegral_nonneg measurableSet_Ioc.compl (fun u _ => hf_nonneg u)
  have htail2 : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 / (9 * h) := by
    have hA : ∫ t in Iic (-h), f t ∂volume + ∫ t in Ioi h, f t ∂volume ≤ 2 * ((9 : ℝ)⁻¹ * h⁻¹) := by
      rw [hleft]
      linarith [htail']
    have hB : 2 * ((9 : ℝ)⁻¹ * h⁻¹) = 2 / (9 * h) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    linarith [hA, hB]
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg hle (fun u _ => hf_nonneg u)
  · rw [hk]
    linarith [htotal, hnn]
  · rw [hk]
    rw [hcomp] at htotal
    linarith [htotal, htail2]

end Conjectures.Goldbach.FiniteMajorSincMass_aux

set_option maxHeartbeats 1600000 in
theorem Conjectures.Goldbach.FiniteMajorSincMass : ∀ h : ℝ, 0<h → let k := intervalIntegral (fun t : ℝ => Real.sinc (Real.pi*t)^2) (-h) h MeasureTheory.volume; 0≤k ∧ k≤1 ∧ 1-2/(9*h)≤k := by
  intro h hh
  have hmain := Conjectures.Goldbach.FiniteMajorSincMass_aux.trunc_bound
    (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2)
    Conjectures.Goldbach.FiniteMajorSincMass_aux.sinc_sq_nonneg
    Conjectures.Goldbach.FiniteMajorSincMass_aux.sinc_sq_even
    Conjectures.Goldbach.FiniteMajorSincMass_aux.sinc_sq_le_inv
    Conjectures.Goldbach.FiniteMajorSincMass_aux.sinc_sq_integrable
    Conjectures.Goldbach.FiniteMajorSincMass_aux.sinc_sq_total h hh
  simpa using hmain

end
