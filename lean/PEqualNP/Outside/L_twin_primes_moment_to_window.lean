import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open MeasureTheory Complex Real Filter
open scoped FourierTransform BigOperators

namespace TwinPrimesMomentToWindow

noncomputable def bump (a b t : ℝ) : ℝ :=
  if a < t ∧ t < b then Real.exp (-1 / ((t - a) * (b - t))) else 0

lemma bump_eq_expNegInvGlue {a b : ℝ} (hab : a < b) (t : ℝ) :
    bump a b t = expNegInvGlue ((t - a) * (b - t)) := by
  unfold bump expNegInvGlue
  by_cases h : a < t ∧ t < b
  · have hpos : 0 < (t - a) * (b - t) := mul_pos (sub_pos.mpr h.1) (sub_pos.mpr h.2)
    rw [if_pos h, if_neg (not_le.mpr hpos)]
    congr 1
    ring
  · have hnonpos : (t - a) * (b - t) ≤ 0 := by
      rcases le_or_gt t a with hta | hta
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hta) (by linarith)
      · have hbt : b ≤ t := by
          by_contra hlt
          exact h ⟨hta, not_le.mp hlt⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hbt)
    rw [if_neg h, if_pos hnonpos]

lemma bump_nonneg (a b t : ℝ) : 0 ≤ bump a b t := by
  unfold bump
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma bump_le_one (a b t : ℝ) : bump a b t ≤ 1 := by
  unfold bump
  split_ifs with h
  · have hpos : 0 < (t - a) * (b - t) := mul_pos (sub_pos.mpr h.1) (sub_pos.mpr h.2)
    have hneg : -1 / ((t - a) * (b - t)) ≤ 0 := by
      rw [div_nonpos_iff]
      exact Or.inr ⟨by norm_num, hpos.le⟩
    exact Real.exp_le_one_iff.mpr hneg
  · norm_num

lemma bump_contDiff {a b : ℝ} (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (bump a b) := by
  have heq : bump a b = fun t => expNegInvGlue ((t - a) * (b - t)) :=
    funext (bump_eq_expNegInvGlue hab)
  rw [heq]
  exact expNegInvGlue.contDiff.comp
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id))

lemma bump_hasCompactSupport {a b : ℝ} : HasCompactSupport (bump a b) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a) (b := b)) (fun t ht => ?_)
  simp only [Function.mem_support, bump] at ht
  by_cases h : a < t ∧ t < b
  · exact ⟨h.1.le, h.2.le⟩
  · rw [if_neg h] at ht
    exact (ht rfl).elim

noncomputable def bFun (t : ℝ) : ℝ := bump (-1 / 40) (1 / 40) t

lemma bFun_neg (t : ℝ) : bFun (-t) = bFun t := by
  unfold bFun bump
  by_cases h : -1 / 40 < t ∧ t < 1 / 40
  · have h' : -1 / 40 < -t ∧ -t < 1 / 40 := ⟨by linarith, by linarith⟩
    rw [if_pos h', if_pos h]
    congr 1
    ring
  · have h' : ¬ (-1 / 40 < -t ∧ -t < 1 / 40) := by
      intro ⟨h1, h2⟩
      exact h ⟨by linarith, by linarith⟩
    rw [if_neg h', if_neg h]

lemma bFun_zero_of_abs {t : ℝ} (ht : (1 : ℝ) / 40 ≤ |t|) : bFun t = 0 := by
  unfold bFun bump
  rw [if_neg]
  intro ⟨h1, h2⟩
  have : |t| < 1 / 40 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma bFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) bFun :=
  bump_contDiff (by norm_num)

lemma bFun_continuous : Continuous bFun :=
  bFun_contDiff.continuous

lemma bFun_hasCompactSupport : HasCompactSupport bFun :=
  bump_hasCompactSupport

lemma bFun_integrable : Integrable bFun :=
  bFun_continuous.integrable_of_hasCompactSupport bFun_hasCompactSupport

noncomputable def kFun (t : ℝ) : ℝ :=
  ∫ v : ℝ, bFun v * Real.cos (2 * Real.pi * v * t)

noncomputable def lFun (t : ℝ) : ℝ :=
  Real.sin (Real.pi * t / 5) * kFun t

lemma kFun_neg (t : ℝ) : kFun (-t) = kFun t := by
  unfold kFun
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  have hcos : Real.cos (2 * Real.pi * v * (-t)) = Real.cos (2 * Real.pi * v * t) := by
    rw [show 2 * Real.pi * v * (-t) = -(2 * Real.pi * v * t) by ring, Real.cos_neg]
  rw [hcos]

lemma lFun_neg (t : ℝ) : lFun (-t) = -lFun t := by
  unfold lFun
  rw [kFun_neg, show Real.pi * (-t) / 5 = -(Real.pi * t / 5) by ring, Real.sin_neg, neg_mul]

noncomputable def gFun (u : ℝ) : ℂ :=
  ((bFun (u + 1 / 10) - bFun (u - 1 / 10) : ℝ) : ℂ) / (2 * Complex.I)

lemma gFun_zero_of_abs {u : ℝ} (hu : (1 : ℝ) / 8 ≤ |u|) : gFun u = 0 := by
  unfold gFun
  have h1 : (1 : ℝ) / 40 ≤ |u + 1 / 10| := by
    have := abs_sub_abs_le_abs_sub u (-1 / 10)
    have heq : u - (-1 / 10) = u + 1 / 10 := by ring
    rw [heq, show |(-1 : ℝ) / 10| = 1 / 10 by norm_num] at this
    linarith
  have h2 : (1 : ℝ) / 40 ≤ |u - 1 / 10| := by
    have := abs_sub_abs_le_abs_sub u (1 / 10)
    rw [show |(1 : ℝ) / 10| = 1 / 10 by norm_num] at this
    linarith
  rw [bFun_zero_of_abs h1, bFun_zero_of_abs h2]
  simp

lemma gFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) gFun := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => bFun (u + 1 / 10)) :=
    bFun_contDiff.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => bFun (u - 1 / 10)) :=
    bFun_contDiff.comp (contDiff_id.sub contDiff_const)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ((bFun (u + 1 / 10) - bFun (u - 1 / 10) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (h1.sub h2)
  exact h3.div_const (2 * Complex.I)

lemma gFun_hasCompactSupport : HasCompactSupport gFun := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 / 8 : ℝ)) (b := 1 / 8)) (fun u hu => ?_)
  simp only [Function.mem_support] at hu
  by_contra hmem
  apply hu
  apply gFun_zero_of_abs
  by_contra hlt
  have habs := abs_lt.mp (not_le.mp hlt)
  exact hmem ⟨by linarith, by linarith⟩

noncomputable def gSchwartz : SchwartzMap ℝ ℂ :=
  gFun_hasCompactSupport.toSchwartzMap gFun_contDiff

lemma integral_bFun_sin_eq_zero (s : ℝ) :
    ∫ v : ℝ, bFun v * Real.sin (2 * Real.pi * v * s) = 0 := by
  have hneg := Measure.integral_comp_mul_left (fun v : ℝ => bFun v * Real.sin (2 * Real.pi * v * s)) (-1 : ℝ)
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at hneg
  have hodd : ∀ v : ℝ, bFun (-1 * v) * Real.sin (2 * Real.pi * (-1 * v) * s) =
      -(bFun v * Real.sin (2 * Real.pi * v * s)) := by
    intro v
    rw [show (-1 : ℝ) * v = -v by ring, bFun_neg,
      show 2 * Real.pi * (-v) * s = -(2 * Real.pi * v * s) by ring, Real.sin_neg, mul_neg]
  simp_rw [hodd] at hneg
  rw [integral_neg] at hneg
  linarith

lemma integrable_bFun_mul_cos (s : ℝ) :
    Integrable (fun v : ℝ => bFun v * Real.cos (2 * Real.pi * v * s)) := by
  refine bFun_integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (bFun_continuous.mul (Real.continuous_cos.comp ((continuous_const.mul continuous_id).mul continuous_const))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |bFun v| * |Real.cos (2 * Real.pi * v * s)|
        ≤ |bFun v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |bFun v| := mul_one _

lemma integrable_bFun_mul_sin (s : ℝ) :
    Integrable (fun v : ℝ => bFun v * Real.sin (2 * Real.pi * v * s)) := by
  refine bFun_integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (bFun_continuous.mul (Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |bFun v| * |Real.sin (2 * Real.pi * v * s)|
        ≤ |bFun v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |bFun v| := mul_one _

lemma fourier_bFun (s : ℝ) :
    𝓕 (fun v : ℝ => (bFun v : ℂ)) s = (kFun s : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * s) * Complex.I) • (bFun v : ℂ) =
      Complex.ofRealCLM (bFun v * Real.cos (2 * Real.pi * v * s)) -
      Complex.I * Complex.ofRealCLM (bFun v * Real.sin (2 * Real.pi * v * s)) := by
    intro v
    rw [smul_eq_mul, show (-2 * Real.pi * v * s : ℝ) = -(2 * Real.pi * v * s) by ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofRealCLM_apply]
    ring
  simp_rw [hpt]
  have h1 : Integrable (fun v : ℝ => Complex.ofRealCLM (bFun v * Real.cos (2 * Real.pi * v * s))) :=
    Complex.ofRealCLM.integrable_comp (integrable_bFun_mul_cos s)
  have h2 : Integrable (fun v : ℝ => Complex.I * Complex.ofRealCLM (bFun v * Real.sin (2 * Real.pi * v * s))) :=
    (Complex.ofRealCLM.integrable_comp (integrable_bFun_mul_sin s)).const_mul Complex.I
  rw [integral_sub h1 h2, integral_const_mul,
    Complex.ofRealCLM.integral_comp_comm (integrable_bFun_mul_cos s),
    Complex.ofRealCLM.integral_comp_comm (integrable_bFun_mul_sin s),
    integral_bFun_sin_eq_zero]
  simp [kFun]

lemma fourier_bFun_shift (a s : ℝ) :
    𝓕 (fun u : ℝ => (bFun (u + a) : ℂ)) s =
      Complex.exp (↑(2 * Real.pi * a * s) * Complex.I) * (kFun s : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (v - a) * s) * Complex.I) • (bFun v : ℂ)) a
  have h1 : ∀ u : ℝ,
      Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) • (bFun (u + a) : ℂ) =
      Complex.exp (↑(-2 * Real.pi * ((u + a) - a) * s) * Complex.I) • (bFun (u + a) : ℂ) := by
    intro u; simp
  simp_rw [h1]
  rw [hshift]
  have hpt : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * (v - a) * s) * Complex.I) • (bFun v : ℂ) =
      Complex.exp (↑(2 * Real.pi * a * s) * Complex.I) *
        (Complex.exp (↑(-2 * Real.pi * v * s) * Complex.I) • (bFun v : ℂ)) := by
    intro v
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← Real.fourier_real_eq_integral_exp_smul, fourier_bFun]

lemma fourier_gFun (s : ℝ) : 𝓕 gFun s = (lFun s : ℂ) := by
  have hg1 : Integrable (fun u : ℝ => (bFun (u + 1 / 10) : ℂ)) :=
    (bFun_integrable.comp_add_right (1 / 10 : ℝ)).ofReal
  have hg2 : Integrable (fun u : ℝ => (bFun (u + (-1 / 10)) : ℂ)) :=
    (bFun_integrable.comp_add_right (-1 / 10 : ℝ)).ofReal
  have hdef : gFun = fun u : ℝ => (2 * Complex.I)⁻¹ * ((bFun (u + 1 / 10) : ℂ) - (bFun (u + (-1 / 10)) : ℂ)) := by
    ext u
    unfold gFun
    have hsub : u - 1 / 10 = u + (-1 / 10) := by ring
    rw [hsub, div_eq_inv_mul, Complex.ofReal_sub]
  rw [hdef, Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ u : ℝ,
      Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) •
        ((2 * Complex.I)⁻¹ * ((bFun (u + 1 / 10) : ℂ) - (bFun (u + (-1 / 10)) : ℂ))) =
      (2 * Complex.I)⁻¹ *
        (Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) • (bFun (u + 1 / 10) : ℂ) -
         Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) • (bFun (u + (-1 / 10)) : ℂ)) := by
    intro u
    simp only [smul_eq_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hcexp_cont : Continuous (fun u : ℝ => Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)
  have hint1 : Integrable (fun u : ℝ =>
      Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) • (bFun (u + 1 / 10) : ℂ)) := by
    refine hg1.norm.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact (hcexp_cont.smul
        (Complex.continuous_ofReal.comp (bFun_continuous.comp (continuous_id.add continuous_const)))).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hint2 : Integrable (fun u : ℝ =>
      Complex.exp (↑(-2 * Real.pi * u * s) * Complex.I) • (bFun (u + (-1 / 10)) : ℂ)) := by
    refine hg2.norm.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact (hcexp_cont.smul
        (Complex.continuous_ofReal.comp (bFun_continuous.comp (continuous_id.add continuous_const)))).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [integral_sub hint1 hint2, ← Real.fourier_real_eq_integral_exp_smul, ← Real.fourier_real_eq_integral_exp_smul,
    fourier_bFun_shift (1 / 10) s, fourier_bFun_shift (-1 / 10) s]
  dsimp only [lFun]
  rw [Complex.ofReal_mul (Real.sin (Real.pi * s / 5)) (kFun s), Complex.ofReal_sin, Complex.sin]
  have he1 : (↑(2 * Real.pi * (1 / 10) * s) : ℂ) * Complex.I = ((Real.pi * s / 5 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have he2 : (↑(2 * Real.pi * (-1 / 10) * s) : ℂ) * Complex.I = -(((Real.pi * s / 5 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [he1, he2]
  have hI : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  field_simp [hI]
  rw [Complex.I_sq]
  ring

lemma fourier_gSchwartz_apply (s : ℝ) : (𝓕 gSchwartz) s = (lFun s : ℂ) := by
  change (𝓕 (gSchwartz : ℝ → ℂ)) s = (lFun s : ℂ)
  exact fourier_gFun s

lemma lFun_continuous : Continuous lFun := by
  have hc : Continuous (fun s : ℝ => ((𝓕 gSchwartz) s).re) :=
    Complex.continuous_re.comp (𝓕 gSchwartz).continuous
  refine hc.congr fun s => ?_
  rw [fourier_gSchwartz_apply]
  simp

lemma lFun_integrable : Integrable lFun := by
  have hi : Integrable (fun s : ℝ => ((𝓕 gSchwartz) s).re) :=
    (𝓕 gSchwartz).integrable.re
  refine hi.congr (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  rw [fourier_gSchwartz_apply]
  simp

lemma lFun_sq_integrable : Integrable (fun s : ℝ => (lFun s) ^ 2) := by
  set B : ℝ := ∫ v : ℝ, ‖gFun v‖
  have hbound : ∀ s : ℝ, |lFun s| ≤ B := by
    intro s
    have h1 := Real.norm_fourier_le_integral_norm gFun s
    rw [fourier_gFun, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  refine (lFun_integrable.norm.const_mul B).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact (lFun_continuous.pow 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_pow, sq, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound s) (abs_nonneg _)

lemma lFun_sq_cexp_eq_zero (β : ℝ) (hβ : (1 : ℝ) / 4 ≤ |β|) :
    ∫ s : ℝ, ((lFun s : ℂ) ^ 2) * Complex.exp (↑(2 * Real.pi * β * s) * Complex.I) = 0 := by
  have hprod_int : Integrable (fun p : ℝ × ℝ =>
      gFun p.2 * (Complex.exp (↑(2 * Real.pi * (β - p.2) * p.1) * Complex.I) * (𝓕 gSchwartz) p.1))
      (volume.prod volume) := by
    have hnorm : Integrable (fun p : ℝ × ℝ => ‖(𝓕 gSchwartz) p.1‖ * ‖gFun p.2‖) (volume.prod volume) :=
      (𝓕 gSchwartz).integrable.norm.mul_prod gSchwartz.integrable.norm
    refine hnorm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have harg : Continuous (fun p : ℝ × ℝ => ((2 * Real.pi * (β - p.2) * p.1 : ℝ) : ℂ) * Complex.I) :=
        (Complex.continuous_ofReal.comp
          ((continuous_const.mul (continuous_const.sub continuous_snd)).mul continuous_fst)).mul continuous_const
      have hcont : Continuous (fun p : ℝ × ℝ =>
          gFun p.2 * (Complex.exp (↑(2 * Real.pi * (β - p.2) * p.1) * Complex.I) * (𝓕 gSchwartz) p.1)) :=
        (gSchwartz.continuous.comp continuous_snd).mul
          ((Complex.continuous_exp.comp harg).mul ((𝓕 gSchwartz).continuous.comp continuous_fst))
      exact hcont.aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_comm]
  have hlhs : ∀ s : ℝ,
      ((lFun s : ℂ) ^ 2) * Complex.exp (↑(2 * Real.pi * β * s) * Complex.I) =
      ∫ v : ℝ, gFun v * (Complex.exp (↑(2 * Real.pi * (β - v) * s) * Complex.I) * (𝓕 gSchwartz) s) := by
    intro s
    have hstep1 : ((lFun s : ℂ) ^ 2) * Complex.exp (↑(2 * Real.pi * β * s) * Complex.I) =
        (𝓕 gFun s) * (Complex.exp (↑(2 * Real.pi * β * s) * Complex.I) * (𝓕 gSchwartz) s) := by
      rw [fourier_gFun, fourier_gSchwartz_apply]
      ring
    rw [hstep1, Real.fourier_real_eq_integral_exp_smul, ← integral_mul_const]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [smul_eq_mul]
    have hexp : Complex.exp (↑(-2 * Real.pi * v * s) * Complex.I) *
        Complex.exp (↑(2 * Real.pi * β * s) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * (β - v) * s) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  simp_rw [hlhs]
  rw [MeasureTheory.integral_integral_swap hprod_int]
  have hinner : ∀ v : ℝ,
      (∫ s : ℝ, gFun v * (Complex.exp (↑(2 * Real.pi * (β - v) * s) * Complex.I) * (𝓕 gSchwartz) s)) = 0 := by
    intro v
    rw [integral_const_mul]
    have hinv : (∫ s : ℝ, Complex.exp (↑(2 * Real.pi * (β - v) * s) * Complex.I) * (𝓕 gSchwartz) s) =
        gFun (β - v) := by
      have h1 : 𝓕⁻ (𝓕 (gSchwartz : ℝ → ℂ)) (β - v) = gFun (β - v) := by
        have hinv_eq := gSchwartz.continuous.fourierInv_fourier_eq gSchwartz.integrable (𝓕 gSchwartz).integrable
        exact congrFun hinv_eq (β - v)
      rw [← h1, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      rw [smul_eq_mul]
      have harg : (↑(2 * Real.pi * (β - v) * s) : ℂ) * Complex.I =
          (↑(-2 * Real.pi * s * -(β - v)) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg]
      rfl
    rw [hinv]
    by_cases hv : (1 : ℝ) / 8 ≤ |v|
    · rw [gFun_zero_of_abs hv, zero_mul]
    · have hv' : |v| < 1 / 8 := not_le.mp hv
      have hbv : (1 : ℝ) / 8 ≤ |β - v| := by
        have := abs_sub_abs_le_abs_sub β v
        linarith
      rw [gFun_zero_of_abs hbv, mul_zero]
  simp_rw [hinner]
  simp

lemma lFun_sq_cos_eq_zero (β : ℝ) (hβ : (1 : ℝ) / 4 ≤ |β|) :
    ∫ s : ℝ, (lFun s) ^ 2 * Real.cos (2 * Real.pi * β * s) = 0 := by
  have hint : Integrable (fun s : ℝ => ((lFun s : ℂ) ^ 2) * Complex.exp (↑(2 * Real.pi * β * s) * Complex.I)) := by
    refine lFun_sq_integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
    · have harg : Continuous (fun s : ℝ => ((2 * Real.pi * β * s : ℝ) : ℂ) * Complex.I) :=
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const
      exact (((Complex.continuous_ofReal.comp lFun_continuous).pow 2).mul
        (Complex.continuous_exp.comp harg)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have hre := congrArg Complex.re (lFun_sq_cexp_eq_zero β hβ)
  have hcomm := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.zero_re] at hcomm hre
  rw [← hcomm] at hre
  refine Eq.trans ?_ hre
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [sq, Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

noncomputable def J (α : ℝ) : ℝ :=
  ∫ s : ℝ, (lFun s) ^ 2 * Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)

lemma integrable_lFun_sq_cos (β : ℝ) :
    Integrable (fun s : ℝ => (lFun s) ^ 2 * Real.cos (2 * Real.pi * β * s)) := by
  refine lFun_sq_integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact ((lFun_continuous.pow 2).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |(lFun s) ^ 2| * |Real.cos (2 * Real.pi * β * s)|
        ≤ |(lFun s) ^ 2| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |(lFun s) ^ 2| := mul_one _

lemma J_eq_zero_of_outside {α : ℝ} (h1 : (1 : ℝ) / 4 ≤ |α + 2|) (h2 : (1 : ℝ) / 4 ≤ |α - 2|) :
    J α = 0 := by
  unfold J
  have htrig : ∀ s : ℝ,
      (lFun s) ^ 2 * Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s) =
      (1 / 2 : ℝ) * ((lFun s) ^ 2 * Real.cos (2 * Real.pi * (α + 2) * s) +
                     (lFun s) ^ 2 * Real.cos (2 * Real.pi * (α - 2) * s)) := by
    intro s
    have hadd := Real.cos_add (2 * Real.pi * α * s) (4 * Real.pi * s)
    have hsub := Real.cos_sub (2 * Real.pi * α * s) (4 * Real.pi * s)
    have ha : 2 * Real.pi * α * s + 4 * Real.pi * s = 2 * Real.pi * (α + 2) * s := by ring
    have hs : 2 * Real.pi * α * s - 4 * Real.pi * s = 2 * Real.pi * (α - 2) * s := by ring
    rw [ha] at hadd
    rw [hs] at hsub
    have hcos : Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s) =
        (1 / 2 : ℝ) * (Real.cos (2 * Real.pi * (α + 2) * s) + Real.cos (2 * Real.pi * (α - 2) * s)) := by
      linarith
    calc (lFun s) ^ 2 * Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)
        = (lFun s) ^ 2 * (Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)) := by ring
      _ = (lFun s) ^ 2 * ((1 / 2 : ℝ) * (Real.cos (2 * Real.pi * (α + 2) * s) + Real.cos (2 * Real.pi * (α - 2) * s))) := by
          rw [hcos]
      _ = (1 / 2 : ℝ) * ((lFun s) ^ 2 * Real.cos (2 * Real.pi * (α + 2) * s) +
                         (lFun s) ^ 2 * Real.cos (2 * Real.pi * (α - 2) * s)) := by ring
  simp_rw [htrig]
  rw [integral_const_mul, integral_add (integrable_lFun_sq_cos (α + 2)) (integrable_lFun_sq_cos (α - 2)),
    lFun_sq_cos_eq_zero (α + 2) h1, lFun_sq_cos_eq_zero (α - 2) h2]
  ring

lemma J_le (α : ℝ) : J α ≤ ∫ s : ℝ, (lFun s) ^ 2 := by
  unfold J
  have hint : Integrable (fun s : ℝ => (lFun s) ^ 2 * Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)) := by
    refine lFun_sq_integrable.norm.mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
    · exact (((lFun_continuous.pow 2).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
      calc |(lFun s) ^ 2| * |Real.cos (4 * Real.pi * s)| * |Real.cos (2 * Real.pi * α * s)|
          ≤ |(lFun s) ^ 2| * 1 * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            · exact Real.abs_cos_le_one _
            · exact abs_nonneg _
            · positivity
        _ = |(lFun s) ^ 2| := by ring
  refine integral_mono hint lFun_sq_integrable (fun s => ?_)
  have hcos : Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s) ≤ 1 := by
    have h1 := Real.abs_cos_le_one (4 * Real.pi * s)
    have h2 := Real.abs_cos_le_one (2 * Real.pi * α * s)
    have habs : |Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)| ≤ 1 := by
      rw [abs_mul]
      calc |Real.cos (4 * Real.pi * s)| * |Real.cos (2 * Real.pi * α * s)|
          ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact (le_abs_self _).trans habs
  calc (lFun s) ^ 2 * Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)
      = (lFun s) ^ 2 * (Real.cos (4 * Real.pi * s) * Real.cos (2 * Real.pi * α * s)) := by ring
    _ ≤ (lFun s) ^ 2 * 1 := mul_le_mul_of_nonneg_left hcos (sq_nonneg _)
    _ = (lFun s) ^ 2 := mul_one _

noncomputable def WFun (t : ℝ) : ℝ := bump 1 (51 / 50) t

noncomputable def TFun (X : ℕ) : ℝ := 2 * Real.pi * (X : ℝ)

def wFin (X : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)

noncomputable def uFun (X n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * WFun ((n : ℝ) / X) / Real.sqrt n

noncomputable def PFun (X : ℕ) (t : ℝ) : ℂ :=
  (wFin X).sum (fun n => (uFun X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))

noncomputable def IFun (X : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (lFun (t / TFun X)) ^ 2 * (1 + σ * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2

lemma uFun_nonneg (X n : ℕ) : 0 ≤ uFun X n := by
  unfold uFun WFun
  exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (bump_nonneg _ _ _)) (Real.sqrt_nonneg _)

lemma PFun_neg (X : ℕ) (t : ℝ) : PFun X (-t) = starRingEnd ℂ (PFun X t) := by
  unfold PFun
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

lemma norm_PFun_neg (X : ℕ) (t : ℝ) : ‖PFun X (-t)‖ = ‖PFun X t‖ := by
  rw [PFun_neg, Complex.norm_conj]

lemma norm_PFun_le (X : ℕ) (t : ℝ) : ‖PFun X t‖ ≤ (wFin X).sum (fun n => |uFun X n|) := by
  unfold PFun
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hexp : ‖Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))‖ = 1 := by
    have heq : -Complex.I * (t : ℂ) * (Real.log n : ℂ) = ↑(-(t * Real.log n)) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.norm_exp_ofReal_mul_I]
  rw [hexp, mul_one]

lemma continuous_PFun (X : ℕ) : Continuous (PFun X) := by
  unfold PFun
  induction (wFin X) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuous_const
  | insert a s ha ih =>
    have hterm : Continuous (fun t : ℝ =>
        (uFun X a : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log a : ℂ))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
    have heq : (fun t : ℝ => (insert a s).sum (fun n =>
        (uFun X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
        fun t : ℝ =>
          (uFun X a : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log a : ℂ)) +
          s.sum (fun n => (uFun X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
      ext t; exact Finset.sum_insert ha
    rw [heq]
    exact hterm.add ih

lemma norm_PFun_sq_expand (X : ℕ) (t : ℝ) :
    ‖PFun X t‖ ^ 2 =
      (wFin X).sum (fun m => (wFin X).sum (fun n =>
        uFun X m * uFun X n * Real.cos (t * (Real.log m - Real.log n)))) := by
  have hsq : ((‖PFun X t‖ ^ 2 : ℝ) : ℂ) = PFun X t * starRingEnd ℂ (PFun X t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hexp : PFun X t * starRingEnd ℂ (PFun X t) =
      (wFin X).sum (fun m => (wFin X).sum (fun n =>
        ((uFun X m * uFun X n : ℝ) : ℂ) *
          Complex.exp (↑(-(t * (Real.log m - Real.log n))) * Complex.I))) := by
    rw [← PFun_neg]
    unfold PFun
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hmul : Complex.exp (-Complex.I * (t : ℂ) * (Real.log m : ℂ)) *
        Complex.exp (-Complex.I * ((-t : ℝ) : ℂ) * (Real.log n : ℂ)) =
        Complex.exp (↑(-(t * (Real.log m - Real.log n))) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (uFun X m : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log m : ℂ)) *
            ((uFun X n : ℂ) * Complex.exp (-Complex.I * ((-t : ℝ) : ℂ) * (Real.log n : ℂ)))
        = ((uFun X m : ℂ) * (uFun X n : ℂ)) *
            (Complex.exp (-Complex.I * (t : ℂ) * (Real.log m : ℂ)) *
             Complex.exp (-Complex.I * ((-t : ℝ) : ℂ) * (Real.log n : ℂ))) := by ring
      _ = ((uFun X m * uFun X n : ℝ) : ℂ) *
            Complex.exp (↑(-(t * (Real.log m - Real.log n))) * Complex.I) := by
          rw [hmul, Complex.ofReal_mul]
  have hre := congrArg Complex.re (hsq.trans hexp)
  simp only [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Real.cos_neg]
  ring

lemma integrable_lFun_sq_div {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => (lFun (t / T)) ^ 2) := by
  have heq : (fun t : ℝ => (lFun (t / T)) ^ 2) = (fun t : ℝ => (lFun (T⁻¹ * t)) ^ 2) := by
    ext t; rw [div_eq_inv_mul]
  rw [heq]
  exact lFun_sq_integrable.comp_mul_left' (inv_ne_zero hT.ne')

lemma integrable_I_integrand (X : ℕ) (hX : 1 ≤ X) (σ : ℝ) :
    Integrable (fun t : ℝ =>
      (lFun (t / TFun X)) ^ 2 * (1 + σ * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2) := by
  have hT : 0 < TFun X := by
    unfold TFun
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    positivity
  set U : ℝ := (wFin X).sum (fun n => |uFun X n|)
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := (1 + |σ|) * U ^ 2
  refine ((integrable_lFun_sq_div hT).norm.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · have hcos_cont : Continuous (fun t : ℝ => Real.cos (4 * Real.pi * t / TFun X)) :=
      Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const _)
    exact ((((lFun_continuous.comp (continuous_id.div_const _)).pow 2).mul
      (continuous_const.add (continuous_const.mul hcos_cont))).mul
      ((continuous_PFun X).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
    have h1 : |1 + σ * Real.cos (4 * Real.pi * t / TFun X)| ≤ 1 + |σ| := by
      calc |1 + σ * Real.cos (4 * Real.pi * t / TFun X)|
          ≤ |1| + |σ * Real.cos (4 * Real.pi * t / TFun X)| := abs_add_le _ _
        _ = 1 + |σ| * |Real.cos (4 * Real.pi * t / TFun X)| := by rw [abs_one, abs_mul]
        _ ≤ 1 + |σ| * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ = 1 + |σ| := by rw [mul_one]
    have h2 : |‖PFun X t‖ ^ 2| ≤ U ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_PFun_le X t) 2
    calc |(lFun (t / TFun X)) ^ 2| * |1 + σ * Real.cos (4 * Real.pi * t / TFun X)| * |‖PFun X t‖ ^ 2|
        ≤ |(lFun (t / TFun X)) ^ 2| * (1 + |σ|) * U ^ 2 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          · exact h2
          · exact abs_nonneg _
          · positivity
      _ = C * |(lFun (t / TFun X)) ^ 2| := by ring

lemma integral_even_eq_two_mul_Ioi {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t) :
    ∫ t : ℝ, f t = 2 * ∫ t in Set.Ioi (0 : ℝ), f t := by
  rw [← integral_comp_abs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, heven]

lemma I_diff_eq (X : ℕ) (hX : 1 ≤ X) :
    IFun X 1 - IFun X (-1) =
      TFun X * (wFin X).sum (fun m => (wFin X).sum (fun n =>
        uFun X m * uFun X n * J ((X : ℝ) * Real.log ((m : ℝ) / n)))) := by
  have hT : 0 < TFun X := by
    unfold TFun
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    positivity
  unfold IFun
  rw [← integral_sub (integrable_I_integrand X hX 1).integrableOn
      (integrable_I_integrand X hX (-1)).integrableOn]
  set G : ℝ → ℝ := fun t =>
    (lFun (t / TFun X)) ^ 2 * Real.cos (4 * Real.pi * t / TFun X) * ‖PFun X t‖ ^ 2
  have hsub : ∀ t : ℝ,
      (lFun (t / TFun X)) ^ 2 * (1 + 1 * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2 -
      (lFun (t / TFun X)) ^ 2 * (1 + (-1) * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2 =
      2 * G t := by
    intro t
    dsimp [G]
    ring
  simp_rw [hsub]
  rw [integral_const_mul]
  have hGint : Integrable G := by
    have hdiff := (integrable_I_integrand X hX 1).sub (integrable_I_integrand X hX (-1))
    have hGeq : G = fun t => (1 / 2 : ℝ) *
        ((lFun (t / TFun X)) ^ 2 * (1 + 1 * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2 -
         (lFun (t / TFun X)) ^ 2 * (1 + (-1) * Real.cos (4 * Real.pi * t / TFun X)) * ‖PFun X t‖ ^ 2) := by
      ext t; dsimp [G]; ring
    rw [hGeq]
    exact hdiff.const_mul (1 / 2)
  have hGeven : ∀ t : ℝ, G (-t) = G t := by
    intro t
    dsimp [G]
    rw [neg_div, lFun_neg, neg_sq, show 4 * Real.pi * (-t) / TFun X = -(4 * Real.pi * t / TFun X) by ring,
      Real.cos_neg, norm_PFun_neg]
  rw [← integral_even_eq_two_mul_Ioi hGeven]
  have hscale : ∫ t : ℝ, G t = TFun X * ∫ s : ℝ, G (TFun X * s) := by
    have h1 := Measure.integral_comp_mul_left G (TFun X)
    rw [abs_of_pos (inv_pos.mpr hT), smul_eq_mul] at h1
    have hne : TFun X ≠ 0 := hT.ne'
    field_simp [hne] at h1 ⊢
    linarith
  rw [hscale]
  refine congrArg (TFun X * ·) ?_
  have hexp' : ∀ s : ℝ,
      G (TFun X * s) = (wFin X).sum (fun m => (wFin X).sum (fun n =>
        uFun X m * uFun X n *
          ((lFun s) ^ 2 * Real.cos (4 * Real.pi * s) *
            Real.cos (2 * Real.pi * ((X : ℝ) * Real.log ((m : ℝ) / n)) * s)))) := by
    intro s
    dsimp [G]
    have hdiv1 : TFun X * s / TFun X = s := mul_div_cancel_left₀ s hT.ne'
    have hdiv2 : 4 * Real.pi * (TFun X * s) / TFun X = 4 * Real.pi * s := by
      field_simp [hT.ne']
    rw [hdiv1, hdiv2, norm_PFun_sq_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : X < m := (Finset.mem_filter.mp hm).2.1
      exact_mod_cast (by omega : 0 < m)
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : X < n := (Finset.mem_filter.mp hn).2.1
      exact_mod_cast (by omega : 0 < n)
    have hlog : TFun X * s * (Real.log m - Real.log n) =
        2 * Real.pi * ((X : ℝ) * Real.log ((m : ℝ) / n)) * s := by
      rw [Real.log_div hmpos.ne' hnpos.ne']
      unfold TFun
      ring
    rw [hlog]
    ring
  simp_rw [hexp']
  have hterm_int : ∀ m n : ℕ, Integrable (fun s : ℝ =>
      uFun X m * uFun X n *
        ((lFun s) ^ 2 * Real.cos (4 * Real.pi * s) *
          Real.cos (2 * Real.pi * ((X : ℝ) * Real.log ((m : ℝ) / n)) * s))) := by
    intro m n
    refine (lFun_sq_integrable.norm.const_mul |uFun X m * uFun X n|).mono' ?_
      (Filter.Eventually.of_forall fun s => ?_)
    · exact (continuous_const.mul (((lFun_continuous.pow 2).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul]
      have h1 := Real.abs_cos_le_one (4 * Real.pi * s)
      have h2 := Real.abs_cos_le_one (2 * Real.pi * ((X : ℝ) * Real.log ((m : ℝ) / n)) * s)
      calc |uFun X m| * |uFun X n| * (|lFun s ^ 2| * |Real.cos (4 * Real.pi * s)| *
              |Real.cos (2 * Real.pi * ((X : ℝ) * Real.log ((m : ℝ) / n)) * s)|)
          ≤ |uFun X m| * |uFun X n| * (|lFun s ^ 2| * 1 * 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            · exact h2
            · exact abs_nonneg _
            · positivity
        _ = |uFun X m| * |uFun X n| * |lFun s ^ 2| := by ring
  have hsum_int_able : ∀ (S : Finset ℕ) (f : ℕ → ℝ → ℝ), (∀ i ∈ S, Integrable (f i)) →
      Integrable (fun s : ℝ => S.sum (fun i => f i s)) := by
    intro S f hf
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact integrable_zero ℝ ℝ volume
    | insert a s ha ih =>
      have hfa : Integrable (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : Integrable (fun x : ℝ => s.sum (fun i => f i x)) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have heq : (fun x : ℝ => (insert a s).sum (fun i => f i x)) =
          fun x : ℝ => f a x + s.sum (fun i => f i x) := by
        ext x; exact Finset.sum_insert ha
      rw [heq]
      exact hfa.add hfs
  have hsum_int : ∀ (S : Finset ℕ) (f : ℕ → ℝ → ℝ), (∀ i ∈ S, Integrable (f i)) →
      ∫ s : ℝ, S.sum (fun i => f i s) = S.sum (fun i => ∫ s : ℝ, f i s) := by
    intro S f hf
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hfa : Integrable (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : Integrable (fun x : ℝ => s.sum (fun i => f i x)) :=
        hsum_int_able s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simp_rw [Finset.sum_insert ha]
      rw [integral_add hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
  rw [hsum_int _ _ (fun m _ => hsum_int_able _ _ (fun n _ => hterm_int m n))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hsum_int _ _ (fun n _ => hterm_int m n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  rfl

lemma log_ratio_outside_of_le {X m n : ℕ} (hX : 1000 ≤ X)
    (hm : m ∈ wFin X) (hn : n ∈ wFin X) (hle : n ≤ m) (hne2 : m ≠ n + 2) :
    (1 : ℝ) / 4 ≤ |(X : ℝ) * Real.log ((m : ℝ) / n) + 2| ∧
    (1 : ℝ) / 4 ≤ |(X : ℝ) * Real.log ((m : ℝ) / n) - 2| := by
  have hnX : X < n := (Finset.mem_filter.mp hn).2.1
  have hn51 : 50 * n < 51 * X := (Finset.mem_filter.mp hn).2.2
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hge1 : (1 : ℝ) ≤ (m : ℝ) / n := by
    rw [one_le_div hnpos]
    exact_mod_cast hle
  have hnonneg : 0 ≤ (X : ℝ) * Real.log ((m : ℝ) / n) :=
    mul_nonneg hXpos.le (Real.log_nonneg hge1)
  have hplus : (1 : ℝ) / 4 ≤ |(X : ℝ) * Real.log ((m : ℝ) / n) + 2| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨hplus, ?_⟩
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rw [div_self hnpos.ne', Real.log_one, mul_zero]
    norm_num
  · by_cases h1 : m = n + 1
    · subst h1
      have hlog : Real.log (((n + 1 : ℕ) : ℝ) / n) ≤ 1 / (n : ℝ) := by
        have hpos : 0 < ((n + 1 : ℕ) : ℝ) / n := div_pos (by positivity) hnpos
        have hle' := Real.log_le_sub_one_of_pos hpos
        have heq : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / (n : ℝ) := by
          push_cast
          field_simp [hnpos.ne']
          ring
        linarith
      have hα : (X : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / n) ≤ 1 := by
        calc (X : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / n)
            ≤ (X : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hlog hXpos.le
          _ = (X : ℝ) / n := by ring
          _ ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hnX.le)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hge3 : n + 3 ≤ m := by omega
      have hratio : ((n + 3 : ℕ) : ℝ) / n ≤ (m : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hge3) hnpos.le
      have hlog1 : Real.log (((n + 3 : ℕ) : ℝ) / n) ≤ Real.log ((m : ℝ) / n) :=
        Real.log_le_log (div_pos (by positivity) hnpos) hratio
      have hlog2 : (3 : ℝ) / ((n : ℝ) + 3) ≤ Real.log (((n + 3 : ℕ) : ℝ) / n) := by
        have hpos : 0 < ((n + 3 : ℕ) : ℝ) / n := div_pos (by positivity) hnpos
        have hlb := Real.one_sub_inv_le_log_of_pos hpos
        have heq : 1 - (((n + 3 : ℕ) : ℝ) / n)⁻¹ = 3 / ((n : ℝ) + 3) := by
          push_cast
          field_simp [hnpos.ne', (show (n : ℝ) + 3 ≠ 0 by positivity)]
          ring
        linarith
      have hn3 : (n : ℝ) + 3 < (52 / 50 : ℝ) * X := by
        have h51 : (50 : ℝ) * n < 51 * X := by exact_mod_cast hn51
        have h1000 : (1000 : ℝ) ≤ X := by exact_mod_cast hX
        linarith
      have hα : (9 : ℝ) / 4 < (X : ℝ) * Real.log ((m : ℝ) / n) := by
        have hstep : (9 : ℝ) / 4 < (X : ℝ) * (3 / ((n : ℝ) + 3)) := by
          rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
          linarith
        exact hstep.trans_le (mul_le_mul_of_nonneg_left (hlog2.trans hlog1) hXpos.le)
      rw [abs_of_nonneg (by linarith)]
      linarith

lemma J_eq_zero_of_ne_two {X m n : ℕ} (hX : 1000 ≤ X)
    (hm : m ∈ wFin X) (hn : n ∈ wFin X) (h1 : m ≠ n + 2) (h2 : n ≠ m + 2) :
    J ((X : ℝ) * Real.log ((m : ℝ) / n)) = 0 := by
  rcases le_total n m with hle | hle
  · obtain ⟨ha, hb⟩ := log_ratio_outside_of_le hX hm hn hle h1
    exact J_eq_zero_of_outside ha hb
  · obtain ⟨ha, hb⟩ := log_ratio_outside_of_le hX hn hm hle h2
    have hlog : Real.log ((m : ℝ) / n) = -Real.log ((n : ℝ) / m) := by
      rw [← Real.log_inv, inv_div]
    have h1' : (1 : ℝ) / 4 ≤ |(X : ℝ) * Real.log ((m : ℝ) / n) + 2| := by
      rw [hlog, mul_neg]
      have : -((X : ℝ) * Real.log ((n : ℝ) / m)) + 2 = -((X : ℝ) * Real.log ((n : ℝ) / m) - 2) := by ring
      rw [this, abs_neg]
      exact hb
    have h2' : (1 : ℝ) / 4 ≤ |(X : ℝ) * Real.log ((m : ℝ) / n) - 2| := by
      rw [hlog, mul_neg]
      have : -((X : ℝ) * Real.log ((n : ℝ) / m)) - 2 = -((X : ℝ) * Real.log ((n : ℝ) / m) + 2) := by ring
      rw [this, abs_neg]
      exact ha
    exact J_eq_zero_of_outside h1' h2'

lemma I_diff_div_T_le (X : ℕ) (hX : 1000 ≤ X) :
    (IFun X 1 - IFun X (-1)) / TFun X ≤
      (2 * ∫ s : ℝ, (lFun s) ^ 2) *
        (((wFin X).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ)) := by
  have hX1 : 1 ≤ X := by omega
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hTpos : 0 < TFun X := by unfold TFun; positivity
  rw [I_diff_eq X hX1, mul_div_cancel_left₀ _ hTpos.ne']
  set C₀ : ℝ := ∫ s : ℝ, (lFun s) ^ 2
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun s => sq_nonneg _)
  have hterm : ∀ m ∈ wFin X,
      (wFin X).sum (fun n => uFun X m * uFun X n * J ((X : ℝ) * Real.log ((m : ℝ) / n))) ≤
      (if m + 2 ∈ wFin X then uFun X m * uFun X (m + 2) * C₀ else 0) +
      (if 2 ≤ m ∧ m - 2 ∈ wFin X then uFun X m * uFun X (m - 2) * C₀ else 0) := by
    intro m hm
    have hsum_le : (wFin X).sum (fun n => uFun X m * uFun X n * J ((X : ℝ) * Real.log ((m : ℝ) / n))) ≤
        (wFin X).sum (fun n =>
          (if n = m + 2 then uFun X m * uFun X (m + 2) * C₀ else 0) +
          (if m = n + 2 then uFun X m * uFun X n * C₀ else 0)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      by_cases h1 : n = m + 2
      · have h2 : m ≠ n + 2 := by omega
        rw [if_pos h1, if_neg h2, add_zero, h1]
        exact mul_le_mul_of_nonneg_left (J_le _) (mul_nonneg (uFun_nonneg X m) (uFun_nonneg X (m + 2)))
      · by_cases h2 : m = n + 2
        · rw [if_neg h1, if_pos h2, zero_add]
          exact mul_le_mul_of_nonneg_left (J_le _) (mul_nonneg (uFun_nonneg X m) (uFun_nonneg X n))
        · rw [if_neg h1, if_neg h2, add_zero, J_eq_zero_of_ne_two hX hm hn h2 h1, mul_zero]
    refine hsum_le.trans ?_
    rw [Finset.sum_add_distrib]
    have hs1 : (wFin X).sum (fun n => if n = m + 2 then uFun X m * uFun X (m + 2) * C₀ else 0) =
        if m + 2 ∈ wFin X then uFun X m * uFun X (m + 2) * C₀ else 0 := by
      simp
    have hs2 : (wFin X).sum (fun n => if m = n + 2 then uFun X m * uFun X n * C₀ else 0) =
        if 2 ≤ m ∧ m - 2 ∈ wFin X then uFun X m * uFun X (m - 2) * C₀ else 0 := by
      by_cases h2m : 2 ≤ m
      · have heq : ∀ n : ℕ, (m = n + 2) ↔ (n = m - 2) := fun n => by omega
        simp_rw [heq]
        simp [h2m]
      · have hno : ∀ n : ℕ, m ≠ n + 2 := fun n => by omega
        simp [h2m, hno]
    rw [hs1, hs2]
  have hsum1 : (wFin X).sum (fun m => (wFin X).sum (fun n =>
      uFun X m * uFun X n * J ((X : ℝ) * Real.log ((m : ℝ) / n)))) ≤
      (wFin X).sum (fun m => if m + 2 ∈ wFin X then uFun X m * uFun X (m + 2) * C₀ else 0) +
      (wFin X).sum (fun m => if 2 ≤ m ∧ m - 2 ∈ wFin X then uFun X m * uFun X (m - 2) * C₀ else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  have hshift_eq :
      (wFin X).sum (fun m => if 2 ≤ m ∧ m - 2 ∈ wFin X then uFun X m * uFun X (m - 2) * C₀ else 0) =
      (wFin X).sum (fun n => if n + 2 ∈ wFin X then uFun X n * uFun X (n + 2) * C₀ else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij (fun m _ => m - 2) ?_ ?_ ?_ ?_
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmw, h2m, hm2w⟩
      exact Finset.mem_filter.mpr ⟨hm2w, by rwa [Nat.sub_add_cancel h2m]⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      have h1 : 2 ≤ m₁ := (Finset.mem_filter.mp hm₁).2.1
      have h2 : 2 ≤ m₂ := (Finset.mem_filter.mp hm₂).2.1
      omega
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnw, hn2w⟩
      refine ⟨n + 2, Finset.mem_filter.mpr ⟨hn2w, by omega, by simpa using hnw⟩, by omega⟩
    · intro m hm
      have h2m : 2 ≤ m := (Finset.mem_filter.mp hm).2.1
      rw [Nat.sub_add_cancel h2m]
      ring
  have hsum2 : (wFin X).sum (fun m => (wFin X).sum (fun n =>
      uFun X m * uFun X n * J ((X : ℝ) * Real.log ((m : ℝ) / n)))) ≤
      (2 * C₀) * (wFin X).sum (fun n => uFun X n * uFun X (n + 2)) := by
    refine hsum1.trans ?_
    rw [hshift_eq, ← two_mul]
    have hpull : 2 * (wFin X).sum (fun n => if n + 2 ∈ wFin X then uFun X n * uFun X (n + 2) * C₀ else 0) ≤
        2 * (wFin X).sum (fun n => uFun X n * uFun X (n + 2) * C₀) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (by norm_num)
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (uFun_nonneg X n) (uFun_nonneg X (n + 2))) hC₀
    refine hpull.trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    linarith
  refine hsum2.trans ?_
  rw [Finset.sum_div]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity)
  have hnX : X < n := (Finset.mem_filter.mp hn).2.1
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsqrt_n : Real.sqrt X ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hnX.le)
  have hsqrt_n2 : Real.sqrt X ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (by omega : X ≤ n + 2))
  have hu1 : uFun X n ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt X := by
    unfold uFun WFun
    calc ArithmeticFunction.vonMangoldt n * bump 1 (51 / 50) ((n : ℝ) / X) / Real.sqrt n
        ≤ ArithmeticFunction.vonMangoldt n * 1 / Real.sqrt n := by
          gcongr
          exact bump_le_one _ _ _
      _ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by rw [mul_one]
      _ ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt X :=
          div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hsqrtX_pos hsqrt_n
  have hu2 : uFun X (n + 2) ≤ ArithmeticFunction.vonMangoldt (n + 2) / Real.sqrt X := by
    unfold uFun WFun
    calc ArithmeticFunction.vonMangoldt (n + 2) * bump 1 (51 / 50) (((n + 2 : ℕ) : ℝ) / X) /
            Real.sqrt ((n + 2 : ℕ) : ℝ)
        ≤ ArithmeticFunction.vonMangoldt (n + 2) * 1 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
          gcongr
          exact bump_le_one _ _ _
      _ = ArithmeticFunction.vonMangoldt (n + 2) / Real.sqrt ((n + 2 : ℕ) : ℝ) := by rw [mul_one]
      _ ≤ ArithmeticFunction.vonMangoldt (n + 2) / Real.sqrt X :=
          div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hsqrtX_pos hsqrt_n2
  calc uFun X n * uFun X (n + 2)
      ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt X) *
        (ArithmeticFunction.vonMangoldt (n + 2) / Real.sqrt X) :=
        mul_le_mul hu1 hu2 (uFun_nonneg X (n + 2))
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrtX_pos.le)
    _ = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) / (Real.sqrt X * Real.sqrt X) := by
        ring
    _ = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) / (X : ℝ) := by
        rw [Real.mul_self_sqrt hXpos.le]

lemma e_le_inv_r (X : ℕ) (hX : 2 ≤ X) :
    Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X ≤
      1024 / Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) := by
  set y : ℝ := 2 + (X : ℝ)
  have hypos : 0 < y := by dsimp [y]; positivity
  set r : ℝ := Real.sqrt (Real.sqrt (Real.sqrt y))
  have hrpos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hypos))
  have hr8 : r ^ 8 = y := by
    have h1 : r ^ 2 = Real.sqrt (Real.sqrt y) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt y)) ^ 2 = Real.sqrt y := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hypos.le
    calc r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
      _ = y := by rw [h1, h2, h3]
  have hlog : Real.log y ≤ 8 * r := by
    rw [← hr8, Real.log_pow]
    have hlr : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hrpos).trans (by linarith)
    push_cast
    linarith
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by dsimp [y]; linarith)
  have hlog3 : Real.log y ^ 3 ≤ 512 * r ^ 3 := by
    calc Real.log y ^ 3 ≤ (8 * r) ^ 3 := pow_le_pow_left₀ hlog0 hlog 3
      _ = 512 * r ^ 3 := by ring
  have hsqrtX : r ^ 4 / 2 ≤ Real.sqrt X := by
    have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hsq : (r ^ 4 / 2) ^ 2 ≤ (Real.sqrt X) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ X)]
      have : (r ^ 4 / 2) ^ 2 = r ^ 8 / 4 := by ring
      rw [this, hr8]
      dsimp [y]
      linarith
    exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
  calc Real.log y ^ 3 / Real.sqrt X
      ≤ (512 * r ^ 3) / (r ^ 4 / 2) := by
        exact div_le_div₀ (by positivity) hlog3 (by positivity) hsqrtX
    _ = 1024 / r := by
        field_simp [hrpos.ne']
        ring

end TwinPrimesMomentToWindow

namespace PEqualNP.Outside

theorem L_twin_primes_moment_to_window :
    (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0;
     let W := bump 1 (51/50);
     let b := bump (-1/40) (1/40);
     let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t);
     let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t;
     let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ);
     let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X);
     let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n;
     let P := fun (X : ℕ) (t : ℝ) => (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)));
     let I := fun (X : ℕ) (σ : ℝ) => ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2;
     ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)) →
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X);
     let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2);
     let M := fun (X : ℕ) => (w X).sum v / (X : ℝ);
     let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X;
     ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  intro hhyp
  dsimp only
  intro K B
  rcases hhyp with ⟨δ, hδ, hB⟩
  set C₀ : ℝ := ∫ s : ℝ, (TwinPrimesMomentToWindow.lFun s) ^ 2
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun s => sq_nonneg _)
  set D : ℝ := 2 * C₀ + 1
  have hDpos : 0 < D := by dsimp [D]; linarith
  set A : ℝ := max K 1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  have hKA : K ≤ A := le_max_left K 1
  set R : ℝ := 1024 * A * D / δ + 1
  have hRpos : 0 < R := by dsimp [R]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (R ^ 8)
  set B' : ℕ := max (max B 1000) N
  obtain ⟨X, hXB', hIX⟩ := hB B'
  have hXB : B < X := lt_of_le_of_lt (le_trans (le_max_left B 1000) (le_max_left _ N)) hXB'
  have hX1000 : 1000 ≤ X := le_of_lt (lt_of_le_of_lt (le_trans (le_max_right B 1000) (le_max_left _ N)) hXB')
  have hXN : N < X := lt_of_le_of_lt (le_max_right _ N) hXB'
  have hX2 : 2 ≤ X := by omega
  refine ⟨X, hXB, ?_⟩
  have hTpos : 0 < TwinPrimesMomentToWindow.TFun X := by
    unfold TwinPrimesMomentToWindow.TFun
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    positivity
  have hI_div : δ < (TwinPrimesMomentToWindow.IFun X 1 - TwinPrimesMomentToWindow.IFun X (-1)) /
      TwinPrimesMomentToWindow.TFun X := by
    rw [lt_div_iff₀ hTpos]
    exact hIX
  have hM_nonneg : 0 ≤ ((TwinPrimesMomentToWindow.wFin X).sum (fun n =>
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ) := by
    refine div_nonneg (Finset.sum_nonneg fun n _ => ?_) (by positivity)
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hM_gt : δ / D < ((TwinPrimesMomentToWindow.wFin X).sum (fun n =>
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ) := by
    have hle := TwinPrimesMomentToWindow.I_diff_div_T_le X hX1000
    have hleD : (2 * C₀) * (((TwinPrimesMomentToWindow.wFin X).sum (fun n =>
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ)) ≤
        D * (((TwinPrimesMomentToWindow.wFin X).sum (fun n =>
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ hM_nonneg
      dsimp [D]
      linarith
    have hltD : δ < D * (((TwinPrimesMomentToWindow.wFin X).sum (fun n =>
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2))) / (X : ℝ)) :=
      hI_div.trans_le (hle.trans hleD)
    rw [div_lt_iff₀ hDpos]
    linarith
  set r : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ))))
  have hrpos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
  have hr8 : r ^ 8 = 2 + (X : ℝ) := by
    have h1 : r ^ 2 = Real.sqrt (Real.sqrt (2 + (X : ℝ))) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) ^ 2 = Real.sqrt (2 + (X : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt (2 + (X : ℝ))) ^ 2 = 2 + (X : ℝ) := Real.sq_sqrt (by positivity)
    calc r ^ 8 = ((r ^ 2) ^ 2) ^ 2 := by ring
      _ = 2 + (X : ℝ) := by rw [h1, h2, h3]
  have hRr : R < r := by
    by_contra hle
    have hrR : r ≤ R := not_lt.mp hle
    have hpow : r ^ 8 ≤ R ^ 8 := pow_le_pow_left₀ hrpos.le hrR 8
    have hNX : (N : ℝ) < (X : ℝ) := by exact_mod_cast hXN
    linarith
  have he_nonneg : 0 ≤ Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X := by
    refine div_nonneg (pow_nonneg (Real.log_nonneg ?_) 3) (Real.sqrt_nonneg _)
    have : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    linarith
  have hKe : K * (Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X) < δ / D := by
    have h1 : K * (Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X) ≤
        A * (1024 / r) := by
      calc K * (Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X)
          ≤ A * (Real.log (2 + (X : ℝ)) ^ 3 / Real.sqrt X) :=
            mul_le_mul_of_nonneg_right hKA he_nonneg
        _ ≤ A * (1024 / r) :=
            mul_le_mul_of_nonneg_left (TwinPrimesMomentToWindow.e_le_inv_r X hX2) hApos.le
    have h2 : A * (1024 / r) < δ / D := by
      have hgt : 1024 * A * D / δ < r := by
        dsimp [R] at hRr
        linarith
      rw [div_lt_iff₀ hδ] at hgt
      have hstep : 1024 * A * D < δ * r := by linarith
      have hdiv : 1024 * A / r < δ / D := by
        rw [div_lt_div_iff₀ hrpos hDpos]
        linarith
      calc A * (1024 / r) = 1024 * A / r := by ring
        _ < δ / D := hdiv
    exact h1.trans_lt h2
  exact hKe.trans hM_gt

end PEqualNP.Outside
