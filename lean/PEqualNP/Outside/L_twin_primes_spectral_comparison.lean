import Mathlib
import Conjectures.TwinPrimes.MovingHeightMellinTail

section Mod1Section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform RealInnerProductSpace BigOperators

namespace SpectralMod1

/-! ### Part 1A: Bump function `bump a b` smoothness, support, and bounds -/

noncomputable def bump (a b t : ℝ) : ℝ :=
  if a < t ∧ t < b then Real.exp (-1 / ((t - a) * (b - t))) else 0

lemma bump_eq_glue {a b : ℝ} (hab : a < b) (t : ℝ) :
    bump a b t = expNegInvGlue ((t - a) * (b - t)) := by
  unfold bump expNegInvGlue
  split_ifs with h1 h2 h2
  · exfalso
    have : 0 < (t - a) * (b - t) := mul_pos (by linarith) (by linarith)
    linarith
  · congr 1; ring
  · rfl
  · exfalso
    rcases lt_or_ge t b with htb | htb
    · rcases lt_or_ge a t with hat | hat
      · exact h1 ⟨hat, htb⟩
      · have : (t - a) * (b - t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        exact h2 this
    · have : (t - a) * (b - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      exact h2 this

lemma contDiff_bump {a b : ℝ} (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (bump a b) := by
  have heq : bump a b = fun t => expNegInvGlue ((t - a) * (b - t)) := funext (bump_eq_glue hab)
  rw [heq]
  exact expNegInvGlue.contDiff.comp ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id))

lemma continuous_bump {a b : ℝ} (hab : a < b) : Continuous (bump a b) :=
  (contDiff_bump hab).continuous

lemma bump_nonneg (a b t : ℝ) : 0 ≤ bump a b t := by
  unfold bump; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma bump_le_one (a b t : ℝ) : bump a b t ≤ 1 := by
  unfold bump; split_ifs with h
  · rw [Real.exp_le_one_iff]
    have hpos : 0 < (t - a) * (b - t) := mul_pos (by linarith) (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
  · norm_num

lemma bump_eq_zero_of_not_mem {a b t : ℝ} (ht : ¬ (a < t ∧ t < b)) : bump a b t = 0 := by
  unfold bump; rw [ite_eq_right_iff]; intro h; exact absurd h ht

lemma hasCompactSupport_bump {a b : ℝ} : HasCompactSupport (bump a b) := by
  refine HasCompactSupport.intro (K := Set.Icc a b) isCompact_Icc fun t ht => ?_
  apply bump_eq_zero_of_not_mem
  intro ⟨h1, h2⟩
  exact ht ⟨h1.le, h2.le⟩

lemma bump_symm {a t : ℝ} : bump (-a) a (-t) = bump (-a) a t := by
  unfold bump
  split_ifs with h1 h2 h2
  · congr 2; ring
  · exfalso; exact h2 ⟨by linarith [h1.2], by linarith [h1.1]⟩
  · exfalso; exact h1 ⟨by linarith [h2.2], by linarith [h2.1]⟩
  · rfl

noncomputable def Wfun : ℝ → ℝ := bump 1 (51 / 50)
noncomputable def bfun : ℝ → ℝ := bump (-1 / 40) (1 / 40)
noncomputable def Kfun (v : ℝ) : ℝ := ∫ u : ℝ, bfun u * bfun (v - u)
noncomputable def kfun (t : ℝ) : ℝ := ∫ v : ℝ, bfun v * Real.cos (2 * Real.pi * v * t)
noncomputable def lfun (t : ℝ) : ℝ := Real.sin (Real.pi * t / 5) * kfun t
noncomputable def omegafun (t : ℝ) : ℝ := (lfun t) ^ 2 * Real.cos (4 * Real.pi * t)
noncomputable def Mfun (v : ℝ) : ℂ :=
  ∫ u : ℝ, ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ))
noncomputable def phiW (y : ℝ) : ℝ := Wfun (Real.exp y)
noncomputable def Wtilde (s : ℂ) : ℂ :=
  ∫ y : ℝ, (phiW y : ℂ) * Complex.exp (s * (y : ℂ))

lemma contDiff_Wfun : ContDiff ℝ (⊤ : ℕ∞) Wfun := contDiff_bump (by norm_num)
lemma contDiff_bfun : ContDiff ℝ (⊤ : ℕ∞) bfun := contDiff_bump (by norm_num)
lemma hasCompactSupport_Wfun : HasCompactSupport Wfun := hasCompactSupport_bump
lemma hasCompactSupport_bfun : HasCompactSupport bfun := hasCompactSupport_bump
lemma contDiff_phiW : ContDiff ℝ (⊤ : ℕ∞) phiW := contDiff_Wfun.comp Real.contDiff_exp

lemma phiW_eq_zero_of_not_mem {y : ℝ} (hy : ¬ (0 < y ∧ y < Real.log (51 / 50))) : phiW y = 0 := by
  unfold phiW Wfun
  apply bump_eq_zero_of_not_mem
  intro ⟨h1, h2⟩
  apply hy
  constructor
  · have := Real.log_lt_log (by norm_num) h1; simpa using this
  · have := Real.log_lt_log (Real.exp_pos y) h2; simpa using this

lemma hasCompactSupport_phiW : HasCompactSupport phiW := by
  refine HasCompactSupport.intro (K := Set.Icc 0 (Real.log (51 / 50))) isCompact_Icc fun y hy => ?_
  apply phiW_eq_zero_of_not_mem
  intro ⟨h1, h2⟩; exact hy ⟨h1.le, h2.le⟩

lemma bfun_symm (v : ℝ) : bfun (-v) = bfun v := by
  have h1 : (-1 / 40 : ℝ) = -(1 / 40) := by norm_num
  unfold bfun
  rw [h1]
  exact bump_symm

/-! ### Part 1B: Substitution `u = exp y` for `Mfun` and `∫ W^2/u` -/

lemma integral_Ioi_eq_integral_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ u in Set.Ioi (0 : ℝ), g u = ∫ y : ℝ, Real.exp y • g (Real.exp y) := by
  have himg : Real.exp '' Set.univ = Set.Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [Measure.restrict_univ]
  congr 1; funext y
  rw [abs_of_pos (Real.exp_pos y)]

lemma Mfun_eq_Wtilde (v : ℝ) : Mfun v = Wtilde (Complex.I * (v : ℂ)) := by
  unfold Mfun Wtilde phiW
  have hzero : ∀ u ≤ (0 : ℝ), ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ)) = 0 := by
    intro u hu
    have hW : Wfun u = 0 := bump_eq_zero_of_not_mem (by intro ⟨h1, _⟩; linarith)
    simp [hW]
  have hIoi : (∫ u : ℝ, ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ))) =
      ∫ u in Set.Ioi (0 : ℝ), ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; funext u
    by_cases hu : 0 < u
    · exact (Set.indicator_of_mem (Set.mem_Ioi.mpr hu)
        (fun u : ℝ => ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ)))).symm
    · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (0 : ℝ) from hu)
        (fun u => ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * (v * Real.log u : ℝ))),
        hzero u (not_lt.mp hu)]
  rw [hIoi, integral_Ioi_eq_integral_exp]
  congr 1; funext y
  have hexp : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  rw [Real.log_exp, Complex.real_smul]
  have h1 : (Real.exp y : ℂ) * ((Wfun (Real.exp y) / Real.exp y : ℝ) : ℂ) = (Wfun (Real.exp y) : ℂ) := by
    rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hexp]
  calc (Real.exp y : ℂ) * (((Wfun (Real.exp y) / Real.exp y : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((v * y : ℝ) : ℂ)))
      = ((Real.exp y : ℂ) * ((Wfun (Real.exp y) / Real.exp y : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((v * y : ℝ) : ℂ)) := by ring
    _ = (Wfun (Real.exp y) : ℂ) * Complex.exp (Complex.I * (v : ℂ) * (y : ℂ)) := by
        rw [h1]; congr 2; push_cast; ring

lemma integral_phiW_sq_eq :
    ∫ y : ℝ, (phiW y) ^ 2 = ∫ u : ℝ, (Wfun u) ^ 2 / u := by
  have hzero : ∀ u ≤ (0 : ℝ), (Wfun u) ^ 2 / u = 0 := by
    intro u hu
    have hW : Wfun u = 0 := bump_eq_zero_of_not_mem (by intro ⟨h1, _⟩; linarith)
    simp [hW]
  have hIoi : (∫ u : ℝ, (Wfun u) ^ 2 / u) = ∫ u in Set.Ioi (0 : ℝ), (Wfun u) ^ 2 / u := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; funext u
    by_cases hu : 0 < u
    · exact (Set.indicator_of_mem (Set.mem_Ioi.mpr hu) _).symm
    · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (0 : ℝ) from hu) (fun u => (Wfun u) ^ 2 / u),
        hzero u (not_lt.mp hu)]
  rw [hIoi, integral_Ioi_eq_integral_exp]
  congr 1; funext y
  simp only [phiW, smul_eq_mul]
  rw [mul_div_cancel₀ _ (Real.exp_pos y).ne']

/-! ### Part 1C: Rapid decay via integration by parts (`C^∞_c` exponential integral) -/

lemma tendsto_zero_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : HasCompactSupport g) :
    Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  have hzero : ∀ y : ℝ, R < |y| → g y = 0 := by
    intro y hy
    by_contra hne
    have := hR (subset_tsupport g hne)
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (-max R 0)] with y hy
    have h1 : R < |y| := by
      rw [abs_of_neg (by linarith [le_max_right R 0])]; linarith [le_max_left R 0]
    exact (hzero y h1).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (max R 0)] with y hy
    have h1 : R < |y| := by
      rw [abs_of_pos (by linarith [le_max_right R 0])]; linarith [le_max_left R 0]
    exact (hzero y h1).symm

lemma hasCompactSupport_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hcomp : HasCompactSupport f) : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hcomp
  | n + 1 => by
    rw [iteratedDeriv_succ]
    exact (hasCompactSupport_iteratedDeriv hcomp n).deriv

lemma contDiff_top_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by
    rw [iteratedDeriv_succ]
    have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) (iteratedDeriv n f) := by
      simpa using contDiff_top_iteratedDeriv hf n
    exact h.deriv'

lemma integral_deriv_mul_cexp_eq {f : ℝ → ℂ} {s : ℂ}
    (hf : ContDiff ℝ 1 f) (hcomp : HasCompactSupport f) :
    ∫ y : ℝ, deriv f y * Complex.exp (s * (y : ℂ)) =
      - s * ∫ y : ℝ, f y * Complex.exp (s * (y : ℂ)) := by
  have h1 : ∀ y : ℝ, HasDerivAt (fun x : ℝ => f x * Complex.exp (s * (x : ℂ)))
      (deriv f y * Complex.exp (s * (y : ℂ)) + f y * (Complex.exp (s * (y : ℂ)) * s)) y := by
    intro y
    have hdf : HasDerivAt f (deriv f y) y := (hf.differentiable one_ne_zero y).hasDerivAt
    have hde : HasDerivAt (fun x : ℝ => Complex.exp (s * (x : ℂ)))
        (Complex.exp (s * (y : ℂ)) * s) y := by
      have hlin : HasDerivAt (fun x : ℝ => s * (x : ℂ)) (s * 1) y :=
        (Complex.ofRealCLM.hasDerivAt).const_mul s
      simpa using hlin.cexp
    exact hdf.mul hde
  have hcomp_prod : HasCompactSupport (fun y : ℝ => f y * Complex.exp (s * (y : ℂ))) :=
    hcomp.mul_right
  have hcomp_d : HasCompactSupport (fun y : ℝ => deriv f y * Complex.exp (s * (y : ℂ))) :=
    (hcomp.deriv).mul_right
  have hcexp : Continuous (fun y : ℝ => Complex.exp (s * (y : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint_d : Integrable (fun y : ℝ => deriv f y * Complex.exp (s * (y : ℂ))) :=
    ((hf.continuous_deriv le_rfl).mul hcexp).integrable_of_hasCompactSupport hcomp_d
  have hint_p : Integrable (fun y : ℝ => f y * Complex.exp (s * (y : ℂ))) :=
    (hf.continuous.mul hcexp).integrable_of_hasCompactSupport hcomp_prod
  have hint_p' : Integrable (fun y : ℝ => f y * (Complex.exp (s * (y : ℂ)) * s)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hint_p.mul_const s
  have ⟨hlim0, hlim1⟩ := tendsto_zero_of_hasCompactSupport hcomp_prod
  have hzero : ∫ y : ℝ, (deriv f y * Complex.exp (s * (y : ℂ)) +
      f y * (Complex.exp (s * (y : ℂ)) * s)) = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto h1 (hint_d.add hint_p') hlim0 hlim1
    simpa using this
  rw [MeasureTheory.integral_add hint_d hint_p'] at hzero
  have h2 : ∫ y : ℝ, f y * (Complex.exp (s * (y : ℂ)) * s) =
      s * ∫ y : ℝ, f y * Complex.exp (s * (y : ℂ)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; ring
  rw [h2] at hzero
  linear_combination hzero

lemma iter_deriv_mul_cexp {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcomp : HasCompactSupport f)
    (s : ℂ) : ∀ n : ℕ,
    (-s) ^ n * ∫ y : ℝ, f y * Complex.exp (s * (y : ℂ)) =
      ∫ y : ℝ, iteratedDeriv n f y * Complex.exp (s * (y : ℂ))
  | 0 => by simp
  | n + 1 => by
    have hfn : ContDiff ℝ 1 (iteratedDeriv n f) :=
      (contDiff_top_iteratedDeriv hf n).of_le (by simp)
    have hcn : HasCompactSupport (iteratedDeriv n f) := hasCompactSupport_iteratedDeriv hcomp n
    rw [pow_succ', mul_assoc, iter_deriv_mul_cexp hf hcomp s n, ← integral_deriv_mul_cexp_eq hfn hcn]
    simp [iteratedDeriv_succ]

lemma norm_cexp_integral_le_of_compact {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcomp : HasCompactSupport f) (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ ≤ C / (1 + |s.im|) ^ n := by
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < |y| → f y = 0 := by
    obtain ⟨K, hK⟩ := hcomp.isCompact.isBounded.subset_closedBall 0
    refine ⟨max K 1, by positivity, fun y hy => ?_⟩
    by_contra hne
    have := hK (subset_tsupport f hne)
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left K 1]
  have hM : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖∫ y : ℝ, iteratedDeriv k f y * Complex.exp (s * (y : ℂ))‖ ≤ M := by
    intro k
    have hck : HasCompactSupport (iteratedDeriv k f) := hasCompactSupport_iteratedDeriv hcomp k
    have hsupp : ∀ y, R < |y| → iteratedDeriv k f y = 0 := by
      intro y hy
      have hopen : IsOpen {x : ℝ | R < |x|} := isOpen_lt continuous_const continuous_abs
      have hev : f =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hopen.mem_nhds hy) (fun x hx => hR x hx)
      rw [hev.iteratedDeriv_eq]; simp
    have hcont : Continuous (fun y => ‖iteratedDeriv k f y‖) :=
      ((contDiff_top_iteratedDeriv hf k).continuous).norm
    have hint : Integrable (fun y => ‖iteratedDeriv k f y‖) :=
      hcont.integrable_of_hasCompactSupport hck.norm
    refine ⟨Real.exp (max |a| |b| * R) * ∫ y : ℝ, ‖iteratedDeriv k f y‖,
      mul_nonneg (Real.exp_pos _).le (MeasureTheory.integral_nonneg fun _ => norm_nonneg _), ?_⟩
    intro s hsa hsb
    calc ‖∫ y : ℝ, iteratedDeriv k f y * Complex.exp (s * (y : ℂ))‖
        ≤ ∫ y : ℝ, ‖iteratedDeriv k f y * Complex.exp (s * (y : ℂ))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ, Real.exp (max |a| |b| * R) * ‖iteratedDeriv k f y‖ := by
          apply MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hint.const_mul _)
          filter_upwards with y
          by_cases hy : R < |y|
          · simp [hsupp y hy]
          · have hy' : |y| ≤ R := not_lt.mp hy
            rw [norm_mul, Complex.norm_exp, mul_comm (Real.exp _)]
            have hre : (s * (y : ℂ)).re = s.re * y := by simp
            rw [hre]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply Real.exp_le_exp.mpr
            have hsab : |s.re| ≤ max |a| |b| := by
              rw [abs_le]
              constructor <;> linarith [le_max_left |a| |b|, le_max_right |a| |b|, neg_abs_le a, le_abs_self b]
            calc s.re * y ≤ |s.re * y| := le_abs_self _
              _ = |s.re| * |y| := abs_mul _ _
              _ ≤ max |a| |b| * R := mul_le_mul hsab hy' (abs_nonneg y) (by positivity)
      _ = Real.exp (max |a| |b| * R) * ∫ y : ℝ, ‖iteratedDeriv k f y‖ :=
          MeasureTheory.integral_const_mul _ _
  obtain ⟨M0, hM0, hb0⟩ := hM 0
  obtain ⟨Mn, hMn, hbn⟩ := hM n
  refine ⟨2 ^ n * (M0 + Mn), by positivity, fun s hsa hsb => ?_⟩
  have h1 : ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ ≤ M0 := by
    simpa using hb0 s hsa hsb
  have h2 : |s.im| ^ n * ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ ≤ Mn := by
    have hiter := congrArg norm (iter_deriv_mul_cexp hf hcomp s n)
    rw [norm_mul, norm_pow, norm_neg] at hiter
    calc |s.im| ^ n * ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖
        ≤ ‖s‖ ^ n * ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ := by
          gcongr; exact Complex.abs_im_le_norm s
      _ = ‖∫ y : ℝ, iteratedDeriv n f y * Complex.exp (s * (y : ℂ))‖ := hiter
      _ ≤ Mn := hbn s hsa hsb
  have hpow : (1 + |s.im|) ^ n ≤ 2 ^ n * (1 + |s.im| ^ n) := by
    by_cases him : |s.im| ≤ 1
    · calc (1 + |s.im|) ^ n ≤ (1 + 1) ^ n := by gcongr
        _ = 2 ^ n * 1 := by ring
        _ ≤ 2 ^ n * (1 + |s.im| ^ n) := by gcongr; linarith [pow_nonneg (abs_nonneg s.im) n]
    · have him' : 1 ≤ |s.im| := (not_le.mp him).le
      calc (1 + |s.im|) ^ n ≤ (|s.im| + |s.im|) ^ n := by gcongr
        _ = 2 ^ n * |s.im| ^ n := by rw [← two_mul, mul_pow]
        _ ≤ 2 ^ n * (1 + |s.im| ^ n) := by gcongr; linarith
  rw [le_div_iff₀ (pow_pos (by linarith [abs_nonneg s.im]) n)]
  calc ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ * (1 + |s.im|) ^ n
      ≤ ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ * (2 ^ n * (1 + |s.im| ^ n)) := by gcongr
    _ = 2 ^ n * (‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖ +
        |s.im| ^ n * ‖∫ y : ℝ, f y * Complex.exp (s * (y : ℂ))‖) := by ring
    _ ≤ 2 ^ n * (M0 + Mn) := by gcongr

lemma Wtilde_rapid_decay (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ n := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (phiW y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_phiW
  have hcomp : HasCompactSupport (fun y : ℝ => (phiW y : ℂ)) :=
    hasCompactSupport_phiW.comp_left Complex.ofReal_zero
  exact norm_cexp_integral_le_of_compact hf hcomp a b n

lemma Mfun_rapid_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n := by
  obtain ⟨C, hC, h⟩ := Wtilde_rapid_decay 0 0 n
  refine ⟨C, hC, fun v => ?_⟩
  rw [Mfun_eq_Wtilde]
  simpa using h (Complex.I * (v : ℂ)) (by simp) (by simp)

/-! ### Part 1D: Entirety of `Wtilde`, Mellin inversion, and Plancherel for `Mfun` -/

lemma differentiable_Wtilde : Differentiable ℂ Wtilde := by
  intro s0
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < |y| → phiW y = 0 := by
    refine ⟨1, one_pos, fun y hy => phiW_eq_zero_of_not_mem ?_⟩
    intro ⟨h1, h2⟩
    have hlog : Real.log (51 / 50) < 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51 / 50)
      linarith
    rw [abs_of_pos h1] at hy
    linarith
  have hbound : ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ s ∈ Metric.ball s0 1, ∀ y : ℝ,
        ‖(phiW y : ℂ) * (Complex.exp (s * (y : ℂ)) * (y : ℂ))‖ ≤ bound y := by
    refine ⟨fun y => Real.exp ((|s0.re| + 1) * R) * (|phiW y| * |y|), ?_, ?_⟩
    · exact ((contDiff_phiW.continuous.abs.mul continuous_abs).integrable_of_hasCompactSupport
        (hasCompactSupport_phiW.abs.mul_right)).const_mul _
    · intro s hs y
      by_cases hy : R < |y|
      · simp [hR y hy]
      · have hy' : |y| ≤ R := not_lt.mp hy
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp]
        have hre : (s * (y : ℂ)).re = s.re * y := by simp
        rw [hre, Real.norm_eq_abs, Real.norm_eq_abs]
        have hsre : |s.re| ≤ |s0.re| + 1 := by
          have h1 : |s.re - s0.re| ≤ ‖s - s0‖ := by simpa using Complex.abs_re_le_norm (s - s0)
          have h2 : ‖s - s0‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs
          have h3 := abs_sub_abs_le_abs_sub s.re s0.re
          linarith
        have hexp : Real.exp (s.re * y) ≤ Real.exp ((|s0.re| + 1) * R) := by
          apply Real.exp_le_exp.mpr
          calc s.re * y ≤ |s.re * y| := le_abs_self _
            _ = |s.re| * |y| := abs_mul _ _
            _ ≤ (|s0.re| + 1) * R := mul_le_mul hsre hy' (abs_nonneg y) (by positivity)
        calc |phiW y| * (Real.exp (s.re * y) * |y|)
            = Real.exp (s.re * y) * (|phiW y| * |y|) := by ring
          _ ≤ Real.exp ((|s0.re| + 1) * R) * (|phiW y| * |y|) := by gcongr
  obtain ⟨bound, hbound_int, hbound_le⟩ := hbound
  have hcexp : ∀ s : ℂ, Continuous (fun y : ℝ => Complex.exp (s * (y : ℂ))) := fun s =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hdiff_res := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s0 one_pos)
    (F := fun s y => (phiW y : ℂ) * Complex.exp (s * (y : ℂ)))
    (F' := fun s y => (phiW y : ℂ) * (Complex.exp (s * (y : ℂ)) * (y : ℂ)))
    (bound := bound)
    (Filter.Eventually.of_forall fun s =>
      ((Complex.continuous_ofReal.comp contDiff_phiW.continuous).mul (hcexp s)).aestronglyMeasurable)
    (((Complex.continuous_ofReal.comp contDiff_phiW.continuous).mul (hcexp s0)).integrable_of_hasCompactSupport
      (hasCompactSupport_phiW.comp_left Complex.ofReal_zero).mul_right)
    (((Complex.continuous_ofReal.comp contDiff_phiW.continuous).mul ((hcexp s0).mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y s hs => hbound_le s hs y)
    hbound_int
    (Filter.Eventually.of_forall fun y s _ => by
      have h1 : HasDerivAt (fun w : ℂ => w * (y : ℂ)) (1 * (y : ℂ)) s := (hasDerivAt_id s).mul_const (y : ℂ)
      simpa using h1.cexp.const_mul (phiW y : ℂ))
  exact hdiff_res.2.differentiableAt

lemma integrable_div_one_add_abs_pow (C : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun t : ℝ => C / (1 + |t|) ^ n) := by
  have hsq : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hcont : Continuous (fun t : ℝ => C / (1 + |t|) ^ n) :=
    continuous_const.div ((continuous_const.add continuous_abs).pow n)
      (fun t => (pow_pos (by linarith [abs_nonneg t]) n).ne')
  refine (hsq.const_mul (2 * |C|)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hposn : 0 < (1 + |t|) ^ n := pow_pos (by linarith [abs_nonneg t]) n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hposn]
  have hpow : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ n :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hn
  have hle : 1 + t ^ 2 ≤ 2 * (1 + |t|) ^ n := by
    have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have h2 : 1 + t ^ 2 ≤ 2 * (1 + |t|) ^ 2 := by rw [ht2]; nlinarith [abs_nonneg t]
    linarith
  rw [div_le_iff₀ hposn]
  have hpos1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  calc |C| = 2 * |C| * (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) / 2) := by
        field_simp [hpos1.ne']
    _ ≤ 2 * |C| * (1 + t ^ 2)⁻¹ * (1 + |t|) ^ n := by
        gcongr; linarith

lemma mellin_inversion_Wfun (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (Wfun x : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * (x : ℂ) ^ (-((c : ℂ) + Complex.I * (τ : ℂ))) := by
  let g : ℝ → ℂ := fun y => (phiW y : ℂ) * Complex.exp ((c : ℂ) * (y : ℂ))
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    (Complex.ofRealCLM.contDiff.comp contDiff_phiW).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  have hg_comp : HasCompactSupport g :=
    (hasCompactSupport_phiW.comp_left Complex.ofReal_zero).mul_right
  have hg_int : Integrable g := hg_smooth.continuous.integrable_of_hasCompactSupport hg_comp
  have hFg_eq : ∀ ξ : ℝ, 𝓕 g ξ = Wtilde ((c : ℂ) + Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) := by
    intro ξ
    rw [Real.fourier_eq']
    unfold Wtilde g
    congr 1; funext y
    rw [smul_eq_mul, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast; ring
  have hFg_int : Integrable (𝓕 g) := by
    obtain ⟨C, hC, hdec⟩ := Wtilde_rapid_decay c c 2
    have hdom : Integrable (fun ξ : ℝ => C / (1 + |(-2 * Real.pi * ξ)|) ^ 2) := by
      have h1 := integrable_div_one_add_abs_pow C 2 le_rfl
      have hne : (-2 * Real.pi : ℝ) ≠ 0 := by
        have : 0 < 2 * Real.pi := by positivity
        linarith
      simpa using h1.comp_mul_left' hne
    have hcont : Continuous (𝓕 g) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hg_int
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hFg_eq ξ]
    have hre : ((c : ℂ) + Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)).re = c := by simp
    have him : ((c : ℂ) + Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)).im = -2 * Real.pi * ξ := by simp
    simpa [hre, him] using hdec ((c : ℂ) + Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) (by simp) (by simp)
  have hinv := hg_int.fourierInv_fourier_eq hFg_int hg_smooth.continuous.continuousAt (v := Real.log x)
  rw [Real.fourierInv_eq'] at hinv
  have hsub : ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ⟪ξ, Real.log x⟫ : ℝ) : ℂ) * Complex.I) • 𝓕 g ξ =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ)) := by
    have hch := MeasureTheory.Measure.integral_comp_mul_left (g := fun τ : ℝ =>
      Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ))) (-2 * Real.pi)
    rw [abs_inv, show |(-2 * Real.pi : ℝ)| = 2 * Real.pi by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) by ring, abs_neg, abs_of_pos (by positivity)]] at hch
    have hch' : ∫ ξ : ℝ, Wtilde ((c : ℂ) + Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ) * (Real.log x : ℂ)) =
        (2 * Real.pi)⁻¹ • ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) *
          Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ)) := hch
    rw [Complex.real_smul, Complex.ofReal_inv] at hch'
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ by push_cast; ring, ← hch']
    congr 1; funext ξ
    rw [hFg_eq ξ, smul_eq_mul, mul_comm]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast; ring
  have hinv' : (phiW (Real.log x) : ℂ) * Complex.exp ((c : ℂ) * (Real.log x : ℂ)) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ)) := by
    rw [← hsub]
    simpa [g] using hinv.symm
  have hphi : phiW (Real.log x) = Wfun x := by simp [phiW, Real.exp_log hx]
  rw [hphi] at hinv'
  calc (Wfun x : ℂ)
      = ((Wfun x : ℂ) * Complex.exp ((c : ℂ) * (Real.log x : ℂ))) * Complex.exp (-((c : ℂ) * (Real.log x : ℂ))) := by
        rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = ((1 / (2 * (Real.pi : ℂ))) *
          ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) *
            Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ))) *
          Complex.exp (-((c : ℂ) * (Real.log x : ℂ))) := by rw [hinv']
    _ = (1 / (2 * (Real.pi : ℂ))) *
          ∫ τ : ℝ, (Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) *
            Complex.exp (-Complex.I * (τ : ℂ) * (Real.log x : ℂ))) *
            Complex.exp (-((c : ℂ) * (Real.log x : ℂ))) := by
        rw [mul_assoc, ← MeasureTheory.integral_mul_const]
    _ = (1 / (2 * (Real.pi : ℂ))) *
          ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) *
            (x : ℂ) ^ (-((c : ℂ) + Complex.I * (τ : ℂ))) := by
        congr 2; funext τ
        rw [mul_assoc, ← Complex.exp_add, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
          ← Complex.ofReal_log hx.le]
        congr 2; ring

lemma integral_norm_sq_Mfun :
    ∫ v : ℝ, ‖Mfun v‖ ^ 2 = 2 * Real.pi * ∫ u : ℝ, (Wfun u) ^ 2 / u := by
  let f : ℝ → ℂ := fun y => (phiW y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := Complex.ofRealCLM.contDiff.comp contDiff_phiW
  have hf_comp : HasCompactSupport f := hasCompactSupport_phiW.comp_left Complex.ofReal_zero
  let S : SchwartzMap ℝ ℂ := hf_comp.toSchwartzMap hf_smooth
  have hpl : ‖𝓕 (S.toLp 2 volume)‖ = ‖S.toLp 2 volume‖ := MeasureTheory.Lp.norm_fourier_eq _
  rw [SchwartzMap.toLp_fourier_eq] at hpl
  have hsq : ‖(𝓕 S).toLp 2 volume‖ ^ 2 = ‖S.toLp 2 volume‖ ^ 2 := by rw [hpl]
  have hnorm_sq : ∀ g : SchwartzMap ℝ ℂ, ‖g.toLp 2 volume‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 := by
    intro g
    have hmem : MemLp g 2 volume := g.memLp 2 volume
    have hcoe : (g.toLp 2 volume : ℝ → ℂ) =ᵐ[volume] g := SchwartzMap.coeFn_toLp g 2 volume
    rw [MeasureTheory.Lp.norm_def, eLpNorm_congr_ae hcoe,
      eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable, eLpNorm']
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
    have hint : Integrable (fun x : ℝ => ‖g x‖ ^ 2) volume := by
      simpa [Real.rpow_two] using hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint.aestronglyMeasurable]
    congr 1; apply lintegral_congr; intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hnorm_sq (𝓕 S), hnorm_sq S] at hsq
  have hFS : ∀ ξ : ℝ, (𝓕 S) ξ = Mfun (-2 * Real.pi * ξ) := by
    intro ξ
    rw [SchwartzMap.fourier_coe, Real.fourier_eq', Mfun_eq_Wtilde]
    unfold Wtilde
    congr 1; funext y
    simp only [S, HasCompactSupport.toSchwartzMap_toFun, f, smul_eq_mul, mul_comm (Complex.exp _),
      RCLike.inner_apply, conj_trivial]
    congr 2; push_cast; ring
  have hLHS : ∫ ξ : ℝ, ‖(𝓕 S) ξ‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ v : ℝ, ‖Mfun v‖ ^ 2 := by
    simp_rw [hFS]
    have hch := MeasureTheory.Measure.integral_comp_mul_left (g := fun v : ℝ => ‖Mfun v‖ ^ 2) (-2 * Real.pi)
    rw [abs_inv, show |(-2 * Real.pi : ℝ)| = 2 * Real.pi by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) by ring, abs_neg, abs_of_pos (by positivity)],
      smul_eq_mul] at hch
    exact hch
  have hRHS : ∫ y : ℝ, ‖S y‖ ^ 2 = ∫ y : ℝ, (phiW y) ^ 2 := by
    congr 1; funext y
    simp [S, f, sq_abs]
  rw [hLHS, hRHS, integral_phiW_sq_eq] at hsq
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  field_simp [h2pi.ne'] at hsq ⊢
  linarith

/-! ### Part 1E: Properties of `Kfun`, `kfun`, `omegafun`, `∫ ω = 0`, and `∫_0^∞ ω(u) log u du` -/

lemma Kfun_nonneg (v : ℝ) : 0 ≤ Kfun v :=
  MeasureTheory.integral_nonneg fun u => mul_nonneg (bump_nonneg _ _ u) (bump_nonneg _ _ (v - u))

lemma Kfun_eq_zero_of_abs_ge {v : ℝ} (hv : (1 / 20 : ℝ) ≤ |v|) : Kfun v = 0 := by
  unfold Kfun
  have h0 : ∀ u : ℝ, bfun u * bfun (v - u) = 0 := by
    intro u
    by_contra hne
    have h1 : bfun u ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have h2 : bfun (v - u) ≠ 0 := (mul_ne_zero_iff.mp hne).2
    have hu : (-1 / 40 : ℝ) < u ∧ u < 1 / 40 := by
      by_contra h; exact h1 (bump_eq_zero_of_not_mem h)
    have hvu : (-1 / 40 : ℝ) < v - u ∧ v - u < 1 / 40 := by
      by_contra h; exact h2 (bump_eq_zero_of_not_mem h)
    have : |v| < 1 / 20 := by
      rw [abs_lt]; constructor <;> linarith
    linarith
  simp [h0]

lemma Kfun_symm (v : ℝ) : Kfun (-v) = Kfun v := by
  unfold Kfun
  calc ∫ u : ℝ, bfun u * bfun (-v - u)
      = ∫ u : ℝ, bfun (-u) * bfun (-v - (-u)) :=
          (MeasureTheory.integral_neg_eq_self (fun u : ℝ => bfun u * bfun (-v - u)) volume).symm
    _ = ∫ u : ℝ, bfun u * bfun (v - u) := by
        congr 1; funext u
        rw [bfun_symm u, show -v - -u = -(v - u) by ring, bfun_symm (v - u)]

lemma continuous_Kfun : Continuous Kfun := by
  have h1 : Kfun = convolution bfun bfun (ContinuousLinearMap.mul ℝ ℝ) := by
    funext v; simp [Kfun, convolution]
  rw [h1]
  exact hasCompactSupport_bfun.continuous_convolution_right _
    contDiff_bfun.continuous.locallyIntegrable contDiff_bfun.continuous

lemma hasCompactSupport_Kfun : HasCompactSupport Kfun :=
  HasCompactSupport.intro (K := Set.Icc (-(1 / 20 : ℝ)) (1 / 20)) isCompact_Icc fun v hv =>
    Kfun_eq_zero_of_abs_ge (by
      rcases not_and_or.mp hv with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)

lemma kfun_even (t : ℝ) : kfun (-t) = kfun t := by
  simp only [kfun, mul_neg, Real.cos_neg]

lemma omegafun_even (t : ℝ) : omegafun (-t) = omegafun t := by
  unfold omegafun lfun
  rw [kfun_even]
  have h1 : Real.pi * -t / 5 = -(Real.pi * t / 5) := by ring
  have h2 : 4 * Real.pi * -t = -(4 * Real.pi * t) := by ring
  rw [h1, h2, Real.sin_neg, Real.cos_neg]; ring

lemma kfun_eq_cexp_integral (t : ℝ) :
    (kfun t : ℂ) = ∫ v : ℝ, (bfun v : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) := by
  have hcos_c : Continuous (fun v : ℝ => Real.cos (2 * Real.pi * v * t)) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hsin_c : Continuous (fun v : ℝ => Real.sin (2 * Real.pi * v * t)) :=
    Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hint_c : Integrable (fun v : ℝ => bfun v * Real.cos (2 * Real.pi * v * t)) :=
    (contDiff_bfun.continuous.mul hcos_c).integrable_of_hasCompactSupport hasCompactSupport_bfun.mul_right
  have hint_s : Integrable (fun v : ℝ => bfun v * Real.sin (2 * Real.pi * v * t)) :=
    (contDiff_bfun.continuous.mul hsin_c).integrable_of_hasCompactSupport hasCompactSupport_bfun.mul_right
  have hsin_zero : ∫ v : ℝ, bfun v * Real.sin (2 * Real.pi * v * t) = 0 := by
    have hneg : ∫ v : ℝ, bfun (-v) * Real.sin (2 * Real.pi * (-v) * t) =
        ∫ v : ℝ, bfun v * Real.sin (2 * Real.pi * v * t) :=
      MeasureTheory.integral_neg_eq_self (fun v : ℝ => bfun v * Real.sin (2 * Real.pi * v * t)) volume
    have hodd : ∀ v : ℝ, bfun (-v) * Real.sin (2 * Real.pi * (-v) * t) =
        -(bfun v * Real.sin (2 * Real.pi * v * t)) := by
      intro v
      rw [bfun_symm v, show 2 * Real.pi * -v * t = -(2 * Real.pi * v * t) by ring, Real.sin_neg]
      ring
    simp_rw [hodd, MeasureTheory.integral_neg] at hneg
    linarith
  have hsplit : ∀ v : ℝ, (bfun v : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) =
      ((bfun v * Real.cos (2 * Real.pi * v * t) : ℝ) : ℂ) +
        Complex.I * ((bfun v * Real.sin (2 * Real.pi * v * t) : ℝ) : ℂ) := by
    intro v
    have harg : Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ) =
        ((2 * Real.pi * v * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  simp_rw [hsplit]
  have hint_cC : Integrable (fun v : ℝ => ((bfun v * Real.cos (2 * Real.pi * v * t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hint_c
  have hint_sC : Integrable (fun v : ℝ => ((bfun v * Real.sin (2 * Real.pi * v * t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hint_s
  have hc1 := Complex.ofRealCLM.integral_comp_comm hint_c
  have hs1 := Complex.ofRealCLM.integral_comp_comm hint_s
  rw [MeasureTheory.integral_add hint_cC (hint_sC.const_mul Complex.I),
    MeasureTheory.integral_const_mul]
  have hc1' : (∫ v : ℝ, ((bfun v * Real.cos (2 * Real.pi * v * t) : ℝ) : ℂ)) = (kfun t : ℂ) := by
    simpa [kfun] using hc1
  have hs1' : (∫ v : ℝ, ((bfun v * Real.sin (2 * Real.pi * v * t) : ℝ) : ℂ)) = 0 := by
    simpa [hsin_zero] using hs1
  rw [hc1', hs1', mul_zero, add_zero]

lemma kfun_rapid_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |kfun t| ≤ C / (1 + |t|) ^ n := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (bfun v : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_bfun
  have hcomp : HasCompactSupport (fun v : ℝ => (bfun v : ℂ)) :=
    hasCompactSupport_bfun.comp_left Complex.ofReal_zero
  obtain ⟨C, hC, hdec⟩ := norm_cexp_integral_le_of_compact hf hcomp 0 0 n
  refine ⟨C, hC, fun t => ?_⟩
  have h1 := hdec (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) (by simp) (by simp)
  rw [← kfun_eq_cexp_integral t, Complex.norm_real, Real.norm_eq_abs] at h1
  have him : (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)).im = 2 * Real.pi * t := by simp
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
  refine h1.trans ?_
  gcongr
  have : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  nlinarith [abs_nonneg t]

lemma hasDerivAt_kfun (t : ℝ) :
    HasDerivAt kfun (∫ v : ℝ, (-2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * t)) t := by
  have hbound : ∃ bound : ℝ → ℝ, Integrable bound ∧ ∀ x : ℝ, ∀ v : ℝ,
      ‖(-2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * x)‖ ≤ bound v := by
    refine ⟨fun v => |2 * Real.pi * v * bfun v|, ?_, fun x v => ?_⟩
    · exact ((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).abs).integrable_of_hasCompactSupport
        ((hasCompactSupport_bfun.mul_left).abs)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |-2 * Real.pi * v * bfun v| * |Real.sin (2 * Real.pi * v * x)|
          ≤ |-2 * Real.pi * v * bfun v| * 1 := by gcongr; exact Real.abs_sin_le_one _
        _ = |2 * Real.pi * v * bfun v| := by
            rw [mul_one, show -2 * Real.pi * v * bfun v = -(2 * Real.pi * v * bfun v) by ring, abs_neg]
  obtain ⟨bound, hbound_int, hbound_le⟩ := hbound
  have hcos_c : ∀ x : ℝ, Continuous (fun v : ℝ => Real.cos (2 * Real.pi * v * x)) := fun x =>
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hsin_c : Continuous (fun v : ℝ => Real.sin (2 * Real.pi * v * t)) :=
    Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t one_pos)
    (F := fun x v => bfun v * Real.cos (2 * Real.pi * v * x))
    (F' := fun x v => (-2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * x))
    (bound := bound)
    (Filter.Eventually.of_forall fun x => (contDiff_bfun.continuous.mul (hcos_c x)).aestronglyMeasurable)
    ((contDiff_bfun.continuous.mul (hcos_c t)).integrable_of_hasCompactSupport hasCompactSupport_bfun.mul_right)
    (((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).mul hsin_c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v x _ => hbound_le x v)
    hbound_int
    (Filter.Eventually.of_forall fun v x _ => by
      have h1 : HasDerivAt (fun y : ℝ => 2 * Real.pi * v * y) (2 * Real.pi * v) x := by
        simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * v)
      have h2 := h1.cos.const_mul (bfun v)
      convert h2 using 1; ring)
  exact hres.2

lemma deriv_kfun_rapid_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv kfun t| ≤ C / (1 + |t|) ^ n := by
  let g : ℝ → ℂ := fun v => ((2 * Real.pi * v * bfun v : ℝ) : ℂ)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).mul contDiff_bfun)
  have hg_comp : HasCompactSupport g :=
    (hasCompactSupport_bfun.mul_left).comp_left Complex.ofReal_zero
  obtain ⟨C, hC, hdec⟩ := norm_cexp_integral_le_of_compact hg_smooth hg_comp 0 0 n
  refine ⟨C, hC, fun t => ?_⟩
  have hd : deriv kfun t = ∫ v : ℝ, (-2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * t) :=
    (hasDerivAt_kfun t).deriv
  have hcos_c : Continuous (fun v : ℝ => Real.cos (2 * Real.pi * v * t)) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hsin_c : Continuous (fun v : ℝ => Real.sin (2 * Real.pi * v * t)) :=
    Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hint_c : Integrable (fun v : ℝ => (2 * Real.pi * v * bfun v) * Real.cos (2 * Real.pi * v * t)) :=
    (((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).mul hcos_c)).integrable_of_hasCompactSupport
      (hasCompactSupport_bfun.mul_left).mul_right
  have hint_s : Integrable (fun v : ℝ => (2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * t)) :=
    (((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).mul hsin_c)).integrable_of_hasCompactSupport
      (hasCompactSupport_bfun.mul_left).mul_right
  have hcos_zero : ∫ v : ℝ, (2 * Real.pi * v * bfun v) * Real.cos (2 * Real.pi * v * t) = 0 := by
    have hneg := MeasureTheory.integral_neg_eq_self
      (fun v : ℝ => (2 * Real.pi * v * bfun v) * Real.cos (2 * Real.pi * v * t)) volume
    have hodd : ∀ v : ℝ, (2 * Real.pi * -v * bfun (-v)) * Real.cos (2 * Real.pi * -v * t) =
        -((2 * Real.pi * v * bfun v) * Real.cos (2 * Real.pi * v * t)) := by
      intro v
      rw [bfun_symm v, show 2 * Real.pi * -v * t = -(2 * Real.pi * v * t) by ring, Real.cos_neg]; ring
    simp_rw [hodd, MeasureTheory.integral_neg] at hneg
    linarith
  have heq_im : (∫ v : ℝ, g v * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) =
      Complex.I * (-((deriv kfun t : ℝ) : ℂ)) := by
    have hsplit : ∀ v : ℝ, g v * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) =
        (((2 * Real.pi * v * bfun v) * Real.cos (2 * Real.pi * v * t) : ℝ) : ℂ) +
        Complex.I * (((2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * t) : ℝ) : ℂ) := by
      intro v
      have harg : Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ) =
          ((2 * Real.pi * v * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [g]; push_cast; ring
    simp_rw [hsplit]
    have hint_cC : Integrable (fun v : ℝ => ((2 * Real.pi * v * bfun v * Real.cos (2 * Real.pi * v * t) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hint_c
    have hint_sC : Integrable (fun v : ℝ => ((2 * Real.pi * v * bfun v * Real.sin (2 * Real.pi * v * t) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp hint_s
    have hc1 := Complex.ofRealCLM.integral_comp_comm hint_c
    have hs1 := Complex.ofRealCLM.integral_comp_comm hint_s
    rw [MeasureTheory.integral_add hint_cC (hint_sC.const_mul Complex.I),
      MeasureTheory.integral_const_mul]
    have h1 : (∫ x : ℝ, ((2 * Real.pi * x * bfun x * Real.cos (2 * Real.pi * x * t) : ℝ) : ℂ)) = 0 := by
      simpa [hcos_zero] using hc1
    have h2 : (∫ x : ℝ, ((2 * Real.pi * x * bfun x * Real.sin (2 * Real.pi * x * t) : ℝ) : ℂ)) =
        (-((deriv kfun t : ℝ) : ℂ)) := by
      have hs1' : (∫ x : ℝ, ((2 * Real.pi * x * bfun x * Real.sin (2 * Real.pi * x * t) : ℝ) : ℂ)) =
          ((∫ x : ℝ, 2 * Real.pi * x * bfun x * Real.sin (2 * Real.pi * x * t) : ℝ) : ℂ) := by
        simpa using hs1
      rw [hs1', hd, ← Complex.ofReal_neg, ← MeasureTheory.integral_neg]
      congr 2; funext v; ring
    rw [h1, h2, zero_add]
  have h1 := hdec (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) (by simp) (by simp)
  rw [heq_im, norm_mul, Complex.norm_I, one_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
  have him : (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)).im = 2 * Real.pi * t := by simp
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
  refine h1.trans ?_
  gcongr
  have : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  nlinarith [abs_nonneg t]

lemma omegafun_rapid_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C / (1 + |t|) ^ n := by
  obtain ⟨C, hC, hk⟩ := kfun_rapid_decay n
  refine ⟨C ^ 2, by positivity, fun t => ?_⟩
  unfold omegafun lfun
  rw [abs_mul, abs_pow, abs_mul]
  have h1 : |Real.sin (Real.pi * t / 5)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.cos (4 * Real.pi * t)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : (|Real.sin (Real.pi * t / 5)| * |kfun t|) ^ 2 ≤ |kfun t| ^ 2 := by
    have : |Real.sin (Real.pi * t / 5)| * |kfun t| ≤ |kfun t| := by
      simpa using mul_le_mul_of_nonneg_right h1 (abs_nonneg (kfun t))
    exact pow_le_pow_left₀ (by positivity) this 2
  have h4 : |kfun t| ^ 2 ≤ (C / (1 + |t|) ^ n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hk t) 2
  have h5 : (C / (1 + |t|) ^ n) ^ 2 ≤ C ^ 2 / (1 + |t|) ^ n := by
    rw [div_pow, ← pow_mul]
    apply div_le_div_of_nonneg_left (sq_nonneg C) (pow_pos (by linarith [abs_nonneg t]) n)
    exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  calc (|Real.sin (Real.pi * t / 5)| * |kfun t|) ^ 2 * |Real.cos (4 * Real.pi * t)|
      ≤ (|Real.sin (Real.pi * t / 5)| * |kfun t|) ^ 2 * 1 := by gcongr
    _ = (|Real.sin (Real.pi * t / 5)| * |kfun t|) ^ 2 := mul_one _
    _ ≤ C ^ 2 / (1 + |t|) ^ n := le_trans h3 (le_trans h4 h5)

lemma differentiable_omegafun : Differentiable ℝ omegafun := by
  have hk : Differentiable ℝ kfun := fun t => (hasDerivAt_kfun t).differentiableAt
  unfold omegafun lfun
  have h1 : Differentiable ℝ (fun t : ℝ => Real.sin (Real.pi * t / 5)) :=
    Real.differentiable_sin.comp ((differentiable_id.const_mul Real.pi).div_const 5)
  have h2 : Differentiable ℝ (fun t : ℝ => Real.cos (4 * Real.pi * t)) :=
    Real.differentiable_cos.comp (differentiable_id.const_mul (4 * Real.pi))
  exact ((h1.mul hk).pow 2).mul h2

lemma deriv_omegafun_rapid_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv omegafun t| ≤ C / (1 + |t|) ^ n := by
  obtain ⟨Ck, hCk, hk⟩ := kfun_rapid_decay n
  obtain ⟨Cd, hCd, hd⟩ := deriv_kfun_rapid_decay n
  refine ⟨(2 * Real.pi / 5 + 4 * Real.pi) * Ck ^ 2 + 2 * Ck * Cd, by positivity, fun t => ?_⟩
  have hdk : HasDerivAt kfun (deriv kfun t) t := (hasDerivAt_kfun t).differentiableAt.hasDerivAt
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x / 5))
      (Real.cos (Real.pi * t / 5) * (Real.pi / 5)) t := by
    have hlin : HasDerivAt (fun x : ℝ => Real.pi * x / 5) (Real.pi / 5) t := by
      have := (hasDerivAt_id t).const_mul Real.pi |>.div_const 5
      simpa using this
    exact hlin.sin
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (4 * Real.pi * x))
      (-Real.sin (4 * Real.pi * t) * (4 * Real.pi)) t := by
    have hlin : HasDerivAt (fun x : ℝ => 4 * Real.pi * x) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    exact hlin.cos
  have hl : HasDerivAt lfun (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
      Real.sin (Real.pi * t / 5) * deriv kfun t) t := hsin.mul hdk
  have hl2 : HasDerivAt (fun x : ℝ => (lfun x) ^ 2)
      (2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t)) t := by
    simpa [pow_one] using hl.fun_pow 2
  have hom : HasDerivAt omegafun
      (2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t) * Real.cos (4 * Real.pi * t) +
      (lfun t) ^ 2 * (-Real.sin (4 * Real.pi * t) * (4 * Real.pi))) t := hl2.mul hcos
  rw [hom.deriv]
  have hkt := hk t
  have hdt := hd t
  have hlt : |lfun t| ≤ |kfun t| := by
    unfold lfun; rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg (kfun t))
  have hden : (1 : ℝ) ≤ (1 + |t|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t])
  have hdenp : 0 < (1 + |t|) ^ n := pow_pos (by linarith [abs_nonneg t]) n
  have hsq : |kfun t| ^ 2 ≤ Ck ^ 2 / (1 + |t|) ^ n := by
    calc |kfun t| ^ 2 ≤ (Ck / (1 + |t|) ^ n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hkt 2
      _ = Ck ^ 2 / ((1 + |t|) ^ n * (1 + |t|) ^ n) := by rw [div_pow, sq ((1 + |t|) ^ n)]
      _ ≤ Ck ^ 2 / (1 + |t|) ^ n := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) hdenp; nlinarith
  have hkd : |kfun t| * |deriv kfun t| ≤ Ck * Cd / (1 + |t|) ^ n := by
    calc |kfun t| * |deriv kfun t| ≤ (Ck / (1 + |t|) ^ n) * (Cd / (1 + |t|) ^ n) :=
          mul_le_mul hkt hdt (abs_nonneg _) (by positivity)
      _ = Ck * Cd / ((1 + |t|) ^ n * (1 + |t|) ^ n) := by ring
      _ ≤ Ck * Cd / (1 + |t|) ^ n := by
          apply div_le_div_of_nonneg_left (mul_nonneg hCk hCd) hdenp; nlinarith
  have h1 : |2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t) * Real.cos (4 * Real.pi * t)| ≤
      2 * (Real.pi / 5) * |kfun t| ^ 2 + 2 * |kfun t| * |deriv kfun t| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hc4 : |Real.cos (4 * Real.pi * t)| ≤ 1 := Real.abs_cos_le_one _
    have hbr : |Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t| ≤
        (Real.pi / 5) * |kfun t| + |deriv kfun t| := by
      calc _ ≤ |Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t| +
            |Real.sin (Real.pi * t / 5) * deriv kfun t| := abs_add_le _ _
        _ = |Real.cos (Real.pi * t / 5)| * (Real.pi / 5) * |kfun t| +
            |Real.sin (Real.pi * t / 5)| * |deriv kfun t| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 5)]
        _ ≤ 1 * (Real.pi / 5) * |kfun t| + 1 * |deriv kfun t| := by
            gcongr; exact Real.abs_cos_le_one _; exact Real.abs_sin_le_one _
        _ = _ := by ring
    calc 2 * |lfun t| * |Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
          Real.sin (Real.pi * t / 5) * deriv kfun t| * |Real.cos (4 * Real.pi * t)|
        ≤ 2 * |kfun t| * ((Real.pi / 5) * |kfun t| + |deriv kfun t|) * 1 := by
          gcongr
      _ = 2 * (Real.pi / 5) * |kfun t| ^ 2 + 2 * |kfun t| * |deriv kfun t| := by ring
  have h2 : |(lfun t) ^ 2 * (-Real.sin (4 * Real.pi * t) * (4 * Real.pi))| ≤
      4 * Real.pi * |kfun t| ^ 2 := by
    rw [abs_mul, abs_pow, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 4 * Real.pi)]
    calc |lfun t| ^ 2 * (|Real.sin (4 * Real.pi * t)| * (4 * Real.pi))
        ≤ |kfun t| ^ 2 * (1 * (4 * Real.pi)) := by
          gcongr; exact Real.abs_sin_le_one _
      _ = 4 * Real.pi * |kfun t| ^ 2 := by ring
  calc |2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
          Real.sin (Real.pi * t / 5) * deriv kfun t) * Real.cos (4 * Real.pi * t) +
        lfun t ^ 2 * (-Real.sin (4 * Real.pi * t) * (4 * Real.pi))|
      ≤ (2 * (Real.pi / 5) * |kfun t| ^ 2 + 2 * |kfun t| * |deriv kfun t|) + 4 * Real.pi * |kfun t| ^ 2 :=
        (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (2 * Real.pi / 5 + 4 * Real.pi) * |kfun t| ^ 2 + 2 * (|kfun t| * |deriv kfun t|) := by ring
    _ ≤ (2 * Real.pi / 5 + 4 * Real.pi) * (Ck ^ 2 / (1 + |t|) ^ n) + 2 * (Ck * Cd / (1 + |t|) ^ n) := by
        gcongr
    _ = ((2 * Real.pi / 5 + 4 * Real.pi) * Ck ^ 2 + 2 * Ck * Cd) / (1 + |t|) ^ n := by ring

lemma omegafun_le_const_mul_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C * t ^ 2 := by
  obtain ⟨Ck, hCk, hk⟩ := kfun_rapid_decay 0
  refine ⟨(Real.pi / 5 * Ck) ^ 2, by positivity, fun t => ?_⟩
  unfold omegafun lfun
  rw [abs_mul, abs_pow, abs_mul]
  have hs : |Real.sin (Real.pi * t / 5)| ≤ |Real.pi * t / 5| := Real.abs_sin_le_abs
  have hkt : |kfun t| ≤ Ck := by simpa using hk t
  have h1 : |Real.sin (Real.pi * t / 5)| * |kfun t| ≤ (Real.pi / 5 * Ck) * |t| := by
    calc |Real.sin (Real.pi * t / 5)| * |kfun t|
        ≤ |Real.pi * t / 5| * Ck := mul_le_mul hs hkt (abs_nonneg _) (abs_nonneg _)
      _ = (Real.pi / 5 * Ck) * |t| := by
          rw [show Real.pi * t / 5 = (Real.pi / 5) * t by ring, abs_mul,
            abs_of_pos (by positivity : 0 < Real.pi / 5)]; ring
  calc (|Real.sin (Real.pi * t / 5)| * |kfun t|) ^ 2 * |Real.cos (4 * Real.pi * t)|
      ≤ ((Real.pi / 5 * Ck) * |t|) ^ 2 * 1 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
    _ = (Real.pi / 5 * Ck) ^ 2 * t ^ 2 := by rw [mul_one, mul_pow, sq_abs]

lemma integrable_omegafun : Integrable omegafun := by
  obtain ⟨C, hC, hdec⟩ := omegafun_rapid_decay 2
  refine (integrable_div_one_add_abs_pow C 2 le_rfl).mono'
    differentiable_omegafun.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hdec t)

lemma kfun_sq_eq_integral_Kfun_cos (t : ℝ) :
    (kfun t) ^ 2 = ∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t) := by
  have hcexp_v : Continuous (fun v : ℝ => Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hsqC : ((kfun t : ℂ) ^ 2) =
      ∫ v : ℝ, (Kfun v : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) := by
    rw [sq, kfun_eq_cexp_integral t]
    rw [← MeasureTheory.integral_mul_const]
    have h1 : (∫ u : ℝ, ((bfun u : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (u : ℂ))) *
        (∫ w : ℝ, (bfun w : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (w : ℂ)))) =
        ∫ u : ℝ, ∫ w : ℝ, ((bfun u : ℂ) * (bfun w : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * ((u + w : ℝ) : ℂ)) := by
      congr 1; funext u
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext w
      rw [show ((bfun u : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (u : ℂ))) *
          ((bfun w : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (w : ℂ))) =
          ((bfun u : ℂ) * (bfun w : ℂ)) * (Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (u : ℂ)) *
            Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (w : ℂ))) by ring,
        ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [h1]
    have hshift : ∀ u : ℝ,
        (∫ w : ℝ, ((bfun u : ℂ) * (bfun w : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * ((u + w : ℝ) : ℂ))) =
        ∫ v : ℝ, ((bfun u : ℂ) * (bfun (v - u) : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ)) := by
      intro u
      have := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun v : ℝ => ((bfun u : ℂ) * (bfun (v - u) : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) (-u)
      simpa [sub_neg_eq_add, add_sub_cancel_right, add_comm] using this
    simp_rw [hshift]
    have hint_uv : Integrable (Function.uncurry fun u v : ℝ =>
        ((bfun u : ℂ) * (bfun (v - u) : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) := by
      have hcont : Continuous (Function.uncurry fun u v : ℝ =>
          ((bfun u : ℂ) * (bfun (v - u) : ℂ)) *
            Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) := by
        unfold Function.uncurry
        exact ((Complex.continuous_ofReal.comp (contDiff_bfun.continuous.comp continuous_fst)).mul
          (Complex.continuous_ofReal.comp (contDiff_bfun.continuous.comp (continuous_snd.sub continuous_fst)))).mul
          (hcexp_v.comp continuous_snd)
      have hcomp : HasCompactSupport (Function.uncurry fun u v : ℝ =>
          ((bfun u : ℂ) * (bfun (v - u) : ℂ)) *
            Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) := by
        refine HasCompactSupport.intro (K := Set.Icc (-(1 / 40 : ℝ)) (1 / 40) ×ˢ Set.Icc (-(1 / 20 : ℝ)) (1 / 20))
          (isCompact_Icc.prod isCompact_Icc) fun p hp => ?_
        simp only [Function.uncurry]
        by_cases h1 : (-1 / 40 : ℝ) < p.1 ∧ p.1 < 1 / 40
        · have h2 : ¬ ((-1 / 40 : ℝ) < p.2 - p.1 ∧ p.2 - p.1 < 1 / 40) := by
            intro hvu; apply hp
            exact ⟨⟨by linarith [h1.1], h1.2.le⟩, ⟨by linarith [h1.1, hvu.1], by linarith [h1.2, hvu.2]⟩⟩
          have hb0 : bfun (p.2 - p.1) = 0 := bump_eq_zero_of_not_mem h2
          rw [hb0]; simp
        · have hb0 : bfun p.1 = 0 := bump_eq_zero_of_not_mem h1
          rw [hb0]; simp
      exact hcont.integrable_of_hasCompactSupport hcomp
    rw [MeasureTheory.integral_integral_swap hint_uv]
    congr 1; funext v
    rw [MeasureTheory.integral_mul_const]
    congr 1
    have hint_K : Integrable (fun u : ℝ => bfun u * bfun (v - u)) :=
      (contDiff_bfun.continuous.mul (contDiff_bfun.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        hasCompactSupport_bfun.mul_right
    have hK_c := Complex.ofRealCLM.integral_comp_comm hint_K
    simpa [Kfun] using hK_c
  have hre := congrArg Complex.re hsqC
  have hint_Kexp : Integrable (fun v : ℝ => (Kfun v : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))) :=
    ((Complex.continuous_ofReal.comp continuous_Kfun).mul hcexp_v).integrable_of_hasCompactSupport
      (hasCompactSupport_Kfun.comp_left Complex.ofReal_zero).mul_right
  have hre_comm := Complex.reCLM.integral_comp_comm hint_Kexp
  have hre_lhs : ((kfun t : ℂ) ^ 2).re = (kfun t) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre_lhs] at hre
  have hre' : (kfun t) ^ 2 = ∫ v : ℝ, ((Kfun v : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ))).re := by
    rw [hre]; simpa using hre_comm.symm
  rw [hre']
  congr 1; funext v
  have harg : Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (v : ℂ) =
      ((2 * Real.pi * v * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one]

lemma omegafun_eq_integral_Kfun (t : ℝ) :
    omegafun t = ∫ v : ℝ, Kfun v *
      ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * t) -
       (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * t) -
       (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * t)) := by
  have htrig : (Real.sin (Real.pi * t / 5)) ^ 2 * Real.cos (4 * Real.pi * t) =
      (1 / 2) * Real.cos (2 * Real.pi * 2 * t) -
      (1 / 4) * Real.cos (2 * Real.pi * (2 + 1 / 5) * t) -
      (1 / 4) * Real.cos (2 * Real.pi * (2 - 1 / 5) * t) := by
    have hs : (Real.sin (Real.pi * t / 5)) ^ 2 = (1 - Real.cos (2 * Real.pi * (1 / 5) * t)) / 2 := by
      have h := Real.cos_two_mul (Real.pi * t / 5)
      have hsc := Real.sin_sq_add_cos_sq (Real.pi * t / 5)
      rw [show 2 * (Real.pi * t / 5) = 2 * Real.pi * (1 / 5) * t by ring] at h
      linarith
    have hprod : Real.cos (2 * Real.pi * (1 / 5) * t) * Real.cos (2 * Real.pi * 2 * t) =
        (Real.cos (2 * Real.pi * (2 + 1 / 5) * t) + Real.cos (2 * Real.pi * (2 - 1 / 5) * t)) / 2 := by
      have h1 := Real.cos_add (2 * Real.pi * 2 * t) (2 * Real.pi * (1 / 5) * t)
      have h2 := Real.cos_sub (2 * Real.pi * 2 * t) (2 * Real.pi * (1 / 5) * t)
      rw [show 2 * Real.pi * 2 * t + 2 * Real.pi * (1 / 5) * t = 2 * Real.pi * (2 + 1 / 5) * t by ring] at h1
      rw [show 2 * Real.pi * 2 * t - 2 * Real.pi * (1 / 5) * t = 2 * Real.pi * (2 - 1 / 5) * t by ring] at h2
      linarith
    rw [hs, show 4 * Real.pi * t = 2 * Real.pi * 2 * t by ring]
    linarith
  have hint_a : ∀ a : ℝ, Integrable (fun v : ℝ => Kfun v * Real.cos (2 * Real.pi * (a + v) * t)) := fun a =>
    (continuous_Kfun.mul (Real.continuous_cos.comp
      ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const))).integrable_of_hasCompactSupport
      hasCompactSupport_Kfun.mul_right
  have hint_am : ∀ a : ℝ, Integrable (fun v : ℝ => Kfun v * Real.cos (2 * Real.pi * (a - v) * t)) := fun a =>
    (continuous_Kfun.mul (Real.continuous_cos.comp
      ((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const))).integrable_of_hasCompactSupport
      hasCompactSupport_Kfun.mul_right
  have hshift_cos : ∀ a : ℝ,
      (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t)) * Real.cos (2 * Real.pi * a * t) =
      ∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (a + v) * t) := by
    intro a
    rw [← MeasureTheory.integral_mul_const]
    have h1 : ∀ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t) * Real.cos (2 * Real.pi * a * t) =
        (1 / 2) * (Kfun v * Real.cos (2 * Real.pi * (a + v) * t)) +
        (1 / 2) * (Kfun v * Real.cos (2 * Real.pi * (a - v) * t)) := by
      intro v
      have hp := Real.cos_add (2 * Real.pi * a * t) (2 * Real.pi * v * t)
      have hm := Real.cos_sub (2 * Real.pi * a * t) (2 * Real.pi * v * t)
      rw [show 2 * Real.pi * a * t + 2 * Real.pi * v * t = 2 * Real.pi * (a + v) * t by ring] at hp
      rw [show 2 * Real.pi * a * t - 2 * Real.pi * v * t = 2 * Real.pi * (a - v) * t by ring] at hm
      linear_combination -(1 / 2) * Kfun v * (hp + hm)
    simp_rw [h1]
    rw [MeasureTheory.integral_add ((hint_a a).const_mul _) ((hint_am a).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have heq2 : ∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (a - v) * t) =
        ∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (a + v) * t) := by
      rw [← MeasureTheory.integral_neg_eq_self (fun v : ℝ => Kfun v * Real.cos (2 * Real.pi * (a - v) * t)) volume]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      dsimp only; rw [Kfun_symm v, sub_neg_eq_add]
    rw [heq2]; ring
  calc omegafun t = ((Real.sin (Real.pi * t / 5)) ^ 2 * Real.cos (4 * Real.pi * t)) * (kfun t) ^ 2 := by
        unfold omegafun lfun; ring
    _ = ((1 / 2) * Real.cos (2 * Real.pi * 2 * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + 1 / 5) * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 - 1 / 5) * t)) *
         (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t)) := by
        rw [htrig, kfun_sq_eq_integral_Kfun_cos]
    _ = (1 / 2) * ((∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t)) * Real.cos (2 * Real.pi * 2 * t)) -
        (1 / 4) * ((∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t)) * Real.cos (2 * Real.pi * (2 + 1 / 5) * t)) -
        (1 / 4) * ((∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * v * t)) * Real.cos (2 * Real.pi * (2 - 1 / 5) * t)) := by
        ring
    _ = (1 / 2) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (2 + v) * t)) -
        (1 / 4) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * ((2 + 1 / 5) + v) * t)) -
        (1 / 4) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * ((2 - 1 / 5) + v) * t)) := by
        rw [hshift_cos 2, hshift_cos (2 + 1 / 5), hshift_cos (2 - 1 / 5)]
    _ = ∫ v : ℝ, Kfun v *
        ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * t)) := by
        have hsub1 := MeasureTheory.integral_sub ((hint_a 2).const_mul (1 / 2)) ((hint_a (2 + 1 / 5)).const_mul (1 / 4))
        have hsub2 := MeasureTheory.integral_sub (((hint_a 2).const_mul (1 / 2)).sub ((hint_a (2 + 1 / 5)).const_mul (1 / 4)))
          ((hint_a (2 - 1 / 5)).const_mul (1 / 4))
        simp only [Pi.sub_apply] at hsub1 hsub2
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hsub1
        rw [MeasureTheory.integral_const_mul, hsub1] at hsub2
        rw [← hsub2]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        have e1 : (2 + 1 / 5 : ℝ) + v = 2 + v + 1 / 5 := by ring
        have e2 : (2 - 1 / 5 : ℝ) + v = 2 + v - 1 / 5 := by ring
        rw [e1, e2]; ring

lemma integral_omegafun_eq_zero : ∫ t : ℝ, omegafun t = 0 := by
  let H : ℝ → ℂ := fun ξ =>
    ((1 / 4 * (Kfun (ξ - 2) + Kfun (ξ + 2)) -
      1 / 8 * (Kfun (ξ - (2 + 1 / 5)) + Kfun (ξ + (2 + 1 / 5)) +
               Kfun (ξ - (2 - 1 / 5)) + Kfun (ξ + (2 - 1 / 5))) : ℝ) : ℂ)
  have hH_cont : Continuous H := by
    refine Complex.continuous_ofReal.comp ?_
    have hc : ∀ a : ℝ, Continuous (fun ξ : ℝ => Kfun (ξ - a)) := fun a =>
      continuous_Kfun.comp (continuous_id.sub continuous_const)
    have hc' : ∀ a : ℝ, Continuous (fun ξ : ℝ => Kfun (ξ + a)) := fun a =>
      continuous_Kfun.comp (continuous_id.add continuous_const)
    exact (continuous_const.mul ((hc 2).add (hc' 2))).sub
      (continuous_const.mul ((((hc (2 + 1 / 5)).add (hc' (2 + 1 / 5))).add (hc (2 - 1 / 5))).add (hc' (2 - 1 / 5))))
  have hH_comp : HasCompactSupport H := by
    refine HasCompactSupport.intro (K := Set.Icc (-3 : ℝ) 3) isCompact_Icc fun ξ hξ => ?_
    have habs : 3 < |ξ| := by
      rcases not_and_or.mp hξ with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hk0 : ∀ a : ℝ, |a| ≤ 11 / 5 → Kfun (ξ - a) = 0 ∧ Kfun (ξ + a) = 0 := by
      intro a ha
      constructor <;> apply Kfun_eq_zero_of_abs_ge
      · have := abs_sub_abs_le_abs_sub ξ a; linarith
      · have := abs_sub_abs_le_abs_sub ξ (-a); rw [abs_neg, sub_neg_eq_add] at this; linarith
    have h1 := hk0 2 (by norm_num)
    have h2 := hk0 (2 + 1 / 5) (by norm_num)
    have h3 := hk0 (2 - 1 / 5) (by norm_num)
    show H ξ = 0
    dsimp only [H]
    rw [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    norm_num
  have hH_int : Integrable H := hH_cont.integrable_of_hasCompactSupport hH_comp
  have hcexp_xt : ∀ t : ℝ, Continuous (fun ξ : ℝ => Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) :=
    fun t => Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_id.mul continuous_const))).mul continuous_const)
  have hshift_F : ∀ a t : ℝ,
      ∫ ξ : ℝ, ((Kfun (ξ - a) + Kfun (ξ + a) : ℝ) : ℂ) *
        Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I) =
      ((2 * ∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (a + v) * t) : ℝ) : ℂ) := by
    intro a t
    have hint1 : Integrable (fun ξ : ℝ => (Kfun (ξ - a) : ℂ) *
        Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.comp (continuous_Kfun.comp (continuous_id.sub continuous_const))).mul
        (hcexp_xt t)).integrable_of_hasCompactSupport
        ((hasCompactSupport_Kfun.comp_homeomorph (Homeomorph.subRight a)).comp_left Complex.ofReal_zero).mul_right
    have hint2 : Integrable (fun ξ : ℝ => (Kfun (ξ + a) : ℂ) *
        Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.comp (continuous_Kfun.comp (continuous_id.add continuous_const))).mul
        (hcexp_xt t)).integrable_of_hasCompactSupport
        ((hasCompactSupport_Kfun.comp_homeomorph (Homeomorph.addRight a)).comp_left Complex.ofReal_zero).mul_right
    simp_rw [Complex.ofReal_add, add_mul]
    rw [MeasureTheory.integral_add hint1 hint2]
    have hI1 : ∫ ξ : ℝ, (Kfun (ξ - a) : ℂ) * Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I) =
        ∫ v : ℝ, (Kfun v : ℂ) * Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) := by
      have := MeasureTheory.integral_add_right_eq_self (μ := volume)
        (fun v : ℝ => (Kfun v : ℂ) * Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) (-a)
      rw [← this]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      dsimp only; rw [sub_eq_add_neg]; congr 3; ring
    have hI2 : ∫ ξ : ℝ, (Kfun (ξ + a) : ℂ) * Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I) =
        ∫ v : ℝ, (Kfun v : ℂ) * Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) := by
      have hneg := MeasureTheory.integral_neg_eq_self
        (fun ξ : ℝ => (Kfun (ξ + a) : ℂ) * Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) volume
      rw [← hneg]
      have hsub := MeasureTheory.integral_add_right_eq_self (μ := volume)
        (fun v : ℝ => (Kfun v : ℂ) * Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) (-a)
      rw [← hsub]
      congr 1; funext ξ
      rw [show -ξ + a = -(ξ - a) by ring, Kfun_symm (ξ - a)]
      congr 2; push_cast; ring
    rw [hI1, hI2]
    have hcexpA : Continuous (fun v : ℝ => Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_const.add continuous_id).mul continuous_const))).mul continuous_const)
    have hcexpB : Continuous (fun v : ℝ => Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_const.add continuous_id).mul continuous_const))).mul continuous_const)
    have hintA : Integrable (fun v : ℝ => (Kfun v : ℂ) * Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.comp continuous_Kfun).mul hcexpA).integrable_of_hasCompactSupport
        (hasCompactSupport_Kfun.comp_left Complex.ofReal_zero).mul_right
    have hintB : Integrable (fun v : ℝ => (Kfun v : ℂ) * Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.comp continuous_Kfun).mul hcexpB).integrable_of_hasCompactSupport
        (hasCompactSupport_Kfun.comp_left Complex.ofReal_zero).mul_right
    rw [← MeasureTheory.integral_add hintA hintB]
    have hcos_sum : ∀ v : ℝ,
        (Kfun v : ℂ) * Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) +
        (Kfun v : ℂ) * Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) =
        ((2 * (Kfun v * Real.cos (2 * Real.pi * (a + v) * t)) : ℝ) : ℂ) := by
      intro v
      have h1 : Complex.exp (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) =
          Complex.cos ((2 * Real.pi * (a + v) * t : ℝ) : ℂ) -
            Complex.sin ((2 * Real.pi * (a + v) * t : ℝ) : ℂ) * Complex.I := by
        rw [show (((-2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) =
            (-((2 * Real.pi * (a + v) * t : ℝ) : ℂ)) * Complex.I by push_cast; ring,
          Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
      have h2 : Complex.exp (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) =
          Complex.cos ((2 * Real.pi * (a + v) * t : ℝ) : ℂ) +
            Complex.sin ((2 * Real.pi * (a + v) * t : ℝ) : ℂ) * Complex.I := by
        rw [show (((2 * Real.pi * ((a + v) * t) : ℝ) : ℂ) * Complex.I) =
            ((2 * Real.pi * (a + v) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_mul_I]
      rw [h1, h2, ← Complex.ofReal_cos]; push_cast; ring
    simp_rw [hcos_sum]
    have hintR : Integrable (fun v : ℝ => Kfun v * Real.cos (2 * Real.pi * (a + v) * t)) :=
      (continuous_Kfun.mul (Real.continuous_cos.comp
        ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const))).integrable_of_hasCompactSupport
        hasCompactSupport_Kfun.mul_right
    have hc := Complex.ofRealCLM.integral_comp_comm (hintR.const_mul 2)
    rw [MeasureTheory.integral_const_mul] at hc
    simpa using hc
  have hFH : ∀ t : ℝ, 𝓕 H t = (omegafun t : ℂ) := by
    intro t
    rw [Real.fourier_eq']
    have hsplit : ∀ ξ : ℝ, Complex.exp (((-2 * Real.pi * ⟪ξ, t⟫ : ℝ) : ℂ) * Complex.I) • H ξ =
        (1 / 4 : ℂ) * (((Kfun (ξ - 2) + Kfun (ξ + 2) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) -
        (1 / 8 : ℂ) * (((Kfun (ξ - (2 + 1 / 5)) + Kfun (ξ + (2 + 1 / 5)) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) -
        (1 / 8 : ℂ) * (((Kfun (ξ - (2 - 1 / 5)) + Kfun (ξ + (2 - 1 / 5)) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) := by
      intro ξ
      simp only [H, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      push_cast; ring
    simp_rw [hsplit]
    have hintP : ∀ a : ℝ, Integrable (fun ξ : ℝ =>
        ((Kfun (ξ - a) + Kfun (ξ + a) : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I)) := fun a =>
      ((Complex.continuous_ofReal.comp ((continuous_Kfun.comp (continuous_id.sub continuous_const)).add
        (continuous_Kfun.comp (continuous_id.add continuous_const)))).mul (hcexp_xt t)).integrable_of_hasCompactSupport
        (((hasCompactSupport_Kfun.comp_homeomorph (Homeomorph.subRight a)).add
          (hasCompactSupport_Kfun.comp_homeomorph (Homeomorph.addRight a))).comp_left Complex.ofReal_zero).mul_right
    have hsub1 := MeasureTheory.integral_sub ((hintP 2).const_mul (1 / 4 : ℂ)) ((hintP (2 + 1 / 5)).const_mul (1 / 8 : ℂ))
    have hsub2 := MeasureTheory.integral_sub
      (((hintP 2).const_mul (1 / 4 : ℂ)).sub ((hintP (2 + 1 / 5)).const_mul (1 / 8 : ℂ)))
      ((hintP (2 - 1 / 5)).const_mul (1 / 8 : ℂ))
    simp only [Pi.sub_apply] at hsub1 hsub2
    rw [hsub2, hsub1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, hshift_F 2 t, hshift_F (2 + 1 / 5) t, hshift_F (2 - 1 / 5) t]
    rw [omegafun_eq_integral_Kfun t]
    have hint_a : ∀ a : ℝ, Integrable (fun v : ℝ => Kfun v * Real.cos (2 * Real.pi * (a + v) * t)) := fun a =>
      (continuous_Kfun.mul (Real.continuous_cos.comp
        ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const))).integrable_of_hasCompactSupport
        hasCompactSupport_Kfun.mul_right
    have heqR : ∫ v : ℝ, Kfun v *
        ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * t) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * t)) =
        (1 / 2) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * (2 + v) * t)) -
        (1 / 4) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * ((2 + 1 / 5) + v) * t)) -
        (1 / 4) * (∫ v : ℝ, Kfun v * Real.cos (2 * Real.pi * ((2 - 1 / 5) + v) * t)) := by
      have hs1 := MeasureTheory.integral_sub ((hint_a 2).const_mul (1 / 2)) ((hint_a (2 + 1 / 5)).const_mul (1 / 4))
      have hs2 := MeasureTheory.integral_sub (((hint_a 2).const_mul (1 / 2)).sub ((hint_a (2 + 1 / 5)).const_mul (1 / 4)))
        ((hint_a (2 - 1 / 5)).const_mul (1 / 4))
      simp only [Pi.sub_apply] at hs1 hs2
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hs1
      rw [MeasureTheory.integral_const_mul, hs1] at hs2
      rw [← hs2]
      congr 1; funext v
      have e1 : (2 + 1 / 5 : ℝ) + v = 2 + v + 1 / 5 := by ring
      have e2 : (2 - 1 / 5 : ℝ) + v = 2 + v - 1 / 5 := by ring
      rw [e1, e2]; ring
    rw [heqR]; push_cast; ring
  have hFH_int : Integrable (𝓕 H) := by
    have : 𝓕 H = fun t : ℝ => (omegafun t : ℂ) := funext hFH
    rw [this]
    exact Complex.ofRealCLM.integrable_comp integrable_omegafun
  have hinv := hH_int.fourierInv_fourier_eq hFH_int hH_cont.continuousAt (v := 0)
  rw [Real.fourierInv_eq'] at hinv
  have hH0 : H 0 = 0 := by
    dsimp only [H]
    have h1 : Kfun (0 - 2) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    have h2 : Kfun (0 + 2) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    have h3 : Kfun (0 - (2 + 1 / 5)) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    have h4 : Kfun (0 + (2 + 1 / 5)) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    have h5 : Kfun (0 - (2 - 1 / 5)) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    have h6 : Kfun (0 + (2 - 1 / 5)) = 0 := Kfun_eq_zero_of_abs_ge (by norm_num)
    rw [h1, h2, h3, h4, h5, h6]; norm_num
  simp only [RCLike.inner_apply, conj_trivial, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, hFH, hH0] at hinv
  have hcomm := Complex.ofRealCLM.integral_comp_comm integrable_omegafun
  have hinv' : ((∫ t : ℝ, omegafun t : ℝ) : ℂ) = 0 := by
    simpa [hinv] using hcomm.symm
  exact Complex.ofReal_injective hinv'

lemma integral_Ioi_omegafun_eq_zero : ∫ t in Set.Ioi (0 : ℝ), omegafun t = 0 := by
  have hsplit : (∫ t in Set.Iic (0 : ℝ), omegafun t) + ∫ t in Set.Ioi (0 : ℝ), omegafun t =
      ∫ t : ℝ, omegafun t := by
    rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      integrable_omegafun.integrableOn integrable_omegafun.integrableOn, Set.Iic_union_Ioi,
      MeasureTheory.setIntegral_univ]
  have hIic : ∫ t in Set.Iic (0 : ℝ), omegafun t = ∫ t in Set.Ioi (0 : ℝ), omegafun t := by
    have h1 := MeasureTheory.integral_Iic_eq_integral_Iio (μ := volume) (f := omegafun) (x := (0 : ℝ))
    rw [h1]
    have h2 : ∫ t in Set.Iio (0 : ℝ), omegafun t = ∫ t in Set.Ioi (0 : ℝ), omegafun (-t) := by
      have himg : Neg.neg '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
        ext x; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
        exact ⟨fun ⟨y, hy, hxy⟩ => by linarith, fun hx => ⟨-x, by linarith, neg_neg x⟩⟩
      rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
        (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) neg_injective.injOn]
      simp
    rw [h2]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => omegafun_even t
  rw [hIic, integral_omegafun_eq_zero] at hsplit
  linarith

lemma integral_Ioi_exp_mul_sin {s a : ℝ} (hs : 0 < s) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-s * u) * Real.sin (a * u) = a / (s ^ 2 + a ^ 2) := by
  let z : ℂ := ((-s : ℝ) : ℂ) + Complex.I * (a : ℂ)
  have hz : z ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [z] at this; linarith
  have hderiv : ∀ u : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (z * (x : ℂ)) / z)
      (Complex.exp (z * (u : ℂ))) u := by
    intro u
    have hlin : HasDerivAt (fun x : ℝ => z * (x : ℂ)) (z * 1) u :=
      (Complex.ofRealCLM.hasDerivAt).const_mul z
    have he := hlin.cexp.div_const z
    simpa [mul_div_cancel_right₀ _ hz] using he
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (z * (u : ℂ))) (Set.Ioi 0) := by
    have hdom : IntegrableOn (fun u : ℝ => Real.exp (-s * u)) (Set.Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    have hcont : Continuous (fun u : ℝ => Complex.exp (z * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]
    have : (z * (u : ℂ)).re = -s * u := by simp [z]
    rw [this]
  have hlim : Tendsto (fun u : ℝ => Complex.exp (z * (u : ℂ)) / z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun u : ℝ => ‖Complex.exp (z * (u : ℂ)) / z‖) = (fun u : ℝ => Real.exp (-s * u) / ‖z‖) := by
      funext u; rw [norm_div, Complex.norm_exp]; simp [z]
    rw [heq]
    have h1 : Tendsto (fun u : ℝ => -s * u) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp h1).div_const ‖z‖
  have hC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hderiv u) hint hlim
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub] at hC
  have him := congrArg Complex.im hC
  have hcomm := Complex.imCLM.integral_comp_comm hint
  have him' : (∫ u in Set.Ioi (0 : ℝ), (Complex.exp (z * (u : ℂ))).im) = (-(1 / z)).im := by
    rw [← him]; simpa using hcomm
  have hlhs : (∫ u in Set.Ioi (0 : ℝ), (Complex.exp (z * (u : ℂ))).im) =
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-s * u) * Real.sin (a * u) := by
    congr 1; funext u
    have : z * (u : ℂ) = ((-s * u : ℝ) : ℂ) + ((a * u : ℝ) : ℂ) * Complex.I := by
      simp only [z]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
  have hrhs : (-(1 / z)).im = a / (s ^ 2 + a ^ 2) := by
    rw [Complex.neg_im, one_div, Complex.inv_im]
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add, one_mul, Complex.normSq_apply]
    ring
  rw [hlhs, hrhs] at him'
  exact him'

lemma integral_Ioi_exp_mul_sin_div {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * u) * (Real.sin (a * u) / u) =
      Real.pi / 2 - Real.arctan (ε / a) := by
  have hinner : ∀ u ∈ Set.Ioi (0 : ℝ),
      Real.exp (-ε * u) * (Real.sin (a * u) / u) =
      ∫ s in Set.Ioi ε, Real.exp (-s * u) * Real.sin (a * u) := by
    intro u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    rw [MeasureTheory.integral_mul_const]
    have hexp : ∫ s in Set.Ioi ε, Real.exp (-s * u) = Real.exp (-ε * u) / u := by
      have h1 : (fun s : ℝ => Real.exp (-s * u)) = (fun s : ℝ => Real.exp ((-u) * s)) := by
        funext s; congr 1; ring
      rw [h1, integral_exp_mul_Ioi (by linarith : -u < 0) ε]
      have : -u * ε = -ε * u := by ring
      rw [this]; ring
    rw [hexp]; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner]
  have hcont_us : Continuous (Function.uncurry fun u s : ℝ => Real.exp (-s * u) * Real.sin (a * u)) :=
    (Real.continuous_exp.comp (continuous_snd.neg.mul continuous_fst)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_fst))
  have hint_prod : Integrable (Function.uncurry fun u s : ℝ => Real.exp (-s * u) * Real.sin (a * u))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi ε))) := by
    rw [MeasureTheory.integrable_prod_iff hcont_us.aestronglyMeasurable]
    constructor
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have h1 : IntegrableOn (fun s : ℝ => Real.exp ((-u) * s)) (Set.Ioi ε) :=
        integrableOn_exp_mul_Ioi (by linarith [Set.mem_Ioi.mp hu]) ε
      have h2 := h1.mul_const (Real.sin (a * u))
      have heq : (fun s : ℝ => Real.exp ((-u) * s) * Real.sin (a * u)) =
          (fun s : ℝ => Real.exp (-s * u) * Real.sin (a * u)) := by
        funext s; congr 2; ring
      dsimp only [Function.uncurry]; rwa [← heq]
    · have hdom : IntegrableOn (fun u : ℝ => a * Real.exp (-ε * u)) (Set.Ioi 0) :=
        (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul a
      refine hdom.mono' (by
        have hcont : ContinuousOn (fun u : ℝ => ∫ s in Set.Ioi ε, ‖Real.exp (-s * u) * Real.sin (a * u)‖)
            (Set.Ioi 0) := by
          have heq : Set.EqOn (fun u : ℝ => ∫ s in Set.Ioi ε, ‖Real.exp (-s * u) * Real.sin (a * u)‖)
              (fun u : ℝ => Real.exp (-ε * u) / u * |Real.sin (a * u)|) (Set.Ioi 0) := by
            intro u hu
            have hu0 : 0 < u := Set.mem_Ioi.mp hu
            simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            rw [MeasureTheory.integral_mul_const]
            have h1 : (fun s : ℝ => Real.exp (-s * u)) = (fun s : ℝ => Real.exp ((-u) * s)) := by
              funext s; congr 1; ring
            rw [h1, integral_exp_mul_Ioi (by linarith : -u < 0) ε]
            have : -u * ε = -ε * u := by ring
            rw [this]; ring
          have hc1 : Continuous (fun u : ℝ => Real.exp (-ε * u)) :=
            Real.continuous_exp.comp (continuous_const.mul continuous_id)
          have hc2 : Continuous (fun u : ℝ => |Real.sin (a * u)|) :=
            (Real.continuous_sin.comp (continuous_const.mul continuous_id)).abs
          exact ContinuousOn.congr ((hc1.continuousOn.div continuousOn_id
            (fun u hu => (Set.mem_Ioi.mp hu).ne')).mul hc2.continuousOn) heq
        exact hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := Set.mem_Ioi.mp hu
      dsimp only [Function.uncurry]
      simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [MeasureTheory.integral_mul_const]
      have h1 : (fun s : ℝ => Real.exp (-s * u)) = (fun s : ℝ => Real.exp ((-u) * s)) := by
        funext s; congr 1; ring
      rw [h1, integral_exp_mul_Ioi (by linarith : -u < 0) ε]
      have hsin : |Real.sin (a * u)| ≤ a * u := by
        simpa [abs_of_pos (mul_pos ha hu0)] using Real.abs_sin_le_abs (x := a * u)
      have heq_e : -Real.exp (-u * ε) / -u = Real.exp (-ε * u) / u := by
        rw [show -u * ε = -ε * u by ring]; ring
      rw [heq_e, abs_of_nonneg (by positivity)]
      calc Real.exp (-ε * u) / u * |Real.sin (a * u)|
          ≤ Real.exp (-ε * u) / u * (a * u) := by gcongr
        _ = a * Real.exp (-ε * u) := by field_simp [hu0.ne']
  rw [MeasureTheory.integral_integral_swap hint_prod]
  have heval : Set.EqOn (fun s : ℝ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-s * u) * Real.sin (a * u))
      (fun s : ℝ => a / (s ^ 2 + a ^ 2)) (Set.Ioi ε) := by
    intro s hs
    exact integral_Ioi_exp_mul_sin (lt_trans hε (Set.mem_Ioi.mp hs))
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heval]
  have hderiv : ∀ s ∈ Set.Ioi ε, HasDerivAt (fun x : ℝ => Real.arctan (x / a)) (a / (s ^ 2 + a ^ 2)) s := by
    intro s _
    have h1 : HasDerivAt (fun x : ℝ => x / a) (1 / a) s := by
      simpa using (hasDerivAt_id s).div_const a
    have h2 := h1.arctan
    convert h2 using 1
    field_simp [ha.ne']; ring
  have hint_atan : IntegrableOn (fun s : ℝ => a / (s ^ 2 + a ^ 2)) (Set.Ioi ε) := by
    have h1 : Integrable (fun s : ℝ => a / (s ^ 2 + a ^ 2)) := by
      have hsq : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq
      have hcomp := (hsq.comp_div ha.ne').const_mul (1 / a)
      refine hcomp.congr (Filter.Eventually.of_forall fun s => ?_)
      field_simp [ha.ne']; ring
    exact h1.integrableOn
  have hlim : Tendsto (fun s : ℝ => Real.arctan (s / a)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const ha)
  have hcont_at : ContinuousWithinAt (fun x : ℝ => Real.arctan (x / a)) (Set.Ici ε) ε :=
    (Real.continuous_arctan.comp (continuous_id.div_const a)).continuousAt.continuousWithinAt
  exact MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont_at hderiv hint_atan hlim

lemma integral_Ioi_omegafun_mul_log :
    ∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u =
      (1 / 16 : ℝ) * ∫ v : ℝ, Kfun v * (1 / (2 + v + 1 / 5) + 1 / (2 + v - 1 / 5) - 2 / (2 + v)) := by
  let F : ℝ → ℝ := fun u => ∫ r in (0 : ℝ)..u, omegafun r
  have hF_deriv : ∀ u : ℝ, HasDerivAt F (omegafun u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right
      (differentiable_omegafun.continuous.intervalIntegrable 0 u)
      (differentiable_omegafun.continuous.stronglyMeasurableAtFilter volume (𝓝 u))
      differentiable_omegafun.continuous.continuousAt
  have hF_tail : ∀ u ≥ (0 : ℝ), F u = - ∫ r in Set.Ioi u, omegafun r := by
    intro u hu
    have h1 : (∫ r in (0 : ℝ)..u, omegafun r) + ∫ r in Set.Ioi u, omegafun r =
        ∫ r in Set.Ioi (0 : ℝ), omegafun r := by
      rw [intervalIntegral.integral_of_le hu]
      have hU : Set.Ioc (0 : ℝ) u ∪ Set.Ioi u = Set.Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hu
      have hD : Disjoint (Set.Ioc (0 : ℝ) u) (Set.Ioi u) := Set.Ioc_disjoint_Ioi_same
      rw [← MeasureTheory.setIntegral_union hD measurableSet_Ioi
        integrable_omegafun.integrableOn integrable_omegafun.integrableOn, hU]
    rw [integral_Ioi_omegafun_eq_zero] at h1
    linarith
  obtain ⟨Cw3, hCw3, hdec3⟩ := omegafun_rapid_decay 3
  obtain ⟨Csq, hCsq, hsq⟩ := omegafun_le_const_mul_sq
  have hF_big : ∀ u ≥ (0 : ℝ), |F u| ≤ Cw3 / (1 + u) ^ 2 := by
    intro u hu
    rw [hF_tail u hu, abs_neg]
    have hint3 : IntegrableOn (fun r : ℝ => Cw3 / (1 + r) ^ 3) (Set.Ioi u) :=
      (integrable_div_one_add_abs_pow Cw3 3 (by norm_num)).integrableOn.congr_fun
        (fun r hr => by dsimp only; rw [abs_of_pos (lt_of_le_of_lt hu (Set.mem_Ioi.mp hr))]) measurableSet_Ioi
    calc |∫ r in Set.Ioi u, omegafun r|
        ≤ ∫ r in Set.Ioi u, |omegafun r| := by
          simpa [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm omegafun
      _ ≤ ∫ r in Set.Ioi u, Cw3 / (1 + r) ^ 3 := by
          apply MeasureTheory.setIntegral_mono_on integrable_omegafun.norm.integrableOn hint3 measurableSet_Ioi
          intro r hr
          have hr0 : 0 < r := lt_of_le_of_lt hu (Set.mem_Ioi.mp hr)
          simpa [abs_of_pos hr0] using hdec3 r
      _ = Cw3 / (2 * (1 + u) ^ 2) := by
          have hd : ∀ r ∈ Set.Ioi u, HasDerivAt (fun x : ℝ => -Cw3 / (2 * (1 + x) ^ 2))
              (Cw3 / (1 + r) ^ 3) r := by
            intro r hr
            have hr1 : 0 < 1 + r := by linarith [Set.mem_Ioi.mp hr]
            have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + r)) r := by
              simpa [pow_one] using ((hasDerivAt_id r).const_add 1).fun_pow 2
            have h2 := (hasDerivAt_const r (-Cw3)).div (h1.const_mul 2) (by positivity)
            convert h2 using 1; field_simp [hr1.ne']; ring
          have hlim : Tendsto (fun x : ℝ => -Cw3 / (2 * (1 + x) ^ 2)) atTop (𝓝 0) := by
            have h1 : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
              tendsto_const_nhds.add_atTop tendsto_id
            have h2 : Tendsto (fun x : ℝ => (1 + x) ^ 2) atTop atTop :=
              (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1
            exact tendsto_const_nhds.div_atTop (h2.const_mul_atTop (by norm_num))
          have hcont : ContinuousWithinAt (fun x : ℝ => -Cw3 / (2 * (1 + x) ^ 2)) (Set.Ici u) u := by
            have hu1 : 2 * (1 + u) ^ 2 ≠ 0 := by positivity
            exact (continuousAt_const.div (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 2)) hu1).continuousWithinAt
          have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint3 hlim
          rw [this]; ring
      _ ≤ Cw3 / (1 + u) ^ 2 := by
          apply div_le_div_of_nonneg_left hCw3 (by positivity)
          nlinarith [sq_nonneg (1 + u)]
  have hF_small : ∀ u ≥ (0 : ℝ), |F u| ≤ Csq * u ^ 3 := by
    intro u hu
    calc |F u| = |∫ r in (0 : ℝ)..u, omegafun r| := rfl
      _ ≤ ∫ r in (0 : ℝ)..u, |omegafun r| := by
          simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := omegafun) hu
      _ ≤ ∫ r in (0 : ℝ)..u, Csq * r ^ 2 := by
          apply intervalIntegral.integral_mono_on hu
            (differentiable_omegafun.continuous.abs.intervalIntegrable 0 u)
            ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 u)
            (fun r _ => hsq r)
      _ = Csq * u ^ 3 / 3 := by
          rw [intervalIntegral.integral_const_mul, integral_pow]; ring
      _ ≤ Csq * u ^ 3 := by
          have : 0 ≤ Csq * u ^ 3 := mul_nonneg hCsq (pow_nonneg hu 3)
          linarith
  have hint_wlog : IntegrableOn (fun u : ℝ => omegafun u * Real.log u) (Set.Ioi 0) := by
    have hdom : IntegrableOn (fun u : ℝ => Cw3 / (1 + u) ^ 2) (Set.Ioi 0) :=
      (integrable_div_one_add_abs_pow Cw3 2 le_rfl).integrableOn.congr_fun
        (fun u hu => by dsimp only; rw [abs_of_pos (Set.mem_Ioi.mp hu)]) measurableSet_Ioi
    have hdom0 : IntegrableOn (fun u : ℝ => Csq * u) (Set.Ioc 0 1) :=
      (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have h1 : IntegrableOn (fun u : ℝ => omegafun u * Real.log u) (Set.Ioc 0 1) := by
      refine hdom0.mono'
        ((differentiable_omegafun.continuous.continuousOn.mul
          (Real.continuousOn_log.mono fun u hu => (Set.mem_Ioc.mp hu).1.ne')).aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_mul]
      have hlog : |Real.log u| ≤ 1 / u := by
        rw [abs_of_nonpos (Real.log_nonpos hu.1.le hu.2)]
        have := Real.log_le_sub_one_of_pos (one_div_pos.mpr hu.1)
        rw [one_div, Real.log_inv, ← one_div] at this
        linarith
      calc |omegafun u| * |Real.log u| ≤ (Csq * u ^ 2) * (1 / u) :=
            mul_le_mul (hsq u) hlog (abs_nonneg _) (by positivity)
        _ = Csq * u := by field_simp [hu.1.ne']
    have h2 : IntegrableOn (fun u : ℝ => omegafun u * Real.log u) (Set.Ioi 1) := by
      refine (hdom.mono_set (Set.Ioi_subset_Ioi zero_le_one)).mono'
        ((differentiable_omegafun.continuous.continuousOn.mul
          (Real.continuousOn_log.mono fun u hu => (lt_trans zero_lt_one (Set.mem_Ioi.mp hu)).ne')).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 < u := Set.mem_Ioi.mp hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hu1.le)]
      have hlog : Real.log u ≤ 1 + u := by linarith [Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hu1)]
      calc |omegafun u| * Real.log u ≤ (Cw3 / (1 + u) ^ 3) * (1 + u) :=
            mul_le_mul (by simpa [abs_of_pos (lt_trans zero_lt_one hu1)] using hdec3 u) hlog
              (Real.log_nonneg hu1.le) (by positivity)
        _ = Cw3 / (1 + u) ^ 2 := by field_simp [(by linarith : 0 < 1 + u).ne']
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h1.union h2
  have hF_cont : Continuous F := continuous_iff_continuousAt.mpr fun u => (hF_deriv u).continuousAt
  have hint_Fu : IntegrableOn (fun u : ℝ => F u / u) (Set.Ioi 0) := by
    have hcont : ContinuousOn (fun u : ℝ => F u / u) (Set.Ioi 0) :=
      hF_cont.continuousOn.div continuousOn_id (fun u hu => (Set.mem_Ioi.mp hu).ne')
    have h1 : IntegrableOn (fun u : ℝ => F u / u) (Set.Ioc 0 1) := by
      have hdom : IntegrableOn (fun u : ℝ => Csq * u ^ 2) (Set.Ioc 0 1) :=
        (continuous_const.mul (continuous_id.pow 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      refine hdom.mono' ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hu.1]
      calc |F u| / u ≤ (Csq * u ^ 3) / u := div_le_div_of_nonneg_right (hF_small u hu.1.le) hu.1.le
        _ = Csq * u ^ 2 := by field_simp [hu.1.ne']
    have h2 : IntegrableOn (fun u : ℝ => F u / u) (Set.Ioi 1) := by
      have hdom : IntegrableOn (fun u : ℝ => Cw3 / (1 + u) ^ 2) (Set.Ioi 1) :=
        ((integrable_div_one_add_abs_pow Cw3 2 le_rfl).integrableOn.congr_fun
          (fun u hu => by rw [abs_of_pos (Set.mem_Ioi.mp hu)]) measurableSet_Ioi).mono_set
          (Set.Ioi_subset_Ioi zero_le_one)
      refine hdom.mono' ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 < u := Set.mem_Ioi.mp hu
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_trans zero_lt_one hu1)]
      calc |F u| / u ≤ |F u| := div_le_self (abs_nonneg _) hu1.le
        _ ≤ Cw3 / (1 + u) ^ 2 := hF_big u (lt_trans zero_lt_one hu1).le
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h1.union h2
  have hibp : ∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u = - ∫ u in Set.Ioi (0 : ℝ), F u / u := by
    have hzero : ∫ u in Set.Ioi (0 : ℝ), (omegafun u * Real.log u + F u * u⁻¹) = 0 := by
      have hlim0 : Tendsto (F * Real.log) (𝓝[>] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (show Tendsto (fun u : ℝ => Csq * u ^ 2) (𝓝[>] 0) (𝓝 0) by
          have hc : Continuous (fun u : ℝ => Csq * u ^ 2) := continuous_const.mul (continuous_id.pow 2)
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds)
        filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
        have hu0 : 0 < u := hu.1
        simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        have hlog : |Real.log u| ≤ 1 / u := by
          rw [abs_of_nonpos (Real.log_nonpos hu0.le hu.2.le)]
          have := Real.log_le_sub_one_of_pos (one_div_pos.mpr hu0)
          rw [one_div, Real.log_inv, ← one_div] at this; linarith
        calc |F u| * |Real.log u| ≤ (Csq * u ^ 3) * (1 / u) :=
              mul_le_mul (hF_small u hu0.le) hlog (abs_nonneg _) (by positivity)
          _ = Csq * u ^ 2 := by field_simp [hu0.ne']
      have hlim1 : Tendsto (F * Real.log) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (show Tendsto (fun u : ℝ => Cw3 / (1 + u)) atTop (𝓝 0) from
          tendsto_const_nhds.div_atTop (tendsto_const_nhds.add_atTop tendsto_id))
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with u hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu
        simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hu.le)]
        have hlog : Real.log u ≤ 1 + u := by linarith [Real.log_le_sub_one_of_pos hu0]
        calc |F u| * Real.log u ≤ (Cw3 / (1 + u) ^ 2) * (1 + u) :=
              mul_le_mul (hF_big u hu0.le) hlog (Real.log_nonneg hu.le) (by positivity)
          _ = Cw3 / (1 + u) := by field_simp [(by linarith : 0 < 1 + u).ne']
      have huv : IntegrableOn (omegafun * Real.log + F * Inv.inv) (Set.Ioi (0 : ℝ)) := by
        have : omegafun * Real.log + F * Inv.inv = fun u : ℝ => omegafun u * Real.log u + F u / u := by
          funext u; simp [div_eq_mul_inv]
        rw [this]; exact hint_wlog.add hint_Fu
      have hres := MeasureTheory.integral_Ioi_deriv_mul_eq_sub
        (fun u _ => hF_deriv u) (fun u hu => Real.hasDerivAt_log (Set.mem_Ioi.mp hu).ne')
        huv hlim0 hlim1
      simpa using hres
    have hzero' : ∫ u in Set.Ioi (0 : ℝ), (omegafun u * Real.log u + F u / u) = 0 := by
      simpa [div_eq_mul_inv] using hzero
    rw [MeasureTheory.integral_add hint_wlog hint_Fu] at hzero'
    linarith
  have hF_formula : ∀ u ≥ (0 : ℝ), F u = ∫ v : ℝ, Kfun v *
      (Real.sin (2 * Real.pi * (2 + v) * u) / (4 * Real.pi * (2 + v)) -
       Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (8 * Real.pi * (2 + v + 1 / 5)) -
       Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (8 * Real.pi * (2 + v - 1 / 5))) := by
    intro u hu
    have h1 : F u = ∫ r in Set.Ioc (0 : ℝ) u, ∫ v : ℝ, Kfun v *
        ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * r)) := by
      simp only [F, intervalIntegral.integral_of_le hu]
      congr 1; funext r; exact omegafun_eq_integral_Kfun r
    rw [h1]
    have hcont_rv : Continuous (Function.uncurry fun r v : ℝ => Kfun v *
        ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * r))) := by
      unfold Function.uncurry
      have hc : ∀ c : ℝ, Continuous (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * (c + p.2) * p.1)) := fun c =>
        Real.continuous_cos.comp ((continuous_const.mul (continuous_const.add continuous_snd)).mul continuous_fst)
      have hc1 : Continuous (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * (2 + p.2 + 1 / 5) * p.1)) :=
        Real.continuous_cos.comp ((continuous_const.mul ((continuous_const.add continuous_snd).add continuous_const)).mul continuous_fst)
      have hc2 : Continuous (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * (2 + p.2 - 1 / 5) * p.1)) :=
        Real.continuous_cos.comp ((continuous_const.mul ((continuous_const.add continuous_snd).sub continuous_const)).mul continuous_fst)
      exact (continuous_Kfun.comp continuous_snd).mul
        (((continuous_const.mul (hc 2)).sub (continuous_const.mul hc1)).sub (continuous_const.mul hc2))
    have hint_rv : Integrable (Function.uncurry fun r v : ℝ => Kfun v *
        ((1 / 2) * Real.cos (2 * Real.pi * (2 + v) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v + 1 / 5) * r) -
         (1 / 4) * Real.cos (2 * Real.pi * (2 + v - 1 / 5) * r)))
        ((volume.restrict (Set.Ioc 0 u)).prod volume) := by
      have hdom : Integrable (Function.uncurry fun _r v : ℝ => Kfun v)
          ((volume.restrict (Set.Ioc 0 u)).prod volume) := by
        have h1 : IntegrableOn (fun _r : ℝ => (1 : ℝ)) (Set.Ioc 0 u) :=
          continuous_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        have h2 : Integrable Kfun := continuous_Kfun.integrable_of_hasCompactSupport hasCompactSupport_Kfun
        exact (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => by simp [Function.uncurry])
      refine hdom.mono' hcont_rv.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Kfun_nonneg p.2)]
      have hb : |(1 / 2) * Real.cos (2 * Real.pi * (2 + p.2) * p.1) -
          (1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 + 1 / 5) * p.1) -
          (1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 - 1 / 5) * p.1)| ≤ 1 := by
        calc _ ≤ |(1 / 2) * Real.cos (2 * Real.pi * (2 + p.2) * p.1) -
              (1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 + 1 / 5) * p.1)| +
              |(1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 - 1 / 5) * p.1)| := abs_sub _ _
          _ ≤ |(1 / 2) * Real.cos (2 * Real.pi * (2 + p.2) * p.1)| +
              |(1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 + 1 / 5) * p.1)| +
              |(1 / 4) * Real.cos (2 * Real.pi * (2 + p.2 - 1 / 5) * p.1)| := by
              gcongr; exact abs_sub _ _
          _ ≤ (1 / 2) * 1 + (1 / 4) * 1 + (1 / 4) * 1 := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
                abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
              gcongr <;> exact Real.abs_cos_le_one _
          _ = 1 := by norm_num
      simpa using mul_le_mul_of_nonneg_left hb (Kfun_nonneg p.2)
    rw [MeasureTheory.integral_integral_swap hint_rv]
    congr 1; funext v
    by_cases hv : (1 / 20 : ℝ) ≤ |v|
    · simp [Kfun_eq_zero_of_abs_ge hv]
    · have hv' : |v| < 1 / 20 := not_le.mp hv
      have hv_lo : -(1 / 20 : ℝ) < v := (abs_lt.mp hv').1
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [← intervalIntegral.integral_of_le hu]
      have hcos_int : ∀ c a : ℝ, a ≠ 0 →
          ∫ r in (0 : ℝ)..u, c * Real.cos (2 * Real.pi * a * r) =
            c * Real.sin (2 * Real.pi * a * u) / (2 * Real.pi * a) := by
        intro c a ha
        have h2pa : 2 * Real.pi * a ≠ 0 := mul_ne_zero (by positivity) ha
        have hd : ∀ r ∈ Set.uIcc (0 : ℝ) u, HasDerivAt
            (fun x : ℝ => c * Real.sin (2 * Real.pi * a * x) / (2 * Real.pi * a))
            (c * Real.cos (2 * Real.pi * a * r)) r := by
          intro r _
          have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * a * x) (2 * Real.pi * a) r := by
            simpa using (hasDerivAt_id r).const_mul (2 * Real.pi * a)
          have h2 := (hlin.sin.const_mul c).div_const (2 * Real.pi * a)
          convert h2 using 1; field_simp [h2pa]
        have hcont : Continuous (fun r : ℝ => c * Real.cos (2 * Real.pi * a * r)) :=
          continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
        have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 u)
        simpa using this
      have hint_ca : ∀ c a : ℝ, IntervalIntegrable (fun r : ℝ => c * Real.cos (2 * Real.pi * a * r)) volume 0 u :=
        fun c a => (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 u
      have hs1 := intervalIntegral.integral_sub (hint_ca (1 / 2) (2 + v)) (hint_ca (1 / 4) (2 + v + 1 / 5))
      have hs2 := intervalIntegral.integral_sub ((hint_ca (1 / 2) (2 + v)).sub (hint_ca (1 / 4) (2 + v + 1 / 5)))
        (hint_ca (1 / 4) (2 + v - 1 / 5))
      rw [hs2, hs1, hcos_int (1 / 2) (2 + v) (by linarith),
        hcos_int (1 / 4) (2 + v + 1 / 5) (by linarith),
        hcos_int (1 / 4) (2 + v - 1 / 5) (by linarith)]
      field_simp [Real.pi_pos.ne', (by linarith : 2 + v ≠ 0), (by linarith : 2 + v + 1 / 5 ≠ 0),
        (by linarith : 2 + v - 1 / 5 ≠ 0)]
      ring
  have habel : ∀ ε > (0 : ℝ),
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-ε * u) * (F u / u) =
      ∫ v : ℝ, Kfun v *
        ((Real.pi / 2 - Real.arctan (ε / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
         (Real.pi / 2 - Real.arctan (ε / (2 * Real.pi * (2 + v + 1 / 5)))) / (8 * Real.pi * (2 + v + 1 / 5)) -
         (Real.pi / 2 - Real.arctan (ε / (2 * Real.pi * (2 + v - 1 / 5)))) / (8 * Real.pi * (2 + v - 1 / 5))) := by
    intro ε hε
    let G : ℝ → ℝ → ℝ := fun u v =>
      Kfun v * Real.exp (-ε * u) *
        (Real.sin (2 * Real.pi * (2 + v) * u) / (4 * Real.pi * (2 + v) * u) -
         Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (8 * Real.pi * (2 + v + 1 / 5) * u) -
         Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (8 * Real.pi * (2 + v - 1 / 5) * u))
    have hcongr : Set.EqOn (fun u : ℝ => Real.exp (-ε * u) * (F u / u))
        (fun u : ℝ => ∫ v : ℝ, G u v) (Set.Ioi 0) := by
      intro u hu
      have hu0 : 0 < u := Set.mem_Ioi.mp hu
      dsimp only
      rw [hF_formula u hu0.le, ← MeasureTheory.integral_div, ← MeasureTheory.integral_const_mul]
      congr 1; funext v; simp only [G, div_mul_eq_div_div]; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
    have hint_uv : Integrable (Function.uncurry G) ((volume.restrict (Set.Ioi 0)).prod volume) := by
      have hG_bound : ∀ u > (0 : ℝ), ∀ v : ℝ, ‖G u v‖ ≤ 2 * Kfun v * Real.exp (-ε * u) := by
        intro u hu v
        by_cases hv : (1 / 20 : ℝ) ≤ |v|
        · simp [G, Kfun_eq_zero_of_abs_ge hv]
        · have hv' : -(1 / 20 : ℝ) < v := (abs_lt.mp (not_le.mp hv)).1
          have hsin_div : ∀ a > (0 : ℝ), |Real.sin (2 * Real.pi * a * u) / (2 * Real.pi * a * u)| ≤ 1 := by
            intro a ha
            have hp : 0 < 2 * Real.pi * a * u := by positivity
            rw [abs_div, abs_of_pos hp, div_le_one hp]
            simpa [abs_of_pos hp] using Real.abs_sin_le_abs (x := 2 * Real.pi * a * u)
          have h1 := hsin_div (2 + v) (by linarith)
          have h2 := hsin_div (2 + v + 1 / 5) (by linarith)
          have h3 := hsin_div (2 + v - 1 / 5) (by linarith)
          simp only [G, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Kfun_nonneg v), abs_of_pos (Real.exp_pos _)]
          have hbr : |Real.sin (2 * Real.pi * (2 + v) * u) / (4 * Real.pi * (2 + v) * u) -
              Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (8 * Real.pi * (2 + v + 1 / 5) * u) -
              Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (8 * Real.pi * (2 + v - 1 / 5) * u)| ≤ 2 := by
            have e1 : Real.sin (2 * Real.pi * (2 + v) * u) / (4 * Real.pi * (2 + v) * u) =
                (1 / 2) * (Real.sin (2 * Real.pi * (2 + v) * u) / (2 * Real.pi * (2 + v) * u)) := by field_simp; ring
            have e2 : Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (8 * Real.pi * (2 + v + 1 / 5) * u) =
                (1 / 4) * (Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (2 * Real.pi * (2 + v + 1 / 5) * u)) := by field_simp; ring
            have e3 : Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (8 * Real.pi * (2 + v - 1 / 5) * u) =
                (1 / 4) * (Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (2 * Real.pi * (2 + v - 1 / 5) * u)) := by field_simp; ring
            rw [e1, e2, e3]
            calc _ ≤ |(1 / 2) * (Real.sin (2 * Real.pi * (2 + v) * u) / (2 * Real.pi * (2 + v) * u)) -
                  (1 / 4) * (Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (2 * Real.pi * (2 + v + 1 / 5) * u))| +
                  |(1 / 4) * (Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (2 * Real.pi * (2 + v - 1 / 5) * u))| := abs_sub _ _
              _ ≤ |(1 / 2) * (Real.sin (2 * Real.pi * (2 + v) * u) / (2 * Real.pi * (2 + v) * u))| +
                  |(1 / 4) * (Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / (2 * Real.pi * (2 + v + 1 / 5) * u))| +
                  |(1 / 4) * (Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / (2 * Real.pi * (2 + v - 1 / 5) * u))| := by
                  gcongr; exact abs_sub _ _
              _ ≤ (1 / 2) * 1 + (1 / 4) * 1 + (1 / 4) * 1 := by
                  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
                    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
                  gcongr
              _ ≤ 2 := by norm_num
          have hK0 : 0 ≤ Kfun v := Kfun_nonneg v
          calc Kfun v * Real.exp (-ε * u) * _ ≤ Kfun v * Real.exp (-ε * u) * 2 := by gcongr
            _ = 2 * Kfun v * Real.exp (-ε * u) := by ring
      have hdom_prod : Integrable (Function.uncurry fun u v : ℝ => 2 * Kfun v * Real.exp (-ε * u))
          ((volume.restrict (Set.Ioi 0)).prod volume) := by
        have h1 : IntegrableOn (fun u : ℝ => Real.exp (-ε * u)) (Set.Ioi 0) :=
          integrableOn_exp_mul_Ioi (by linarith) 0
        have h2 : Integrable (fun v : ℝ => 2 * Kfun v) :=
          (continuous_Kfun.integrable_of_hasCompactSupport hasCompactSupport_Kfun).const_mul 2
        have hp := h1.mul_prod h2
        refine hp.congr (Filter.Eventually.of_forall fun p => ?_)
        simp only [Function.uncurry]; ring
      have hmeas : Measurable (Function.uncurry G) := by
        unfold Function.uncurry G
        have m1 : Measurable (fun p : ℝ × ℝ => Kfun p.2) := continuous_Kfun.measurable.comp measurable_snd
        have m2 : Measurable (fun p : ℝ × ℝ => Real.exp (-ε * p.1)) :=
          Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)
        have m_sd : ∀ c d : ℝ, Measurable (fun p : ℝ × ℝ =>
            Real.sin (2 * Real.pi * (2 + p.2 + c) * p.1) / (d * Real.pi * (2 + p.2 + c) * p.1)) := fun c d =>
          (Real.continuous_sin.measurable.comp
            ((measurable_const.mul ((measurable_const.add measurable_snd).add measurable_const)).mul measurable_fst)).div
            ((measurable_const.mul ((measurable_const.add measurable_snd).add measurable_const)).mul measurable_fst)
        have m_s0 : Measurable (fun p : ℝ × ℝ =>
            Real.sin (2 * Real.pi * (2 + p.2) * p.1) / (4 * Real.pi * (2 + p.2) * p.1)) :=
          (Real.continuous_sin.measurable.comp
            ((measurable_const.mul (measurable_const.add measurable_snd)).mul measurable_fst)).div
            ((measurable_const.mul (measurable_const.add measurable_snd)).mul measurable_fst)
        have m_sm : Measurable (fun p : ℝ × ℝ =>
            Real.sin (2 * Real.pi * (2 + p.2 - 1 / 5) * p.1) / (8 * Real.pi * (2 + p.2 - 1 / 5) * p.1)) :=
          (Real.continuous_sin.measurable.comp
            ((measurable_const.mul ((measurable_const.add measurable_snd).sub measurable_const)).mul measurable_fst)).div
            ((measurable_const.mul ((measurable_const.add measurable_snd).sub measurable_const)).mul measurable_fst)
        exact (m1.mul m2).mul ((m_s0.sub (m_sd (1 / 5) 8)).sub m_sm)
      refine hdom_prod.mono' hmeas.aestronglyMeasurable ?_
      have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi 0)).prod volume), p.1 ∈ Set.Ioi (0 : ℝ) := by
        have := MeasureTheory.ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
        exact (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)).mpr (by
          filter_upwards [this] with u hu
          exact Filter.Eventually.of_forall fun _ => hu)
      filter_upwards [hae] with p hp
      exact hG_bound p.1 (Set.mem_Ioi.mp hp) p.2
    rw [MeasureTheory.integral_integral_swap hint_uv]
    congr 1; funext v
    by_cases hv : (1 / 20 : ℝ) ≤ |v|
    · simp [G, Kfun_eq_zero_of_abs_ge hv]
    · have hv' : -(1 / 20 : ℝ) < v := (abs_lt.mp (not_le.mp hv)).1
      have hterm : ∀ c a : ℝ, 0 < a →
          IntegrableOn (fun u : ℝ => c * (Real.exp (-ε * u) * (Real.sin (2 * Real.pi * a * u) / u))) (Set.Ioi 0) := by
        intro c a ha
        have hdom : IntegrableOn (fun u : ℝ => |c| * (2 * Real.pi * a) * Real.exp (-ε * u)) (Set.Ioi 0) :=
          (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
        have hm : Measurable (fun u : ℝ => c * (Real.exp (-ε * u) * (Real.sin (2 * Real.pi * a * u) / u))) :=
          measurable_const.mul ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
            ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).div measurable_id))
        refine hdom.mono' hm.aestronglyMeasurable ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := Set.mem_Ioi.mp hu
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos hu0]
        have hs : |Real.sin (2 * Real.pi * a * u)| ≤ 2 * Real.pi * a * u := by
          simpa [abs_of_pos (by positivity : 0 < 2 * Real.pi * a * u)] using
            Real.abs_sin_le_abs (x := 2 * Real.pi * a * u)
        calc |c| * (Real.exp (-ε * u) * (|Real.sin (2 * Real.pi * a * u)| / u))
            ≤ |c| * (Real.exp (-ε * u) * ((2 * Real.pi * a * u) / u)) := by gcongr
          _ = |c| * (2 * Real.pi * a) * Real.exp (-ε * u) := by field_simp [hu0.ne']
      have heqG : ∀ u : ℝ, G u v = Kfun v * (
          (1 / (4 * Real.pi * (2 + v))) * (Real.exp (-ε * u) * (Real.sin (2 * Real.pi * (2 + v) * u) / u)) -
          (1 / (8 * Real.pi * (2 + v + 1 / 5))) * (Real.exp (-ε * u) * (Real.sin (2 * Real.pi * (2 + v + 1 / 5) * u) / u)) -
          (1 / (8 * Real.pi * (2 + v - 1 / 5))) * (Real.exp (-ε * u) * (Real.sin (2 * Real.pi * (2 + v - 1 / 5) * u) / u))) := by
        intro u; simp only [G, div_mul_eq_div_div]; ring
      simp_rw [heqG]
      rw [MeasureTheory.integral_const_mul]
      congr 1
      have ht1 := hterm (1 / (4 * Real.pi * (2 + v))) (2 + v) (by linarith)
      have ht2 := hterm (1 / (8 * Real.pi * (2 + v + 1 / 5))) (2 + v + 1 / 5) (by linarith)
      have ht3 := hterm (1 / (8 * Real.pi * (2 + v - 1 / 5))) (2 + v - 1 / 5) (by linarith)
      have hs1 := MeasureTheory.integral_sub ht1 ht2
      have hs2 := MeasureTheory.integral_sub (ht1.sub ht2) ht3
      simp only [Pi.sub_apply] at hs1 hs2
      rw [hs2, hs1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul,
        integral_Ioi_exp_mul_sin_div hε (mul_pos (by positivity) (by linarith : (0 : ℝ) < 2 + v)),
        integral_Ioi_exp_mul_sin_div hε (mul_pos (by positivity) (by linarith : (0 : ℝ) < 2 + v + 1 / 5)),
        integral_Ioi_exp_mul_sin_div hε (mul_pos (by positivity) (by linarith : (0 : ℝ) < 2 + v - 1 / 5))]
      ring
  have hLHS_lim : Tendsto (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(1 / ((n : ℝ) + 1)) * u) * (F u / u))
      atTop (𝓝 (∫ u in Set.Ioi (0 : ℝ), F u / u)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun u : ℝ => |F u / u|) ?_ ?_ ?_ ?_
    · intro n
      have hm1 : Measurable (fun u : ℝ => Real.exp (-(1 / ((n : ℝ) + 1)) * u)) :=
        Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
      exact hm1.aestronglyMeasurable.mul hint_Fu.aestronglyMeasurable
    · exact hint_Fu.norm
    · intro n
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(1 / ((n : ℝ) + 1)) * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hu0 : 0 < u := Set.mem_Ioi.mp hu
        nlinarith [div_pos one_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      simpa using mul_le_mul_of_nonneg_right hle (abs_nonneg (F u / u))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u _
      have h0 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)) * u) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using h1.neg.mul_const u
      simpa using (Real.continuous_exp.tendsto 0 |>.comp h0).mul_const (F u / u)
  have hRHS_lim : Tendsto (fun n : ℕ =>
      ∫ v : ℝ, Kfun v *
        ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
         (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (8 * Real.pi * (2 + v + 1 / 5)) -
         (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (8 * Real.pi * (2 + v - 1 / 5))))
      atTop (𝓝 (∫ v : ℝ, Kfun v * (1 / (8 * (2 + v)) - 1 / (16 * (2 + v + 1 / 5)) - 1 / (16 * (2 + v - 1 / 5))))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun v : ℝ => Kfun v) ?_ ?_ ?_ ?_
    · intro n
      have hmt : ∀ (d : ℝ) (f : ℝ → ℝ), Measurable f →
          Measurable (fun v : ℝ => (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * f v))) / (d * Real.pi * f v)) :=
        fun d f hf =>
          (measurable_const.sub (Real.continuous_arctan.measurable.comp
            (measurable_const.div (measurable_const.mul hf)))).div (measurable_const.mul hf)
      have hm : Measurable (fun v : ℝ => Kfun v *
          ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
           (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (8 * Real.pi * (2 + v + 1 / 5)) -
           (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (8 * Real.pi * (2 + v - 1 / 5)))) :=
        continuous_Kfun.measurable.mul
          (((hmt 4 (fun v => 2 + v) (measurable_const.add measurable_id)).sub
            (hmt 8 (fun v => 2 + v + 1 / 5) ((measurable_const.add measurable_id).add measurable_const))).sub
            (hmt 8 (fun v => 2 + v - 1 / 5) ((measurable_const.add measurable_id).sub measurable_const)))
      exact hm.aestronglyMeasurable
    · exact continuous_Kfun.integrable_of_hasCompactSupport hasCompactSupport_Kfun
    · intro n
      filter_upwards with v
      by_cases hv : (1 / 20 : ℝ) ≤ |v|
      · simp [Kfun_eq_zero_of_abs_ge hv]
      · have hv' : -(1 / 20 : ℝ) < v := (abs_lt.mp (not_le.mp hv)).1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Kfun_nonneg v)]
        have hterm_le : ∀ a : ℝ, 1 ≤ a →
            |(Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * a))) / (4 * Real.pi * a)| ≤ 1 / 4 := by
          intro a ha
          have hatan0 : 0 ≤ Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * a)) :=
            Real.arctan_nonneg.mpr (by positivity)
          have hatan_lt : Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * a)) < Real.pi / 2 :=
            Real.arctan_lt_pi_div_two _
          rw [abs_div, abs_of_pos (by linarith), abs_of_pos (by positivity : 0 < 4 * Real.pi * a),
            div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_pos]
        have h1 := hterm_le (2 + v) (by linarith)
        have h2 := hterm_le (2 + v + 1 / 5) (by linarith)
        have h3 := hterm_le (2 + v - 1 / 5) (by linarith)
        have hbr : |(Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
            (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (8 * Real.pi * (2 + v + 1 / 5)) -
            (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (8 * Real.pi * (2 + v - 1 / 5))| ≤ 1 := by
          have e2 : ∀ x y : ℝ, x / (8 * Real.pi * y) = (1 / 2) * (x / (4 * Real.pi * y)) := fun _ _ => by ring
          rw [e2, e2]
          calc _ ≤ |(Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
                (1 / 2) * ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (4 * Real.pi * (2 + v + 1 / 5)))| +
                |(1 / 2) * ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (4 * Real.pi * (2 + v - 1 / 5)))| := abs_sub _ _
            _ ≤ |(Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v))| +
                |(1 / 2) * ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (4 * Real.pi * (2 + v + 1 / 5)))| +
                |(1 / 2) * ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (4 * Real.pi * (2 + v - 1 / 5)))| := by
                gcongr; exact abs_sub _ _
            _ ≤ 1 / 4 + (1 / 2) * (1 / 4) + (1 / 2) * (1 / 4) := by
                rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; gcongr
            _ ≤ 1 := by norm_num
        simpa using mul_le_mul_of_nonneg_left hbr (Kfun_nonneg v)
    · filter_upwards with v
      by_cases hv : (1 / 20 : ℝ) ≤ |v|
      · simp [Kfun_eq_zero_of_abs_ge hv]
      · have hv' : -(1 / 20 : ℝ) < v := (abs_lt.mp (not_le.mp hv)).1
        have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have ht : ∀ a : ℝ, 0 < a → Tendsto (fun n : ℕ => Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * a)))
            atTop (𝓝 (Real.pi / 2)) := fun a _ => by
          have hdiv : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / (2 * Real.pi * a)) atTop (𝓝 0) := by
            simpa only [zero_div] using h1n.div_const (2 * Real.pi * a)
          have := (Real.continuous_arctan.tendsto 0).comp hdiv
          simpa using tendsto_const_nhds.sub this
        have hlim1 := (ht (2 + v) (by linarith)).div_const (4 * Real.pi * (2 + v))
        have hlim2 := (ht (2 + v + 1 / 5) (by linarith)).div_const (8 * Real.pi * (2 + v + 1 / 5))
        have hlim3 := (ht (2 + v - 1 / 5) (by linarith)).div_const (8 * Real.pi * (2 + v - 1 / 5))
        have hcomb := ((hlim1.sub hlim2).sub hlim3).const_mul (Kfun v)
        have hsimp1 : Real.pi / 2 / (4 * Real.pi * (2 + v)) = 1 / (8 * (2 + v)) := by
          field_simp [Real.pi_pos.ne', (by linarith : 2 + v ≠ 0)]; ring
        have hsimp2 : Real.pi / 2 / (8 * Real.pi * (2 + v + 1 / 5)) = 1 / (16 * (2 + v + 1 / 5)) := by
          field_simp [Real.pi_pos.ne', (by linarith : 2 + v + 1 / 5 ≠ 0)]; ring
        have hsimp3 : Real.pi / 2 / (8 * Real.pi * (2 + v - 1 / 5)) = 1 / (16 * (2 + v - 1 / 5)) := by
          field_simp [Real.pi_pos.ne', (by linarith : 2 + v - 1 / 5 ≠ 0)]; ring
        rw [hsimp1, hsimp2, hsimp3] at hcomb
        exact hcomb
  have hFu_eq : ∫ u in Set.Ioi (0 : ℝ), F u / u =
      ∫ v : ℝ, Kfun v * (1 / (8 * (2 + v)) - 1 / (16 * (2 + v + 1 / 5)) - 1 / (16 * (2 + v - 1 / 5))) := by
    have heq_seq : (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(1 / ((n : ℝ) + 1)) * u) * (F u / u)) =
        (fun n : ℕ => ∫ v : ℝ, Kfun v *
          ((Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v)))) / (4 * Real.pi * (2 + v)) -
           (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v + 1 / 5)))) / (8 * Real.pi * (2 + v + 1 / 5)) -
           (Real.pi / 2 - Real.arctan ((1 / ((n : ℝ) + 1)) / (2 * Real.pi * (2 + v - 1 / 5)))) / (8 * Real.pi * (2 + v - 1 / 5)))) :=
      funext fun n => habel (1 / ((n : ℝ) + 1)) (by positivity)
    rw [heq_seq] at hLHS_lim
    exact tendsto_nhds_unique hLHS_lim hRHS_lim
  rw [hibp, hFu_eq, ← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  by_cases hv : (1 / 20 : ℝ) ≤ |v|
  · simp [Kfun_eq_zero_of_abs_ge hv]
  · have hv' : -(1 / 20 : ℝ) < v := (abs_lt.mp (not_le.mp hv)).1
    field_simp [(by linarith : 2 + v ≠ 0), (by linarith : 2 + v + 1 / 5 ≠ 0), (by linarith : 2 + v - 1 / 5 ≠ 0)]
    ring

lemma continuous_Mfun : Continuous Mfun := by
  have heq : Mfun = fun v : ℝ => Wtilde (Complex.I * (v : ℂ)) := funext Mfun_eq_Wtilde
  rw [heq]
  exact differentiable_Wtilde.continuous.comp (continuous_const.mul Complex.continuous_ofReal)

lemma continuous_kfun : Continuous kfun :=
  (show Differentiable ℝ kfun from fun t => (hasDerivAt_kfun t).differentiableAt).continuous

lemma continuous_deriv_kfun : Continuous (deriv kfun) := by
  have heq : deriv kfun = fun t : ℝ => ∫ v : ℝ, (-2 * Real.pi * v * bfun v) * Real.sin (2 * Real.pi * v * t) :=
    funext fun t => (hasDerivAt_kfun t).deriv
  rw [heq]
  refine MeasureTheory.continuous_of_dominated (bound := fun v : ℝ => |2 * Real.pi * v * bfun v|) ?_ ?_ ?_ ?_
  · intro t
    exact ((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).mul
      (Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const))).aestronglyMeasurable
  · intro t
    refine Filter.Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |-2 * Real.pi * v * bfun v| * |Real.sin (2 * Real.pi * v * t)|
        ≤ |-2 * Real.pi * v * bfun v| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |2 * Real.pi * v * bfun v| := by
          rw [mul_one, show -2 * Real.pi * v * bfun v = -(2 * Real.pi * v * bfun v) by ring, abs_neg]
  · exact ((continuous_const.mul continuous_id |>.mul contDiff_bfun.continuous).abs).integrable_of_hasCompactSupport
      hasCompactSupport_bfun.mul_left.abs
  · refine Filter.Eventually.of_forall fun v => ?_
    exact continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma continuous_deriv_omegafun : Continuous (deriv omegafun) := by
  have heq : deriv omegafun = fun t : ℝ =>
      2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t) * Real.cos (4 * Real.pi * t) +
      (lfun t) ^ 2 * (-Real.sin (4 * Real.pi * t) * (4 * Real.pi)) := by
    funext t
    have hdk : HasDerivAt kfun (deriv kfun t) t := (hasDerivAt_kfun t).differentiableAt.hasDerivAt
    have hsin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x / 5))
        (Real.cos (Real.pi * t / 5) * (Real.pi / 5)) t := by
      have hlin : HasDerivAt (fun x : ℝ => Real.pi * x / 5) (Real.pi / 5) t := by
        simpa using (hasDerivAt_id t).const_mul Real.pi |>.div_const 5
      exact hlin.sin
    have hcos : HasDerivAt (fun x : ℝ => Real.cos (4 * Real.pi * x))
        (-Real.sin (4 * Real.pi * t) * (4 * Real.pi)) t := by
      have hlin : HasDerivAt (fun x : ℝ => 4 * Real.pi * x) (4 * Real.pi) t := by
        simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
      exact hlin.cos
    have hl : HasDerivAt lfun (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
        Real.sin (Real.pi * t / 5) * deriv kfun t) t := hsin.mul hdk
    have hl2 : HasDerivAt (fun x : ℝ => (lfun x) ^ 2)
        (2 * lfun t * (Real.cos (Real.pi * t / 5) * (Real.pi / 5) * kfun t +
          Real.sin (Real.pi * t / 5) * deriv kfun t)) t := by
      simpa [pow_one] using hl.fun_pow 2
    exact (hl2.mul hcos).deriv
  rw [heq]
  have hcl : Continuous lfun :=
    (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 5)).mul continuous_kfun
  have hcsin : Continuous (fun t : ℝ => Real.sin (Real.pi * t / 5)) :=
    Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 5)
  have hccos : Continuous (fun t : ℝ => Real.cos (Real.pi * t / 5)) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 5)
  have hc4cos : Continuous (fun t : ℝ => Real.cos (4 * Real.pi * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hc4sin : Continuous (fun t : ℝ => Real.sin (4 * Real.pi * t)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  exact (((continuous_const.mul hcl).mul
    (((hccos.mul continuous_const).mul continuous_kfun).add (hcsin.mul continuous_deriv_kfun))).mul hc4cos).add
    ((hcl.pow 2).mul (hc4sin.neg.mul continuous_const))

end SpectralMod1

end Mod1Section

section Mod2Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators

namespace SpectralMod2

/-! ### Module 2: Complex Digamma Series, Asymptotic `ψ(z) = log z + O(1/|z|)`, and `ζ'/ζ(-1/2 + iτ)` -/

noncomputable def digammaSeries (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) - ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)

lemma digammaSeries_term_eq (z : ℂ) (k : ℕ) (hzk : z + (k : ℂ) ≠ 0) :
    (z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹ = (1 - z) / ((z + (k : ℂ)) * ((k : ℂ) + 1)) := by
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  field_simp [hzk, hk1]
  ring

lemma norm_add_nat_ge_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (k : ℕ) :
    ((k : ℝ) + ‖z‖) / 2 ≤ ‖z + (k : ℂ)‖ := by
  have h1 : (‖z‖ ^ 2 + (k : ℝ) ^ 2) ≤ ‖z + (k : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, add_zero]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hz hk0]
  have h2 : (((k : ℝ) + ‖z‖) / 2) ^ 2 ≤ ‖z‖ ^ 2 + (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - ‖z‖)]
  have hnn : 0 ≤ ((k : ℝ) + ‖z‖) / 2 := by positivity
  nlinarith [sq_nonneg (‖z + (k : ℂ)‖ - ((k : ℝ) + ‖z‖) / 2), norm_nonneg (z + (k : ℂ))]

lemma norm_add_nat_ge_of_re_pos (z : ℂ) (k : ℕ) :
    z.re + (k : ℝ) ≤ ‖z + (k : ℂ)‖ := by
  have := Complex.re_le_norm (z + (k : ℂ))
  simpa using this

lemma summable_one_div_add_one_sq : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective Nat.succ_injective
  refine h.congr fun k => ?_
  simp [one_div, Nat.cast_succ]

lemma summable_digammaSeries_term {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℕ => (z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) := by
  have hdom : Summable (fun k : ℕ => (‖1 - z‖ / min z.re 1) * (1 / ((k : ℝ) + 1) ^ 2)) :=
    summable_one_div_add_one_sq.mul_left _
  refine Summable.of_norm_bounded hdom fun k => ?_
  have hzk : z + (k : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [digammaSeries_term_eq z k hzk, norm_div, norm_mul]
  have hlb1 : min z.re 1 * ((k : ℝ) + 1) ≤ ‖z + (k : ℂ)‖ := by
    have hre := norm_add_nat_ge_of_re_pos z k
    have hm1 : min z.re 1 ≤ z.re := min_le_left _ _
    have hm2 : min z.re 1 ≤ 1 := min_le_right _ _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hlb2 : ((k : ℝ) + 1) = ‖(k : ℂ) + 1‖ := by
    have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [← hlb2]
  have hmpos : 0 < min z.re 1 := lt_min hz one_pos
  have hden : 0 < min z.re 1 * ((k : ℝ) + 1) * ((k : ℝ) + 1) := by positivity
  calc ‖1 - z‖ / (‖z + (k : ℂ)‖ * ((k : ℝ) + 1))
      ≤ ‖1 - z‖ / (min z.re 1 * ((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) hden
        exact mul_le_mul_of_nonneg_right hlb1 (by positivity)
    _ = ‖1 - z‖ / min z.re 1 * (1 / ((k : ℝ) + 1) ^ 2) := by
        field_simp [hmpos.ne']

lemma hasSum_digammaSeries_of_real_pos {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = digammaSeries (x : ℂ) := by
  have hreal_diff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (Real.log ∘ Real.Gamma) y := by
    intro y hy
    exact (Real.differentiableAt_Gamma (fun m => by linarith [Nat.cast_nonneg (α := ℝ) m])).log
      (Real.Gamma_pos_of_pos hy).ne'
  have hrec : ∀ y : ℝ, 0 < y → (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hdg_eq : ∀ y : ℝ, 0 < y →
      Complex.digamma (y : ℂ) = ((deriv (Real.log ∘ Real.Gamma) y : ℝ) : ℂ) := by
    intro y hy
    rw [Complex.digamma_def, logDeriv_apply]
    have hCG : HasDerivAt Complex.Gamma ((deriv Real.Gamma y : ℝ) : ℂ) (y : ℂ) := by
      have hdR : HasDerivAt Real.Gamma (deriv Real.Gamma y) y :=
        (Real.differentiableAt_Gamma (fun m => by linarith [Nat.cast_nonneg (α := ℝ) m])).hasDerivAt
      have hdC : DifferentiableAt ℂ Complex.Gamma (y : ℂ) :=
        Complex.differentiableAt_Gamma _ (fun m => by
          intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m])
      have hcomp : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) (deriv Complex.Gamma (y : ℂ)) y :=
        hdC.hasDerivAt.comp_ofReal
      have hfun : (fun t : ℝ => Complex.Gamma (t : ℂ)) = (fun t : ℝ => (Real.Gamma t : ℂ)) :=
        funext Complex.Gamma_ofReal
      rw [hfun] at hcomp
      have hcomp2 : HasDerivAt (fun t : ℝ => (Real.Gamma t : ℂ)) ((deriv Real.Gamma y : ℝ) : ℂ) y :=
        hdR.ofReal_comp
      have heq := hcomp.unique hcomp2
      rw [← heq]
      exact hdC.hasDerivAt
    rw [hCG.deriv, Complex.Gamma_ofReal]
    have hlogd : deriv (Real.log ∘ Real.Gamma) y = deriv Real.Gamma y / Real.Gamma y :=
      deriv.log (Real.differentiableAt_Gamma (fun m => by linarith [Nat.cast_nonneg (α := ℝ) m]))
        (Real.Gamma_pos_of_pos hy).ne'
    rw [hlogd, Complex.ofReal_div]
  have hpart : ∀ N : ℕ,
      (Complex.digamma ((x : ℂ) + (N : ℂ)) - (Real.log ((N : ℝ) + 1) : ℂ)) -
      ((harmonic N : ℂ) - (Real.log ((N : ℝ) + 1) : ℂ) - (Real.eulerMascheroniConstant : ℂ)) =
      Complex.digamma (x : ℂ) + (Real.eulerMascheroniConstant : ℂ) +
        ∑ k ∈ Finset.range N, (((x : ℂ) + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) := by
    intro N
    have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Complex.digamma_apply_add_nat hne N, Finset.sum_sub_distrib]
    have hharm : (harmonic N : ℂ) = ∑ k ∈ Finset.range N, ((k : ℂ) + 1)⁻¹ := by
      simp [harmonic]
    rw [hharm]; ring
  have ht1 : Tendsto (fun N : ℕ => Complex.digamma ((x : ℂ) + (N : ℂ)) - (Real.log ((N : ℝ) + 1) : ℂ))
      atTop (𝓝 0) := by
    have hR : Tendsto (fun N : ℕ => deriv (Real.log ∘ Real.Gamma) (x + (N : ℝ)) - Real.log ((N : ℝ) + 1))
        atTop (𝓝 0) := by
      have hconv := Real.convexOn_log_Gamma
      have hlo : ∀ᶠ N : ℕ in atTop, Real.log (x + (N : ℝ) - 1) - Real.log ((N : ℝ) + 1) ≤
          deriv (Real.log ∘ Real.Gamma) (x + (N : ℝ)) - Real.log ((N : ℝ) + 1) := by
        filter_upwards [Filter.eventually_ge_atTop 2] with N hN
        have hxN : 0 < x + (N : ℝ) := by positivity
        have hxN1 : 0 < x + (N : ℝ) - 1 := by
          have : (2 : ℝ) ≤ N := by exact_mod_cast hN
          linarith
        have hslope := hconv.slope_le_deriv (Set.mem_Ioi.mpr hxN1) (Set.mem_Ioi.mpr hxN)
          (by linarith) (hreal_diff _ hxN)
        have heq : slope (Real.log ∘ Real.Gamma) (x + (N : ℝ) - 1) (x + (N : ℝ)) = Real.log (x + (N : ℝ) - 1) := by
          rw [slope_def_field, show x + (N : ℝ) - (x + (N : ℝ) - 1) = 1 by ring, div_one]
          have := hrec (x + (N : ℝ) - 1) hxN1
          rw [show x + (N : ℝ) - 1 + 1 = x + (N : ℝ) by ring] at this
          linarith
        linarith
      have hhi : ∀ᶠ N : ℕ in atTop, deriv (Real.log ∘ Real.Gamma) (x + (N : ℝ)) - Real.log ((N : ℝ) + 1) ≤
          Real.log (x + (N : ℝ)) - Real.log ((N : ℝ) + 1) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with N _
        have hxN : 0 < x + (N : ℝ) := by positivity
        have hxN1 : 0 < x + (N : ℝ) + 1 := by positivity
        have hslope := hconv.deriv_le_slope (Set.mem_Ioi.mpr hxN) (Set.mem_Ioi.mpr hxN1)
          (by linarith) (hreal_diff _ hxN)
        have heq : slope (Real.log ∘ Real.Gamma) (x + (N : ℝ)) (x + (N : ℝ) + 1) = Real.log (x + (N : ℝ)) := by
          rw [slope_def_field, show x + (N : ℝ) + 1 - (x + (N : ℝ)) = 1 by ring, div_one, hrec _ hxN]
          ring
        linarith
      have hlim_lo : Tendsto (fun N : ℕ => Real.log (x + (N : ℝ) - 1) - Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
        have hrat : Tendsto (fun N : ℕ => (x + (N : ℝ) - 1) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
          have : ∀ N : ℕ, (x + (N : ℝ) - 1) / ((N : ℝ) + 1) = 1 + (x - 2) / ((N : ℝ) + 1) := by
            intro N; field_simp; ring
          simp_rw [this]
          have h0 : Tendsto (fun N : ℕ => (x - 2) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using tendsto_const_nhds.add h0
        have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hrat
        simp only [Real.log_one] at hlog
        refine hlog.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 2] with N hN
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        simp only [Function.comp_apply]
        rw [Real.log_div (by linarith) (by positivity)]
      have hlim_hi : Tendsto (fun N : ℕ => Real.log (x + (N : ℝ)) - Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
        have hrat : Tendsto (fun N : ℕ => (x + (N : ℝ)) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
          have : ∀ N : ℕ, (x + (N : ℝ)) / ((N : ℝ) + 1) = 1 + (x - 1) / ((N : ℝ) + 1) := by
            intro N; field_simp; ring
          simp_rw [this]
          have h0 : Tendsto (fun N : ℕ => (x - 1) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using tendsto_const_nhds.add h0
        have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hrat
        simp only [Real.log_one] at hlog
        refine hlog.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N _
        simp only [Function.comp_apply]
        rw [Real.log_div (by positivity) (by positivity)]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_lo hlim_hi hlo hhi
    have hC := (Complex.continuous_ofReal.tendsto 0).comp hR
    simp only [Complex.ofReal_zero] at hC
    refine hC.congr fun N => ?_
    simp only [Function.comp_apply, Complex.ofReal_sub]
    have hxN : 0 < x + (N : ℝ) := by positivity
    rw [← hdg_eq (x + (N : ℝ)) hxN]
    push_cast; rfl
  have ht2 : Tendsto (fun N : ℕ => ((harmonic N : ℂ) - (Real.log ((N : ℝ) + 1) : ℂ) -
      (Real.eulerMascheroniConstant : ℂ))) atTop (𝓝 0) := by
    have hR : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log ((N : ℝ) + 1) - Real.eulerMascheroniConstant)
        atTop (𝓝 0) := by
      simpa using Real.tendsto_harmonic_sub_log_add_one.sub_const Real.eulerMascheroniConstant
    have hC := (Complex.continuous_ofReal.tendsto 0).comp hR
    simp only [Complex.ofReal_zero] at hC
    refine hC.congr fun N => ?_
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_ratCast]
  have hLHS : Tendsto (fun N : ℕ =>
      (Complex.digamma ((x : ℂ) + (N : ℂ)) - (Real.log ((N : ℝ) + 1) : ℂ)) -
      ((harmonic N : ℂ) - (Real.log ((N : ℝ) + 1) : ℂ) - (Real.eulerMascheroniConstant : ℂ)))
      atTop (𝓝 0) := by
    simpa using ht1.sub ht2
  have hRHS : Tendsto (fun N : ℕ =>
      Complex.digamma (x : ℂ) + (Real.eulerMascheroniConstant : ℂ) +
        ∑ k ∈ Finset.range N, (((x : ℂ) + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹))
      atTop (𝓝 (Complex.digamma (x : ℂ) + (Real.eulerMascheroniConstant : ℂ) +
        ∑' k : ℕ, (((x : ℂ) + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹))) :=
    tendsto_const_nhds.add (summable_digammaSeries_term (by simpa using hx)).hasSum.tendsto_sum_nat
  simp_rw [hpart] at hLHS
  have heq := tendsto_nhds_unique hLHS hRHS
  unfold digammaSeries
  linear_combination -heq

lemma differentiableOn_digammaSeries : DifferentiableOn ℂ digammaSeries {z : ℂ | 0 < z.re} := by
  intro z0 hz0
  have hz0_pos : 0 < z0.re := hz0
  set δ := z0.re / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hsub : ∀ z ∈ Metric.ball z0 δ, δ < z.re := by
    intro z hz
    have hre : |z.re - z0.re| ≤ ‖z - z0‖ := by simpa using Complex.abs_re_le_norm (z - z0)
    have hlt : ‖z - z0‖ < δ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    linarith [(abs_le.mp hre).1]
  set M := ‖1 - z0‖ + δ
  have hM0 : 0 ≤ M := by positivity
  set c := min δ 1
  have hcpos : 0 < c := lt_min hδpos one_pos
  have hsum_bound : Summable (fun k : ℕ => (M / c) * (1 / ((k : ℝ) + 1) ^ 2)) :=
    summable_one_div_add_one_sq.mul_left _
  have hdiff_tsum : DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)) (Metric.ball z0 δ) := by
    refine differentiableOn_tsum_of_summable_norm hsum_bound (fun k => ?_) Metric.isOpen_ball (fun k z hz => ?_)
    · intro z hz
      have hzre : δ < z.re := hsub z hz
      have hzk : z + (k : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
        linarith [Nat.cast_nonneg (α := ℝ) k]
      have hd : DifferentiableAt ℂ (fun w : ℂ => (w + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) z :=
        (((differentiableAt_id (x := z)).add (differentiableAt_const (k : ℂ))).inv hzk).sub (differentiableAt_const _)
      exact hd.differentiableWithinAt
    · have hzre : δ < z.re := hsub z hz
      have hzk : z + (k : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
        linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [digammaSeries_term_eq z k hzk, norm_div, norm_mul]
      have h1z : ‖1 - z‖ ≤ M := by
        have hlt : ‖z - z0‖ < δ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
        calc ‖1 - z‖ = ‖(1 - z0) - (z - z0)‖ := by ring_nf
          _ ≤ ‖1 - z0‖ + ‖z - z0‖ := norm_sub_le _ _
          _ ≤ M := by linarith
      have hlb : c * ((k : ℝ) + 1) ≤ ‖z + (k : ℂ)‖ := by
        have hre := norm_add_nat_ge_of_re_pos z k
        have hm1 : c ≤ δ := min_le_left _ _
        have hm2 : c ≤ 1 := min_le_right _ _
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hlb2 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
        have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hlb2]
      calc ‖1 - z‖ / (‖z + (k : ℂ)‖ * ((k : ℝ) + 1))
          ≤ M / (c * ((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
            apply div_le_div₀ hM0 h1z (by positivity)
            exact mul_le_mul_of_nonneg_right hlb (by positivity)
        _ = M / c * (1 / ((k : ℝ) + 1) ^ 2) := by field_simp [hcpos.ne']
  have hdiff_ball : DifferentiableOn ℂ digammaSeries (Metric.ball z0 δ) :=
    (differentiableOn_const _).sub hdiff_tsum
  exact (hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))).differentiableWithinAt

theorem digamma_eq_digammaSeries {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = digammaSeries z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hdiff_Gamma : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    have hwpos : 0 < w.re := hw
    have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
    exact (Complex.differentiableAt_Gamma w hne).differentiableWithinAt
  have han1 : AnalyticOnNhd ℂ Complex.digamma {w : ℂ | 0 < w.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro w hw
    have hwpos : 0 < w.re := hw
    have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hd : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w hne
    have hgne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hne
    have hana : AnalyticAt ℂ Complex.Gamma w := hdiff_Gamma.analyticAt (hopen.mem_nhds hw)
    have hderiv_diff : DifferentiableAt ℂ (deriv Complex.Gamma) w := hana.deriv.differentiableAt
    have hdig : Complex.digamma = fun s => deriv Complex.Gamma s / Complex.Gamma s := by
      funext s; rw [Complex.digamma_def, logDeriv_apply]
    rw [hdig]
    exact (hderiv_diff.div hd hgne).differentiableWithinAt
  have han2 : AnalyticOnNhd ℂ digammaSeries {w : ℂ | 0 < w.re} :=
    differentiableOn_digammaSeries.analyticOnNhd hopen
  have heq_on : Set.EqOn Complex.digamma digammaSeries {w : ℂ | 0 < w.re} := by
    refine han1.eqOn_of_preconnected_of_frequently_eq han2 hconn (z₀ := (1 : ℂ)) (by simp) ?_
    rw [Filter.frequently_iff]
    intro U hU
    rw [Metric.mem_nhdsWithin_iff] at hU
    obtain ⟨ε, hε, hsub⟩ := hU
    refine ⟨((1 + ε / 2 : ℝ) : ℂ), hsub ⟨?_, ?_⟩, hasSum_digammaSeries_of_real_pos (by positivity)⟩
    · simp only [Metric.mem_ball, dist_eq_norm]
      have : ((1 + ε / 2 : ℝ) : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  exact heq_on hz

/-! ### Part 2B: Asymptotic `‖digamma z - Complex.log z‖ ≤ 20 / ‖z‖` for `1/4 ≤ z.re` -/

lemma norm_digamma_sub_log_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖Complex.digamma z - Complex.log z‖ ≤ 20 / ‖z‖ := by
  have hzpos : 0 < z.re := by linarith
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzpos
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hznorm_ge : (1 / 4 : ℝ) ≤ ‖z‖ := le_trans hz (Complex.re_le_norm z)
  have hstep_int : ∀ k : ℕ,
      ∫ u in (k : ℝ)..((k : ℝ) + 1), (z + (u : ℂ))⁻¹ =
        Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ)) := by
    intro k
    have hderiv : ∀ u ∈ Set.uIcc (k : ℝ) ((k : ℝ) + 1),
        HasDerivAt (fun t : ℝ => Complex.log (z + (t : ℂ))) (z + (u : ℂ))⁻¹ u := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hu
      have hslit : z + (u : ℂ) ∈ Complex.slitPlane := by
        left; simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
      have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ)) (1 : ℂ) u := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_add z
      have h2 := (Complex.hasDerivAt_log hslit).comp u h1
      simpa [Function.comp_def] using h2
    have hint : IntervalIntegrable (fun u : ℝ => (z + (u : ℂ))⁻¹) volume (k : ℝ) ((k : ℝ) + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hu
      have hne : z + (u : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
        linarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
      exact ((continuousAt_const.add Complex.continuous_ofReal.continuousAt).inv₀ hne).continuousWithinAt
    have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using hres
  have hdiff_k : ∀ k : ℕ,
      ‖((z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ))))‖ ≤
        4 / ((k : ℝ) + ‖z‖) ^ 2 := by
    intro k
    rw [← hstep_int k]
    have hconst : (z + (k : ℂ))⁻¹ = ∫ _u in (k : ℝ)..((k : ℝ) + 1), (z + (k : ℂ))⁻¹ := by
      simp
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const]
    · have hnorm_le : ‖∫ u in (k : ℝ)..((k : ℝ) + 1), ((z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹)‖ ≤
          ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖(z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      refine hnorm_le.trans ?_
      have hbound : ∀ u ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
          ‖(z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹‖ ≤ 4 / ((k : ℝ) + ‖z‖) ^ 2 := by
        intro u hu
        have hne1 : z + (k : ℂ) ≠ 0 := by
          intro h0; have := congrArg Complex.re h0; simp at this; linarith [Nat.cast_nonneg (α := ℝ) k]
        have hne2 : z + (u : ℂ) ≠ 0 := by
          intro h0; have := congrArg Complex.re h0; simp at this
          linarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
        have hsub : (z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹ = ((u : ℂ) - (k : ℂ)) / ((z + (k : ℂ)) * (z + (u : ℂ))) := by
          field_simp [hne1, hne2]; ring
        rw [hsub, norm_div, norm_mul]
        have hnum : ‖(u : ℂ) - (k : ℂ)‖ ≤ 1 := by
          have : (u : ℂ) - (k : ℂ) = ((u - (k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith [hu.1])]
          linarith [hu.2]
        have hlb1 : ((k : ℝ) + ‖z‖) / 2 ≤ ‖z + (k : ℂ)‖ :=
          norm_add_nat_ge_of_re_nonneg hzpos.le k
        have hlb2 : ((k : ℝ) + ‖z‖) / 2 ≤ ‖z + (u : ℂ)‖ := by
          have h1 : ‖z‖ ^ 2 + u ^ 2 ≤ ‖z + (u : ℂ)‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
            simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
            nlinarith [mul_nonneg hzpos.le (le_trans (Nat.cast_nonneg k) hu.1)]
          have h2 : (k : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
          have h3 : (((k : ℝ) + ‖z‖) / 2) ^ 2 ≤ ‖z‖ ^ 2 + (k : ℝ) ^ 2 := by
            nlinarith [sq_nonneg ((k : ℝ) - ‖z‖)]
          nlinarith [sq_nonneg (‖z + (u : ℂ)‖ - ((k : ℝ) + ‖z‖) / 2), norm_nonneg (z + (u : ℂ))]
        have hpos_half : 0 < ((k : ℝ) + ‖z‖) / 2 := by positivity
        calc ‖(u : ℂ) - (k : ℂ)‖ / (‖z + (k : ℂ)‖ * ‖z + (u : ℂ)‖)
            ≤ 1 / ((((k : ℝ) + ‖z‖) / 2) * (((k : ℝ) + ‖z‖) / 2)) := by
              apply div_le_div₀ zero_le_one hnum (mul_pos hpos_half hpos_half)
              exact mul_le_mul hlb1 hlb2 hpos_half.le (norm_nonneg _)
          _ = 4 / ((k : ℝ) + ‖z‖) ^ 2 := by field_simp; ring
      have hint_norm : IntervalIntegrable (fun u : ℝ => ‖(z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹‖)
          volume (k : ℝ) ((k : ℝ) + 1) := by
        apply ContinuousOn.intervalIntegrable
        intro u hu
        rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hu
        have hne : z + (u : ℂ) ≠ 0 := by
          intro h0; have := congrArg Complex.re h0; simp at this
          linarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
        exact (continuousAt_const.sub ((continuousAt_const.add Complex.continuous_ofReal.continuousAt).inv₀ hne)).norm.continuousWithinAt
      calc ∫ u in (k : ℝ)..((k : ℝ) + 1), ‖(z + (k : ℂ))⁻¹ - (z + (u : ℂ))⁻¹‖
          ≤ ∫ _u in (k : ℝ)..((k : ℝ) + 1), (4 / ((k : ℝ) + ‖z‖) ^ 2) :=
            intervalIntegral.integral_mono_on (by linarith) hint_norm intervalIntegrable_const hbound
        _ = 4 / ((k : ℝ) + ‖z‖) ^ 2 := by simp
    · apply ContinuousOn.intervalIntegrable
      intro u hu
      rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at hu
      have hne : z + (u : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this
        linarith [hu.1, Nat.cast_nonneg (α := ℝ) k]
      exact ((continuousAt_const.add Complex.continuous_ofReal.continuousAt).inv₀ hne).continuousWithinAt
  have hsum_tail : ∀ N : ℕ, ∑ k ∈ Finset.range N, (4 : ℝ) / ((k : ℝ) + ‖z‖) ^ 2 ≤ 20 / ‖z‖ := by
    intro N
    cases N with
    | zero => simp; positivity
    | succ M =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add]
      have h0 : 4 / ‖z‖ ^ 2 ≤ 16 / ‖z‖ := by
        rw [div_le_div_iff₀ (by positivity) hznorm_pos]
        nlinarith
      have htail : ∑ k ∈ Finset.range M, (4 : ℝ) / ((((k + 1 : ℕ) : ℝ)) + ‖z‖) ^ 2 ≤ 4 / ‖z‖ := by
        have hstep : ∀ k : ℕ, (4 : ℝ) / ((((k + 1 : ℕ) : ℝ)) + ‖z‖) ^ 2 ≤
            4 * (1 / ((k : ℝ) + ‖z‖) - 1 / (((k + 1 : ℕ) : ℝ) + ‖z‖)) := by
          intro k
          have hp1 : 0 < (k : ℝ) + ‖z‖ := by positivity
          have hp2 : 0 < (((k + 1 : ℕ) : ℝ)) + ‖z‖ := by positivity
          have heq : 1 / ((k : ℝ) + ‖z‖) - 1 / (((k + 1 : ℕ) : ℝ) + ‖z‖) =
              1 / (((k : ℝ) + ‖z‖) * ((((k + 1 : ℕ) : ℝ)) + ‖z‖)) := by
            push_cast; field_simp [hp1.ne', hp2.ne']; ring
          rw [heq, mul_one_div]
          apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hp1 hp2)
          push_cast; nlinarith
        calc ∑ k ∈ Finset.range M, (4 : ℝ) / ((((k + 1 : ℕ) : ℝ)) + ‖z‖) ^ 2
            ≤ ∑ k ∈ Finset.range M, 4 * (1 / ((k : ℝ) + ‖z‖) - 1 / (((k + 1 : ℕ) : ℝ) + ‖z‖)) :=
              Finset.sum_le_sum fun k _ => hstep k
          _ = 4 * ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + ‖z‖) - 1 / (((k + 1 : ℕ) : ℝ) + ‖z‖)) := by
              rw [Finset.mul_sum]
          _ = 4 * (1 / ‖z‖ - 1 / ((M : ℝ) + ‖z‖)) := by
              congr 1
              have ht := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + ‖z‖)) M
              simpa using ht
          _ = 4 / ‖z‖ - 4 / ((M : ℝ) + ‖z‖) := by ring
          _ ≤ 4 / ‖z‖ := by
              have : 0 ≤ 4 / ((M : ℝ) + ‖z‖) := by positivity
              linarith
      calc ∑ k ∈ Finset.range M, 4 / ((((k + 1 : ℕ) : ℝ)) + ‖z‖) ^ 2 + 4 / ‖z‖ ^ 2
          ≤ 4 / ‖z‖ + 16 / ‖z‖ := add_le_add htail h0
        _ = 20 / ‖z‖ := by ring
  have htele : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ))) =
        Complex.log (z + (N : ℂ)) - Complex.log z := by
    intro N
    have h := Finset.sum_range_sub (fun k : ℕ => Complex.log (z + (k : ℂ))) N
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hpart : ∀ N : ℕ,
      -(Real.eulerMascheroniConstant : ℂ) -
        ∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) - Complex.log z =
      ((harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) - (Real.eulerMascheroniConstant : ℂ)) +
      ((Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ))) -
      ∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ)))) := by
    intro N
    have hharm : (harmonic N : ℂ) = ∑ k ∈ Finset.range N, ((k : ℂ) + 1)⁻¹ := by
      simp [harmonic]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htele N, hharm]
    ring
  have hlog_diff : Tendsto (fun N : ℕ => (Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ))) atTop (𝓝 0) := by
    have hzdiv : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖z / (N : ℂ)‖) = (fun N : ℕ => ‖z‖ / (N : ℝ)) := by
        funext N; rw [norm_div, Complex.norm_natCast]
      rw [this]
      exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun N : ℕ => (z + (N : ℂ)) / (N : ℂ)) atTop (𝓝 1) := by
      have h1 : ∀ᶠ N : ℕ in atTop, (z + (N : ℂ)) / (N : ℂ) = 1 + z / (N : ℂ) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        field_simp [hN0]; ring
      refine (by simpa using tendsto_const_nhds.add hzdiv : Tendsto (fun N : ℕ => (1 : ℂ) + z / (N : ℂ)) atTop (𝓝 1)).congr' ?_
      filter_upwards [h1] with N hN; rw [hN]
    have hclog := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp hdiv
    simp only [Complex.log_one] at hclog
    refine hclog.neg.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNpos.ne'
    have hre1 : 0 < ((z + (N : ℂ)) / (N : ℂ)).re := by
      have : ((z + (N : ℂ)) / (N : ℂ)) = z / (N : ℂ) + 1 := by field_simp [hN0]
      rw [this, Complex.add_re, Complex.one_re]
      have : (z / (N : ℂ)).re = z.re / (N : ℝ) := by
        rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
      rw [this]; positivity
    have hlog_eq : Complex.log ((z + (N : ℂ)) / (N : ℂ)) = Complex.log (z + (N : ℂ)) - (Real.log (N : ℝ) : ℂ) := by
      have hmul : (z + (N : ℂ)) = ((z + (N : ℂ)) / (N : ℂ)) * (N : ℂ) := by field_simp [hN0]
      have hlog_mul : Complex.log (z + (N : ℂ)) =
          Complex.log ((z + (N : ℂ)) / (N : ℂ)) + Complex.log (N : ℂ) := by
        conv_lhs => rw [hmul]
        rw [Complex.log_mul]
        · intro h0; rw [h0, Complex.zero_re] at hre1; exact lt_irrefl _ hre1
        · exact hN0
        · have harg_N : (N : ℂ).arg = 0 := by
            rw [← Complex.ofReal_natCast]; exact Complex.arg_ofReal_of_nonneg hNpos.le
          rw [harg_N, add_zero]
          exact Complex.arg_mem_Ioc _
      have hlogN : Complex.log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hNpos.le]
      rw [hlogN] at hlog_mul
      linear_combination -hlog_mul
    simp only [Function.comp_apply] at hlog_eq ⊢
    rw [hlog_eq]; ring
  have hharm_lim : Tendsto (fun N : ℕ => (harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) -
      (Real.eulerMascheroniConstant : ℂ)) atTop (𝓝 0) := by
    have hR : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant)
        atTop (𝓝 0) := by
      simpa using Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
    have hC := (Complex.continuous_ofReal.tendsto 0).comp hR
    simp only [Complex.ofReal_zero] at hC
    refine hC.congr fun N => ?_
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_ratCast]
  have hLHS_lim : Tendsto (fun N : ℕ =>
      ‖-(Real.eulerMascheroniConstant : ℂ) -
        ∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) - Complex.log z‖)
      atTop (𝓝 ‖Complex.digamma z - Complex.log z‖) := by
    rw [digamma_eq_digammaSeries hzpos]
    unfold digammaSeries
    exact ((tendsto_const_nhds.sub (summable_digammaSeries_term hzpos).hasSum.tendsto_sum_nat).sub
      tendsto_const_nhds).norm
  have hRHS_lim : Tendsto (fun N : ℕ =>
      ‖(harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) - (Real.eulerMascheroniConstant : ℂ)‖ +
      ‖(Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ))‖ + 20 / ‖z‖)
      atTop (𝓝 (20 / ‖z‖)) := by
    have := (hharm_lim.norm.add hlog_diff.norm).add (tendsto_const_nhds (x := 20 / ‖z‖))
    simpa using this
  refine le_of_tendsto_of_tendsto hLHS_lim hRHS_lim (Filter.Eventually.of_forall fun N => ?_)
  dsimp only
  rw [hpart N]
  have htri : ‖((harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) - (Real.eulerMascheroniConstant : ℂ)) +
      ((Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ))) -
      ∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ))))‖ ≤
      ‖(harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) - (Real.eulerMascheroniConstant : ℂ)‖ +
      ‖(Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ))‖ +
      ‖∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ))))‖ := by
    calc _ ≤ ‖((harmonic N : ℂ) - (Real.log (N : ℝ) : ℂ) - (Real.eulerMascheroniConstant : ℂ)) +
          ((Real.log (N : ℝ) : ℂ) - Complex.log (z + (N : ℂ)))‖ + _ := norm_sub_le _ _
      _ ≤ _ := by gcongr; exact norm_add_le _ _
  refine htri.trans ?_
  gcongr
  calc ‖∑ k ∈ Finset.range N, ((z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ))))‖
      ≤ ∑ k ∈ Finset.range N, ‖(z + (k : ℂ))⁻¹ - (Complex.log (z + ((k : ℂ) + 1)) - Complex.log (z + (k : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, (4 : ℝ) / ((k : ℝ) + ‖z‖) ^ 2 := Finset.sum_le_sum fun k _ => hdiff_k k
    _ ≤ 20 / ‖z‖ := hsum_tail N

/-! ### Part 2C: Bound on `logDeriv riemannZeta (-1/2 + I * τ)` via functional equation -/

lemma sq_norm_sin_add_mul_I (x y : ℝ) :
    ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, Complex.sq_norm, Complex.normSq_apply]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul, add_zero, Complex.add_im, Complex.mul_im,
    sub_self]
  have h1 := Real.cosh_sq y
  have h2 := Real.sin_sq_add_cos_sq x
  nlinarith

lemma sq_norm_cos_add_mul_I (x y : ℝ) :
    ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, Complex.sq_norm, Complex.normSq_apply]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul, add_zero, Complex.sub_im, Complex.mul_im,
    sub_self, zero_sub]
  have h1 := Real.cosh_sq y
  have h2 := Real.sin_sq_add_cos_sq x
  nlinarith

lemma norm_tan_three_pi_div_four_add_I (y : ℝ) :
    ‖Complex.tan ((3 * Real.pi / 4 : ℝ) + Complex.I * (y : ℂ))‖ = 1 := by
  have harg : ((3 * Real.pi / 4 : ℝ) : ℂ) + Complex.I * (y : ℂ) =
      ((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by ring
  rw [harg, Complex.tan_eq_sin_div_cos, norm_div]
  have hsin := sq_norm_sin_add_mul_I (3 * Real.pi / 4) y
  have hcos := sq_norm_cos_add_mul_I (3 * Real.pi / 4) y
  have hs : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four]
  have hc : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  have hsq : (-(Real.sqrt 2 / 2)) ^ 2 = 1 / 2 := by
    rw [neg_sq, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have htrig : Real.sin (3 * Real.pi / 4) ^ 2 = Real.cos (3 * Real.pi / 4) ^ 2 := by
    rw [hs, hc]; ring
  have hpos : 0 < ‖Complex.cos (((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hcos, hc, hsq]; linarith [sq_nonneg (Real.sinh y)]
  have heq : ‖Complex.sin (((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ =
      ‖Complex.cos (((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ := by
    nlinarith [norm_nonneg (Complex.sin (((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)),
      norm_nonneg (Complex.cos (((3 * Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))]
  rw [heq, div_self (by intro h; rw [h] at hpos; norm_num at hpos)]

theorem norm_logDeriv_riemannZeta_neg_half_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤
      C * Real.log (2 + |τ|) := by
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (3 / 2 : ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num)).norm
  set B := ∑' n : ℕ, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (3 / 2 : ℂ) n‖ with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨2 * (B + Real.log (2 * Real.pi) + 20 + Real.pi + Real.pi / 2 + 2), by positivity, fun τ => ?_⟩
  set s : ℂ := (3 / 2 : ℂ) - Complex.I * (τ : ℂ) with hsdef
  have h1s : 1 - s = -(1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by rw [hsdef]; ring
  have hs_re_val : s.re = 3 / 2 := by
    rw [hsdef]; simp
  have hs_nint : ∀ n : ℤ, s ≠ (n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    rw [hs_re_val, Complex.intCast_re] at hre
    have : (3 : ℤ) = 2 * n := by
      have : ((3 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hs_re : (1 : ℝ) < s.re := by linarith
  have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs_re
  have hfe := logDeriv_riemannZeta_one_sub hs_nint hzne
  rw [h1s] at hfe
  have hfe' : logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
      -logDeriv riemannZeta s + Complex.log (2 * Real.pi) - Complex.digamma s +
        (Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * s / 2) := by
    linear_combination hfe
  rw [hfe']
  have ht1 : ‖-logDeriv riemannZeta s‖ ≤ B := by
    rw [norm_neg]
    have hl := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs_re
    have hld : -logDeriv riemannZeta s = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s := by
      rw [logDeriv_apply, hl]; ring
    rw [← norm_neg, hld]
    unfold LSeries
    refine (norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_vonMangoldt hs_re).norm).trans ?_
    refine Summable.tsum_le_tsum (fun n => ?_) (ArithmeticFunction.LSeriesSummable_vonMangoldt hs_re).norm hsum
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte, norm_div]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hre_eq : s.re = (3 / 2 : ℂ).re := by rw [hs_re_val]; simp
      rw [hre_eq]
  have ht2 : ‖Complex.log (2 * Real.pi)‖ ≤ Real.log (2 * Real.pi) := by
    have h2p : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_log h2p.le,
      Complex.norm_real, Real.norm_of_nonneg hlog2pi]
  have hs_norm_ge1 : (1 : ℝ) ≤ ‖s‖ := by
    have := Complex.re_le_norm s
    linarith
  have hs_norm_le : ‖s‖ ≤ 2 + |τ| := by
    calc ‖s‖ ≤ ‖(3 / 2 : ℂ)‖ + ‖Complex.I * (τ : ℂ)‖ := norm_sub_le _ _
      _ = 3 / 2 + |τ| := by simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 + |τ| := by linarith
  have ht3 : ‖Complex.digamma s‖ ≤ Real.log (2 + |τ|) + Real.pi + 20 := by
    have hdg := norm_digamma_sub_log_le (z := s) (by linarith)
    have hlog : ‖Complex.log s‖ ≤ Real.log ‖s‖ + Real.pi := by
      have h1 : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + |s.arg| := by
        calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |Real.log ‖s‖| + |s.arg| := by simp [Complex.log_re, Complex.log_im]
      have harg : |s.arg| ≤ Real.pi := Complex.abs_arg_le_pi s
      have hln : 0 ≤ Real.log ‖s‖ := Real.log_nonneg hs_norm_ge1
      rw [abs_of_nonneg hln] at h1
      linarith
    have hlog2' : Real.log ‖s‖ ≤ Real.log (2 + |τ|) := Real.log_le_log (by positivity) hs_norm_le
    have h20 : 20 / ‖s‖ ≤ 20 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    calc ‖Complex.digamma s‖ = ‖Complex.log s + (Complex.digamma s - Complex.log s)‖ := by ring_nf
      _ ≤ ‖Complex.log s‖ + ‖Complex.digamma s - Complex.log s‖ := norm_add_le _ _
      _ ≤ (Real.log (2 + |τ|) + Real.pi) + 20 := by linarith
      _ = Real.log (2 + |τ|) + Real.pi + 20 := by ring
  have ht4 : ‖(Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤ Real.pi / 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have htan_arg : (Real.pi : ℂ) * s / 2 = ((3 * Real.pi / 4 : ℝ) : ℂ) + Complex.I * ((-(Real.pi * τ / 2) : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [htan_arg, norm_tan_three_pi_div_four_add_I]
    simp
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (2 + |τ|) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg τ]))
  have hsum_all : ‖-logDeriv riemannZeta s + Complex.log (2 * Real.pi) - Complex.digamma s +
      (Real.pi : ℂ) / 2 * Complex.tan ((Real.pi : ℂ) * s / 2)‖ ≤
      B + Real.log (2 * Real.pi) + (Real.log (2 + |τ|) + Real.pi + 20) + Real.pi / 2 := by
    calc _ ≤ ‖-logDeriv riemannZeta s + Complex.log (2 * Real.pi) - Complex.digamma s‖ + _ := norm_add_le _ _
      _ ≤ (‖-logDeriv riemannZeta s + Complex.log (2 * Real.pi)‖ + ‖Complex.digamma s‖) + _ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ((‖-logDeriv riemannZeta s‖ + ‖Complex.log (2 * Real.pi)‖) + ‖Complex.digamma s‖) + _ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith
  refine hsum_all.trans ?_
  have hconst_pos : 0 ≤ B + Real.log (2 * Real.pi) + 20 + Real.pi + Real.pi / 2 := by positivity
  nlinarith

end SpectralMod2

end Mod2Section

section Mod3Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators

namespace SpectralMod3

/-! ### Module 3: Entirety and Polynomial Growth of `(s - 1) * riemannZeta s` on `-2 ≤ s.re ≤ 6` -/

noncomputable def zetaExt (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

noncomputable def emIntegral (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))

noncomputable def emZeta (s : ℂ) : ℂ :=
  s - s * (s - 1) * emIntegral s

/-! #### Part 3A: 1-step Euler-Maclaurin identity and right half-plane growth -/

lemma integrableOn_rpow_neg_Ioi {α : ℝ} (hα : 1 < α) :
    IntegrableOn (fun x : ℝ => x ^ (-α)) (Set.Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

lemma integral_rpow_neg_Ioi {α : ℝ} (hα : 1 < α) :
    ∫ x in Set.Ioi (1 : ℝ), x ^ (-α) = 1 / (α - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have h1 : α - 1 ≠ 0 := by linarith
  have h2 : -α + 1 ≠ 0 := by linarith
  field_simp [h1, h2]; ring

lemma cpow_ofReal_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]

lemma continuousOn_ofReal_cpow (w : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ w) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * w)) (Set.Ioi 0) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun x hx => (Set.mem_Ioi.mp hx).ne')).mul continuousOn_const)
  exact h1.congr fun x hx => cpow_ofReal_eq_exp (Set.mem_Ioi.mp hx) w

lemma integrableOn_fract_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-(s.re + 1))) (Set.Ioi 1) :=
    integrableOn_rpow_neg_Ioi (by linarith)
  refine hdom.mono' ?_ ?_
  · have hm1 : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (volume.restrict (Set.Ioi 1)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioi 1)) :=
      ((continuousOn_ofReal_cpow (-(s + 1))).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    exact hm1.mul hm2
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [hre]
    simpa using mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (Real.rpow_nonneg hx0.le _)

lemma intervalIntegral_cpow_of_pos {a b : ℝ} (ha : 0 < a) (hb : a ≤ b) {w : ℂ} (hw : w ≠ -1) :
    ∫ x in a..b, (x : ℂ) ^ w = ((b : ℂ) ^ (w + 1) - (a : ℂ) ^ (w + 1)) / (w + 1) := by
  have hw1 : w + 1 ≠ 0 := by intro h; apply hw; linear_combination h
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (w + 1) / (w + 1)) ((x : ℂ) ^ w) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hlog : HasDerivAt (fun t : ℝ => (Real.log t : ℂ) * (w + 1)) ((x⁻¹ : ℝ) * (w + 1)) x :=
      ((Real.hasDerivAt_log hxpos.ne').ofReal_comp).mul_const (w + 1)
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((Real.log t : ℂ) * (w + 1)) / (w + 1))
        (Complex.exp ((Real.log x : ℂ) * (w + 1)) * ((x⁻¹ : ℝ) * (w + 1)) / (w + 1)) x :=
      hlog.cexp.div_const (w + 1)
    have hev : (fun t : ℝ => (t : ℂ) ^ (w + 1) / (w + 1)) =ᶠ[𝓝 x]
        (fun t : ℝ => Complex.exp ((Real.log t : ℂ) * (w + 1)) / (w + 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hxpos)] with t ht
      rw [cpow_ofReal_eq_exp (Set.mem_Ioi.mp ht)]
    have hd := hexp.congr_of_eventuallyEq hev
    convert hd using 1
    rw [← cpow_ofReal_eq_exp hxpos (w + 1), Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hxpos.ne'),
      Complex.cpow_one, Complex.ofReal_inv]
    field_simp [hw1, Complex.ofReal_ne_zero.mpr hxpos.ne']
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_ofReal_cpow w).mono (fun x hx => by
      rw [Set.uIcc_of_le hb] at hx; exact lt_of_lt_of_le ha hx.1)
  have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hres, sub_div]

lemma em_finite_identity {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℂ) / ((k : ℂ) + 1) ^ s =
      s / (s - 1) - s * (∫ x in (1 : ℝ)..((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        s * ((N : ℂ) + 1) ^ (1 - s) / (1 - s) + (N : ℂ) * ((N : ℂ) + 1) ^ (-s) := by
  have hs1' : 1 - s ≠ 0 := by intro h; apply hs1; linear_combination -h
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add,
      intervalIntegral.integral_same, mul_zero, sub_zero, add_zero, Complex.one_cpow, mul_one]
    field_simp [hs1', hs1'']
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit : ∫ x in (1 : ℝ)..(((n + 1 : ℕ) : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        (∫ x in (1 : ℝ)..((n : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        (∫ x in ((n : ℝ) + 1)..(((n + 1 : ℕ) : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
      have hint_sub : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
          IntervalIntegrable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) volume a b := by
        intro a b ha hab
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
        have hdom : IntegrableOn (fun x : ℝ => x ^ (-(s.re + 1))) (Set.Ioc a b) := by
          have hcont : ContinuousOn (fun x : ℝ => x ^ (-(s.re + 1))) (Set.Icc a b) :=
            ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by linarith [hx.1]))
          exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        refine hdom.mono' ?_ ?_
        · have hm1 : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (volume.restrict (Set.Ioc a b)) :=
            (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
          have hm2 : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioc a b)) :=
            ((continuousOn_ofReal_cpow (-(s + 1))).mono (fun x hx => by
              show (0 : ℝ) < x; linarith [hx.1])).aestronglyMeasurable measurableSet_Ioc
          exact hm1.mul hm2
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          have hx0 : 0 < x := by linarith [hx.1]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x),
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(s + 1)).re = -(s.re + 1) := by simp
          rw [hre]
          simpa using mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (Real.rpow_nonneg hx0.le _)
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hint_sub 1 ((n : ℝ) + 1) le_rfl (by linarith [Nat.cast_nonneg (α := ℝ) n]))
        (hint_sub ((n : ℝ) + 1) (((n + 1 : ℕ) : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (by push_cast; linarith))).symm
    have hstep : ∫ x in ((n : ℝ) + 1)..(((n + 1 : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        ((((n + 1 : ℕ) : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 1) ^ (1 - s)) / (1 - s) -
        ((n : ℂ) + 1) * ((((n + 1 : ℕ) : ℂ) + 1) ^ (-s) - ((n : ℂ) + 1) ^ (-s)) / (-s) := by
      have hle : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hcongr : ∫ x in ((n : ℝ) + 1)..(((n + 1 : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
          ∫ x in ((n : ℝ) + 1)..(((n + 1 : ℕ) : ℝ) + 1),
            ((x : ℂ) ^ (-s) - ((n : ℂ) + 1) * (x : ℂ) ^ (-(s + 1))) := by
        rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
        rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have hfl : Int.floor x = (n + 1 : ℤ) := by
          rw [Int.floor_eq_iff]
          push_cast at hx ⊢
          exact ⟨hx.1.le, hx.2⟩
        have hfr : Int.fract x = x - ((n : ℝ) + 1) := by
          rw [Int.fract, hfl]; push_cast; ring
        have hxpos : 0 < x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
        have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
        rw [hfr]
        have hmul : (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
          calc (x : ℂ) * (x : ℂ) ^ (-(s + 1))
              = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
            _ = (x : ℂ) ^ ((1 : ℂ) + -(s + 1)) := (Complex.cpow_add _ _ hxne).symm
            _ = (x : ℂ) ^ (-s) := by congr 1; ring
        push_cast
        rw [sub_mul, hmul]
      rw [hcongr]
      have hcont_pow : ∀ w : ℂ, IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w) volume ((n : ℝ) + 1) (((n + 1 : ℕ) : ℝ) + 1) := by
        intro w
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_ofReal_cpow w).mono (fun x hx => by
          rw [Set.uIcc_of_le hle] at hx
          show (0 : ℝ) < x
          linarith [hx.1, Nat.cast_nonneg (α := ℝ) n])
      rw [intervalIntegral.integral_sub (hcont_pow (-s)) ((hcont_pow (-(s + 1))).const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral_cpow_of_pos (by positivity) hle (by intro h; apply hs1; linear_combination -h),
        intervalIntegral_cpow_of_pos (by positivity) hle (by intro h; apply hs0; linear_combination -h)]
      have he1 : -s + 1 = 1 - s := by ring
      have he2 : -(s + 1) + 1 = -s := by ring
      rw [he1, he2]
      push_cast; ring
    rw [hsplit, hstep]
    have hpow : (1 : ℂ) / ((n : ℂ) + 1) ^ s = ((n : ℂ) + 1) ^ (-s) := by
      rw [Complex.cpow_neg, one_div]
    rw [hpow]
    push_cast
    field_simp [hs0, hs1', hs1'']
    ring

lemma zetaExt_eq_emZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaExt s = emZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (1 : ℂ) / ((k : ℂ) + 1) ^ s)
      atTop (𝓝 (riemannZeta s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have hsumm : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ s) := by
      have := (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective
      refine this.congr fun k => ?_
      simp [Nat.cast_succ]
    exact hsumm.hasSum.tendsto_sum_nat
  have hN1_top : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hint_lim : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..((N : ℝ) + 1),
      ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) atTop (𝓝 (emIntegral s)) := by
    unfold emIntegral
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (1 : ℝ))
      (b := fun N : ℕ => (N : ℝ) + 1) (integrableOn_fract_cpow (by linarith)) hN1_top
  have hrpow_lim : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h2 : (fun x : ℝ => x ^ (-(s.re - 1))) = (fun x : ℝ => x ^ (1 - s.re)) := by
      funext x; congr 1; ring
    rw [h2] at h1
    exact h1.comp hN1_top
  have hpow1 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun N : ℕ => ‖((N : ℂ) + 1) ^ (1 - s)‖) = (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re)) := by
      funext N
      have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp
    rw [heq]; exact hrpow_lim
  have hpow2 : Tendsto (fun N : ℕ => (N : ℂ) * ((N : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm' (a := fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re)) ?_ hrpow_lim
    filter_upwards with N
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_natCast]
    have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc (N : ℝ) * ((N : ℝ) + 1) ^ (-s.re)
        ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-s.re) := by gcongr; linarith
      _ = ((N : ℝ) + 1) ^ (1 : ℝ) * ((N : ℝ) + 1) ^ (-s.re) := by rw [Real.rpow_one]
      _ = ((N : ℝ) + 1) ^ (1 - s.re) := by rw [← Real.rpow_add hpos]; ring_nf
  have hRHS : Tendsto (fun N : ℕ =>
      s / (s - 1) - s * (∫ x in (1 : ℝ)..((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        s * ((N : ℂ) + 1) ^ (1 - s) / (1 - s) + (N : ℂ) * ((N : ℂ) + 1) ^ (-s))
      atTop (𝓝 (s / (s - 1) - s * emIntegral s)) := by
    have h1 := (tendsto_const_nhds (x := s / (s - 1))).sub (hint_lim.const_mul s)
    have h2 : Tendsto (fun N : ℕ => s * ((N : ℂ) + 1) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
      simpa using (hpow1.const_mul s).div_const (1 - s)
    simpa using (h1.add h2).add hpow2
  have heq_seq : (fun N : ℕ => ∑ k ∈ Finset.range N, (1 : ℂ) / ((k : ℂ) + 1) ^ s) =
      (fun N : ℕ =>
        s / (s - 1) - s * (∫ x in (1 : ℝ)..((N : ℝ) + 1), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
          s * ((N : ℂ) + 1) ^ (1 - s) / (1 - s) + (N : ℂ) * ((N : ℂ) + 1) ^ (-s)) :=
    funext fun N => em_finite_identity hs0 hs1 N
  rw [heq_seq] at hsum
  have hzeta := tendsto_nhds_unique hsum hRHS
  unfold zetaExt emZeta
  simp only [hs1, ↓reduceIte, hzeta]
  field_simp [hs1'']

lemma differentiableOn_emIntegral : DifferentiableOn ℂ emIntegral {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0_pos : 0 < s0.re := hs0
  set δ := s0.re / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hbound : ∃ bound : ℝ → ℝ, IntegrableOn bound (Set.Ioi 1) ∧
      ∀ s ∈ Metric.ball s0 δ, ∀ x ∈ Set.Ioi (1 : ℝ),
        ‖((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(s + 1)) * (-Complex.log (x : ℂ)))‖ ≤ bound x := by
    refine ⟨fun x => Real.log x * x ^ (-(δ + 1)), ?_, ?_⟩
    · have hdom : IntegrableOn (fun x : ℝ => (2 / δ) * x ^ (-(δ / 2 + 1))) (Set.Ioi 1) :=
        (integrableOn_rpow_neg_Ioi (by linarith)).const_mul _
      refine hdom.mono' (by
        have hm : Measurable (fun x : ℝ => Real.log x * x ^ (-(δ + 1))) :=
          Real.measurable_log.mul (measurable_id.pow_const _)
        exact hm.aestronglyMeasurable) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 < x := Set.mem_Ioi.mp hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx1
      rw [Real.norm_of_nonneg (mul_nonneg (Real.log_nonneg hx1.le) (Real.rpow_nonneg hx0.le _))]
      have hlog : Real.log x ≤ (2 / δ) * x ^ (δ / 2) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (δ / 2))
        rw [Real.log_rpow hx0] at h1
        have h2 : (δ / 2) * Real.log x ≤ x ^ (δ / 2) := by linarith
        calc Real.log x = (2 / δ) * ((δ / 2) * Real.log x) := by field_simp [hδpos.ne']
          _ ≤ (2 / δ) * x ^ (δ / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      calc Real.log x * x ^ (-(δ + 1))
          ≤ ((2 / δ) * x ^ (δ / 2)) * x ^ (-(δ + 1)) := by gcongr
        _ = (2 / δ) * (x ^ (δ / 2) * x ^ (-(δ + 1))) := by ring
        _ = (2 / δ) * x ^ (-(δ / 2 + 1)) := by rw [← Real.rpow_add hx0]; ring_nf
    · intro s hs x hx
      have hx1 : 1 < x := Set.mem_Ioi.mp hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx1
      have hsre : δ < s.re := by
        have h1 : |s.re - s0.re| ≤ ‖s - s0‖ := by simpa using Complex.abs_re_le_norm (s - s0)
        have h2 : ‖s - s0‖ < δ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs
        linarith [(abs_le.mp h1).1]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Int.fract_nonneg x),
        Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        ← Complex.ofReal_log hx0.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg hx1.le)]
      have hre : (-(s + 1)).re = -(s.re + 1) := by simp
      rw [hre]
      have hrp : x ^ (-(s.re + 1)) ≤ x ^ (-(δ + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      calc Int.fract x * (x ^ (-(s.re + 1)) * Real.log x)
          ≤ 1 * (x ^ (-(δ + 1)) * Real.log x) :=
            mul_le_mul (Int.fract_lt_one x).le
              (mul_le_mul_of_nonneg_right hrp (Real.log_nonneg hx1.le))
              (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx1.le)) zero_le_one
        _ = Real.log x * x ^ (-(δ + 1)) := by ring
  obtain ⟨bound, hbound_int, hbound_le⟩ := hbound
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s0 hδpos)
    (μ := volume.restrict (Set.Ioi 1))
    (F := fun s x => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)))
    (F' := fun s x => ((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(s + 1)) * (-Complex.log (x : ℂ))))
    (bound := bound)
    (Filter.Eventually.of_forall fun s => by
      have hm1 : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (volume.restrict (Set.Ioi 1)) :=
        (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioi 1)) :=
        ((continuousOn_ofReal_cpow (-(s + 1))).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
      exact hm1.mul hm2)
    (integrableOn_fract_cpow hs0_pos)
    (by
      have hm1 : AEStronglyMeasurable (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (volume.restrict (Set.Ioi 1)) :=
        (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-(s0 + 1))) (volume.restrict (Set.Ioi 1)) :=
        ((continuousOn_ofReal_cpow (-(s0 + 1))).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
      have hm3 : AEStronglyMeasurable (fun x : ℝ => -Complex.log (x : ℂ)) (volume.restrict (Set.Ioi 1)) :=
        ((Complex.measurable_log.comp Complex.continuous_ofReal.measurable).neg).aestronglyMeasurable
      exact hm1.mul (hm2.mul hm3))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx s hs
      exact hbound_le s hs x hx)
    hbound_int
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx s _
      have hx0 : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
      have hlin : HasDerivAt (fun w : ℂ => (Real.log x : ℂ) * (-(w + 1))) ((Real.log x : ℂ) * (-1)) s :=
        (((hasDerivAt_id s).add_const 1).neg).const_mul (Real.log x : ℂ)
      have hexp := (hlin.cexp).const_mul ((Int.fract x : ℝ) : ℂ)
      have heq : (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) =
          (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * Complex.exp ((Real.log x : ℂ) * (-(w + 1)))) := by
        funext w; rw [cpow_ofReal_eq_exp hx0]
      rw [heq]
      convert hexp using 1
      rw [← cpow_ofReal_eq_exp hx0, Complex.ofReal_log hx0.le]; ring)
  exact hres.2.differentiableAt.differentiableWithinAt

lemma isPreconnected_re_pos_diff_one : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  let U1 : Set ℂ := {s | 1 < s.re}
  let U2 : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}
  let U3 : Set ℂ := {s | 0 < s.re ∧ s.im < 0}
  let U4 : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  have h1 : IsPreconnected U1 := (convex_halfSpace_re_gt 1).isPreconnected
  have h2 : IsPreconnected U2 := ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have h3 : IsPreconnected U3 := ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have h4 : IsPreconnected U4 := ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have h12 : IsPreconnected (U1 ∪ U2) :=
    h1.union' ⟨2 + Complex.I, ⟨by simp [U1], by simp [U2]⟩⟩ h2
  have h123 : IsPreconnected ((U1 ∪ U2) ∪ U3) :=
    h12.union' ⟨2 - Complex.I, ⟨Or.inl (by simp [U1]), by simp [U3]⟩⟩ h3
  have h1234 : IsPreconnected (((U1 ∪ U2) ∪ U3) ∪ U4) :=
    h123.union' ⟨1 / 2 + Complex.I, ⟨Or.inl (Or.inr (by simp [U2])), by simp [U4]; norm_num⟩⟩ h4
  have heq : (((U1 ∪ U2) ∪ U3) ∪ U4) = {s : ℂ | 0 < s.re} \ {1} := by
    ext s
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, U1, U2, U3, U4, Set.mem_ofPred_eq]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨by linarith, fun hs => by rw [hs, Complex.one_re] at h; linarith⟩
      · exact ⟨h.1, fun hs => by rw [hs, Complex.one_im] at h; linarith [h.2]⟩
      · exact ⟨h.1, fun hs => by rw [hs, Complex.one_im] at h; linarith [h.2]⟩
      · exact ⟨h.1, fun hs => by rw [hs, Complex.one_re] at h; linarith [h.2]⟩
    · rintro ⟨hpos, hne⟩
      rcases lt_trichotomy s.re 1 with hlt | heq1 | hgt
      · exact Or.inr ⟨hpos, hlt⟩
      · rcases lt_trichotomy s.im 0 with him | him0 | him
        · exact Or.inl (Or.inr ⟨hpos, him⟩)
        · exfalso; apply hne; exact Complex.ext heq1 him0
        · exact Or.inl (Or.inl (Or.inr ⟨hpos, him⟩))
      · exact Or.inl (Or.inl (Or.inl hgt))
  rwa [← heq]

lemma zetaExt_eq_emZeta {s : ℂ} (hs : 0 < s.re) : zetaExt s = emZeta s := by
  by_cases h1 : s = 1
  · subst h1; simp [zetaExt, emZeta]
  · have hopen : IsOpen ({w : ℂ | 0 < w.re} \ {1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    have han1 : AnalyticOnNhd ℂ zetaExt ({w : ℂ | 0 < w.re} \ {1}) := by
      apply DifferentiableOn.analyticOnNhd _ hopen
      intro w hw
      have hw1 : w ≠ 1 := hw.2
      have hd : DifferentiableAt ℂ (fun u => (u - 1) * riemannZeta u) w :=
        (differentiableAt_id.sub (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hw1)
      have hev : zetaExt =ᶠ[𝓝 w] fun u => (u - 1) * riemannZeta u := by
        filter_upwards [isOpen_ne.mem_nhds hw1] with u hu
        simp [zetaExt, hu]
      exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
    have han2 : AnalyticOnNhd ℂ emZeta ({w : ℂ | 0 < w.re} \ {1}) := by
      apply DifferentiableOn.analyticOnNhd _ hopen
      have hdiff : DifferentiableOn ℂ emZeta {w : ℂ | 0 < w.re} :=
        differentiableOn_id.sub ((differentiableOn_id.mul (differentiableOn_id.sub (differentiableOn_const 1))).mul
          differentiableOn_emIntegral)
      exact hdiff.mono Set.sdiff_subset
    have heq : Set.EqOn zetaExt emZeta ({w : ℂ | 0 < w.re} \ {1}) := by
      refine han1.eqOn_of_preconnected_of_frequently_eq han2 isPreconnected_re_pos_diff_one
        (z₀ := (2 : ℂ)) ⟨by simp, by norm_num⟩ ?_
      rw [Filter.frequently_iff]
      intro U hU
      rw [Metric.mem_nhdsWithin_iff] at hU
      obtain ⟨ε, hε, hsub⟩ := hU
      set δ := min (ε / 2) (1 / 2)
      have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
      refine ⟨(2 : ℂ) + (δ : ℂ), hsub ⟨?_, ?_⟩, zetaExt_eq_emZeta_of_one_lt_re (by simp; linarith)⟩
      · simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg hδpos.le]
        linarith [min_le_left (ε / 2) (1 / 2)]
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    exact heq ⟨hs, h1⟩

theorem differentiable_zetaExt : Differentiable ℂ zetaExt := by
  intro s
  by_cases h1 : s = 1
  · subst h1
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : zetaExt =ᶠ[𝓝 (1 : ℂ)] emZeta := by
      filter_upwards [hopen.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
      exact zetaExt_eq_emZeta hw
    have hd : DifferentiableAt ℂ emZeta 1 := by
      have hdiff : DifferentiableOn ℂ emZeta {w : ℂ | 0 < w.re} :=
        differentiableOn_id.sub ((differentiableOn_id.mul (differentiableOn_id.sub (differentiableOn_const 1))).mul
          differentiableOn_emIntegral)
      exact hdiff.differentiableAt (hopen.mem_nhds (by simp))
    exact hd.congr_of_eventuallyEq hev
  · have hd : DifferentiableAt ℂ (fun u => (u - 1) * riemannZeta u) s :=
      (differentiableAt_id.sub (differentiableAt_const 1)).mul (differentiableAt_riemannZeta h1)
    have hev : zetaExt =ᶠ[𝓝 s] fun u => (u - 1) * riemannZeta u := by
      filter_upwards [isOpen_ne.mem_nhds h1] with u hu
      simp [zetaExt, hu]
    exact hd.congr_of_eventuallyEq hev

lemma norm_zetaExt_right_le {s : ℂ} (hlo : (1 / 4 : ℝ) ≤ s.re) (hhi : s.re ≤ 6) :
    ‖zetaExt s‖ ≤ 400 * (2 + |s.im|) ^ 2 := by
  rw [zetaExt_eq_emZeta (by linarith)]
  unfold emZeta emIntegral
  have hint_le : ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤ 4 := by
    calc ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖
        ≤ ∫ x in Set.Ioi (1 : ℝ), ‖((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (1 : ℝ), x ^ (-(5 / 4 : ℝ)) := by
          apply MeasureTheory.setIntegral_mono_on (integrableOn_fract_cpow (by linarith)).norm
            (integrableOn_rpow_neg_Ioi (by norm_num)) measurableSet_Ioi
          intro x hx
          have hx1 : 1 < x := Set.mem_Ioi.mp hx
          have hx0 : 0 < x := lt_trans zero_lt_one hx1
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg x),
            Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (-(s + 1)).re = -(s.re + 1) := by simp
          rw [hre]
          calc Int.fract x * x ^ (-(s.re + 1))
              ≤ 1 * x ^ (-(5 / 4 : ℝ)) :=
                mul_le_mul (Int.fract_lt_one x).le
                  (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
                  (Real.rpow_nonneg hx0.le _) zero_le_one
            _ = x ^ (-(5 / 4 : ℝ)) := one_mul _
      _ = 4 := by
          rw [integral_rpow_neg_Ioi (by norm_num)]; norm_num
  have hsn : ‖s‖ ≤ 6 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 6 + |s.im| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hs1n : ‖s - 1‖ ≤ 7 + |s.im| := by
    calc ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
      _ ≤ 7 + |s.im| := by linarith
  calc ‖s - s * (s - 1) * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ + ‖s * (s - 1) * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ :=
        norm_sub_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (6 + |s.im|) + (6 + |s.im|) * (7 + |s.im|) * 4 := by gcongr
    _ ≤ 400 * (2 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]

/-! #### Part 3B: Lower bound on `Re s = 2`: `Re ζ(2 + it) ≥ 1/4` and `‖zetaExt (2 + it)‖ ≥ 1/4` -/

lemma re_riemannZeta_two_add_I_ge (t : ℝ) :
    (1 / 4 : ℝ) ≤ (riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ))).re ∧
    ‖riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ)) - 1‖ ≤ 3 / 4 := by
  set s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = 2 := by simp [s]
  have hgt : 1 < s.re := by linarith
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hgt
  have hsumm : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ s) := by
    have := (Complex.summable_one_div_nat_cpow.mpr hgt).comp_injective Nat.succ_injective
    refine this.congr fun k => ?_
    simp [Nat.cast_succ]
  have hsub : riemannZeta s - 1 = ∑' k : ℕ, (1 : ℂ) / ((k : ℂ) + 2) ^ s := by
    rw [hzeta, hsumm.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one, add_sub_cancel_left]
    congr 1; funext k; push_cast; ring_nf
  have htail_sum : ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 2) ^ 2 ≤ 3 / 4 := by
    have hnn : ∀ k : ℕ, 0 ≤ (1 : ℝ) / ((k : ℝ) + 2) ^ 2 := fun k => by positivity
    refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
    cases N with
    | zero => norm_num
    | succ M =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add]
      have hstep : ∀ k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) ^ 2 ≤
          1 / ((k : ℝ) + 2) - 1 / (((k + 1 : ℕ) : ℝ) + 2) := by
        intro k
        have hp1 : 0 < (k : ℝ) + 2 := by positivity
        have hp2 : 0 < ((k + 1 : ℕ) : ℝ) + 2 := by positivity
        rw [div_sub_div _ _ hp1.ne' hp2.ne', div_le_div_iff₀ (by positivity) (mul_pos hp1 hp2)]
        push_cast; nlinarith
      have hM : ∑ k ∈ Finset.range M, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) ^ 2 ≤ 1 / 2 := by
        calc ∑ k ∈ Finset.range M, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 2) ^ 2
            ≤ ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 2) - 1 / (((k + 1 : ℕ) : ℝ) + 2)) :=
              Finset.sum_le_sum fun k _ => hstep k
          _ = 1 / 2 - 1 / ((M : ℝ) + 2) := by
              have ht := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) M
              simpa using ht
          _ ≤ 1 / 2 := by
              have : 0 ≤ 1 / ((M : ℝ) + 2) := by positivity
              linarith
      norm_num at hM ⊢; linarith
  have hnorm_sub : ‖riemannZeta s - 1‖ ≤ 3 / 4 := by
    rw [hsub]
    have hsumm2 : Summable (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 2) ^ s) := by
      have := hsumm.comp_injective Nat.succ_injective
      refine this.congr fun k => ?_
      simp only [Function.comp_def, Nat.cast_succ]; ring_nf
    have hsummR : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2) ^ 2) := by
      have := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective (Nat.succ_injective.comp Nat.succ_injective)
      refine this.congr fun k => ?_
      simp only [Function.comp_def, one_div, Nat.cast_succ]; ring_nf
    refine (norm_tsum_le_tsum_norm hsumm2.norm).trans ?_
    refine (Summable.tsum_le_tsum (fun k => ?_) hsumm2.norm hsummR).trans htail_sum
    have hcast : ((k : ℂ) + 2) = (((k : ℝ) + 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hsre, Real.rpow_two]
  refine ⟨?_, hnorm_sub⟩
  have hre : |(riemannZeta s).re - 1| ≤ ‖riemannZeta s - 1‖ := by
    simpa using Complex.abs_re_le_norm (riemannZeta s - 1)
  linarith [(abs_le.mp hre).1]

lemma norm_zetaExt_two_add_I_ge (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖zetaExt ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  set s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp [s] at this
  unfold zetaExt
  simp only [hs1, ↓reduceIte, norm_mul]
  have h1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have := Complex.re_le_norm (s - 1)
    simp [s] at this; linarith
  have h2 : (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ :=
    le_trans (re_riemannZeta_two_add_I_ge t).1 (Complex.re_le_norm _)
  nlinarith

/-! #### Part 3C: Phragmen-Lindelof bound on `Gamma w * cos(π w / 2)` and strip `-2 ≤ s.re ≤ 6` -/

lemma sq_norm_cos_pi_quarter_mul_add_I (m : ℤ) (y : ℝ) :
    ‖Complex.cos ((((2 * m + 1 : ℤ) : ℝ) * Real.pi / 4 : ℝ) + (y : ℂ) * Complex.I)‖ ^ 2 =
      Real.cosh (2 * y) / 2 := by
  set θ : ℝ := ((2 * m + 1 : ℤ) : ℝ) * Real.pi / 4
  rw [Complex.cos_add_mul_I, Complex.sq_norm, Complex.normSq_apply]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul, add_zero, Complex.sub_im, Complex.mul_im,
    sub_self, zero_sub]
  have hcos_sq : Real.cos θ ^ 2 = 1 / 2 := by
    have h2 := Real.cos_two_mul θ
    have harg : 2 * θ = Real.pi / 2 + (m : ℝ) * Real.pi := by
      simp only [θ]; push_cast; ring
    rw [harg, Real.cos_add_int_mul_pi, Real.cos_pi_div_two] at h2
    simp only [mul_zero] at h2
    linarith
  have hsin_sq : Real.sin θ ^ 2 = 1 / 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  have hch := Real.cosh_sq y
  have hch2 : Real.cosh (2 * y) = 2 * Real.sinh y ^ 2 + 1 := by
    have := Real.cosh_two_mul y
    linarith
  nlinarith

lemma norm_Gamma_half_add_I_mul_cos (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
      Complex.cos ((Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / 2)‖ =
      Real.sqrt (Real.pi / 2) := by
  set w : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have h1w : 1 - w = starRingEnd ℂ w := by
    apply Complex.ext <;> simp [w]; norm_num
  have href := Complex.Gamma_mul_Gamma_one_sub w
  rw [h1w, Complex.Gamma_conj] at href
  have hsin : Complex.sin ((Real.pi : ℂ) * w) = (Real.cosh (Real.pi * t) : ℂ) := by
    have harg : (Real.pi : ℂ) * w = ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
      simp only [w]; push_cast; ring
    rw [harg, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp
  rw [hsin] at href
  have hnorm_Gsq : ‖Complex.Gamma w‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
    have h1 := congrArg norm href
    rw [norm_mul, Complex.norm_conj, ← sq, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (Real.cosh_pos _).le] at h1
    exact h1
  have hcos_arg : (Real.pi : ℂ) * w / 2 =
      ((((2 * (0 : ℤ) + 1 : ℤ) : ℝ) * Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [w]; push_cast; ring
  have hnorm_Csq : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2 = Real.cosh (Real.pi * t) / 2 := by
    rw [hcos_arg, sq_norm_cos_pi_quarter_mul_add_I 0 (Real.pi * t / 2)]
    congr 2; ring
  have hprod_sq : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ^ 2 = Real.pi / 2 := by
    rw [norm_mul, mul_pow, hnorm_Gsq, hnorm_Csq]
    have hch : Real.cosh (Real.pi * t) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp [hch]
  rw [← Real.sqrt_sq (norm_nonneg _), hprod_sq]

lemma norm_Gamma_mul_cos_strip_le {w : ℂ} (hlo : (1 / 2 : ℝ) ≤ w.re) (hhi : w.re ≤ 7 / 2) :
    ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 4 * ‖w + 1‖ ^ 3 := by
  let f : ℂ → ℂ := fun z => Complex.Gamma z * Complex.cos ((Real.pi : ℂ) * z / 2) / (z + 1) ^ 3
  have hstrip_diff : DifferentiableOn ℂ f {z : ℂ | 0 < z.re} := by
    intro z hz
    have hzpos : 0 < z.re := hz
    have hne_neg : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hz1 : (z + 1) ^ 3 ≠ 0 := by
      intro h; have h0 := eq_zero_of_pow_eq_zero h
      have := congrArg Complex.re h0; simp at this; linarith
    have hdG : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hne_neg
    have hdC : DifferentiableAt ℂ (fun u => Complex.cos ((Real.pi : ℂ) * u / 2)) z := by fun_prop
    have hdD : DifferentiableAt ℂ (fun u => (u + 1) ^ 3) z := by fun_prop
    exact ((hdG.mul hdC).div hdD hz1).differentiableWithinAt
  have hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo (1 / 2) (7 / 2)) := by
    have hsub : closure (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (7 / 2)) ⊆ {z : ℂ | 0 < z.re} := by
      have hcl : closure (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (7 / 2)) ⊆ Complex.re ⁻¹' Set.Icc (1 / 2) (7 / 2) :=
        closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
      intro z hz
      have hmem := hcl hz
      simp only [Set.mem_preimage, Set.mem_Icc] at hmem
      show (0 : ℝ) < z.re
      linarith [hmem.1]
    exact ⟨hstrip_diff.mono (fun z hz => by
        simp only [Set.mem_preimage, Set.mem_Ioo] at hz
        show (0 : ℝ) < z.re
        linarith [hz.1]),
      (hstrip_diff.continuousOn).mono hsub⟩
  have hB : ∃ c < Real.pi / ((7 / 2 : ℝ) - 1 / 2), ∃ B : ℝ,
      f =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo (1 / 2) (7 / 2))]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1 / 2, by linarith [Real.pi_gt_three], 4, ?_⟩
    have hGcont : ContinuousOn Real.Gamma (Set.Icc (1 / 2 : ℝ) (7 / 2)) := fun x hx =>
      (Real.differentiableAt_Gamma (fun m => by
        linarith [hx.1, Nat.cast_nonneg (α := ℝ) m])).continuousAt.continuousWithinAt
    obtain ⟨MG, hMG⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 7 / 2)).exists_bound_of_continuousOn hGcont
    rw [Asymptotics.isBigO_iff]
    refine ⟨max MG 0 + 1, ?_⟩
    have hmem : Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (7 / 2) ∈
        comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo (1 / 2) (7 / 2)) :=
      Filter.mem_inf_of_right (Filter.mem_principal_self _)
    filter_upwards [hmem] with z hz
    have hz' : (1 / 2 : ℝ) < z.re ∧ z.re < 7 / 2 := hz
    have hGz : ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
      rw [Complex.Gamma_eq_integral (by linarith [hz'.1]), Real.Gamma_eq_integral (by linarith [hz'.1])]
      unfold Complex.GammaIntegral
      refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := Set.mem_Ioi.mp hx
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    have hGz_le : Real.Gamma z.re ≤ max MG 0 + 1 := by
      have h1 := hMG z.re ⟨hz'.1.le, hz'.2.le⟩
      rw [Real.norm_eq_abs] at h1
      linarith [le_abs_self (Real.Gamma z.re), le_max_left MG 0]
    have hcos_le : ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ ≤ Real.exp (Real.pi * |z.im| / 2) := by
      rw [Complex.cos]
      have htri : ‖(Complex.exp ((Real.pi : ℂ) * z / 2 * Complex.I) +
          Complex.exp (-((Real.pi : ℂ) * z / 2) * Complex.I)) / 2‖ ≤
          (‖Complex.exp ((Real.pi : ℂ) * z / 2 * Complex.I)‖ +
           ‖Complex.exp (-((Real.pi : ℂ) * z / 2) * Complex.I)‖) / 2 := by
        rw [norm_div, Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      refine htri.trans ?_
      rw [Complex.norm_exp, Complex.norm_exp]
      have hre1 : ((Real.pi : ℂ) * z / 2 * Complex.I).re = -(Real.pi * z.im / 2) := by
        simp [Complex.mul_re, Complex.div_ofNat_re, Complex.mul_im, Complex.div_ofNat_im]
      have hre2 : (-((Real.pi : ℂ) * z / 2) * Complex.I).re = Real.pi * z.im / 2 := by
        simp [Complex.mul_re, Complex.div_ofNat_re, Complex.mul_im, Complex.div_ofNat_im]
      rw [hre1, hre2]
      have ha1 : -(Real.pi * z.im / 2) ≤ Real.pi * |z.im| / 2 := by
        have := neg_le_abs z.im
        nlinarith [Real.pi_pos]
      have ha2 : Real.pi * z.im / 2 ≤ Real.pi * |z.im| / 2 := by
        have := le_abs_self z.im
        nlinarith [Real.pi_pos]
      have he1 := Real.exp_le_exp.mpr ha1
      have he2 := Real.exp_le_exp.mpr ha2
      linarith
    have hden_ge : (1 : ℝ) ≤ ‖(z + 1) ^ 3‖ := by
      rw [norm_pow]
      have h1 : (1 : ℝ) ≤ ‖z + 1‖ := by
        have := Complex.re_le_norm (z + 1)
        simp only [Complex.add_re, Complex.one_re] at this
        linarith [hz'.1]
      exact one_le_pow₀ h1
    have hexp_le : Real.exp (Real.pi * |z.im| / 2) ≤ Real.exp (4 * Real.exp ((1 / 2 : ℝ) * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have h1 := Real.add_one_le_exp ((1 / 2 : ℝ) * |z.im|)
      have hpi := Real.pi_lt_four
      nlinarith [abs_nonneg z.im]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    calc ‖f z‖ = ‖Complex.Gamma z‖ * ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ / ‖(z + 1) ^ 3‖ := by
          simp only [f, norm_div, norm_mul]
      _ ≤ ‖Complex.Gamma z‖ * ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ :=
          div_le_self (by positivity) hden_ge
      _ ≤ (max MG 0 + 1) * Real.exp (Real.pi * |z.im| / 2) :=
          mul_le_mul (hGz.trans hGz_le) hcos_le (norm_nonneg _) (by positivity)
      _ ≤ (max MG 0 + 1) * Real.exp (4 * Real.exp ((1 / 2 : ℝ) * |z.im|)) := by gcongr
  have hsqrt_le : Real.sqrt (Real.pi / 2) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith [Real.pi_lt_four]
  have hle_a : ∀ z : ℂ, z.re = 1 / 2 → ‖f z‖ ≤ 4 := by
    intro z hz
    have hzeq : z = (1 / 2 : ℂ) + Complex.I * (z.im : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [show f z = Complex.Gamma z * Complex.cos ((Real.pi : ℂ) * z / 2) / (z + 1) ^ 3 from rfl,
      norm_div, hzeq, norm_Gamma_half_add_I_mul_cos]
    have hden : (1 : ℝ) ≤ ‖((1 / 2 : ℂ) + Complex.I * (z.im : ℂ) + 1) ^ 3‖ := by
      rw [norm_pow]
      have h1 : (1 : ℝ) ≤ ‖(1 / 2 : ℂ) + Complex.I * (z.im : ℂ) + 1‖ := by
        have := Complex.re_le_norm ((1 / 2 : ℂ) + Complex.I * (z.im : ℂ) + 1)
        simp at this; norm_num at this; linarith
      exact one_le_pow₀ h1
    exact (div_le_self (Real.sqrt_nonneg _) hden).trans hsqrt_le
  have hle_b : ∀ z : ℂ, z.re = 7 / 2 → ‖f z‖ ≤ 4 := by
    intro z hz
    set t := z.im
    set u : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
    have hzeq : z = u + 3 := by
      apply Complex.ext <;> simp [u, t, hz]; norm_num
    have hG3 : Complex.Gamma z = (u + 2) * (u + 1) * u * Complex.Gamma u := by
      have hu0 : u ≠ 0 := by intro h; have := congrArg Complex.re h; simp [u] at this
      have hu1 : u + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp [u] at this; norm_num at this
      have hu2 : u + 2 ≠ 0 := by intro h; have := congrArg Complex.re h; simp [u] at this; norm_num at this
      rw [hzeq, show u + 3 = (u + 2) + 1 by ring, Complex.Gamma_add_one (u + 2) hu2,
        show u + 2 = (u + 1) + 1 by ring, Complex.Gamma_add_one (u + 1) hu1,
        Complex.Gamma_add_one u hu0]
      ring
    have hcos_eq : ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ = ‖Complex.cos ((Real.pi : ℂ) * u / 2)‖ := by
      have h1 : (Real.pi : ℂ) * z / 2 =
          ((((2 * (3 : ℤ) + 1 : ℤ) : ℝ) * Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
        rw [hzeq]; simp only [u]; push_cast; ring
      have h2 : (Real.pi : ℂ) * u / 2 =
          ((((2 * (0 : ℤ) + 1 : ℤ) : ℝ) * Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
        simp only [u]; push_cast; ring
      have hsq1 : ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ ^ 2 = Real.cosh (Real.pi * t) / 2 := by
        rw [h1, sq_norm_cos_pi_quarter_mul_add_I 3 (Real.pi * t / 2)]; congr 2; ring
      have hsq2 : ‖Complex.cos ((Real.pi : ℂ) * u / 2)‖ ^ 2 = Real.cosh (Real.pi * t) / 2 := by
        rw [h2, sq_norm_cos_pi_quarter_mul_add_I 0 (Real.pi * t / 2)]; congr 2; ring
      nlinarith [norm_nonneg (Complex.cos ((Real.pi : ℂ) * z / 2)),
        norm_nonneg (Complex.cos ((Real.pi : ℂ) * u / 2))]
    have hnorm_le_re : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ‖(a : ℂ) + Complex.I * (t : ℂ)‖ ≤ ‖(b : ℂ) + Complex.I * (t : ℂ)‖ := by
      intro a b ha hab
      have hsq : ‖(a : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 ≤ ‖(b : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im, zero_add]
        nlinarith
      nlinarith [norm_nonneg ((a : ℂ) + Complex.I * (t : ℂ)), norm_nonneg ((b : ℂ) + Complex.I * (t : ℂ))]
    have hz1_eq : z + 1 = ((9 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
      rw [hzeq]; simp only [u]; push_cast; ring
    have hu_le : ‖u‖ ≤ ‖z + 1‖ := by
      rw [hz1_eq]; simpa [u] using hnorm_le_re (1 / 2) (9 / 2) (by norm_num) (by norm_num)
    have hu1_le : ‖u + 1‖ ≤ ‖z + 1‖ := by
      rw [hz1_eq]
      have : u + 1 = ((3 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by simp only [u]; push_cast; ring
      rw [this]; exact hnorm_le_re (3 / 2) (9 / 2) (by norm_num) (by norm_num)
    have hu2_le : ‖u + 2‖ ≤ ‖z + 1‖ := by
      rw [hz1_eq]
      have : u + 2 = ((5 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by simp only [u]; push_cast; ring
      rw [this]; exact hnorm_le_re (5 / 2) (9 / 2) (by norm_num) (by norm_num)
    have hz1_pos : 0 < ‖z + 1‖ := by
      have := Complex.re_le_norm (z + 1)
      simp only [Complex.add_re, Complex.one_re, hz] at this; linarith
    have hnum : ‖Complex.Gamma z * Complex.cos ((Real.pi : ℂ) * z / 2)‖ ≤ 4 * ‖z + 1‖ ^ 3 := by
      calc ‖Complex.Gamma z * Complex.cos ((Real.pi : ℂ) * z / 2)‖
          = ‖u + 2‖ * ‖u + 1‖ * ‖u‖ * ‖Complex.Gamma u * Complex.cos ((Real.pi : ℂ) * u / 2)‖ := by
            rw [norm_mul, hG3, hcos_eq, norm_mul, norm_mul, norm_mul, norm_mul]; ring
        _ = ‖u + 2‖ * ‖u + 1‖ * ‖u‖ * Real.sqrt (Real.pi / 2) := by
            rw [norm_Gamma_half_add_I_mul_cos t]
        _ ≤ ‖z + 1‖ * ‖z + 1‖ * ‖z + 1‖ * 4 := by gcongr
        _ = 4 * ‖z + 1‖ ^ 3 := by ring
    simp only [f, norm_div, norm_pow]
    rw [div_le_iff₀ (pow_pos hz1_pos 3)]
    exact hnum
  have hpl := PhragmenLindelof.vertical_strip hfd hB hle_a hle_b hlo hhi
  have hw1_pos : 0 < ‖w + 1‖ := by
    have := Complex.re_le_norm (w + 1)
    simp only [Complex.add_re, Complex.one_re] at this; linarith
  simp only [f, norm_div, norm_pow] at hpl
  rwa [div_le_iff₀ (pow_pos hw1_pos 3)] at hpl

theorem norm_zetaExt_strip_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 6 →
      ‖zetaExt s‖ ≤ C * (2 + |s.im|) ^ 6 := by
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    differentiable_zetaExt.continuous.continuousOn
  refine ⟨max (max M0 0) 200000, by positivity, fun s hlo hhi => ?_⟩
  have hge2 : (2 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
  have hpow6 : (1 : ℝ) ≤ (2 + |s.im|) ^ 6 := one_le_pow₀ (by linarith)
  by_cases hright : (1 / 4 : ℝ) ≤ s.re
  · have h1 := norm_zetaExt_right_le hright hhi
    have h26 : (2 + |s.im|) ^ 2 ≤ (2 + |s.im|) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖zetaExt s‖ ≤ 400 * (2 + |s.im|) ^ 2 := h1
      _ ≤ 400 * (2 + |s.im|) ^ 6 := by gcongr
      _ ≤ max (max M0 0) 200000 * (2 + |s.im|) ^ 6 := by
          gcongr; exact le_trans (by norm_num) (le_max_right _ _)
  · have hlt : s.re < 1 / 4 := not_le.mp hright
    by_cases hball : ‖s‖ ≤ 1 / 2
    · have hmem : s ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hball
      have h1 := hM0 s hmem
      calc ‖zetaExt s‖ ≤ M0 := h1
        _ ≤ max M0 0 := le_max_left _ _
        _ ≤ max (max M0 0) 200000 := le_max_left _ _
        _ = max (max M0 0) 200000 * 1 := (mul_one _).symm
        _ ≤ max (max M0 0) 200000 * (2 + |s.im|) ^ 6 := by gcongr
    · have hgt : 1 / 2 < ‖s‖ := not_le.mp hball
      set w : ℂ := 1 - s
      have hw_re : w.re = 1 - s.re := by simp [w]
      have hw_im : w.im = -s.im := by simp [w]
      have hw_lo : (1 / 2 : ℝ) ≤ w.re := by linarith
      have hw_hi : w.re ≤ 7 / 2 := by linarith
      have hw_nneg : ∀ n : ℕ, w ≠ -(n : ℂ) := fun n h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hw1 : w ≠ 1 := by
        intro h; have hs0 : s = 0 := by linear_combination -h
        rw [hs0, norm_zero] at hgt; norm_num at hgt
      have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hlt; norm_num at hlt
      have h1w : 1 - w = s := by simp [w]
      have hfe := riemannZeta_one_sub hw_nneg hw1
      rw [h1w] at hfe
      have hzeta_w : riemannZeta w = zetaExt w / (w - 1) := by
        unfold zetaExt
        simp only [hw1, ↓reduceIte]
        have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
        field_simp [hw1']
      have hEq : zetaExt s =
          (s - 1) * (2 * (2 * (Real.pi : ℂ)) ^ (-w)) *
          (Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)) *
          (zetaExt w / (w - 1)) := by
        conv_lhs => unfold zetaExt
        simp only [hs1, ↓reduceIte, hfe, hzeta_w]
        ring
      rw [hEq, norm_mul, norm_mul, norm_mul, norm_div]
      have hb1 : ‖s - 1‖ ≤ 2 * (2 + |s.im|) := by
        calc ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |s.re - 1| + |s.im| := by simp
          _ ≤ 3 + |s.im| := by rw [abs_of_nonpos (by linarith)]; linarith
          _ ≤ 2 * (2 + |s.im|) := by linarith [abs_nonneg s.im]
      have hb2 : ‖2 * (2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 2 := by
        rw [norm_mul, Complex.norm_ofNat]
        have h2p : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
        rw [h2p, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        have hpow_le : (2 * Real.pi) ^ (-w).re ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
          simp only [Complex.neg_re]; linarith
        linarith
      have hb3 : ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ 32 * (2 + |s.im|) ^ 3 := by
        have hgc := norm_Gamma_mul_cos_strip_le hw_lo hw_hi
        have hw1n : ‖w + 1‖ ≤ 2 * (2 + |s.im|) := by
          calc ‖w + 1‖ ≤ |(w + 1).re| + |(w + 1).im| := Complex.norm_le_abs_re_add_abs_im _
            _ = |w.re + 1| + |s.im| := by simp [hw_im]
            _ ≤ 4 + |s.im| := by rw [abs_of_pos (by linarith)]; linarith
            _ ≤ 2 * (2 + |s.im|) := by linarith [abs_nonneg s.im]
        calc ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
            ≤ 4 * ‖w + 1‖ ^ 3 := hgc
          _ ≤ 4 * (2 * (2 + |s.im|)) ^ 3 := by gcongr
          _ = 32 * (2 + |s.im|) ^ 3 := by ring
      have hb4 : ‖zetaExt w‖ / ‖w - 1‖ ≤ 800 * (2 + |s.im|) ^ 2 := by
        have hz_w : ‖zetaExt w‖ ≤ 400 * (2 + |s.im|) ^ 2 := by
          have := norm_zetaExt_right_le (by linarith : (1 / 4 : ℝ) ≤ w.re) (by linarith : w.re ≤ 6)
          simpa [hw_im] using this
        have hwn : 1 / 2 < ‖w - 1‖ := by
          have : w - 1 = -s := by simp [w]
          rw [this, norm_neg]; exact hgt
        rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg (2 + |s.im|)]
      calc ‖s - 1‖ * ‖2 * (2 * (Real.pi : ℂ)) ^ (-w)‖ *
            ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ *
            (‖zetaExt w‖ / ‖w - 1‖)
          ≤ (2 * (2 + |s.im|)) * 2 * (32 * (2 + |s.im|) ^ 3) * (800 * (2 + |s.im|) ^ 2) := by gcongr
        _ = 102400 * (2 + |s.im|) ^ 6 := by ring
        _ ≤ max (max M0 0) 200000 * (2 + |s.im|) ^ 6 := by
            gcongr; exact le_trans (by norm_num) (le_max_right _ _)

end SpectralMod3

end Mod3Section

section Mod4Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators

namespace SpectralMod4

/-! ### Module 4: Jensen Zero Count, Blaschke–Borel–Caratheodory, Good Heights, and `S(T)` -/

noncomputable def zetaExt (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

section WithZetaBounds

variable (hF_diff : Differentiable ℂ zetaExt)
variable (hF_two : ∀ t : ℝ, (1 / 4 : ℝ) ≤ ‖zetaExt ((2 : ℂ) + Complex.I * (t : ℂ))‖)
variable (C3 : ℝ)
variable (hF_bound : ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 6 → ‖zetaExt s‖ ≤ C3 * (2 + |s.im|) ^ 6)

/-! #### Part 4A: Analytic order of `zetaExt` vs `riemannZeta` and Jensen zero count -/

include hF_diff in
lemma zetaExt_analyticOnNhd : AnalyticOnNhd ℂ zetaExt Set.univ :=
  (hF_diff.differentiableOn).analyticOnNhd isOpen_univ

include hF_diff in
lemma analyticOrderAt_zetaExt_ne_top (z : ℂ) : analyticOrderAt zetaExt z ≠ ⊤ := by
  intro htop
  have heq : zetaExt = fun _ => 0 := by
    have han := zetaExt_analyticOnNhd hF_diff
    have heqOn := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero han
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop)
    funext w; exact heqOn (Set.mem_univ w)
  have h1 : zetaExt 1 = 1 := by simp [zetaExt]
  rw [heq] at h1
  norm_num at h1

include hF_diff in
lemma meromorphicOrderAt_zetaExt_ne_top (z : ℂ) : meromorphicOrderAt zetaExt z ≠ ⊤ := by
  rw [(zetaExt_analyticOnNhd hF_diff z (Set.mem_univ z)).meromorphicOrderAt_eq]
  intro h
  have := ENat.map_eq_top_iff.mp h
  exact analyticOrderAt_zetaExt_ne_top hF_diff z this

include hF_diff in
lemma divisor_zetaExt_eq_analyticOrderNatAt {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor zetaExt U z = (analyticOrderNatAt zetaExt z : ℤ) := by
  have han : AnalyticOnNhd ℂ zetaExt U := (zetaExt_analyticOnNhd hF_diff).mono (Set.subset_univ U)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hz]
  have hne := analyticOrderAt_zetaExt_ne_top hF_diff z
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hnat : analyticOrderNatAt zetaExt z = n := by
    simp [analyticOrderNatAt, ← hn]
  rw [← hn, hnat]; rfl

lemma analyticOrderNatAt_zetaExt_eq_riemannZeta {z : ℂ} (hz : z ≠ 1) :
    analyticOrderNatAt zetaExt z = analyticOrderNatAt riemannZeta z := by
  have hev : zetaExt =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp [zetaExt, hw]
  have han_z : AnalyticAt ℂ riemannZeta z :=
    (differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hz))
  have han_lin : AnalyticAt ℂ (fun w : ℂ => w - 1) z := analyticAt_id.sub analyticAt_const
  have h1 : analyticOrderAt zetaExt z = analyticOrderAt ((fun w : ℂ => w - 1) * riemannZeta) z :=
    analyticOrderAt_congr hev
  rw [analyticOrderAt_mul han_lin han_z, han_lin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz),
    zero_add] at h1
  simp only [analyticOrderNatAt, h1]

include hF_diff in
lemma zetaExt_eq_zero_iff_analyticOrderNatAt_pos {z : ℂ} :
    zetaExt z = 0 ↔ 0 < analyticOrderNatAt zetaExt z := by
  have han : AnalyticAt ℂ zetaExt z := zetaExt_analyticOnNhd hF_diff z (Set.mem_univ z)
  have hne := analyticOrderAt_zetaExt_ne_top hF_diff z
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hnat : analyticOrderNatAt zetaExt z = n := by simp [analyticOrderNatAt, ← hn]
  rw [hnat]
  constructor
  · intro hz0
    by_contra h0
    have hn0 : n = 0 := by omega
    rw [hn0, Nat.cast_zero] at hn
    exact han.analyticOrderAt_eq_zero.mp hn.symm hz0
  · intro hpos
    by_contra hne0
    have h0 := han.analyticOrderAt_eq_zero.mpr hne0
    rw [← hn] at h0
    have : n = 0 := by exact_mod_cast h0
    omega

include hF_bound in
lemma norm_zetaExt_ball4_le (t : ℝ) {z : ℂ} (hz : z ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 4) :
    ‖zetaExt z‖ ≤ (max C3 1) * 729 * (2 + |t|) ^ 6 := by
  have hdist : ‖z - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre_diff : |z.re - 2| ≤ 4 := by
    have := Complex.abs_re_le_norm (z - ((2 : ℂ) + Complex.I * (t : ℂ)))
    simp at this; linarith
  have him_diff : |z.im - t| ≤ 4 := by
    have := Complex.abs_im_le_norm (z - ((2 : ℂ) + Complex.I * (t : ℂ)))
    simp at this; linarith
  have hlo : -2 ≤ z.re := by linarith [(abs_le.mp hre_diff).1]
  have hhi : z.re ≤ 6 := by linarith [(abs_le.mp hre_diff).2]
  have him : 2 + |z.im| ≤ 3 * (2 + |t|) := by
    have h1 : |z.im| ≤ |t| + 4 := by
      have := abs_sub_abs_le_abs_sub z.im t; linarith
    linarith [abs_nonneg t]
  calc ‖zetaExt z‖ ≤ C3 * (2 + |z.im|) ^ 6 := hF_bound z hlo hhi
    _ ≤ max C3 1 * (3 * (2 + |t|)) ^ 6 := by
        gcongr; exact le_max_left C3 1
    _ = max C3 1 * 729 * (2 + |t|) ^ 6 := by ring

include hF_diff hF_two C3 hF_bound in
lemma jensen_ball_zero_count (r : ℝ) (hr0 : 0 < r) (hr4 : r < 4) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ t : ℝ,
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) r) u : ℝ)) ≤
        CJ * Real.log (2 + |t|) := by
  set A := max C3 1 * 729 with hAdef
  have hA1 : 1 ≤ A := by
    have : 1 ≤ max C3 1 := le_max_right C3 1
    linarith
  have hlog_den : 0 < Real.log (4 / r) := Real.log_pos ((one_lt_div hr0).mpr hr4)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨(2 * Real.log (4 * A) + 6) / Real.log (4 / r), by
    have h4A : 1 ≤ 4 * A := by linarith
    have : 0 ≤ Real.log (4 * A) := Real.log_nonneg h4A
    positivity, fun t => ?_⟩
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  set M : ℝ := A * (2 + |t|) ^ 6
  have hge2 : (2 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (2 + |t|) ^ 6 := one_le_pow₀ (by linarith)
    nlinarith
  have hFc : zetaExt c ≠ 0 := by
    intro h0; have := hF_two t; rw [h0, norm_zero] at this; norm_num at this
  have hhan : AnalyticOnNhd ℂ zetaExt (Metric.closedBall c |4|) :=
    (zetaExt_analyticOnNhd hF_diff).mono (Set.subset_univ _)
  have hbd : ∀ z ∈ Metric.sphere c |4|, ‖zetaExt z‖ ≤ M := by
    intro z hz
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hz
    exact norm_zetaExt_ball4_le C3 hF_bound t (Metric.sphere_subset_closedBall hz)
  have hj := hhan.sum_divisor_le (r := r) (R := 4)
    (by rw [abs_of_pos hr0]; exact hr0)
    (by rw [abs_of_pos hr0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; exact hr4)
    hM1 hFc hbd
  rw [abs_of_pos hr0] at hj
  have hcast : (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall c r) u : ℝ)) =
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor zetaExt (Metric.closedBall c r) u : ℤ) : ℝ) := by
    exact (map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor zetaExt (Metric.closedBall c r)).finiteSupport (isCompact_closedBall c r))).symm
  rw [hcast]
  refine hj.trans ?_
  have hlog_num : Real.log (M / ‖zetaExt c‖) ≤ (2 * Real.log (4 * A) + 6) * Real.log (2 + |t|) := by
    have hFc_pos : 0 < ‖zetaExt c‖ := lt_of_lt_of_le (by norm_num) (hF_two t)
    have hrat : M / ‖zetaExt c‖ ≤ 4 * A * (2 + |t|) ^ 6 := by
      rw [div_le_iff₀ hFc_pos]
      have := hF_two t
      have hM0 : 0 ≤ M := by positivity
      calc M = 4 * M * (1 / 4) := by ring
        _ ≤ 4 * M * ‖zetaExt c‖ := by gcongr
        _ = 4 * A * (2 + |t|) ^ 6 * ‖zetaExt c‖ := by ring
    have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (2 + |t|) :=
      hlog2.trans (Real.log_le_log (by norm_num) hge2)
    have hlog4A : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
    calc Real.log (M / ‖zetaExt c‖)
        ≤ Real.log (4 * A * (2 + |t|) ^ 6) :=
          Real.log_le_log (div_pos (by positivity) hFc_pos) hrat
      _ = Real.log (4 * A) + 6 * Real.log (2 + |t|) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; ring
      _ ≤ 2 * Real.log (4 * A) * Real.log (2 + |t|) + 6 * Real.log (2 + |t|) := by nlinarith
      _ = (2 * Real.log (4 * A) + 6) * Real.log (2 + |t|) := by ring
  calc Real.log (M / ‖zetaExt c‖) / Real.log (4 / r)
      ≤ ((2 * Real.log (4 * A) + 6) * Real.log (2 + |t|)) / Real.log (4 / r) :=
        div_le_div_of_nonneg_right hlog_num hlog_den.le
    _ = (2 * Real.log (4 * A) + 6) / Real.log (4 / r) * Real.log (2 + |t|) := by ring

/-! #### Part 4B: Holomorphic logarithm on a ball, Blaschke factorization, and Borel-Caratheodory -/

lemma exists_holomorphic_log_on_ball {c : ℂ} {R : ℝ} (hR : 0 < R) {G : ℂ → ℂ}
    (hG_diff : DifferentiableOn ℂ G (Metric.ball c R))
    (hG_ne : ∀ z ∈ Metric.ball c R, G z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball c R) ∧
      h c = 0 ∧
      (∀ z ∈ Metric.ball c R, Complex.exp (h z) = G z / G c) ∧
      (∀ z ∈ Metric.ball c R, deriv h z = logDeriv G z) := by
  have hGc : G c ≠ 0 := hG_ne c (Metric.mem_ball_self hR)
  have hU_sc : IsSimplyConnected (Metric.ball c R) := by
    have : ContractibleSpace (Metric.ball c R) :=
      (convex_ball c R).contractibleSpace (Metric.nonempty_ball.mpr hR)
    exact SimplyConnectedSpace.ofContractible _
  have hg_cont : ContinuousOn (fun z => G z / G c) (Metric.ball c R) :=
    hG_diff.continuousOn.div_const (G c)
  have hg_ne0 : (0 : ℂ) ∉ (fun z => G z / G c) '' Metric.ball c R := by
    rintro ⟨z, hz, hz0⟩
    exact div_ne_zero (hG_ne z hz) hGc hz0
  obtain ⟨f, hf_cont, hf_exp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hU_sc Metric.isOpen_ball hg_cont hg_ne0
  let h : ℂ → ℂ := fun z => f z - f c
  have hhc : h c = 0 := sub_self (f c)
  have hexp : ∀ z ∈ Metric.ball c R, Complex.exp (h z) = G z / G c := by
    intro z hz
    have hfc : Complex.exp (f c) = 1 := by
      have := hf_exp (Metric.mem_ball_self hR)
      simp only [Function.comp_apply, div_self hGc] at this
      exact this
    have hfz : Complex.exp (f z) = G z / G c := hf_exp hz
    rw [show h z = f z - f c from rfl, Complex.exp_sub, hfz, hfc, div_one]
  have hdiff : ∀ z ∈ Metric.ball c R, HasDerivAt h (logDeriv G z) z := by
    intro z hz
    have hGz : G z ≠ 0 := hG_ne z hz
    have hopen : IsOpen (Metric.ball c R) := Metric.isOpen_ball
    have hnhds : Metric.ball c R ∈ 𝓝 z := hopen.mem_nhds hz
    have hcont_at : ContinuousAt h z :=
      (hf_cont.sub continuousOn_const).continuousAt hnhds
    -- Near `z`, `‖h w - h z‖ < π`, so `h w = h z + Complex.log (G w / G z)`!
    have hclose : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball c R ∧ ‖h w - h z‖ < Real.pi ∧
        (G w / G z) ∈ Complex.slitPlane := by
      have h1 : ∀ᶠ w in 𝓝 z, ‖h w - h z‖ < Real.pi := by
        have := hcont_at.tendsto (Metric.ball_mem_nhds (h z) Real.pi_pos)
        filter_upwards [this] with w hw
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have h2 : ∀ᶠ w in 𝓝 z, G w / G z ∈ Complex.slitPlane := by
        have hcontG : ContinuousAt (fun w => G w / G z) z :=
          (hG_diff.continuousOn.div_const (G z)).continuousAt hnhds
        have h1mem : (1 : ℂ) ∈ Complex.slitPlane := by simp
        have hopen_slit : IsOpen Complex.slitPlane := Complex.isOpen_slitPlane
        have := hcontG.tendsto (hopen_slit.mem_nhds (by rwa [div_self hGz]))
        exact this
      filter_upwards [hnhds, h1, h2] with w hw1 hw2 hw3
      exact ⟨hw1, hw2, hw3⟩
    have hev : h =ᶠ[𝓝 z] fun w => h z + Complex.log (G w / G z) := by
      filter_upwards [hclose] with w ⟨hw_ball, hw_pi, _⟩
      have hexp_diff : Complex.exp (h w - h z) = G w / G z := by
        rw [Complex.exp_sub, hexp w hw_ball, hexp z hz]
        field_simp [hGc, hGz]
      have him_lt : |(h w - h z).im| < Real.pi :=
        lt_of_le_of_lt (Complex.abs_im_le_norm _) hw_pi
      have hlog : Complex.log (G w / G z) = h w - h z := by
        rw [← hexp_diff]
        exact Complex.log_exp (by linarith [(abs_lt.mp him_lt).1]) (by linarith [(abs_lt.mp him_lt).2])
      rw [hlog]; ring
    have hdG : HasDerivAt G (deriv G z) z := (hG_diff.differentiableAt hnhds).hasDerivAt
    have hdDiv : HasDerivAt (fun w => G w / G z) (deriv G z / G z) z := hdG.div_const (G z)
    have hlogD : HasDerivAt (fun w => h z + Complex.log (G w / G z))
        ((G z / G z)⁻¹ * (deriv G z / G z)) z := by
      have hcl : HasDerivAt Complex.log (G z / G z)⁻¹ (G z / G z) :=
        Complex.hasDerivAt_log (by rw [div_self hGz]; simp)
      have hcomp := hcl.comp z hdDiv
      simpa [Function.comp_def] using hcomp.const_add (h z)
    have hd' := hlogD.congr_of_eventuallyEq hev
    convert hd' using 1
    rw [div_self hGz, inv_one, one_mul, logDeriv_apply]
  exact ⟨h, fun z hz => (hdiff z hz).differentiableAt.differentiableWithinAt,
    hhc, hexp, fun z hz => (hdiff z hz).deriv⟩

lemma norm_blaschke_denom_eq_on_sphere {c ρ z : ℂ} {R : ℝ} (_hR : 0 < R)
    (hz : z ∈ Metric.sphere c R) :
    ‖(R : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)‖ = R * ‖z - ρ‖ := by
  have hzc : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hR2 : (R : ℂ) ^ 2 = (z - c) * starRingEnd ℂ (z - c) := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hzc]; push_cast; rfl
  rw [hR2]
  have hfac : (z - c) * starRingEnd ℂ (z - c) - starRingEnd ℂ (ρ - c) * (z - c) =
      (z - c) * starRingEnd ℂ (z - ρ) := by
    have : starRingEnd ℂ (z - c) - starRingEnd ℂ (ρ - c) = starRingEnd ℂ (z - ρ) := by
      rw [← map_sub]; congr 1; ring
    rw [← this]; ring
  rw [hfac, norm_mul, hzc, Complex.norm_conj]

include hF_diff hF_two C3 hF_bound in
lemma borel_caratheodory_logDeriv_zetaExt :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ t : ℝ,
      ∃ (R₀ : ℝ) (Z : Finset ℂ),
        (7 / 2 : ℝ) < R₀ ∧ R₀ < 15 / 4 ∧
        (∀ ρ ∈ Z, ρ ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) R₀ ∧ zetaExt ρ = 0) ∧
        (∀ z ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R₀, zetaExt z = 0 → z ∈ Z) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ)) ≤ CB * Real.log (2 + |t|) ∧
        (∀ z ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 3, z ∉ Z →
          ‖logDeriv zetaExt z - ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (z - ρ)‖ ≤
            CB * Real.log (2 + |t|)) := by
  obtain ⟨CJ, hCJ, hJ⟩ := jensen_ball_zero_count hF_diff hF_two C3 hF_bound (15 / 4) (by norm_num) (by norm_num)
  set A := max C3 1 * 729
  have hA1 : 1 ≤ A := by have := le_max_right C3 1; linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set Clog : ℝ := 2 * Real.log (4 * A) + 6
  have hClog0 : 0 ≤ Clog := by
    have : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨max CJ (104 * Clog + 3 * CJ), by positivity, fun t => ?_⟩
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  -- Finite support of divisor in `closedBall c (15/4)`
  have hfin_supp : (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4))).support.Finite :=
    (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4))).finiteSupport (isCompact_closedBall c (15 / 4))
  -- Pick `R₀ ∈ (7/2, 15/4)` not equal to `‖ρ - c‖` for any `ρ ∈ hfin_supp`
  let rads : Set ℝ := (fun ρ : ℂ => ‖ρ - c‖) '' hfin_supp.toFinset
  have hrads_fin : rads.Finite := (hfin_supp.toFinset.finite_toSet).image _
  have hinf : (Set.Ioo (7 / 2 : ℝ) (15 / 4)).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨R₀, hR₀_mem, hR₀_not⟩ := (hinf.sdiff hrads_fin).nonempty
  have hR₀_lo : (7 / 2 : ℝ) < R₀ := hR₀_mem.1
  have hR₀_hi : R₀ < 15 / 4 := hR₀_mem.2
  have hR₀_pos : 0 < R₀ := by linarith
  -- Define `Z` as the zeros of `zetaExt` in `ball c R₀`
  classical
  let Z : Finset ℂ := hfin_supp.toFinset.filter (fun ρ => ρ ∈ Metric.ball c R₀)
  have hZ_spec : ∀ ρ, ρ ∈ Z ↔ ρ ∈ Metric.ball c R₀ ∧ zetaExt ρ = 0 := by
    intro ρ
    simp only [Z, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · rintro ⟨hdiv, hball⟩
      have hcb : ρ ∈ Metric.closedBall c (15 / 4) :=
        Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR₀_hi.le) hball
      rw [divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb] at hdiv
      have hpos : 0 < analyticOrderNatAt zetaExt ρ := by
        have : analyticOrderNatAt zetaExt ρ ≠ 0 := by exact_mod_cast hdiv
        omega
      exact ⟨hball, (zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mpr hpos⟩
    · rintro ⟨hball, hz0⟩
      have hcb : ρ ∈ Metric.closedBall c (15 / 4) :=
        Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR₀_hi.le) hball
      rw [divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb]
      have hpos := (zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mp hz0
      exact ⟨by exact_mod_cast hpos.ne', hball⟩
  have hno_sphere : ∀ z ∈ Metric.closedBall c R₀, zetaExt z = 0 → z ∈ Z := by
    intro z hz hz0
    have hcb : z ∈ Metric.closedBall c (15 / 4) :=
      Metric.closedBall_subset_closedBall hR₀_hi.le hz
    have hmem_supp : z ∈ hfin_supp.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb]
      have hpos := (zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mp hz0
      exact_mod_cast hpos.ne'
    have hne_R0 : ‖z - c‖ ≠ R₀ := fun heq => hR₀_not ⟨z, hmem_supp, heq⟩
    have hle : ‖z - c‖ ≤ R₀ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hlt : ‖z - c‖ < R₀ := lt_of_le_of_ne hle hne_R0
    exact (hZ_spec z).mpr ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hlt, hz0⟩
  -- Pick `R₁ ∈ (R₀, 15/4)` with no zeros in `[R₀, R₁)` and `R₁ * max_{ρ ∈ Z} ‖ρ - c‖ < R₀ ^ 2`
  have hgap : ∃ R₁ : ℝ, R₀ < R₁ ∧ R₁ < 15 / 4 ∧
      (∀ z ∈ Metric.ball c R₁, zetaExt z = 0 → z ∈ Z) ∧
      (∀ ρ ∈ Z, R₁ * ‖ρ - c‖ < R₀ ^ 2) := by
    let out_rads : Finset ℝ := (hfin_supp.toFinset.filter (fun ρ => R₀ < ‖ρ - c‖)).image (fun ρ => ‖ρ - c‖)
    let in_rads : Finset ℝ := Z.image (fun ρ => ‖ρ - c‖)
    have hB1 : ∃ B1 : ℝ, R₀ < B1 ∧ B1 < 15 / 4 ∧ ∀ ρ ∈ hfin_supp.toFinset, R₀ < ‖ρ - c‖ → B1 < ‖ρ - c‖ := by
      by_cases hemp : out_rads.Nonempty
      · have hmin_gt : R₀ < out_rads.min' hemp := by
          obtain ⟨ρ, hρ, hmin⟩ := Finset.mem_image.mp (Finset.min'_mem out_rads hemp)
          rw [← hmin]; exact (Finset.mem_filter.mp hρ).2
        set U := min (out_rads.min' hemp) (15 / 4)
        have hU : R₀ < U := lt_min hmin_gt hR₀_hi
        refine ⟨(R₀ + U) / 2, by linarith, by linarith [min_le_right (out_rads.min' hemp) (15 / 4)], fun ρ hρ hgt => ?_⟩
        have hle := Finset.min'_le out_rads ‖ρ - c‖ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hρ, hgt⟩))
        have : U ≤ ‖ρ - c‖ := le_trans (min_le_left _ _) hle
        linarith
      · refine ⟨(R₀ + 15 / 4) / 2, by linarith, by linarith, fun ρ hρ hgt => ?_⟩
        exfalso; exact hemp ⟨‖ρ - c‖, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hρ, hgt⟩)⟩
    have hB2 : ∃ B2 : ℝ, R₀ < B2 ∧ ∀ ρ ∈ Z, B2 * ‖ρ - c‖ < R₀ ^ 2 := by
      by_cases hemp : in_rads.Nonempty
      · have hmax_lt : in_rads.max' hemp < R₀ := by
          obtain ⟨ρ, hρ, hmax⟩ := Finset.mem_image.mp (Finset.max'_mem in_rads hemp)
          rw [← hmax]
          simpa [Metric.mem_ball, dist_eq_norm] using ((hZ_spec ρ).mp hρ).1
        set m := max (in_rads.max' hemp) (R₀ / 2)
        have hm_pos : 0 < m := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hm_lt : m < R₀ := max_lt hmax_lt (by linarith)
        have hgt : R₀ < R₀ ^ 2 / m := by
          rw [lt_div_iff₀ hm_pos]; nlinarith
        refine ⟨(R₀ + R₀ ^ 2 / m) / 2, by linarith, fun ρ hρ => ?_⟩
        have hle : ‖ρ - c‖ ≤ m :=
          le_trans (Finset.le_max' in_rads ‖ρ - c‖ (Finset.mem_image_of_mem _ hρ)) (le_max_left _ _)
        have hBpos : 0 < (R₀ + R₀ ^ 2 / m) / 2 := by positivity
        calc ((R₀ + R₀ ^ 2 / m) / 2) * ‖ρ - c‖
            ≤ ((R₀ + R₀ ^ 2 / m) / 2) * m := mul_le_mul_of_nonneg_left hle hBpos.le
          _ < (R₀ ^ 2 / m) * m := mul_lt_mul_of_pos_right (by linarith) hm_pos
          _ = R₀ ^ 2 := div_mul_cancel₀ _ hm_pos.ne'
      · refine ⟨R₀ + 1, by linarith, fun ρ hρ => ?_⟩
        exfalso; exact hemp ⟨‖ρ - c‖, Finset.mem_image_of_mem _ hρ⟩
    obtain ⟨B1, hB1_lo, hB1_hi, hB1_out⟩ := hB1
    obtain ⟨B2, hB2_lo, hB2_in⟩ := hB2
    refine ⟨min B1 B2, lt_min hB1_lo hB2_lo, lt_of_le_of_lt (min_le_left _ _) hB1_hi, ?_, ?_⟩
    · intro z hz hz0
      have hcb : z ∈ Metric.closedBall c (15 / 4) :=
        Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (le_trans (min_le_left _ _) hB1_hi.le)) hz
      have hmem : z ∈ hfin_supp.toFinset := by
        rw [Set.Finite.mem_toFinset, Function.mem_support, divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb]
        exact_mod_cast ((zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mp hz0).ne'
      have hlt_min : ‖z - c‖ < min B1 B2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hlt_B1 : ‖z - c‖ < B1 := lt_of_lt_of_le hlt_min (min_le_left _ _)
      have hle_R0 : ‖z - c‖ ≤ R₀ := by
        by_contra hgt; exact not_lt.mpr (hB1_out z hmem (not_le.mp hgt)).le hlt_B1
      exact hno_sphere z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hle_R0) hz0
    · intro ρ hρ
      have hle : min B1 B2 ≤ B2 := min_le_right _ _
      calc min B1 B2 * ‖ρ - c‖ ≤ B2 * ‖ρ - c‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ < R₀ ^ 2 := hB2_in ρ hρ
  obtain ⟨R₁, hR₁_lo, hR₁_hi, hR₁_zeros, hR₁_blaschke⟩ := hgap
  -- Bound `∑_{ρ ∈ Z} m_ρ ≤ CJ * log (2 + |t|)`
  have hsumZ_le : (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ)) ≤ CJ * Real.log (2 + |t|) := by
    have hJ_t := hJ t
    have hfinsum_eq : ∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u : ℝ) =
        ∑ u ∈ hfin_supp.toFinset, (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u : ℝ) := by
      refine finsum_eq_sum_of_support_subset _ fun u hu => ?_
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; apply hu; simp [h0]
    rw [hfinsum_eq] at hJ_t
    have hZsub : Z ⊆ hfin_supp.toFinset := Finset.filter_subset _ _
    have hnn : ∀ u ∈ hfin_supp.toFinset, (0 : ℝ) ≤ (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u : ℝ) := by
      intro u hu
      have hcb : u ∈ Metric.closedBall c (15 / 4) := by
        by_contra hnot
        have h0 : MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u = 0 := by
          unfold MeromorphicOn.divisor; simp [hnot]
        exact (Set.Finite.mem_toFinset hfin_supp).mp hu h0
      rw [divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb]; positivity
    have hsum_sub : ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) ≤
        ∑ u ∈ hfin_supp.toFinset, (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u : ℝ) := by
      calc ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ)
          = ∑ ρ ∈ Z, (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) ρ : ℝ) := by
              refine Finset.sum_congr rfl fun ρ hρ => ?_
              have hcb : ρ ∈ Metric.closedBall c (15 / 4) :=
                Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR₀_hi.le) ((hZ_spec ρ).mp hρ).1
              rw [divisor_zetaExt_eq_analyticOrderNatAt hF_diff hcb]; simp
        _ ≤ ∑ u ∈ hfin_supp.toFinset, (MeromorphicOn.divisor zetaExt (Metric.closedBall c (15 / 4)) u : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hZsub fun u hu _ => hnn u hu
    exact hsum_sub.trans hJ_t
  -- Extract zeros on `Metric.ball c R₁` via `MeromorphicOn.extract_zeros_poles`
  have hdiv_U : ∀ u : ℂ, MeromorphicOn.divisor zetaExt (Metric.ball c R₁) u =
      if u ∈ Z then (analyticOrderNatAt zetaExt u : ℤ) else 0 := by
    intro u
    by_cases hu : u ∈ Metric.ball c R₁
    · rw [divisor_zetaExt_eq_analyticOrderNatAt hF_diff hu]
      by_cases hZ : u ∈ Z
      · simp only [hZ, ↓reduceIte]
      · simp only [hZ, ↓reduceIte]
        have hne0 : zetaExt u ≠ 0 := fun h0 => hZ (hR₁_zeros u hu h0)
        have h0 : analyticOrderNatAt zetaExt u = 0 := by
          by_contra hpos
          exact hne0 ((zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mpr (Nat.pos_of_ne_zero hpos))
        simp [h0]
    · have hnotZ : u ∉ Z := fun hZ => hu (Metric.ball_subset_ball hR₁_lo.le ((hZ_spec u).mp hZ).1)
      simp only [hnotZ, ↓reduceIte]
      unfold MeromorphicOn.divisor; simp [hu]
  have hfin_U : (MeromorphicOn.divisor zetaExt (Metric.ball c R₁)).support.Finite := by
    refine Z.finite_toSet.subset fun u hu => ?_
    rw [Function.mem_support, hdiv_U u] at hu
    by_contra hnot; rw [Finset.mem_coe] at hnot; simp [hnot] at hu
  have hmero_U : MeromorphicOn zetaExt (Metric.ball c R₁) :=
    ((zetaExt_analyticOnNhd hF_diff).mono (Set.subset_univ _)).meromorphicOn
  obtain ⟨g, hg_an, hg_ne, hfac_ae⟩ := hmero_U.extract_zeros_poles
    (fun u => meromorphicOrderAt_zetaExt_ne_top hF_diff u.1) hfin_U
  -- Upgrade `hfac_ae` from `codiscreteWithin` to EVERY point of `Metric.ball c R₁`
  have hfac_eq : ∀ z ∈ Metric.ball c R₁,
      zetaExt z = (∏ ρ ∈ Z, (z - ρ) ^ (analyticOrderNatAt zetaExt ρ)) * g z := by
    let P : ℂ → ℂ := fun z => (∏ ρ ∈ Z, (z - ρ) ^ (analyticOrderNatAt zetaExt ρ)) * g z
    have hP_cont : ContinuousOn P (Metric.ball c R₁) := by
      have hprod_cont : Continuous (fun z : ℂ => ∏ ρ ∈ Z, (z - ρ) ^ (analyticOrderNatAt zetaExt ρ)) := by
        fun_prop
      exact hprod_cont.continuousOn.mul hg_an.continuousOn
    have hF_cont : ContinuousOn zetaExt (Metric.ball c R₁) :=
      hF_diff.continuous.continuousOn
    have hprod_eq : ∀ z : ℂ, (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor zetaExt (Metric.ball c R₁) u) z =
        ∏ ρ ∈ Z, (z - ρ) ^ (analyticOrderNatAt zetaExt ρ) := by
      intro z
      rw [Function.FactorizedRational.finprod_eq_fun hfin_U]
      dsimp only
      rw [finprod_eq_prod_of_mulSupport_subset _ (s := Z) (by
        intro u hu
        rw [Function.mem_mulSupport] at hu
        by_contra hnot
        rw [Finset.mem_coe] at hnot
        rw [hdiv_U u] at hu; simp [hnot] at hu)]
      refine Finset.prod_congr rfl fun ρ hρ => ?_
      rw [hdiv_U ρ]; simp [hρ]
    -- Since `zetaExt = P` on a codiscrete (hence dense!) subset of `ball c R₁`, they agree everywhere on `ball c R₁`
    intro z hz
    have hev : ∀ᶠ w in 𝓝[≠] z, zetaExt w = P w := by
      have hnhds : Metric.ball c R₁ ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
      have hdz := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfac_ae z hz
      filter_upwards [nhdsWithin_le_nhds hnhds, hdz] with w hw_ball hw_eq
      have hw : zetaExt w = ((∏ᶠ u, (· - u) ^ MeromorphicOn.divisor zetaExt (Metric.ball c R₁) u) • g) w :=
        hw_eq.resolve_right (not_not.mpr hw_ball)
      simp only [Pi.smul_apply', smul_eq_mul, hprod_eq w] at hw
      exact hw
    have hlim1 : Tendsto zetaExt (𝓝[≠] z) (𝓝 (zetaExt z)) :=
      (hF_diff.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto P (𝓝[≠] z) (𝓝 (P z)) :=
      (hP_cont.continuousAt (Metric.isOpen_ball.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hlim1.congr' hev) hlim2
  -- Define Blaschke-adjusted function `G` on `Metric.ball c R₁`
  let G : ℂ → ℂ := fun z => g z * ∏ ρ ∈ Z, (((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)) / (R₀ : ℂ)) ^ (analyticOrderNatAt zetaExt ρ)
  have hden_ne : ∀ ρ ∈ Z, ∀ z ∈ Metric.ball c R₁,
      (R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c) ≠ 0 := by
    intro ρ hρ z hz h0
    have heq : (R₀ : ℂ) ^ 2 = starRingEnd ℂ (ρ - c) * (z - c) := sub_eq_zero.mp h0
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR₀_pos.le, norm_mul, Complex.norm_conj] at hn
    have hz_lt : ‖z - c‖ < R₁ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hlt := hR₁_blaschke ρ hρ
    have hle : ‖ρ - c‖ * ‖z - c‖ ≤ R₁ * ‖ρ - c‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hz_lt.le (norm_nonneg _)
    linarith
  have hG_diff : DifferentiableOn ℂ G (Metric.ball c R₁) := by
    have hg_diff : DifferentiableOn ℂ g (Metric.ball c R₁) := hg_an.differentiableOn
    have hprod_diff : DifferentiableOn ℂ
        (fun z => ∏ ρ ∈ Z, (((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)) / (R₀ : ℂ)) ^ (analyticOrderNatAt zetaExt ρ))
        (Metric.ball c R₁) := by
      have h1 : Differentiable ℂ (fun z : ℂ => ∏ ρ ∈ Z, (((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)) / (R₀ : ℂ)) ^ (analyticOrderNatAt zetaExt ρ)) := by
        fun_prop
      exact h1.differentiableOn
    exact hg_diff.mul hprod_diff
  have hG_ne : ∀ z ∈ Metric.ball c R₁, G z ≠ 0 := by
    intro z hz
    apply mul_ne_zero (hg_ne ⟨z, hz⟩)
    rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact pow_ne_zero _ (div_ne_zero (hden_ne ρ hρ z hz) (Complex.ofReal_ne_zero.mpr hR₀_pos.ne'))
  -- On `sphere c R₀`, `‖G z‖ = ‖zetaExt z‖ ≤ M`
  set M : ℝ := A * (2 + |t|) ^ 6
  have hG_sphere : ∀ z ∈ Metric.sphere c R₀, ‖G z‖ = ‖zetaExt z‖ := by
    intro z hz
    have hz_ball1 : z ∈ Metric.ball c R₁ := by
      have : ‖z - c‖ = R₀ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      simpa [Metric.mem_ball, dist_eq_norm, this] using hR₁_lo
    rw [hfac_eq z hz_ball1, norm_mul, norm_mul, mul_comm ‖g z‖]
    congr 1
    rw [norm_prod, norm_prod]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [norm_pow, norm_pow, norm_div, norm_blaschke_denom_eq_on_sphere hR₀_pos hz,
      Complex.norm_real, Real.norm_of_nonneg hR₀_pos.le, mul_div_cancel_left₀ _ hR₀_pos.ne']
  have hG_bound_ball0 : ∀ z ∈ Metric.closedBall c R₀, ‖G z‖ ≤ M := by
    have hsub : Metric.closedBall c R₀ ⊆ Metric.ball c R₁ := Metric.closedBall_subset_ball hR₁_lo
    have hdc : DiffContOnCl ℂ G (Metric.ball c R₀) :=
      ⟨hG_diff.mono (Metric.ball_subset_ball hR₁_lo.le),
        hG_diff.continuousOn.mono (by rw [closure_ball c hR₀_pos.ne']; exact hsub)⟩
    intro z hz
    have hz_cl : z ∈ closure (Metric.ball c R₀) := by rwa [closure_ball c hR₀_pos.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc (fun w hw => ?_) hz_cl
    have hw_sph : w ∈ Metric.sphere c R₀ := by rwa [frontier_ball c hR₀_pos.ne'] at hw
    rw [hG_sphere w hw_sph]
    have hw4 : w ∈ Metric.closedBall c 4 :=
      Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw_sph
    exact norm_zetaExt_ball4_le C3 hF_bound t hw4
  -- At center `c`, `‖G c‖ ≥ ‖zetaExt c‖ ≥ 1/4`
  have hGc_ge : (1 / 4 : ℝ) ≤ ‖G c‖ := by
    have hc_ball1 : c ∈ Metric.ball c R₁ := Metric.mem_ball_self (by linarith)
    have hGc_eq : G c = g c * ∏ ρ ∈ Z, (R₀ : ℂ) ^ (analyticOrderNatAt zetaExt ρ) := by
      simp only [G, sub_self, mul_zero, sub_zero]
      congr 1; refine Finset.prod_congr rfl fun ρ _ => ?_
      rw [sq, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hR₀_pos.ne')]
    have hFc_le : ‖zetaExt c‖ ≤ ‖G c‖ := by
      rw [hfac_eq c hc_ball1, hGc_eq, norm_mul, norm_mul, mul_comm ‖g c‖, norm_prod, norm_prod]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (g c))
      gcongr with ρ hρ
      rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR₀_pos.le]
      have hlt : ‖c - ρ‖ ≤ R₀ := by
        have := ((hZ_spec ρ).mp hρ).1
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
        exact this.le
      exact pow_le_pow_left₀ (norm_nonneg _) hlt _
    exact (hF_two t).trans hFc_le
  -- Holomorphic log `h` of `G / G c` on `Metric.ball c R₀`
  obtain ⟨h, hh_diff, hhc, hh_exp, hh_deriv⟩ :=
    exists_holomorphic_log_on_ball hR₀_pos (hG_diff.mono (Metric.ball_subset_ball hR₁_lo.le))
      (fun z hz => hG_ne z (Metric.ball_subset_ball hR₁_lo.le hz))
  -- Apply Borel-Caratheodory to `w ↦ h (c + w)` on `Metric.ball 0 R₀`
  set B : ℝ := Clog * Real.log (2 + |t|)
  have hB_pos : 0 < B := by
    have hge2 : (2 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (2 + |t|) := hlog2.trans (Real.log_le_log (by norm_num) hge2)
    have hClog_pos : 0 < Clog := by
      have : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hre_h : ∀ z ∈ Metric.ball c R₀, (h z).re ≤ B := by
    intro z hz
    have hnorm_exp : ‖Complex.exp (h z)‖ = ‖G z‖ / ‖G c‖ := by
      rw [hh_exp z hz, norm_div]
    rw [Complex.norm_exp] at hnorm_exp
    have hGz_le : ‖G z‖ ≤ M := hG_bound_ball0 z (Metric.ball_subset_closedBall hz)
    have hGc_pos : 0 < ‖G c‖ := lt_of_lt_of_le (by norm_num) hGc_ge
    have hrat : ‖G z‖ / ‖G c‖ ≤ 4 * A * (2 + |t|) ^ 6 := by
      rw [div_le_iff₀ hGc_pos]
      calc ‖G z‖ ≤ M := hGz_le
        _ = 4 * M * (1 / 4) := by ring
        _ ≤ 4 * M * ‖G c‖ := by gcongr
        _ = 4 * A * (2 + |t|) ^ 6 * ‖G c‖ := by ring
    have hge2 : (2 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (2 + |t|) := hlog2.trans (Real.log_le_log (by norm_num) hge2)
    have hlog4A : 0 ≤ Real.log (4 * A) := Real.log_nonneg (by linarith)
    have hlog_eq : (h z).re = Real.log (‖G z‖ / ‖G c‖) := by
      rw [← hnorm_exp, Real.log_exp]
    rw [hlog_eq]
    have hGz_pos : 0 < ‖G z‖ := norm_pos_iff.mpr (hG_ne z (Metric.ball_subset_ball hR₁_lo.le hz))
    calc Real.log (‖G z‖ / ‖G c‖)
        ≤ Real.log (4 * A * (2 + |t|) ^ 6) := Real.log_le_log (div_pos hGz_pos hGc_pos) hrat
      _ = Real.log (4 * A) + 6 * Real.log (2 + |t|) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; ring
      _ ≤ (2 * Real.log (4 * A) + 6) * Real.log (2 + |t|) := by nlinarith
      _ = B := rfl
  have hh_norm_le : ∀ z ∈ Metric.closedBall c (13 / 4), ‖h z‖ ≤ 26 * B := by
    intro z hz
    have hdiff0 : DifferentiableOn ℂ (fun w => h (c + w)) (Metric.ball 0 R₀) :=
      hh_diff.comp ((differentiable_const c).add differentiable_id).differentiableOn (fun w hw => by
        simpa [Metric.mem_ball, dist_eq_norm] using hw)
    have hmaps : Set.MapsTo (fun w => h (c + w)) (Metric.ball 0 R₀) {u : ℂ | u.re ≤ B} := fun w hw =>
      hre_h (c + w) (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    have hzc_le : ‖z - c‖ ≤ 13 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzc_mem : z - c ∈ Metric.ball (0 : ℂ) R₀ := by
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hzc_le (by linarith)
    have hbc := Complex.borelCaratheodory_zero hB_pos hdiff0 hmaps hR₀_pos hzc_mem (by simp [hhc])
    simp only [add_sub_cancel] at hbc
    refine hbc.trans ?_
    have hden : (1 / 4 : ℝ) ≤ R₀ - ‖z - c‖ := by linarith
    calc 2 * B * ‖z - c‖ / (R₀ - ‖z - c‖)
        ≤ 2 * B * (13 / 4) / (1 / 4) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hzc_le (by positivity))
            (by norm_num) hden
      _ = 26 * B := by ring
  -- Cauchy derivative bound on `Metric.closedBall c 3`: `‖deriv h z‖ ≤ 104 * B`
  have hdh_le : ∀ z ∈ Metric.closedBall c 3, ‖deriv h z‖ ≤ 104 * B := by
    intro z hz
    have hsub : Metric.closedBall z (1 / 4) ⊆ Metric.closedBall c (13 / 4) := by
      intro w hw
      have h1 : ‖w - z‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      have h2 : ‖z - c‖ ≤ 3 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have h3 : ‖w - c‖ ≤ 13 / 4 := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
          _ ≤ 13 / 4 := by linarith
      simpa [Metric.mem_closedBall, dist_eq_norm] using h3
    have hsub_open : Metric.closedBall z (1 / 4) ⊆ Metric.ball c R₀ :=
      hsub.trans (Metric.closedBall_subset_ball (by linarith))
    have hcderiv := cderiv_eq_deriv Metric.isOpen_ball hh_diff (by norm_num : (0 : ℝ) < 1 / 4) hsub_open
    rw [← hcderiv]
    unfold cderiv
    have hbd_sph : ∀ w ∈ Metric.sphere z (1 / 4), ‖((w - z) ^ 2)⁻¹ • h w‖ ≤ 16 * (26 * B) := by
      intro w hw
      have hw_norm : ‖w - z‖ = 1 / 4 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have hhw : ‖h w‖ ≤ 26 * B := hh_norm_le w (hsub (Metric.sphere_subset_closedBall hw))
      rw [norm_smul, norm_inv, norm_pow, hw_norm]
      have : ((1 / 4 : ℝ) ^ 2)⁻¹ = 16 := by norm_num
      rw [this]; exact mul_le_mul_of_nonneg_left hhw (by norm_num)
    have hci := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num : (0 : ℝ) ≤ 1 / 4) hbd_sph
    calc ‖(2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(z, (1 / 4 : ℝ)), ((w - z) ^ 2)⁻¹ • h w‖
        ≤ (1 / 4 : ℝ) * (16 * (26 * B)) := hci
      _ = 104 * B := by ring
  -- Now assemble `logDeriv zetaExt z - ∑_{ρ ∈ Z} m_ρ / (z - ρ)` for `z ∈ closedBall c 3`, `z ∉ Z`!
  refine ⟨R₀, Z, hR₀_lo, hR₀_hi, fun ρ hρ => (hZ_spec ρ).mp hρ, hno_sphere,
    hsumZ_le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith [abs_nonneg t]))), ?_⟩
  intro z hz hnotZ
  have hz_ball0 : z ∈ Metric.ball c R₀ := Metric.closedBall_subset_ball (by linarith) hz
  have hz_ball1 : z ∈ Metric.ball c R₁ := Metric.ball_subset_ball hR₁_lo.le hz_ball0
  have hlogD_eq : logDeriv zetaExt z - ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (z - ρ) =
      deriv h z + ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) *
        (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c))) := by
    -- Express `zetaExt w = G w * ∏_{ρ ∈ Z} (R₀*(w-ρ)/(R₀² - conj(ρ-c)*(w-c)))^{m_ρ}` near `z`
    have hB_fac : ∀ w ∈ Metric.ball c R₁,
        zetaExt w = G w * ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ) := by
      intro w hw
      rw [hfac_eq w hw]
      simp only [G]
      rw [mul_assoc, mul_comm (g w)]
      congr 1
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ρ hρ => ?_
      rw [← mul_pow]
      congr 1
      have hdne := hden_ne ρ hρ w hw
      have hRne : (R₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₀_pos.ne'
      field_simp [hdne, hRne]
    have hnhds : Metric.ball c R₁ ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz_ball1
    have hev : zetaExt =ᶠ[𝓝 z] fun w =>
        G w * ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ) :=
      Filter.eventually_of_mem hnhds hB_fac
    have hld_congr : logDeriv zetaExt z = logDeriv (fun w =>
        G w * ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) z := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hld_congr]
    have hterm_ne : ∀ ρ ∈ Z, ((R₀ : ℂ) * (z - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c))) ^ (analyticOrderNatAt zetaExt ρ) ≠ 0 := by
      intro ρ hρ
      have hzr : z - ρ ≠ 0 := sub_ne_zero.mpr (fun heq => hnotZ (heq ▸ hρ))
      exact pow_ne_zero _ (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hR₀_pos.ne') hzr)
        (hden_ne ρ hρ z hz_ball1))
    have hterm_diff : ∀ ρ ∈ Z, DifferentiableAt ℂ
        (fun w => ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) z := by
      intro ρ hρ
      have h1 : DifferentiableAt ℂ (fun w => (R₀ : ℂ) * (w - ρ)) z := by fun_prop
      have h2 : DifferentiableAt ℂ (fun w => (R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c)) z := by fun_prop
      exact (h1.div h2 (hden_ne ρ hρ z hz_ball1)).pow _
    have hprod_ne : (∏ ρ ∈ Z, ((R₀ : ℂ) * (z - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c))) ^ (analyticOrderNatAt zetaExt ρ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hterm_ne
    have hprod_diff : DifferentiableAt ℂ
        (fun w => ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) z := by
      have heq : (fun w => ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) =
          ∏ ρ ∈ Z, (fun w => ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) := by
        ext w; simp [Finset.prod_apply]
      rw [heq]; exact DifferentiableAt.finsetProd hterm_diff
    rw [logDeriv_fun_mul (f := G)
        (g := fun w => ∏ ρ ∈ Z, ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ))
        z (hG_ne z hz_ball1) hprod_ne (hG_diff.differentiableAt hnhds) hprod_diff,
      logDeriv_fun_prod (f := fun ρ w => ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ))
        hterm_ne hterm_diff, ← hh_deriv z hz_ball0]
    have hterm_ld : ∀ ρ ∈ Z,
        logDeriv (fun w => ((R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c))) ^ (analyticOrderNatAt zetaExt ρ)) z =
          (analyticOrderNatAt zetaExt ρ : ℂ) / (z - ρ) +
          (analyticOrderNatAt zetaExt ρ : ℂ) * (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c))) := by
      intro ρ hρ
      have hzr : z - ρ ≠ 0 := sub_ne_zero.mpr (fun heq => hnotZ (heq ▸ hρ))
      have hdne := hden_ne ρ hρ z hz_ball1
      have hRne : (R₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₀_pos.ne'
      have hnum_d : HasDerivAt (fun w : ℂ => (R₀ : ℂ) * (w - ρ)) (R₀ : ℂ) z := by
        simpa using ((hasDerivAt_id z).sub_const ρ).const_mul (R₀ : ℂ)
      have hden_d : HasDerivAt (fun w : ℂ => (R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c)) (-(starRingEnd ℂ (ρ - c))) z := by
        have h1 : HasDerivAt (fun w : ℂ => starRingEnd ℂ (ρ - c) * (w - c)) (starRingEnd ℂ (ρ - c)) z := by
          simpa using ((hasDerivAt_id z).sub_const c).const_mul (starRingEnd ℂ (ρ - c))
        exact h1.const_sub ((R₀ : ℂ) ^ 2)
      have hq_hd : HasDerivAt
          (fun w : ℂ => (R₀ : ℂ) * (w - ρ) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (w - c)))
          (((R₀ : ℂ) * ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)) -
            ((R₀ : ℂ) * (z - ρ)) * (-(starRingEnd ℂ (ρ - c)))) /
            ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)) ^ 2) z :=
        hnum_d.div hden_d hdne
      rw [logDeriv_fun_pow hq_hd.differentiableAt, logDeriv_apply, hq_hd.deriv]
      field_simp [hRne, hzr, hdne]; ring
    rw [Finset.sum_congr rfl hterm_ld, Finset.sum_add_distrib]
    ring
  rw [hlogD_eq]
  have hsecond : ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) *
      (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)))‖ ≤
      3 * CJ * Real.log (2 + |t|) := by
    calc _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt zetaExt ρ : ℂ) *
            (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, 3 * (analyticOrderNatAt zetaExt ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_conj]
          have hρ_lt : ‖ρ - c‖ < R₀ := by simpa [Metric.mem_ball, dist_eq_norm] using ((hZ_spec ρ).mp hρ).1
          have hz_le : ‖z - c‖ ≤ 3 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
          have hden_ge : (7 / 4 : ℝ) ≤ ‖(R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)‖ := by
            have htri := norm_sub_norm_le ((R₀ : ℂ) ^ 2) (starRingEnd ℂ (ρ - c) * (z - c))
            rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR₀_pos.le, norm_mul, Complex.norm_conj] at htri
            have hmul : ‖ρ - c‖ * ‖z - c‖ ≤ R₀ * 3 := mul_le_mul hρ_lt.le hz_le (norm_nonneg _) hR₀_pos.le
            nlinarith
          have hfrac : ‖ρ - c‖ / ‖(R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)‖ ≤ 3 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
          calc (analyticOrderNatAt zetaExt ρ : ℝ) * (‖ρ - c‖ / ‖(R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)‖)
              ≤ (analyticOrderNatAt zetaExt ρ : ℝ) * 3 := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
            _ = 3 * (analyticOrderNatAt zetaExt ρ : ℝ) := by ring
      _ = 3 * ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * (CJ * Real.log (2 + |t|)) := mul_le_mul_of_nonneg_left hsumZ_le (by norm_num)
      _ = 3 * CJ * Real.log (2 + |t|) := by ring
  calc ‖deriv h z + ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) *
        (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)))‖
      ≤ ‖deriv h z‖ + ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) *
        (starRingEnd ℂ (ρ - c) / ((R₀ : ℂ) ^ 2 - starRingEnd ℂ (ρ - c) * (z - c)))‖ := norm_add_le _ _
    _ ≤ 104 * B + 3 * CJ * Real.log (2 + |t|) := add_le_add (hdh_le z hz) hsecond
    _ = (104 * Clog + 3 * CJ) * Real.log (2 + |t|) := by simp only [B]; ring
    _ ≤ max CJ (104 * Clog + 3 * CJ) * Real.log (2 + |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by linarith [abs_nonneg t]))

/-! #### Part 4C: Corollaries — Good Heights and Horizontal `S(T)` Bound -/

lemma logDeriv_zetaExt_eq_riemannZeta {s : ℂ} (hs1 : s ≠ 1) (hsz : riemannZeta s ≠ 0) :
    logDeriv zetaExt s = (s - 1)⁻¹ + logDeriv riemannZeta s := by
  have hev : zetaExt =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
    simp [zetaExt, hw]
  have h1 : logDeriv zetaExt s = logDeriv (fun w : ℂ => (w - 1) * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [h1, logDeriv_fun_mul (f := fun w : ℂ => w - 1) (g := riemannZeta) s (sub_ne_zero.mpr hs1) hsz
    (differentiableAt_id.sub (differentiableAt_const 1)) (differentiableAt_riemannZeta hs1)]
  congr 1
  have hd1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := by simpa using (hasDerivAt_id s).sub_const (1 : ℂ)
  rw [logDeriv_apply, hd1.deriv, one_div]

include hF_diff hF_two C3 hF_bound in
theorem exists_good_height :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀ k : ℤ, 2 ≤ |k| →
      ∃ H : ℝ, (k : ℝ) ≤ H ∧ H ≤ (k : ℝ) + 1 ∧
        (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
          riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤
            CH * (Real.log (2 + |H|)) ^ 2) := by
  obtain ⟨CB, hCB, hBC⟩ := borel_caratheodory_logDeriv_zetaExt hF_diff hF_two C3 hF_bound
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨8 * (CB + 1) ^ 2 + 16, by positivity, fun k hk => ?_⟩
  set t0 : ℝ := (k : ℝ) + 1 / 2 with ht0
  obtain ⟨R₀, Z, hR₀_lo, hR₀_hi, hZ_mem, hZ_all, hZ_sum, hZ_ld⟩ := hBC t0
  -- Pigeonhole on `N + 1` disjoint intervals inside `[k, k + 1]` where `N = Z.card`
  set N : ℕ := Z.card
  let slot : ℕ → Set ℝ := fun j => Set.Ioo ((k : ℝ) + (j : ℝ) / ((N : ℝ) + 1)) ((k : ℝ) + ((j : ℝ) + 1) / ((N : ℝ) + 1))
  have hex_slot : ∃ j ∈ Finset.range (N + 1), ∀ ρ ∈ Z, ρ.im ∉ slot j := by
    by_contra hall
    push Not at hall
    have hcard_le : (Finset.range (N + 1)).card ≤ Z.card := by
      have hf : ∀ j : ℕ, ∃ ρ : ℂ, j ∈ Finset.range (N + 1) → ρ ∈ Z ∧ ρ.im ∈ slot j := fun j =>
        if hj : j ∈ Finset.range (N + 1) then
          let ⟨ρ, h1, h2⟩ := hall j hj
          ⟨ρ, fun _ => ⟨h1, h2⟩⟩
        else ⟨0, fun h => (hj h).elim⟩
      choose f hf using hf
      have hinj : Set.InjOn f (Finset.range (N + 1) : Set ℕ) := by
        intro j1 hj1 j2 hj2 heq
        have h1 := (hf j1 (Finset.mem_coe.mp hj1)).2
        have h2 := (hf j2 (Finset.mem_coe.mp hj2)).2
        rw [heq] at h1
        have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (j1 : ℝ) + 1 ≤ (j2 : ℝ) := by exact_mod_cast hlt
          have : ((j1 : ℝ) + 1) / ((N : ℝ) + 1) ≤ (j2 : ℝ) / ((N : ℝ) + 1) :=
            div_le_div_of_nonneg_right hle hNpos.le
          linarith [h1.2, h2.1]
        · have hle : (j2 : ℝ) + 1 ≤ (j1 : ℝ) := by exact_mod_cast hgt
          have : ((j2 : ℝ) + 1) / ((N : ℝ) + 1) ≤ (j1 : ℝ) / ((N : ℝ) + 1) :=
            div_le_div_of_nonneg_right hle hNpos.le
          linarith [h2.2, h1.1]
      calc (Finset.range (N + 1)).card = ((Finset.range (N + 1)).image f).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ Z.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun j hj => (hf j hj).1)
    rw [Finset.card_range] at hcard_le
    omega
  obtain ⟨j, hj_mem, hj_empty⟩ := hex_slot
  have hj_lt : j < N + 1 := Finset.mem_range.mp hj_mem
  set H : ℝ := (k : ℝ) + ((j : ℝ) + 1 / 2) / ((N : ℝ) + 1)
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hHk_lo : (k : ℝ) ≤ H := by
    have : 0 ≤ ((j : ℝ) + 1 / 2) / ((N : ℝ) + 1) := by positivity
    linarith
  have hHk_hi : H ≤ (k : ℝ) + 1 := by
    have hjle : (j : ℝ) + 1 / 2 ≤ (N : ℝ) + 1 := by
      have : (j : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast hj_lt
      linarith
    have : ((j : ℝ) + 1 / 2) / ((N : ℝ) + 1) ≤ 1 := (div_le_one hNpos).mpr hjle
    linarith
  have hH_dist : ∀ ρ ∈ Z, 1 / (2 * ((N : ℝ) + 1)) ≤ |H - ρ.im| := by
    intro ρ hρ
    have hnot := hj_empty ρ hρ
    simp only [slot, Set.mem_Ioo, not_and_or, not_lt] at hnot
    rcases hnot with hlo | hhi
    · rw [abs_of_nonneg (by
        have : (j : ℝ) / ((N : ℝ) + 1) ≤ ((j : ℝ) + 1 / 2) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right (by linarith) hNpos.le
        linarith)]
      have heq : H - ((k : ℝ) + (j : ℝ) / ((N : ℝ) + 1)) = 1 / (2 * ((N : ℝ) + 1)) := by
        simp only [H]; field_simp [hNpos.ne']; ring
      linarith
    · rw [abs_of_nonpos (by
        have : ((j : ℝ) + 1 / 2) / ((N : ℝ) + 1) ≤ ((j : ℝ) + 1) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right (by linarith) hNpos.le
        linarith)]
      have heq : ((k : ℝ) + ((j : ℝ) + 1) / ((N : ℝ) + 1)) - H = 1 / (2 * ((N : ℝ) + 1)) := by
        simp only [H]; field_simp [hNpos.ne']; ring
      linarith
  have hH_abs_ge1 : (1 : ℝ) ≤ |H| := by
    have hk_abs : (2 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hk
    rcases le_or_gt 0 (k : ℝ) with hkp | hkn
    · rw [abs_of_nonneg hkp] at hk_abs
      rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_neg hkn] at hk_abs
      rw [abs_of_neg (by linarith)]; linarith
  have hlog_comp : Real.log (2 + |t0|) ≤ 2 * Real.log (2 + |H|) := by
    have ht0_le : 2 + |t0| ≤ (2 + |H|) ^ 2 := by
      have hdiff : |t0 - H| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [ht0, hHk_lo, hHk_hi]
      have : |t0| ≤ |H| + 1 / 2 := by have := abs_sub_abs_le_abs_sub t0 H; linarith
      nlinarith [abs_nonneg H]
    calc Real.log (2 + |t0|) ≤ Real.log ((2 + |H|) ^ 2) := Real.log_le_log (by positivity) ht0_le
      _ = 2 * Real.log (2 + |H|) := by rw [Real.log_pow]; ring
  have hN_le : (N : ℝ) ≤ CB * Real.log (2 + |t0|) := by
    have h1 : (N : ℝ) = ∑ _ρ ∈ Z, (1 : ℝ) := by simp [N]
    rw [h1]
    refine (Finset.sum_le_sum fun ρ hρ => ?_).trans hZ_sum
    have hpos : 0 < analyticOrderNatAt zetaExt ρ :=
      (zetaExt_eq_zero_iff_analyticOrderNatAt_pos hF_diff).mp ((hZ_mem ρ hρ).2)
    exact_mod_cast hpos
  refine ⟨H, hHk_lo, hHk_hi, fun σ hσlo hσhi => ?_⟩
  set s : ℂ := (σ : ℂ) + Complex.I * (H : ℂ)
  have hs_in3 : s ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t0 : ℂ)) 3 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hre : (s - ((2 : ℂ) + Complex.I * (t0 : ℂ))).re = σ - 2 := by simp [s]
    have him : (s - ((2 : ℂ) + Complex.I * (t0 : ℂ))).im = H - t0 := by simp [s]
    have hsq : ‖s - ((2 : ℂ) + Complex.I * (t0 : ℂ))‖ ^ 2 ≤ 9 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      have h1 : |σ - 2| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith
      have h2 : |H - t0| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [ht0, hHk_lo, hHk_hi]
      have h1sq : (σ - 2) ^ 2 ≤ (5 / 2) ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg (σ - 2)]
      have h2sq : (H - t0) ^ 2 ≤ (1 / 2) ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg (H - t0)]
      nlinarith
    nlinarith [norm_nonneg (s - ((2 : ℂ) + Complex.I * (t0 : ℂ)))]
  have hs_notZ : s ∉ Z := by
    intro hmem
    have := hH_dist s hmem
    have hsim : s.im = H := by simp [s]
    rw [hsim, sub_self, abs_zero] at this
    linarith [div_pos one_pos (by positivity : (0 : ℝ) < 2 * ((N : ℝ) + 1))]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [s] at this
    rw [this, abs_zero] at hH_abs_ge1; norm_num at hH_abs_ge1
  have hzne : riemannZeta s ≠ 0 := by
    intro hz0
    have hF0 : zetaExt s = 0 := by simp [zetaExt, hs1, hz0]
    exact hs_notZ (hZ_all s (Metric.closedBall_subset_closedBall (by linarith) hs_in3) hF0)
  refine ⟨hzne, ?_⟩
  have hld_rel := logDeriv_zetaExt_eq_riemannZeta hs1 hzne
  have hld_bound := hZ_ld s hs_in3 hs_notZ
  have hsum_poles : ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖ ≤
      2 * ((N : ℝ) + 1) * (CB * Real.log (2 + |t0|)) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, 2 * ((N : ℝ) + 1) * (analyticOrderNatAt zetaExt ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_div, Complex.norm_natCast]
          have hlb : 1 / (2 * ((N : ℝ) + 1)) ≤ ‖s - ρ‖ := by
            have h1 := hH_dist ρ hρ
            have h2 := Complex.abs_im_le_norm (s - ρ)
            simp [s] at h2
            exact h1.trans h2
          rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlb)]
          have hpos : (0 : ℝ) ≤ (analyticOrderNatAt zetaExt ρ : ℝ) := Nat.cast_nonneg _
          calc (analyticOrderNatAt zetaExt ρ : ℝ)
              = 2 * ((N : ℝ) + 1) * (analyticOrderNatAt zetaExt ρ : ℝ) * (1 / (2 * ((N : ℝ) + 1))) := by
                field_simp [hNpos.ne']
            _ ≤ 2 * ((N : ℝ) + 1) * (analyticOrderNatAt zetaExt ρ : ℝ) * ‖s - ρ‖ := by gcongr
      _ = 2 * ((N : ℝ) + 1) * ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ((N : ℝ) + 1) * (CB * Real.log (2 + |t0|)) := by gcongr
  have hs1_inv : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have : (1 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp [s] at this; linarith
    exact inv_le_one_of_one_le₀ this
  have hld_total : ‖logDeriv riemannZeta s‖ ≤
      1 + CB * Real.log (2 + |t0|) + 2 * ((N : ℝ) + 1) * (CB * Real.log (2 + |t0|)) := by
    have hsplit : logDeriv riemannZeta s =
        -(s - 1)⁻¹ + (logDeriv zetaExt s - ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)) +
          ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ) := by
      linear_combination -hld_rel
    rw [hsplit]
    calc _ ≤ ‖-(s - 1)⁻¹ + (logDeriv zetaExt s - ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ))‖ +
            ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
      _ ≤ (‖-(s - 1)⁻¹‖ + ‖logDeriv zetaExt s - ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖) +
            ‖∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (s - ρ)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ (1 + CB * Real.log (2 + |t0|)) + 2 * ((N : ℝ) + 1) * (CB * Real.log (2 + |t0|)) := by
          rw [norm_neg]; gcongr
  refine hld_total.trans ?_
  have hlogH : (1 / 2 : ℝ) ≤ Real.log (2 + |H|) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg H]))
  have hlogH_pos : 0 ≤ Real.log (2 + |H|) := by linarith
  have hCB_log : CB * Real.log (2 + |t0|) ≤ 2 * CB * Real.log (2 + |H|) := by
    have := mul_le_mul_of_nonneg_left hlog_comp hCB; linarith
  have hN_le' : (N : ℝ) ≤ 2 * CB * Real.log (2 + |H|) := hN_le.trans hCB_log
  have h1_le : (1 : ℝ) ≤ 4 * (Real.log (2 + |H|)) ^ 2 := by nlinarith
  have hL_le : Real.log (2 + |H|) ≤ 2 * (Real.log (2 + |H|)) ^ 2 := by nlinarith
  have hprod_le : (N : ℝ) * (CB * Real.log (2 + |t0|)) ≤ 4 * CB ^ 2 * (Real.log (2 + |H|)) ^ 2 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hCB0 : 0 ≤ CB * Real.log (2 + |t0|) := mul_nonneg hCB (Real.log_nonneg (by linarith [abs_nonneg t0]))
    calc (N : ℝ) * (CB * Real.log (2 + |t0|))
        ≤ (2 * CB * Real.log (2 + |H|)) * (2 * CB * Real.log (2 + |H|)) := mul_le_mul hN_le' hCB_log hCB0 (by positivity)
      _ = 4 * CB ^ 2 * (Real.log (2 + |H|)) ^ 2 := by ring
  nlinarith [sq_nonneg CB, sq_nonneg (Real.log (2 + |H|))]

lemma abs_integral_im_inv_sub_le (a b : ℝ) (hb : b ≠ 0) (x1 x2 : ℝ) (_hx : x1 ≤ x2) :
    |∫ σ in x1..x2, (((σ : ℂ) - (a : ℂ) + Complex.I * (b : ℂ))⁻¹).im| ≤ Real.pi := by
  have heq : ∀ σ : ℝ, (((σ : ℂ) - (a : ℂ) + Complex.I * (b : ℂ))⁻¹).im =
      -b / ((σ - a) ^ 2 + b ^ 2) := by
    intro σ
    rw [Complex.inv_im]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
      Complex.sub_im, Complex.mul_im, one_mul, zero_add, Complex.normSq_apply]
    ring
  simp_rw [heq]
  have hderiv : ∀ σ ∈ Set.uIcc x1 x2,
      HasDerivAt (fun x : ℝ => -Real.arctan ((x - a) / b)) (-b / ((σ - a) ^ 2 + b ^ 2)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun x : ℝ => (x - a) / b) (1 / b) σ := by
      simpa using ((hasDerivAt_id σ).sub_const a).div_const b
    have h2 := h1.arctan.neg
    convert h2 using 1
    have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    have hden : (σ - a) ^ 2 + b ^ 2 ≠ 0 := by positivity
    field_simp [hb, hden]; ring
  have hcont : Continuous (fun σ : ℝ => -b / ((σ - a) ^ 2 + b ^ 2)) :=
    continuous_const.div (((continuous_id.sub continuous_const).pow 2).add continuous_const)
      (fun σ => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable x1 x2)]
  have h1 : |Real.arctan ((x2 - a) / b)| < Real.pi / 2 := abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have h2 : |Real.arctan ((x1 - a) / b)| < Real.pi / 2 := abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  calc |-Real.arctan ((x2 - a) / b) - -Real.arctan ((x1 - a) / b)|
      = |Real.arctan ((x1 - a) / b) - Real.arctan ((x2 - a) / b)| := by ring_nf
    _ ≤ |Real.arctan ((x1 - a) / b)| + |Real.arctan ((x2 - a) / b)| := abs_sub _ _
    _ ≤ Real.pi := by linarith

include hF_diff hF_two C3 hF_bound in
set_option maxHeartbeats 400000 in
theorem horizontal_im_logDeriv_riemannZeta_bound :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ T : ℝ, 2 ≤ T →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T) →
      |∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im| ≤
        CS * Real.log (2 + T) := by
  obtain ⟨CB, hCB, hBC⟩ := borel_caratheodory_logDeriv_zetaExt hF_diff hF_two C3 hF_bound
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨(Real.pi + 3 / 2) * CB + 2 * Real.pi, by positivity, fun T hT hne_seg hne_im => ?_⟩
  obtain ⟨R₀, Z, hR₀_lo, hR₀_hi, hZ_mem, hZ_all, hZ_sum, hZ_ld⟩ := hBC T
  have hT_abs : |T| = T := abs_of_pos (by linarith)
  have hs_in3 : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      ((σ : ℂ) + Complex.I * (T : ℂ)) ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) 3 := by
    intro σ hσ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : ((σ : ℂ) + Complex.I * (T : ℂ)) - ((2 : ℂ) + Complex.I * (T : ℂ)) = ((σ - 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hs_notZ : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, ((σ : ℂ) + Complex.I * (T : ℂ)) ∉ Z := by
    intro σ hσ hmem
    have hF0 := (hZ_mem _ hmem).2
    have hs1 : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    simp [zetaExt, hs1] at hF0
    exact hne_seg σ hσ.1 hσ.2 (hF0.resolve_left (sub_ne_zero.mpr hs1))
  let E : ℝ → ℝ := fun σ => (logDeriv zetaExt ((σ : ℂ) + Complex.I * (T : ℂ)) -
      ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (((σ : ℂ) + Complex.I * (T : ℂ)) - ρ)).im
  have hdecomp : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
      (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im =
        -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im) +
        (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
          ((((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im)) + E σ := by
    intro σ hσ
    have hs1 : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have hrel := logDeriv_zetaExt_eq_riemannZeta hs1 (hne_seg σ hσ.1 hσ.2)
    have hsplit : logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) =
        -(((σ : ℂ) + Complex.I * (T : ℂ) - 1)⁻¹) +
        (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (((σ : ℂ) + Complex.I * (T : ℂ)) - ρ)) +
        (logDeriv zetaExt ((σ : ℂ) + Complex.I * (T : ℂ)) -
          ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (((σ : ℂ) + Complex.I * (T : ℂ)) - ρ)) := by
      linear_combination -hrel
    have him := congrArg Complex.im hsplit
    rw [Complex.add_im, Complex.add_im, Complex.neg_im, Complex.im_sum] at him
    rw [him]
    congr 2
    · congr 2; ring
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [div_eq_mul_inv, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      have harg : ((σ : ℂ) + Complex.I * (T : ℂ) - ρ) =
          ((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ)) := by
        apply Complex.ext <;> simp
      rw [harg]
  have hZ_ne_im : ∀ ρ ∈ Z, T - ρ.im ≠ 0 := by
    intro ρ hρ
    have hF0 := (hZ_mem ρ hρ).2
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hF0; simp [zetaExt] at hF0
    simp [zetaExt, hρ1] at hF0
    have hz0 := hF0.resolve_left (sub_ne_zero.mpr hρ1)
    exact sub_ne_zero.mpr (hne_im ρ hz0).symm
  -- Interval integrability of each piece on `[1/2, 2]`
  have hint_inv1 : IntervalIntegrable (fun σ : ℝ => -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im)) volume (1 / 2) 2 := by
    apply Continuous.intervalIntegrable
    have hne : ∀ σ : ℝ, (σ : ℂ) - 1 + Complex.I * (T : ℂ) ≠ 0 := fun σ h => by
      have := congrArg Complex.im h; simp at this; linarith
    exact (Complex.continuous_im.comp (((Complex.continuous_ofReal.sub continuous_const).add continuous_const).inv₀ hne)).neg
  have hint_pole : ∀ ρ ∈ Z, IntervalIntegrable
      (fun σ : ℝ => (analyticOrderNatAt zetaExt ρ : ℝ) *
        (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) volume (1 / 2) 2 := by
    intro ρ hρ
    apply Continuous.intervalIntegrable
    have hne : ∀ σ : ℝ, (σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ) ≠ 0 := fun σ h => by
      have := congrArg Complex.im h; simp at this; exact hZ_ne_im ρ hρ this
    exact continuous_const.mul (Complex.continuous_im.comp
      (((Complex.continuous_ofReal.sub continuous_const).add continuous_const).inv₀ hne))
  have hint_E : IntervalIntegrable E volume (1 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    have hpath : ContinuousOn (fun x : ℝ => (x : ℂ) + Complex.I * (T : ℂ)) (Set.Icc (1 / 2) 2) :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have han : AnalyticOnNhd ℂ zetaExt Set.univ := zetaExt_analyticOnNhd hF_diff
    have hFne : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, zetaExt ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
      intro σ hσ
      have hs1 : ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      simp [zetaExt, hs1]
      exact ⟨sub_ne_zero.mpr hs1, hne_seg σ hσ.1 hσ.2⟩
    have hld_cont : ContinuousOn (fun x : ℝ => logDeriv zetaExt ((x : ℂ) + Complex.I * (T : ℂ))) (Set.Icc (1 / 2) 2) := by
      show ContinuousOn (fun x : ℝ => deriv zetaExt ((x : ℂ) + Complex.I * (T : ℂ)) /
        zetaExt ((x : ℂ) + Complex.I * (T : ℂ))) (Set.Icc (1 / 2) 2)
      exact (han.deriv.continuousOn.comp hpath (fun _ _ => Set.mem_univ _)).div
        (han.continuousOn.comp hpath (fun _ _ => Set.mem_univ _)) hFne
    have hsum_cont_aux : ∀ (S : Finset ℂ) (φ : ℂ → ℝ → ℂ),
        (∀ ρ ∈ S, ContinuousOn (φ ρ) (Set.Icc (1 / 2) 2)) →
        ContinuousOn (fun x : ℝ => ∑ ρ ∈ S, φ ρ x) (Set.Icc (1 / 2) 2) := by
      intro S φ hφ
      induction S using Finset.induction_on with
      | empty => simp [continuousOn_const]
      | @insert a s ha ih =>
        have heq : (fun x : ℝ => ∑ ρ ∈ insert a s, φ ρ x) = fun x : ℝ => φ a x + ∑ ρ ∈ s, φ ρ x := by
          ext x; exact Finset.sum_insert ha
        rw [heq]
        exact (hφ a (Finset.mem_insert_self a s)).add (ih fun ρ hρ => hφ ρ (Finset.mem_insert_of_mem hρ))
    have hsum_cont : ContinuousOn (fun x : ℝ => ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) /
        (((x : ℂ) + Complex.I * (T : ℂ)) - ρ)) (Set.Icc (1 / 2) 2) := by
      refine hsum_cont_aux Z
        (fun ρ x => (analyticOrderNatAt zetaExt ρ : ℂ) / (((x : ℂ) + Complex.I * (T : ℂ)) - ρ))
        fun ρ hρ => ?_
      have hden : ContinuousOn (fun x : ℝ => ((x : ℂ) + Complex.I * (T : ℂ)) - ρ) (Set.Icc (1 / 2) 2) :=
        hpath.sub continuousOn_const
      refine (continuousOn_const (c := (analyticOrderNatAt zetaExt ρ : ℂ))).div hden fun σ hσ => ?_
      exact sub_ne_zero.mpr fun h => hs_notZ σ hσ (by rw [h]; exact hρ)
    exact Complex.continuous_im.comp_continuousOn (hld_cont.sub hsum_cont)
  have hcongr : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im =
      (∫ σ in (1 / 2 : ℝ)..2, -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im)) +
      (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
        ∫ σ in (1 / 2 : ℝ)..2, (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) +
      (∫ σ in (1 / 2 : ℝ)..2, E σ) := by
    have h1 : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im =
        ∫ σ in (1 / 2 : ℝ)..2, (-((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im) +
          (∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
            (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) + E σ) :=
      intervalIntegral.integral_congr fun σ hσ => hdecomp σ (by rwa [Set.uIcc_of_le (by norm_num)] at hσ)
    have hint_sum : IntervalIntegrable (fun σ : ℝ => ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
        (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) volume (1 / 2) 2 := by
      have heq : (fun σ : ℝ => ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
          (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) =
          ∑ ρ ∈ Z, (fun σ : ℝ => (analyticOrderNatAt zetaExt ρ : ℝ) *
          (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im) := by
        ext σ; simp [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum Z hint_pole
    have hsum_int : ∀ (S : Finset ℂ) (f : ℂ → ℝ → ℝ),
        (∀ ρ ∈ S, IntervalIntegrable (f ρ) volume (1 / 2) 2) →
        ∫ σ in (1 / 2 : ℝ)..2, ∑ ρ ∈ S, f ρ σ = ∑ ρ ∈ S, ∫ σ in (1 / 2 : ℝ)..2, f ρ σ := by
      intro S f hf
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp_rw [Finset.sum_insert ha]
        have hs : IntervalIntegrable (fun σ => ∑ ρ ∈ s, f ρ σ) volume (1 / 2) 2 := by
          have heq : (fun σ => ∑ ρ ∈ s, f ρ σ) = ∑ ρ ∈ s, f ρ := by ext σ; simp [Finset.sum_apply]
          rw [heq]; exact IntervalIntegrable.sum s (fun ρ hρ => hf ρ (Finset.mem_insert_of_mem hρ))
        rw [intervalIntegral.integral_add (hf a (Finset.mem_insert_self a s)) hs,
          ih (fun ρ hρ => hf ρ (Finset.mem_insert_of_mem hρ))]
    rw [h1,
      intervalIntegral.integral_add (hint_inv1.add hint_sum) hint_E,
      intervalIntegral.integral_add hint_inv1 hint_sum,
      hsum_int Z _ hint_pole]
    congr 2; refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [hcongr]
  have hb1 : |∫ σ in (1 / 2 : ℝ)..2, -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im)| ≤ Real.pi := by
    rw [intervalIntegral.integral_neg, abs_neg]
    exact abs_integral_im_inv_sub_le 1 T (by linarith) (1 / 2) 2 (by norm_num)
  have hb2 : |∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
      ∫ σ in (1 / 2 : ℝ)..2, (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im| ≤
      Real.pi * CB * Real.log (2 + T) := by
    calc _ ≤ ∑ ρ ∈ Z, |(analyticOrderNatAt zetaExt ρ : ℝ) *
            ∫ σ in (1 / 2 : ℝ)..2, (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ Z, Real.pi * (analyticOrderNatAt zetaExt ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          have := abs_integral_im_inv_sub_le ρ.re (T - ρ.im) (hZ_ne_im ρ hρ) (1 / 2) 2 (by norm_num)
          calc (analyticOrderNatAt zetaExt ρ : ℝ) * _ ≤ (analyticOrderNatAt zetaExt ρ : ℝ) * Real.pi :=
                mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
            _ = Real.pi * (analyticOrderNatAt zetaExt ρ : ℝ) := by ring
      _ = Real.pi * ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.pi * (CB * Real.log (2 + T)) := by
          rw [← hT_abs]; exact mul_le_mul_of_nonneg_left hZ_sum Real.pi_pos.le
      _ = Real.pi * CB * Real.log (2 + T) := by ring
  have hb3 : |∫ σ in (1 / 2 : ℝ)..2, E σ| ≤ (3 / 2) * CB * Real.log (2 + T) := by
    calc |∫ σ in (1 / 2 : ℝ)..2, E σ|
        ≤ ∫ σ in (1 / 2 : ℝ)..2, |E σ| := by
          simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := E) (by norm_num)
      _ ≤ ∫ _σ in (1 / 2 : ℝ)..2, (CB * Real.log (2 + T)) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hint_E.abs intervalIntegrable_const fun σ hσ => ?_
          have h1 : |E σ| ≤ ‖logDeriv zetaExt ((σ : ℂ) + Complex.I * (T : ℂ)) -
              ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℂ) / (((σ : ℂ) + Complex.I * (T : ℂ)) - ρ)‖ :=
            Complex.abs_im_le_norm _
          have h2 := hZ_ld ((σ : ℂ) + Complex.I * (T : ℂ)) (hs_in3 σ hσ) (hs_notZ σ hσ)
          rw [hT_abs] at h2
          exact h1.trans h2
      _ = (3 / 2) * CB * Real.log (2 + T) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hlogT : (1 / 2 : ℝ) ≤ Real.log (2 + T) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  calc _ ≤ |∫ σ in (1 / 2 : ℝ)..2, -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im)| +
        |∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
          ∫ σ in (1 / 2 : ℝ)..2, (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im| +
        |∫ σ in (1 / 2 : ℝ)..2, E σ| := by
          calc _ ≤ |(∫ σ in (1 / 2 : ℝ)..2, -((((σ : ℂ) - 1 + Complex.I * (T : ℂ))⁻¹).im)) +
                ∑ ρ ∈ Z, (analyticOrderNatAt zetaExt ρ : ℝ) *
                  ∫ σ in (1 / 2 : ℝ)..2, (((σ : ℂ) - (ρ.re : ℂ) + Complex.I * ((T - ρ.im : ℝ) : ℂ))⁻¹).im| +
                |∫ σ in (1 / 2 : ℝ)..2, E σ| := abs_add_le _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ Real.pi + Real.pi * CB * Real.log (2 + T) + (3 / 2) * CB * Real.log (2 + T) := by linarith
    _ ≤ ((Real.pi + 3 / 2) * CB + 2 * Real.pi) * Real.log (2 + T) := by nlinarith [Real.pi_pos]

end WithZetaBounds

end SpectralMod4

end Mod4Section

section Mod5Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace SpectralMod5

/-! ### Module 5: Conjugate Symmetry, Rectangular Argument Principle, and Riemann-von Mangoldt -/

noncomputable def zetaExt (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

noncomputable def xiFun (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-! #### Part 5A: Conjugate Symmetry and Properties of `xiFun` -/

lemma hasDerivAt_conj_comp {f : ℂ → ℂ} {f' s : ℂ} (hf : HasDerivAt f f' (starRingEnd ℂ s)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') s := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hcomp := hf.comp (Complex.continuous_conj.tendsto s)
  refine hcomp.congr fun w => ?_
  dsimp only [Function.comp_apply]
  have h1 : ‖starRingEnd ℂ w - starRingEnd ℂ s‖ = ‖w - s‖ := by
    rw [← map_sub, Complex.norm_conj]
  have h2 : ‖f (starRingEnd ℂ w) - f (starRingEnd ℂ s) - (starRingEnd ℂ w - starRingEnd ℂ s) * f'‖ =
      ‖starRingEnd ℂ (f (starRingEnd ℂ w)) - starRingEnd ℂ (f (starRingEnd ℂ s)) - (w - s) * starRingEnd ℂ f'‖ := by
    rw [← Complex.norm_conj]
    congr 1
    simp only [map_sub, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  simp only [smul_eq_mul]
  rw [h1, h2]

lemma differentiable_conj_comp {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) :=
  fun s => (hasDerivAt_conj_comp (hf (starRingEnd ℂ s)).hasDerivAt).differentiableAt

lemma analyticAt_conj_comp {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (starRingEnd ℂ s)) :
    AnalyticAt ℂ (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) s := by
  obtain ⟨r, hr, hdiff⟩ := hf.exists_ball_analyticOnNhd
  have hdiff' : DifferentiableOn ℂ (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) (Metric.ball s r) := by
    intro w hw
    have hw' : starRingEnd ℂ w ∈ Metric.ball (starRingEnd ℂ s) r := by
      simp only [Metric.mem_ball, dist_eq_norm] at hw ⊢
      rw [← map_sub, Complex.norm_conj]; exact hw
    have hda : DifferentiableAt ℂ f (starRingEnd ℂ w) := (hdiff _ hw').differentiableAt
    exact (hasDerivAt_conj_comp hda.hasDerivAt).differentiableAt.differentiableWithinAt
  exact hdiff'.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

lemma entire_conj_eq_self {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, 1 < x → (f (x : ℂ)).im = 0) :
    ∀ s : ℂ, f (starRingEnd ℂ s) = starRingEnd ℂ (f s) := by
  let g : ℂ → ℂ := fun w => starRingEnd ℂ (f (starRingEnd ℂ w))
  have hg : Differentiable ℂ g := differentiable_conj_comp hf
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ w in 𝓝[≠] (2 : ℂ), g w = f w := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [Metric.mem_nhdsWithin_iff] at hU
    obtain ⟨ε, hε, hsub⟩ := hU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    let x : ℝ := 2 + 1 / ((n : ℝ) + 1)
    refine ⟨(x : ℂ), hsub ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : (x : ℂ) - 2 = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
        simp only [x]; push_cast; ring
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact hn
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      have := congrArg Complex.re h0
      simp only [x, Complex.ofReal_re, Complex.re_ofNat] at this
      linarith [div_pos one_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    · have hx1 : 1 < x := by
        simp only [x]; linarith [div_pos one_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      have him0 : (f (x : ℂ)).im = 0 := hreal x hx1
      simp only [g, Complex.conj_ofReal]
      exact Complex.conj_eq_iff_im.mpr him0
  have heq : Set.EqOn g f Set.univ :=
    hga.eqOn_of_preconnected_of_frequently_eq hfa isPreconnected_univ (Set.mem_univ (2 : ℂ)) hfreq
  intro s
  have h1 : g s = f s := heq (Set.mem_univ s)
  have h2 := congrArg (starRingEnd ℂ) h1
  simpa [g] using h2

lemma riemannZeta_ofReal_im_eq_zero {x : ℝ} (hx : 1 < x) :
    (riemannZeta (x : ℂ)).im = 0 := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hx)]
  have heq : (fun n : ℕ => 1 / (n : ℂ) ^ (x : ℂ)) = (fun n : ℕ => ((1 / (n : ℝ) ^ x : ℝ) : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0)),
        Real.zero_rpow (by linarith)]
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast; rfl
  rw [heq, ← Complex.ofReal_tsum, Complex.ofReal_im]

lemma differentiable_xiFun : Differentiable ℂ xiFun := by
  unfold xiFun
  exact ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).mul
    differentiable_completedZeta₀).add (differentiable_const 1)

lemma xiFun_one_sub (s : ℂ) : xiFun (1 - s) = xiFun s := by
  unfold xiFun
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma xiFun_zero : xiFun 0 = 1 := by simp [xiFun]

lemma xiFun_one : xiFun 1 = 1 := by simp [xiFun]

lemma xiFun_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiFun s = s * (s - 1) * completedRiemannZeta s := by
  rw [xiFun, completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

lemma xiFun_eq_mul_riemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hre : 0 < s.re) :
    xiFun s = s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) * riemannZeta s := by
  rw [xiFun_eq_mul_completedRiemannZeta hs0 hs1, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
    exact Complex.exp_ne_zero _
  have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hmul : (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 := mul_ne_zero hpi hG
  field_simp [hmul]

lemma xiFun_ne_zero_of_one_le_re {s : ℂ} (hre : 1 ≤ s.re) : xiFun s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, xiFun_one]; exact one_ne_zero
  · have hs0 : s ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
    rw [xiFun_eq_mul_riemannZeta hs0 hs1 (by linarith)]
    have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
      exact Complex.exp_ne_zero _
    have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hpi hG))
      (riemannZeta_ne_zero_of_one_le_re hre)

lemma xiFun_ne_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) : xiFun s ≠ 0 := by
  rw [← xiFun_one_sub]
  exact xiFun_ne_zero_of_one_le_re (by simp; linarith)

lemma xiFun_conj (s : ℂ) : xiFun (starRingEnd ℂ s) = starRingEnd ℂ (xiFun s) := by
  refine entire_conj_eq_self differentiable_xiFun (fun x hx => ?_) s
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hx1 : (x : ℂ) ≠ 1 := by intro h; exact (by linarith : x ≠ 1) (Complex.ofReal_injective h)
  rw [xiFun_eq_mul_riemannZeta hx0 hx1 (by simpa using (by linarith : (0 : ℝ) < x))]
  have hpi : (Real.pi : ℂ) ^ (-(x : ℂ) / 2) = ((Real.pi ^ (-x / 2) : ℝ) : ℂ) := by
    rw [show -(x : ℂ) / 2 = ((-x / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow Real.pi_pos.le]
  have hG : Complex.Gamma ((x : ℂ) / 2) = ((Real.Gamma (x / 2) : ℝ) : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have hz : riemannZeta (x : ℂ) = (((riemannZeta (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [riemannZeta_ofReal_im_eq_zero hx]
  rw [hpi, hG, hz]
  norm_cast

lemma zetaExt_conj (hF_diff : Differentiable ℂ zetaExt) (s : ℂ) :
    zetaExt (starRingEnd ℂ s) = starRingEnd ℂ (zetaExt s) := by
  refine entire_conj_eq_self hF_diff (fun x hx => ?_) s
  have hx1 : (x : ℂ) ≠ 1 := by intro h; exact (by linarith : x ≠ 1) (Complex.ofReal_injective h)
  simp only [zetaExt, hx1, ↓reduceIte]
  have hz : riemannZeta (x : ℂ) = (((riemannZeta (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [riemannZeta_ofReal_im_eq_zero hx]
  rw [hz]
  norm_cast

lemma riemannZeta_conj (hF_diff : Differentiable ℂ zetaExt) {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  have hs' : starRingEnd ℂ s ≠ 1 := by
    intro h; apply hs; simpa using congrArg (starRingEnd ℂ) h
  have h := zetaExt_conj hF_diff s
  simp only [zetaExt, hs, hs', ↓reduceIte, map_mul, map_sub, map_one] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs') h

lemma analyticOrderNatAt_eq_of_conj_symm {f : ℂ → ℂ} {z₀ : ℂ}
    (hfa : AnalyticAt ℂ f z₀) (hfa' : AnalyticAt ℂ f (starRingEnd ℂ z₀))
    (hsym : ∀ᶠ w in 𝓝 z₀, f (starRingEnd ℂ w) = starRingEnd ℂ (f w)) :
    analyticOrderNatAt f (starRingEnd ℂ z₀) = analyticOrderNatAt f z₀ := by
  by_cases htop : analyticOrderAt f z₀ = ⊤
  · have hev0 : ∀ᶠ w in 𝓝 z₀, f w = 0 := analyticOrderAt_eq_top.mp htop
    have hev0' : ∀ᶠ w in 𝓝 (starRingEnd ℂ z₀), f w = 0 := by
      have h1 : ∀ᶠ w in 𝓝 (starRingEnd ℂ z₀), starRingEnd ℂ w ∈ {u | f u = 0 ∧ f (starRingEnd ℂ u) = starRingEnd ℂ (f u)} := by
        have ht : Tendsto (starRingEnd ℂ) (𝓝 (starRingEnd ℂ z₀)) (𝓝 z₀) := by
          simpa using Complex.continuous_conj.tendsto (starRingEnd ℂ z₀)
        exact ht (hev0.and hsym)
      filter_upwards [h1] with w ⟨hw1, hw2⟩
      simpa [hw1] using hw2
    have htop' : analyticOrderAt f (starRingEnd ℂ z₀) = ⊤ := analyticOrderAt_eq_top.mpr hev0'
    simp [analyticOrderNatAt, htop, htop']
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hn' : analyticOrderAt f z₀ = (n : ℕ∞) := hn.symm
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hfa.analyticOrderAt_eq_natCast.mp hn'
    let gc : ℂ → ℂ := fun w => starRingEnd ℂ (g (starRingEnd ℂ w))
    have hgc_an : AnalyticAt ℂ gc (starRingEnd ℂ z₀) := analyticAt_conj_comp (by simpa using hg_an)
    have hgc_ne : gc (starRingEnd ℂ z₀) ≠ 0 := by
      simp only [gc, RingHomCompTriple.comp_apply, RingHom.id_apply]
      simpa using hg_ne
    have hgc_eq : ∀ᶠ w in 𝓝 (starRingEnd ℂ z₀), f w = (w - starRingEnd ℂ z₀) ^ n • gc w := by
      have ht : Tendsto (starRingEnd ℂ) (𝓝 (starRingEnd ℂ z₀)) (𝓝 z₀) := by
        simpa using Complex.continuous_conj.tendsto (starRingEnd ℂ z₀)
      filter_upwards [ht (hg_eq.and hsym)] with w ⟨hw1, hw2⟩
      have hw3 : f w = starRingEnd ℂ (f (starRingEnd ℂ w)) := by simpa using hw2
      rw [hw3, hw1]
      simp only [gc, smul_eq_mul, map_mul, map_pow, map_sub]
      simp
    have hord' : analyticOrderAt f (starRingEnd ℂ z₀) = (n : ℕ∞) :=
      hfa'.analyticOrderAt_eq_natCast.mpr ⟨gc, hgc_an, hgc_ne, hgc_eq⟩
    simp [analyticOrderNatAt, hn', hord']

lemma analyticOrderNatAt_xiFun_conj (s : ℂ) :
    analyticOrderNatAt xiFun (starRingEnd ℂ s) = analyticOrderNatAt xiFun s :=
  analyticOrderNatAt_eq_of_conj_symm
    ((differentiable_xiFun.differentiableOn.analyticOnNhd isOpen_univ) s (Set.mem_univ _))
    ((differentiable_xiFun.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _))
    (Filter.Eventually.of_forall fun w => xiFun_conj w)

lemma analyticOrderNatAt_riemannZeta_conj (hF_diff : Differentiable ℂ zetaExt) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta (starRingEnd ℂ s) = analyticOrderNatAt riemannZeta s := by
  have hs' : starRingEnd ℂ s ≠ 1 := by
    intro h; apply hs; simpa using congrArg (starRingEnd ℂ) h
  refine analyticOrderNatAt_eq_of_conj_symm
    (differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hs))
    (differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hs')) ?_
  filter_upwards [isOpen_ne.mem_nhds hs] with w hw
  exact riemannZeta_conj hF_diff hw

lemma analyticOrderNatAt_xiFun_eq_riemannZeta {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderNatAt xiFun s = analyticOrderNatAt riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hre; simp at hre
  let P : ℂ → ℂ := fun w => w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2))
  have hP_an : AnalyticAt ℂ P s := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ P {w : ℂ | 0 < w.re} := by
      intro w hw
      have hre_w : 0 < w.re := hw
      have hd1 : DifferentiableAt ℂ (fun u : ℂ => u * (u - 1)) w := by fun_prop
      have hd2 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) w := by
        have hlin : DifferentiableAt ℂ (fun u : ℂ => -u / 2) w := by fun_prop
        exact (differentiableAt_const (Real.pi : ℂ)).cpow hlin (Or.inl (by simpa using Real.pi_pos))
      have hd3 : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma (u / 2)) w := by
        have hne : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
          intro m hm; have := congrArg Complex.re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
        exact (Complex.differentiableAt_Gamma (w / 2) hne).comp w (by fun_prop)
      exact (hd1.mul (hd2.mul hd3)).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hre)
  have hP_ne : P s ≠ 0 := by
    have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
      exact Complex.exp_ne_zero _
    have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hpi hG)
  have hev : xiFun =ᶠ[𝓝 s] P * riemannZeta := by
    have hopen : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | w ≠ 1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hre, hs1⟩] with w ⟨hwre, hw1⟩
    have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
    exact xiFun_eq_mul_riemannZeta hw0 hw1 hwre
  have hza : AnalyticAt ℂ riemannZeta s := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hs1)
  have h1 : analyticOrderAt xiFun s = analyticOrderAt (P * riemannZeta) s := analyticOrderAt_congr hev
  rw [analyticOrderAt_mul hP_an hza, hP_an.analyticOrderAt_eq_zero.mpr hP_ne, zero_add] at h1
  simp only [analyticOrderNatAt, h1]

lemma logDeriv_xiFun_one_sub (s : ℂ) : logDeriv xiFun (1 - s) = -logDeriv xiFun s := by
  have hd : HasDerivAt (fun w : ℂ => xiFun (1 - w)) (-deriv xiFun (1 - s)) s := by
    have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) s := (hasDerivAt_id s).const_sub 1
    have hc : HasDerivAt (fun w : ℂ => xiFun (1 - w)) (deriv xiFun (1 - s) * (-1)) s :=
      (differentiable_xiFun (1 - s)).hasDerivAt.comp s h1
    simpa [mul_neg, mul_one] using hc
  have heq : (fun w : ℂ => xiFun (1 - w)) = xiFun := funext xiFun_one_sub
  rw [heq] at hd
  have hder : deriv xiFun s = -deriv xiFun (1 - s) := hd.deriv
  rw [logDeriv_apply, logDeriv_apply, xiFun_one_sub, hder]; ring

lemma logDeriv_xiFun_conj (s : ℂ) :
    logDeriv xiFun (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiFun s) := by
  have hd := hasDerivAt_conj_comp (differentiable_xiFun (starRingEnd ℂ s)).hasDerivAt
  have heq : (fun w : ℂ => starRingEnd ℂ (xiFun (starRingEnd ℂ w))) = xiFun := by
    funext w; rw [xiFun_conj]; simp
  rw [heq] at hd
  have hder : deriv xiFun s = starRingEnd ℂ (deriv xiFun (starRingEnd ℂ s)) := hd.deriv
  have hder' : deriv xiFun (starRingEnd ℂ s) = starRingEnd ℂ (deriv xiFun s) := by
    simpa using congrArg (starRingEnd ℂ) hder.symm
  rw [logDeriv_apply, logDeriv_apply, hder', xiFun_conj, map_div₀]

lemma logDeriv_xiFun_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) (hsz : riemannZeta s ≠ 0) :
    logDeriv xiFun s =
      s⁻¹ + (s - 1)⁻¹ - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
      (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
    exact Complex.exp_ne_zero _
  have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hev : xiFun =ᶠ[𝓝 s]
      fun w => w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) * riemannZeta w := by
    have hopen : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | w ≠ 1}) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hre, hs1⟩] with w ⟨hwre, hw1⟩
    have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
    exact xiFun_eq_mul_riemannZeta hw0 hw1 hwre
  have hld_eq : logDeriv xiFun s =
      logDeriv (fun w => w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hld_eq]
  have hd_id : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have hd_sub : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub (differentiableAt_const 1)
  have hd_pi : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((-(Complex.log (Real.pi : ℂ)) / 2) * (Real.pi : ℂ) ^ (-s / 2)) s := by
    have heq_pi : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) =
        (fun w : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-w / 2))) := by
      funext w; rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
    rw [heq_pi]
    have hlin : HasDerivAt (fun w : ℂ => Complex.log (Real.pi : ℂ) * (-w / 2))
        (Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2)) s :=
      ((hasDerivAt_id s).neg.div_const 2).const_mul (Complex.log (Real.pi : ℂ))
    convert hlin.cexp using 1
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]; ring
  have hd_G : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ)) s := by
    have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hm; have := congrArg Complex.re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    have h1 := (Complex.differentiableAt_Gamma (s / 2) hne).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    exact h1.comp s h2
  have hd_z : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hld_mul1 := logDeriv_fun_mul (f := fun w : ℂ => w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)))
    (g := riemannZeta) s (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hpi hG)) hsz
    ((hd_id.mul hd_sub).mul (hd_pi.differentiableAt.mul hd_G.differentiableAt)) hd_z
  have hld_mul2 := logDeriv_fun_mul (f := fun w : ℂ => w * (w - 1))
    (g := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s
    (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hpi hG)
    (hd_id.mul hd_sub) (hd_pi.differentiableAt.mul hd_G.differentiableAt)
  have hld_mul3 := logDeriv_fun_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s
    hs0 (sub_ne_zero.mpr hs1) hd_id hd_sub
  have hld_mul4 := logDeriv_fun_mul (f := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
    (g := fun w : ℂ => Complex.Gamma (w / 2)) s hpi hG hd_pi.differentiableAt hd_G.differentiableAt
  rw [hld_mul1, hld_mul2, hld_mul3, hld_mul4]
  have h1 : logDeriv (fun w : ℂ => w) s = s⁻¹ := by
    rw [logDeriv_apply, deriv_id'', one_div]
  have h2 : logDeriv (fun w : ℂ => w - 1) s = (s - 1)⁻¹ := by
    have hd1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := by simpa using (hasDerivAt_id s).sub_const (1 : ℂ)
    rw [logDeriv_apply, hd1.deriv, one_div]
  have h3 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s = -((Real.log Real.pi / 2 : ℝ) : ℂ) := by
    rw [logDeriv_apply, hd_pi.deriv, mul_div_cancel_right₀ _ hpi, ← Complex.ofReal_log Real.pi_pos.le]
    push_cast; ring
  have h4 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s = (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) := by
    rw [logDeriv_apply, logDeriv_apply, hd_G.deriv]; ring
  rw [h1, h2, h3, h4]; ring

/-! #### Part 5B: Rectangular Contour Integral and General Logarithmic-Derivative Residue Formula -/

noncomputable def rectIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + Complex.I * (c : ℂ))) -
  (∫ x in a..b, f ((x : ℂ) + Complex.I * (d : ℂ))) +
  Complex.I * (∫ y in c..d, f ((b : ℂ) + Complex.I * (y : ℂ))) -
  Complex.I * (∫ y in c..d, f ((a : ℂ) + Complex.I * (y : ℂ)))

lemma rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectIntegral f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + Complex.I * (c : ℂ)) ((b : ℂ) + Complex.I * (d : ℂ))
  have hre1 : ((a : ℂ) + Complex.I * (c : ℂ)).re = a := by simp
  have him1 : ((a : ℂ) + Complex.I * (c : ℂ)).im = c := by simp
  have hre2 : ((b : ℂ) + Complex.I * (d : ℂ)).re = b := by simp
  have him2 : ((b : ℂ) + Complex.I * (d : ℂ)).im = d := by simp
  rw [hre1, him1, hre2, him2] at h
  have h0 := h hf
  unfold rectIntegral
  convert h0 using 1
  simp only [smul_eq_mul, mul_comm Complex.I]

lemma rectIntegral_const_mul (f : ℂ → ℂ) (c₀ : ℂ) (a b c d : ℝ) :
    rectIntegral (fun z => c₀ * f z) a b c d = c₀ * rectIntegral f a b c d := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma rectIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + Complex.I * (c : ℂ))) volume a b)
    (hf2 : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + Complex.I * (d : ℂ))) volume a b)
    (hf3 : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + Complex.I * (y : ℂ))) volume c d)
    (hf4 : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + Complex.I * (y : ℂ))) volume c d)
    (hg1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + Complex.I * (c : ℂ))) volume a b)
    (hg2 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + Complex.I * (d : ℂ))) volume a b)
    (hg3 : IntervalIntegrable (fun y : ℝ => g ((b : ℂ) + Complex.I * (y : ℂ))) volume c d)
    (hg4 : IntervalIntegrable (fun y : ℝ => g ((a : ℂ) + Complex.I * (y : ℂ))) volume c d) :
    rectIntegral (fun z => f z + g z) a b c d = rectIntegral f a b c d + rectIntegral g a b c d := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add hf1 hg1, intervalIntegral.integral_add hf2 hg2,
    intervalIntegral.integral_add hf3 hg3, intervalIntegral.integral_add hf4 hg4]
  ring

lemma intervalIntegral_finset_sum_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ x in a..b, ∑ i ∈ s, f i x = ∑ i ∈ s, ∫ x in a..b, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k t hk ih =>
    simp_rw [Finset.sum_insert hk]
    have ht : IntervalIntegrable (fun x => ∑ i ∈ t, f i x) volume a b := by
      have heq : (fun x => ∑ i ∈ t, f i x) = ∑ i ∈ t, f i := by ext x; simp [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum t (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [intervalIntegral.integral_add (hf k (Finset.mem_insert_self k t)) ht,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma rectIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {a b c d : ℝ}
    (h1 : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i ((x : ℂ) + Complex.I * (c : ℂ))) volume a b)
    (h2 : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i ((x : ℂ) + Complex.I * (d : ℂ))) volume a b)
    (h3 : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i ((b : ℂ) + Complex.I * (y : ℂ))) volume c d)
    (h4 : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i ((a : ℂ) + Complex.I * (y : ℂ))) volume c d) :
    rectIntegral (fun z => ∑ i ∈ s, f i z) a b c d = ∑ i ∈ s, rectIntegral (f i) a b c d := by
  unfold rectIntegral
  rw [intervalIntegral_finset_sum_aux s _ h1, intervalIntegral_finset_sum_aux s _ h2,
    intervalIntegral_finset_sum_aux s _ h3, intervalIntegral_finset_sum_aux s _ h4]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma rectIntegral_congr {f g : ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d,
      (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → f z = g z) :
    rectIntegral f a b c d = rectIntegral g a b c d := by
  unfold rectIntegral
  have hb1 : ∫ x in a..b, f ((x : ℂ) + Complex.I * (c : ℂ)) =
      ∫ x in a..b, g ((x : ℂ) + Complex.I * (c : ℂ)) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [Set.uIcc_of_le hab] at hx
      exact h _ ⟨by simpa using hx, by simp [hcd]⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  have hb2 : ∫ x in a..b, f ((x : ℂ) + Complex.I * (d : ℂ)) =
      ∫ x in a..b, g ((x : ℂ) + Complex.I * (d : ℂ)) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [Set.uIcc_of_le hab] at hx
      exact h _ ⟨by simpa using hx, by simp [hcd]⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  have hb3 : ∫ y in c..d, f ((b : ℂ) + Complex.I * (y : ℂ)) =
      ∫ y in c..d, g ((b : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_congr fun y hy => by
      rw [Set.uIcc_of_le hcd] at hy
      exact h _ ⟨by simp [hab], by simpa using hy⟩ (Or.inr (Or.inl (by simp)))
  have hb4 : ∫ y in c..d, f ((a : ℂ) + Complex.I * (y : ℂ)) =
      ∫ y in c..d, g ((a : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_congr fun y hy => by
      rw [Set.uIcc_of_le hcd] at hy
      exact h _ ⟨by simp [hab], by simpa using hy⟩ (Or.inl (by simp))
  rw [hb1, hb2, hb3, hb4]

lemma integral_inv_horiz (a b α δ : ℝ) (hδ : δ ≠ 0) :
    ∫ x in a..b, (((x : ℂ) - (α : ℂ) + Complex.I * (δ : ℂ))⁻¹) =
      ((1 / 2 * (Real.log ((b - α) ^ 2 + δ ^ 2) - Real.log ((a - α) ^ 2 + δ ^ 2)) : ℝ) : ℂ) +
      Complex.I * (((-Real.arctan ((b - α) / δ) + Real.arctan ((a - α) / δ) : ℝ) : ℂ)) := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  have hsplit : ∀ x : ℝ, (((x : ℂ) - (α : ℂ) + Complex.I * (δ : ℂ))⁻¹) =
      (((x - α) / ((x - α) ^ 2 + δ ^ 2) : ℝ) : ℂ) +
      Complex.I * (((-δ / ((x - α) ^ 2 + δ ^ 2) : ℝ) : ℂ)) := by
    intro x
    apply Complex.ext
    · rw [Complex.inv_re]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.sub_im, Complex.mul_im, one_mul, zero_add, Complex.normSq_apply]
      ring
    · rw [Complex.inv_im]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.sub_im, Complex.mul_im, one_mul, zero_add, Complex.normSq_apply]
      ring
  simp_rw [hsplit]
  have hc1 : Continuous (fun x : ℝ => (x - α) / ((x - α) ^ 2 + δ ^ 2)) :=
    (continuous_id.sub continuous_const).div
      (((continuous_id.sub continuous_const).pow 2).add continuous_const) (fun x => ne_of_gt (by positivity : 0 < (x - α) ^ 2 + δ ^ 2))
  have hc2 : Continuous (fun x : ℝ => -δ / ((x - α) ^ 2 + δ ^ 2)) :=
    continuous_const.div
      (((continuous_id.sub continuous_const).pow 2).add continuous_const) (fun x => ne_of_gt (by positivity : 0 < (x - α) ^ 2 + δ ^ 2))
  have hi1 : IntervalIntegrable (fun x : ℝ => (((x - α) / ((x - α) ^ 2 + δ ^ 2) : ℝ) : ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp hc1).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun x : ℝ => Complex.I * (((-δ / ((x - α) ^ 2 + δ ^ 2) : ℝ) : ℂ))) volume a b :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable a b
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hint1 : ∫ x in a..b, (x - α) / ((x - α) ^ 2 + δ ^ 2) =
      1 / 2 * (Real.log ((b - α) ^ 2 + δ ^ 2) - Real.log ((a - α) ^ 2 + δ ^ 2)) := by
    have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => 1 / 2 * Real.log ((t - α) ^ 2 + δ ^ 2))
        ((x - α) / ((x - α) ^ 2 + δ ^ 2)) x := by
      intro x _
      have hpos : (x - α) ^ 2 + δ ^ 2 ≠ 0 := by positivity
      have h1 : HasDerivAt (fun t : ℝ => (t - α) ^ 2 + δ ^ 2) (2 * (x - α)) x := by
        simpa [pow_one] using (((hasDerivAt_id x).sub_const α).fun_pow 2).add_const (δ ^ 2)
      have h2 := (h1.log hpos).const_mul (1 / 2 : ℝ)
      convert h2 using 1; field_simp [hpos]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable a b)]
    ring
  have hint2 : ∫ x in a..b, -δ / ((x - α) ^ 2 + δ ^ 2) =
      -Real.arctan ((b - α) / δ) + Real.arctan ((a - α) / δ) := by
    have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -Real.arctan ((t - α) / δ))
        (-δ / ((x - α) ^ 2 + δ ^ 2)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => (t - α) / δ) (1 / δ) x := by
        simpa using ((hasDerivAt_id x).sub_const α).div_const δ
      have h2 := h1.arctan.neg
      convert h2 using 1
      have hpos : (x - α) ^ 2 + δ ^ 2 ≠ 0 := by positivity
      field_simp [hδ, hpos]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable a b)]
    ring
  rw [hint1, hint2]

lemma integral_inv_vert (c d β δ : ℝ) (hδ : δ ≠ 0) :
    Complex.I * (∫ y in c..d, (((δ : ℂ) + Complex.I * ((y : ℂ) - (β : ℂ)))⁻¹)) =
      ((1 / 2 * (Real.log (δ ^ 2 + (d - β) ^ 2) - Real.log (δ ^ 2 + (c - β) ^ 2)) : ℝ) : ℂ) +
      Complex.I * (((Real.arctan ((d - β) / δ) - Real.arctan ((c - β) / δ) : ℝ) : ℂ)) := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  have hsplit : ∀ y : ℝ, (((δ : ℂ) + Complex.I * ((y : ℂ) - (β : ℂ)))⁻¹) =
      ((δ / (δ ^ 2 + (y - β) ^ 2) : ℝ) : ℂ) +
      Complex.I * (((-(y - β) / (δ ^ 2 + (y - β) ^ 2) : ℝ) : ℂ)) := by
    intro y
    apply Complex.ext
    · rw [Complex.inv_re]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.sub_im, Complex.mul_im, one_mul, zero_add, Complex.normSq_apply]
      ring
    · rw [Complex.inv_im]
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.sub_im, Complex.mul_im, one_mul, zero_add, Complex.normSq_apply]
      ring
  simp_rw [hsplit]
  have hc1 : Continuous (fun y : ℝ => δ / (δ ^ 2 + (y - β) ^ 2)) :=
    continuous_const.div
      (continuous_const.add ((continuous_id.sub continuous_const).pow 2)) (fun y => ne_of_gt (by positivity : 0 < δ ^ 2 + (y - β) ^ 2))
  have hc2 : Continuous (fun y : ℝ => -(y - β) / (δ ^ 2 + (y - β) ^ 2)) :=
    (continuous_id.sub continuous_const).neg.div
      (continuous_const.add ((continuous_id.sub continuous_const).pow 2)) (fun y => ne_of_gt (by positivity : 0 < δ ^ 2 + (y - β) ^ 2))
  have hi1 : IntervalIntegrable (fun y : ℝ => ((δ / (δ ^ 2 + (y - β) ^ 2) : ℝ) : ℂ)) volume c d :=
    (Complex.continuous_ofReal.comp hc1).intervalIntegrable c d
  have hi2 : IntervalIntegrable (fun y : ℝ => Complex.I * (((-(y - β) / (δ ^ 2 + (y - β) ^ 2) : ℝ) : ℂ))) volume c d :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable c d
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hint1 : ∫ y in c..d, δ / (δ ^ 2 + (y - β) ^ 2) =
      Real.arctan ((d - β) / δ) - Real.arctan ((c - β) / δ) := by
    have hd : ∀ y ∈ Set.uIcc c d, HasDerivAt (fun t : ℝ => Real.arctan ((t - β) / δ))
        (δ / (δ ^ 2 + (y - β) ^ 2)) y := by
      intro y _
      have h1 : HasDerivAt (fun t : ℝ => (t - β) / δ) (1 / δ) y := by
        simpa using ((hasDerivAt_id y).sub_const β).div_const δ
      have h2 := h1.arctan
      convert h2 using 1
      have hpos : δ ^ 2 + (y - β) ^ 2 ≠ 0 := by positivity
      field_simp [hδ, hpos]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable c d)
  have hint2 : ∫ y in c..d, -(y - β) / (δ ^ 2 + (y - β) ^ 2) =
      -(1 / 2 * (Real.log (δ ^ 2 + (d - β) ^ 2) - Real.log (δ ^ 2 + (c - β) ^ 2))) := by
    have hd : ∀ y ∈ Set.uIcc c d, HasDerivAt (fun t : ℝ => -(1 / 2 * Real.log (δ ^ 2 + (t - β) ^ 2)))
        (-(y - β) / (δ ^ 2 + (y - β) ^ 2)) y := by
      intro y _
      have hpos : δ ^ 2 + (y - β) ^ 2 ≠ 0 := by positivity
      have h1 : HasDerivAt (fun t : ℝ => δ ^ 2 + (t - β) ^ 2) (2 * (y - β)) y := by
        simpa [pow_one] using (((hasDerivAt_id y).sub_const β).fun_pow 2).const_add (δ ^ 2)
      have h2 := ((h1.log hpos).const_mul (1 / 2 : ℝ)).neg
      convert h2 using 1; field_simp [hpos]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable c d)]
    ring
  rw [hint1, hint2]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im]

lemma rectIntegral_inv_sub {ρ : ℂ} {a b c d : ℝ}
    (ha : a < ρ.re) (hb : ρ.re < b) (hc : c < ρ.im) (hd : ρ.im < d) :
    rectIntegral (fun z => (z - ρ)⁻¹) a b c d = 2 * Real.pi * Complex.I := by
  set α : ℝ := ρ.re
  set β : ℝ := ρ.im
  have hρ : ρ = (α : ℂ) + Complex.I * (β : ℂ) := by
    apply Complex.ext <;> simp [α, β]
  have h1 : ∫ x in a..b, ((x : ℂ) + Complex.I * (c : ℂ) - ρ)⁻¹ =
      ∫ x in a..b, (((x : ℂ) - (α : ℂ) + Complex.I * ((c - β : ℝ) : ℂ))⁻¹) :=
    intervalIntegral.integral_congr fun x _ => by rw [hρ]; congr 1; push_cast; ring
  have h2 : ∫ x in a..b, ((x : ℂ) + Complex.I * (d : ℂ) - ρ)⁻¹ =
      ∫ x in a..b, (((x : ℂ) - (α : ℂ) + Complex.I * ((d - β : ℝ) : ℂ))⁻¹) :=
    intervalIntegral.integral_congr fun x _ => by rw [hρ]; congr 1; push_cast; ring
  have h3 : ∫ y in c..d, ((b : ℂ) + Complex.I * (y : ℂ) - ρ)⁻¹ =
      ∫ y in c..d, ((((b - α : ℝ) : ℂ) + Complex.I * ((y : ℂ) - (β : ℂ)))⁻¹) :=
    intervalIntegral.integral_congr fun y _ => by rw [hρ]; congr 1; push_cast; ring
  have h4 : ∫ y in c..d, ((a : ℂ) + Complex.I * (y : ℂ) - ρ)⁻¹ =
      ∫ y in c..d, ((((a - α : ℝ) : ℂ) + Complex.I * ((y : ℂ) - (β : ℂ)))⁻¹) :=
    intervalIntegral.integral_congr fun y _ => by rw [hρ]; congr 1; push_cast; ring
  unfold rectIntegral
  rw [h1, h2, h3, h4,
    integral_inv_horiz a b α (c - β) (by linarith),
    integral_inv_horiz a b α (d - β) (by linarith),
    integral_inv_vert c d β (b - α) (by linarith),
    integral_inv_vert c d β (a - α) (by linarith)]
  have hpq : ∀ p q : ℝ, 0 < p → 0 < q → Real.arctan (p / q) + Real.arctan (q / p) = Real.pi / 2 := by
    intro p q hp hq
    have hinv : Real.arctan ((p / q)⁻¹) = Real.pi / 2 - Real.arctan (p / q) :=
      Real.arctan_inv_of_pos (div_pos hp hq)
    rw [inv_div] at hinv
    linarith
  set u1 : ℝ := α - a
  set u2 : ℝ := b - α
  set v1 : ℝ := β - c
  set v2 : ℝ := d - β
  have hu1 : 0 < u1 := by linarith
  have hu2 : 0 < u2 := by linarith
  have hv1 : 0 < v1 := by linarith
  have hv2 : 0 < v2 := by linarith
  have hdiv1 : (b - α) / (c - β) = -(u2 / v1) := by
    simp only [u2, v1]; field_simp [(by linarith : c - β ≠ 0), hv1.ne']; ring
  have hdiv2 : (a - α) / (c - β) = u1 / v1 := by
    simp only [u1, v1]; field_simp [(by linarith : c - β ≠ 0), hv1.ne']; ring
  have hdiv3 : (b - α) / (d - β) = u2 / v2 := by simp only [u2, v2]
  have hdiv4 : (a - α) / (d - β) = -(u1 / v2) := by
    simp only [u1, v2]; field_simp [hv2.ne']; ring
  have hdiv5 : (d - β) / (b - α) = v2 / u2 := by simp only [v2, u2]
  have hdiv6 : (c - β) / (b - α) = -(v1 / u2) := by
    simp only [v1, u2]; field_simp [hu2.ne']; ring
  have hdiv7 : (d - β) / (a - α) = -(v2 / u1) := by
    simp only [v2, u1]; field_simp [(by linarith : a - α ≠ 0), hu1.ne']; ring
  have hdiv8 : (c - β) / (a - α) = v1 / u1 := by
    simp only [v1, u1]; field_simp [(by linarith : a - α ≠ 0), hu1.ne']; ring
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.re_ofNat,
      Complex.im_ofNat, Complex.mul_im]
    ring
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_re, mul_zero, one_mul, add_zero, zero_add,
      Complex.im_ofNat, Complex.re_ofNat, Complex.mul_re]
    rw [hdiv1, hdiv2, hdiv3, hdiv4, hdiv5, hdiv6, hdiv7, hdiv8,
      Real.arctan_neg, Real.arctan_neg, Real.arctan_neg, Real.arctan_neg]
    have s1 := hpq u2 v1 hu2 hv1
    have s2 := hpq u1 v1 hu1 hv1
    have s3 := hpq u2 v2 hu2 hv2
    have s4 := hpq u1 v2 hu1 hv2
    linarith

lemma logDeriv_zpow_sub (ρ : ℂ) (k : ℤ) {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w : ℂ => (w - ρ) ^ k) z = (k : ℂ) / (z - ρ) := by
  have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hz
  have h1 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := by simpa using (hasDerivAt_id z).sub_const ρ
  have hd : HasDerivAt (fun w : ℂ => (w - ρ) ^ k) ((k : ℂ) * (z - ρ) ^ (k - 1)) z := by
    have hc := (hasDerivAt_zpow k (z - ρ) (Or.inl hne)).comp z h1
    change HasDerivAt (fun w : ℂ => (w - ρ) ^ k) ((k : ℂ) * (z - ρ) ^ (k - 1) * 1) z at hc
    rwa [mul_one] at hc
  rw [logDeriv_apply, hd.deriv, zpow_sub₀ hne, zpow_one]
  field_simp [hne, zpow_ne_zero k hne]

set_option maxHeartbeats 400000 in
theorem rectIntegral_logDeriv_mul {U : Set ℂ} (hU : IsOpen U) {F W : ℂ → ℂ}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hR_sub : Set.Icc a b ×ℂ Set.Icc c d ⊆ U)
    (hF_mero : MeromorphicOn F U)
    (hF_ntop : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (hW_diff : DifferentiableOn ℂ W U)
    (hbdy : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d,
      (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    rectIntegral (fun z => logDeriv F z * W z) a b c d =
      2 * Real.pi * Complex.I *
        ∑ᶠ ρ : ℂ, if ρ ∈ Set.Ioo a b ×ℂ Set.Ioo c d then (MeromorphicOn.divisor F U ρ : ℂ) * W ρ else 0 := by
  -- Step 1: Thicken `R` inside `U` to an open rectangle `V` with compact closure `K ⊆ U`
  set R : Set ℂ := Set.Icc a b ×ℂ Set.Icc c d
  have hR_comp : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨ε, hε, hthick⟩ := hR_comp.exists_thickening_subset_open hU hR_sub
  set δ : ℝ := ε / 3
  have hδ : 0 < δ := by positivity
  set K : Set ℂ := Set.Icc (a - δ) (b + δ) ×ℂ Set.Icc (c - δ) (d + δ)
  set V : Set ℂ := Set.Ioo (a - δ) (b + δ) ×ℂ Set.Ioo (c - δ) (d + δ)
  have hV_open : IsOpen V := isOpen_Ioo.reProdIm isOpen_Ioo
  have hK_comp : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hVK : V ⊆ K := fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hRV : R ⊆ V := by
    intro z hz
    refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hKU : K ⊆ U := by
    intro z hz
    apply hthick
    rw [Metric.mem_thickening_iff]
    let x : ℝ := max a (min b z.re)
    let y : ℝ := max c (min d z.im)
    have hx_lo : a ≤ x := le_max_left _ _
    have hx_hi : x ≤ b := max_le hab.le (min_le_left _ _)
    have hy_lo : c ≤ y := le_max_left _ _
    have hy_hi : y ≤ d := max_le hcd.le (min_le_left _ _)
    refine ⟨(x : ℂ) + Complex.I * (y : ℂ),
      ⟨⟨by simpa using hx_lo, by simpa using hx_hi⟩,
       ⟨by simpa using hy_lo, by simpa using hy_hi⟩⟩, ?_⟩
    rw [dist_eq_norm]
    have hre : |(z - ((x : ℂ) + Complex.I * (y : ℂ))).re| ≤ δ := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, x]
      rw [abs_le]
      rcases le_or_gt z.re a with h1 | h1
      · rw [min_eq_right (le_trans h1 hab.le), max_eq_left h1]
        constructor <;> linarith [hz.1.1]
      · rcases le_or_gt z.re b with h2 | h2
        · rw [min_eq_right h2, max_eq_right h1.le]
          constructor <;> linarith
        · rw [min_eq_left h2.le, max_eq_right hab.le]
          constructor <;> linarith [hz.1.2]
    have him : |(z - ((x : ℂ) + Complex.I * (y : ℂ))).im| ≤ δ := by
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, y]
      rw [abs_le]
      rcases le_or_gt z.im c with h1 | h1
      · rw [min_eq_right (le_trans h1 hcd.le), max_eq_left h1]
        constructor <;> linarith [hz.2.1]
      · rcases le_or_gt z.im d with h2 | h2
        · rw [min_eq_right h2, max_eq_right h1.le]
          constructor <;> linarith
        · rw [min_eq_left h2.le, max_eq_right hcd.le]
          constructor <;> linarith [hz.2.2]
    have hnorm : ‖z - ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ |(z - ((x : ℂ) + Complex.I * (y : ℂ))).re| +
        |(z - ((x : ℂ) + Complex.I * (y : ℂ))).im| := Complex.norm_le_abs_re_add_abs_im _
    have hδ_eq : δ = ε / 3 := rfl
    linarith
  have hVU : V ⊆ U := hVK.trans hKU
  -- Step 2: Divisor finiteness and factorization on `V`
  have hmero_K : MeromorphicOn F K := fun z hz => hF_mero z (hKU hz)
  have hmero_V : MeromorphicOn F V := fun z hz => hF_mero z (hVU hz)
  have hdiv_eq : ∀ z ∈ V, MeromorphicOn.divisor F V z = MeromorphicOn.divisor F U z := by
    intro z hz
    rw [MeromorphicOn.divisor_apply hmero_V hz, MeromorphicOn.divisor_apply hF_mero (hVU hz)]
  have hfin_K : (MeromorphicOn.divisor F K).support.Finite :=
    (MeromorphicOn.divisor F K).finiteSupport hK_comp
  have hfin_V : (MeromorphicOn.divisor F V).support.Finite := by
    refine hfin_K.subset fun z hz => ?_
    rw [Function.mem_support] at hz ⊢
    have hzV : z ∈ V := by
      by_contra hnot
      have : MeromorphicOn.divisor F V z = 0 := by unfold MeromorphicOn.divisor; simp [hnot]
      exact hz this
    rw [MeromorphicOn.divisor_apply hmero_K (hVK hzV), ← MeromorphicOn.divisor_apply hmero_V hzV]
    exact hz
  obtain ⟨g, hg_an, hg_ne, hfac_ae⟩ := hmero_V.extract_zeros_poles
    (fun u => hF_ntop u.1 (hVU u.2)) hfin_V
  set S : Finset ℂ := hfin_V.toFinset
  have hS_mem : ∀ z : ℂ, z ∈ S ↔ MeromorphicOn.divisor F V z ≠ 0 := by
    intro z; simp [S, Function.mem_support]
  have hS_sub_V : ∀ ρ ∈ S, ρ ∈ V := by
    intro ρ hρ
    by_contra hnot
    have : MeromorphicOn.divisor F V ρ = 0 := by unfold MeromorphicOn.divisor; simp [hnot]
    exact (hS_mem ρ).mp hρ this
  -- Step 3: On `∂R`, `F` agrees with `P` in a neighborhood, giving explicit `logDeriv F`
  let P : ℂ → ℂ := fun z => (∏ ρ ∈ S, (z - ρ) ^ (MeromorphicOn.divisor F V ρ)) * g z
  have hprod_eq : ∀ z : ℂ, (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor F V u) z =
      ∏ ρ ∈ S, (z - ρ) ^ (MeromorphicOn.divisor F V ρ) := by
    intro z
    rw [Function.FactorizedRational.finprod_eq_fun hfin_V]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      by_contra hnot
      rw [Finset.mem_coe] at hnot
      have h0 : MeromorphicOn.divisor F V u = 0 := not_not.mp ((hS_mem u).not.mp hnot)
      simp [h0] at hu)]
  have hnotS_bdy : ∀ z ∈ R, (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → z ∉ S := by
    intro z hz hb hmem
    obtain ⟨hFan, hFne⟩ := hbdy z hz hb
    have hdiv0 : MeromorphicOn.divisor F V z = 0 := by
      rw [MeromorphicOn.divisor_apply hmero_V (hRV hz), hFan.meromorphicOrderAt_eq,
        hFan.analyticOrderAt_eq_zero.mpr hFne]
      rfl
    exact (hS_mem z).mp hmem hdiv0
  have hlogDeriv_bdy : ∀ z ∈ R, (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) →
      logDeriv F z = (∑ ρ ∈ S, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ)) + logDeriv g z := by
    intro z hz hb
    obtain ⟨hFan, _⟩ := hbdy z hz hb
    have hzV : z ∈ V := hRV hz
    have hzS : z ∉ S := hnotS_bdy z hz hb
    obtain ⟨r, hr, hFan_ball⟩ := hFan.exists_ball_analyticOnNhd
    let O : Set ℂ := Metric.ball z r ∩ (V \ (S : Set ℂ))
    have hO_open : IsOpen O := Metric.isOpen_ball.inter (hV_open.sdiff S.finite_toSet.isClosed)
    have hzO : z ∈ O := ⟨Metric.mem_ball_self hr, hzV, hzS⟩
    have hP_cont : ContinuousOn P O := by
      have hprod_cont : ∀ (T : Finset ℂ),
          (∀ ρ ∈ T, ContinuousOn (fun w : ℂ => (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) O) →
          ContinuousOn (fun w : ℂ => ∏ ρ ∈ T, (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) O := by
        intro T hT
        induction T using Finset.induction_on with
        | empty => simp [continuousOn_const]
        | @insert p t hp ih =>
          have hmul_eq : (fun w : ℂ => ∏ ρ ∈ insert p t, (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) =
              fun w : ℂ => (w - p) ^ (MeromorphicOn.divisor F V p) *
                ∏ ρ ∈ t, (w - ρ) ^ (MeromorphicOn.divisor F V ρ) := by
            ext w; exact Finset.prod_insert hp
          rw [hmul_eq]
          exact (hT p (Finset.mem_insert_self p t)).mul (ih fun ρ hρ => hT ρ (Finset.mem_insert_of_mem hρ))
      have hp : ContinuousOn (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) O :=
        hprod_cont S fun ρ hρ =>
          ContinuousOn.zpow₀ (continuous_id.sub continuous_const).continuousOn _ fun w hw => Or.inl
            (sub_ne_zero.mpr fun (heq : w = ρ) => hw.2.2 (heq ▸ hρ))
      exact hp.mul (hg_an.continuousOn.mono fun w hw => hw.2.1)
    have hF_cont : ContinuousOn F O := hFan_ball.continuousOn.mono Set.inter_subset_left
    have hFP_eq : ∀ w ∈ O, F w = P w := by
      intro w hw
      have hev : ∀ᶠ u in 𝓝[≠] w, F u = P u := by
        have hnhds : O ∈ 𝓝 w := hO_open.mem_nhds hw
        have hdw := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfac_ae w hw.2.1
        filter_upwards [nhdsWithin_le_nhds hnhds, hdw] with u huO hu_eq
        have hu : F u = ((∏ᶠ v, (· - v) ^ MeromorphicOn.divisor F V v) • g) u :=
          hu_eq.resolve_right (not_not.mpr huO.2.1)
        simp only [Pi.smul_apply', smul_eq_mul, hprod_eq u] at hu
        exact hu
      have h1 : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
        (hF_cont.continuousAt (hO_open.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto P (𝓝[≠] w) (𝓝 (P w)) :=
        (hP_cont.continuousAt (hO_open.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique (h1.congr' hev) h2
    have hev_FP : F =ᶠ[𝓝 z] P := by
      filter_upwards [hO_open.mem_nhds hzO] with w hw using hFP_eq w hw
    have hld1 : logDeriv F z = logDeriv P z := by
      rw [logDeriv_apply, logDeriv_apply, hev_FP.deriv_eq, hev_FP.eq_of_nhds]
    rw [hld1]
    have hterm_ne : ∀ ρ ∈ S, (z - ρ) ^ (MeromorphicOn.divisor F V ρ) ≠ 0 :=
      fun ρ hρ => zpow_ne_zero _ (sub_ne_zero.mpr fun heq => hzS (heq ▸ hρ))
    have hterm_diff : ∀ ρ ∈ S, DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) z := by
      intro ρ hρ
      have h1 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := by simpa using (hasDerivAt_id z).sub_const ρ
      exact ((hasDerivAt_zpow (MeromorphicOn.divisor F V ρ) (z - ρ)
        (Or.inl (sub_ne_zero.mpr fun heq => hzS (heq ▸ hρ)))).comp z h1).differentiableAt
    have hprod_ne : (∏ ρ ∈ S, (z - ρ) ^ (MeromorphicOn.divisor F V ρ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hterm_ne
    have hprod_diff : DifferentiableAt ℂ (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) z := by
      have heq : (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) =
          ∏ ρ ∈ S, (fun w : ℂ => (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) := by
        ext w; simp [Finset.prod_apply]
      rw [heq]; exact DifferentiableAt.finsetProd hterm_diff
    have hld_P := logDeriv_fun_mul (f := fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (MeromorphicOn.divisor F V ρ))
      (g := g) z hprod_ne (hg_ne ⟨z, hzV⟩) hprod_diff (hg_an z hzV).differentiableAt
    rw [hld_P]
    congr 1
    rw [logDeriv_fun_prod (f := fun ρ w => (w - ρ) ^ (MeromorphicOn.divisor F V ρ)) hterm_ne hterm_diff]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    exact logDeriv_zpow_sub ρ (MeromorphicOn.divisor F V ρ) (fun heq => hzS (heq ▸ hρ))
  -- Step 4: Split `S` into `S_in` (inside open rectangle) and `S_out` (outside closed rectangle)
  let S_in : Finset ℂ := S.filter (fun ρ => ρ ∈ Set.Ioo a b ×ℂ Set.Ioo c d)
  let S_out : Finset ℂ := S.filter (fun ρ => ρ ∉ Set.Ioo a b ×ℂ Set.Ioo c d)
  have hS_out_notR : ∀ ρ ∈ S_out, ρ ∉ R := by
    intro ρ hρ hρR
    have hρS : ρ ∈ S := (Finset.mem_filter.mp hρ).1
    have hnot_int : ρ ∉ Set.Ioo a b ×ℂ Set.Ioo c d := (Finset.mem_filter.mp hρ).2
    have hbdy_ρ : ρ.re = a ∨ ρ.re = b ∨ ρ.im = c ∨ ρ.im = d := by
      by_contra hnot
      push Not at hnot
      exact hnot_int ⟨⟨lt_of_le_of_ne hρR.1.1 hnot.1.symm, lt_of_le_of_ne hρR.1.2 hnot.2.1⟩,
        ⟨lt_of_le_of_ne hρR.2.1 hnot.2.2.1.symm, lt_of_le_of_ne hρR.2.2 hnot.2.2.2⟩⟩
    exact hnotS_bdy ρ hρR hbdy_ρ hρS
  -- Define holomorphic remainder `H` on `R`
  let H : ℂ → ℂ := fun z =>
    (∑ ρ ∈ S_in, (MeromorphicOn.divisor F V ρ : ℂ) * dslope W ρ z) +
    (∑ ρ ∈ S_out, (MeromorphicOn.divisor F V ρ : ℂ) * W z / (z - ρ)) +
    logDeriv g z * W z
  have hH_diff : DifferentiableOn ℂ H (Set.uIcc a b ×ℂ Set.uIcc c d) := by
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le hcd.le]
    have hsum_diff : ∀ (T : Finset ℂ) (φ : ℂ → ℂ → ℂ),
        (∀ ρ ∈ T, DifferentiableOn ℂ (φ ρ) R) → DifferentiableOn ℂ (fun z => ∑ ρ ∈ T, φ ρ z) R := by
      intro T φ hφ
      induction T using Finset.induction_on with
      | empty => simp [differentiableOn_const]
      | @insert p t hp ih =>
        have hsum_eq : (fun z => ∑ ρ ∈ insert p t, φ ρ z) = fun z => φ p z + ∑ ρ ∈ t, φ ρ z := by
          ext z; exact Finset.sum_insert hp
        rw [hsum_eq]
        exact (hφ p (Finset.mem_insert_self p t)).add (ih (fun ρ hρ => hφ ρ (Finset.mem_insert_of_mem hρ)))
    have h1 : DifferentiableOn ℂ (fun z => ∑ ρ ∈ S_in, (MeromorphicOn.divisor F V ρ : ℂ) * dslope W ρ z) R := by
      refine hsum_diff S_in _ fun ρ hρ => ?_
      have hρV : ρ ∈ V := hS_sub_V ρ (Finset.mem_filter.mp hρ).1
      have hdsl : DifferentiableOn ℂ (dslope W ρ) V :=
        (Complex.differentiableOn_dslope (hV_open.mem_nhds hρV)).mpr (hW_diff.mono hVU)
      exact (differentiableOn_const _).mul (hdsl.mono hRV)
    have h2 : DifferentiableOn ℂ (fun z => ∑ ρ ∈ S_out, (MeromorphicOn.divisor F V ρ : ℂ) * W z / (z - ρ)) R := by
      refine hsum_diff S_out _ fun ρ hρ => ?_
      have hne : ∀ z ∈ R, z - ρ ≠ 0 := fun z hz h0 => hS_out_notR ρ hρ (sub_eq_zero.mp h0 ▸ hz)
      exact ((differentiableOn_const _).mul (hW_diff.mono hR_sub)).div
        (differentiableOn_id.sub (differentiableOn_const ρ)) hne
    have h3 : DifferentiableOn ℂ (fun z => logDeriv g z * W z) R := by
      have hg_ld : DifferentiableOn ℂ (logDeriv g) V := by
        intro z hz
        rw [logDeriv]
        exact ((hg_an.deriv z hz).differentiableAt.div (hg_an z hz).differentiableAt (hg_ne ⟨z, hz⟩)).differentiableWithinAt
      exact (hg_ld.mono hRV).mul (hW_diff.mono hR_sub)
    exact (h1.add h2).add h3
  have hH_zero : rectIntegral H a b c d = 0 := rectIntegral_eq_zero_of_differentiableOn hH_diff
  -- On `∂R`, `logDeriv F z * W z = H z + ∑ ρ ∈ S_in, d(ρ) * W(ρ) * (z - ρ)⁻¹`
  have hbdy_decomp : ∀ z ∈ R, (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) →
      logDeriv F z * W z =
        H z + ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (z - ρ)⁻¹ := by
    intro z hz hb
    rw [hlogDeriv_bdy z hz hb, add_mul, Finset.sum_mul]
    have hsplit_S : ∑ ρ ∈ S, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ) * W z =
        (∑ ρ ∈ S_in, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ) * W z) +
        (∑ ρ ∈ S_out, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ) * W z) :=
      (Finset.sum_filter_add_sum_filter_not S (fun ρ => ρ ∈ Set.Ioo a b ×ℂ Set.Ioo c d) _).symm
    rw [hsplit_S]
    have hin_eq : ∑ ρ ∈ S_in, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ) * W z =
        (∑ ρ ∈ S_in, (MeromorphicOn.divisor F V ρ : ℂ) * dslope W ρ z) +
        (∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (z - ρ)⁻¹) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hzρ : z ≠ ρ := fun heq => hnotS_bdy z hz hb (heq ▸ (Finset.mem_filter.mp hρ).1)
      rw [dslope_of_ne _ hzρ, slope_def_field]
      have hne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
      field_simp [hne]; ring
    have hout_eq : ∑ ρ ∈ S_out, (MeromorphicOn.divisor F V ρ : ℂ) / (z - ρ) * W z =
        ∑ ρ ∈ S_out, (MeromorphicOn.divisor F V ρ : ℂ) * W z / (z - ρ) :=
      Finset.sum_congr rfl fun ρ _ => by ring
    rw [hin_eq, hout_eq]
    simp only [H]; ring
  rw [rectIntegral_congr hab.le hcd.le hbdy_decomp]
  -- Continuity of `H` and `(z - ρ)⁻¹` along the 4 edges gives `IntervalIntegrable`
  have hH_cont : ContinuousOn H R := by
    have := hH_diff.continuousOn
    rwa [Set.uIcc_of_le hab.le, Set.uIcc_of_le hcd.le] at this
  have hinv_cont : ∀ ρ ∈ S_in, ContinuousOn (fun z => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (z - ρ)⁻¹)
      (R \ {ρ}) := fun ρ _ =>
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.mpr hz.2)
  have hH_int1 : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + Complex.I * (c : ℂ))) volume a b :=
    (hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => by
      rw [Set.uIcc_of_le hab.le] at hx; exact ⟨by simpa using hx, by simp [hcd.le]⟩).intervalIntegrable
  have hH_int2 : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + Complex.I * (d : ℂ))) volume a b :=
    (hH_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => by
      rw [Set.uIcc_of_le hab.le] at hx; exact ⟨by simpa using hx, by simp [hcd.le]⟩).intervalIntegrable
  have hH_int3 : IntervalIntegrable (fun y : ℝ => H ((b : ℂ) + Complex.I * (y : ℂ))) volume c d :=
    (hH_cont.comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy => by
      rw [Set.uIcc_of_le hcd.le] at hy; exact ⟨by simp [hab.le], by simpa using hy⟩).intervalIntegrable
  have hH_int4 : IntervalIntegrable (fun y : ℝ => H ((a : ℂ) + Complex.I * (y : ℂ))) volume c d :=
    (hH_cont.comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy => by
      rw [Set.uIcc_of_le hcd.le] at hy; exact ⟨by simp [hab.le], by simpa using hy⟩).intervalIntegrable
  have hp_int1 : ∀ ρ ∈ S_in, IntervalIntegrable
      (fun x : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (c : ℂ)) - ρ)⁻¹) volume a b := by
    intro ρ hρ
    have hρ_int := (Finset.mem_filter.mp hρ).2
    exact ((hinv_cont ρ hρ).comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => by
      rw [Set.uIcc_of_le hab.le] at hx
      refine ⟨⟨by simpa using hx, by simp [hcd.le]⟩, fun heq => ?_⟩
      have := congrArg Complex.im heq; simp at this; linarith [hρ_int.2.1]).intervalIntegrable
  have hp_int2 : ∀ ρ ∈ S_in, IntervalIntegrable
      (fun x : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (d : ℂ)) - ρ)⁻¹) volume a b := by
    intro ρ hρ
    have hρ_int := (Finset.mem_filter.mp hρ).2
    exact ((hinv_cont ρ hρ).comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx => by
      rw [Set.uIcc_of_le hab.le] at hx
      refine ⟨⟨by simpa using hx, by simp [hcd.le]⟩, fun heq => ?_⟩
      have := congrArg Complex.im heq; simp at this; linarith [hρ_int.2.2]).intervalIntegrable
  have hp_int3 : ∀ ρ ∈ S_in, IntervalIntegrable
      (fun y : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((b : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) volume c d := by
    intro ρ hρ
    have hρ_int := (Finset.mem_filter.mp hρ).2
    exact ((hinv_cont ρ hρ).comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy => by
      rw [Set.uIcc_of_le hcd.le] at hy
      refine ⟨⟨by simp [hab.le], by simpa using hy⟩, fun heq => ?_⟩
      have := congrArg Complex.re heq; simp at this; linarith [hρ_int.1.2]).intervalIntegrable
  have hp_int4 : ∀ ρ ∈ S_in, IntervalIntegrable
      (fun y : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((a : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) volume c d := by
    intro ρ hρ
    have hρ_int := (Finset.mem_filter.mp hρ).2
    exact ((hinv_cont ρ hρ).comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy => by
      rw [Set.uIcc_of_le hcd.le] at hy
      refine ⟨⟨by simp [hab.le], by simpa using hy⟩, fun heq => ?_⟩
      have := congrArg Complex.re heq; simp at this; linarith [hρ_int.1.1]).intervalIntegrable
  have hp_sum1 : IntervalIntegrable (fun x : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (c : ℂ)) - ρ)⁻¹) volume a b := by
    have heq : (fun x : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (c : ℂ)) - ρ)⁻¹) =
        ∑ ρ ∈ S_in, (fun x : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (c : ℂ)) - ρ)⁻¹) := by
      ext x; simp [Finset.sum_apply]
    rw [heq]; exact IntervalIntegrable.sum S_in hp_int1
  have hp_sum2 : IntervalIntegrable (fun x : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (d : ℂ)) - ρ)⁻¹) volume a b := by
    have heq : (fun x : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (d : ℂ)) - ρ)⁻¹) =
        ∑ ρ ∈ S_in, (fun x : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((x : ℂ) + Complex.I * (d : ℂ)) - ρ)⁻¹) := by
      ext x; simp [Finset.sum_apply]
    rw [heq]; exact IntervalIntegrable.sum S_in hp_int2
  have hp_sum3 : IntervalIntegrable (fun y : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((b : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) volume c d := by
    have heq : (fun y : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((b : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) =
        ∑ ρ ∈ S_in, (fun y : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((b : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) := by
      ext y; simp [Finset.sum_apply]
    rw [heq]; exact IntervalIntegrable.sum S_in hp_int3
  have hp_sum4 : IntervalIntegrable (fun y : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((a : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) volume c d := by
    have heq : (fun y : ℝ => ∑ ρ ∈ S_in, ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((a : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) =
        ∑ ρ ∈ S_in, (fun y : ℝ => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (((a : ℂ) + Complex.I * (y : ℂ)) - ρ)⁻¹) := by
      ext y; simp [Finset.sum_apply]
    rw [heq]; exact IntervalIntegrable.sum S_in hp_int4
  rw [rectIntegral_add hH_int1 hH_int2 hH_int3 hH_int4 hp_sum1 hp_sum2 hp_sum3 hp_sum4,
    hH_zero, zero_add,
    rectIntegral_finset_sum S_in _ hp_int1 hp_int2 hp_int3 hp_int4]
  have hsum_eval : ∑ ρ ∈ S_in, rectIntegral (fun z => ((MeromorphicOn.divisor F V ρ : ℂ) * W ρ) * (z - ρ)⁻¹) a b c d =
      2 * Real.pi * Complex.I * ∑ ρ ∈ S_in, (MeromorphicOn.divisor F U ρ : ℂ) * W ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρS : ρ ∈ S := (Finset.mem_filter.mp hρ).1
    have hρ_int := (Finset.mem_filter.mp hρ).2
    rw [rectIntegral_const_mul, rectIntegral_inv_sub hρ_int.1.1 hρ_int.1.2 hρ_int.2.1 hρ_int.2.2,
      hdiv_eq ρ (hS_sub_V ρ hρS)]
    ring
  rw [hsum_eval]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := S_in)]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    simp [(Finset.mem_filter.mp hρ).2]
  · intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hint : ρ ∈ Set.Ioo a b ×ℂ Set.Ioo c d
    · simp only [hint, ↓reduceIte] at hρ
      have hρV : ρ ∈ V := hRV ⟨⟨hint.1.1.le, hint.1.2.le⟩, ⟨hint.2.1.le, hint.2.2.le⟩⟩
      have hdne : MeromorphicOn.divisor F V ρ ≠ 0 := by
        rw [hdiv_eq ρ hρV]
        intro h0; simp [h0] at hρ
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(hS_mem ρ).mpr hdne, hint⟩)
    · simp [hint] at hρ

/-! #### Part 5C: Riemann-von Mangoldt Formula -/

lemma riemannZeta_no_zero_im_of_good_height {H : ℝ} (hH : 2 ≤ H)
    (hseg : ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 → riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ H := by
  intro ρ hρ him
  by_cases hre1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re hre1 hρ
  · by_cases hre0 : ρ.re ≤ 0
    · have hxi : xiFun ρ ≠ 0 := xiFun_ne_zero_of_re_nonpos hre0
      -- Functional equation at `1 - ρ`: `riemannZeta ρ = 0` with `ρ.im = H ≥ 2` contradicts `ξ(ρ) ≠ 0`
      have hρ0 : ρ ≠ 0 := by intro h; rw [h] at him; simp at him; linarith
      have hρ1 : ρ ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
      have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
      have hne_neg : ∀ n : ℕ, 1 - ρ ≠ -(n : ℂ) := by
        intro n h; have := congrArg Complex.im h; simp [him] at this; linarith
      have hfe := riemannZeta_one_sub hne_neg (by intro h; have := congrArg Complex.im h; simp [him] at this; linarith)
      rw [sub_sub_cancel] at hfe
      rw [hρ] at hfe
      have hpi : (2 * (Real.pi : ℂ)) ^ (-(1 - ρ)) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))]
        exact Complex.exp_ne_zero _
      have hG : Complex.Gamma (1 - ρ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
      have hcos : Complex.cos ((Real.pi : ℂ) * (1 - ρ) / 2) ≠ 0 := by
        intro hc
        rw [Complex.cos_eq_zero_iff] at hc
        obtain ⟨k, hk⟩ := hc
        have := congrArg Complex.im hk
        simp [him] at this
        have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
        have : H = 0 := by nlinarith
        linarith
      have hzr : riemannZeta (1 - ρ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
      have hprod_ne : 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - ρ)) * Complex.Gamma (1 - ρ) *
          Complex.cos ((Real.pi : ℂ) * (1 - ρ) / 2) * riemannZeta (1 - ρ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hG) hcos) hzr
      exact hprod_ne hfe.symm
    · push Not at hre1 hre0
      have hEq : ρ = ((ρ.re : ℂ) + Complex.I * (H : ℂ)) := by
        apply Complex.ext <;> simp [him]
      rw [hEq] at hρ
      exact hseg ρ.re (by linarith) (by linarith) hρ

lemma integral_re_logDeriv_zeta_two_bound
    (hzeta2_re : ∀ t : ℝ, (1 / 4 : ℝ) ≤ (riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ))).re)
    (T : ℝ) (_hT : 0 ≤ T) :
    |∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re| ≤ 2 * Real.pi := by
  let g : ℝ → ℂ := fun y => Complex.log (riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
  have hslit : ∀ y : ℝ, riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) ∈ Complex.slitPlane :=
    fun y => Or.inl (lt_of_lt_of_le (by norm_num) (hzeta2_re y))
  have hzne : ∀ y : ℝ, riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) ≠ 0 :=
    fun y => Complex.slitPlane_ne_zero (hslit y)
  have hne1 : ∀ y : ℝ, ((2 : ℂ) + Complex.I * (y : ℂ)) ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (g t).im)
      (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re y := by
    intro y
    have h1 : HasDerivAt (fun z : ℂ => (2 : ℂ) + Complex.I * z) Complex.I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).const_mul Complex.I).const_add (2 : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => riemannZeta ((2 : ℂ) + Complex.I * z))
        (deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) * Complex.I) (y : ℂ) :=
      (differentiableAt_riemannZeta (hne1 y)).hasDerivAt.comp (y : ℂ) h1
    have h3 : HasDerivAt (fun z : ℂ => Complex.log (riemannZeta ((2 : ℂ) + Complex.I * z)))
        ((deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) * Complex.I) /
          riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) (y : ℂ) :=
      h2.clog (hslit y)
    have h3r : HasDerivAt g
        ((deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) * Complex.I) /
          riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) y :=
      h3.comp_ofReal
    have h4 : HasDerivAt (fun x : ℝ => (g x).im)
        (((deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) * Complex.I) /
          riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).im) y :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h3r
    convert h4 using 1
    rw [logDeriv_apply]
    have heq : (deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) * Complex.I) /
        riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) =
        Complex.I * (deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) /
          riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) := by ring
    rw [heq]; simp
  have hcont : Continuous (fun y : ℝ => (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re) := by
    have hdz : Continuous (fun y : ℝ => deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) := by
      have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
        differentiableOn_riemannZeta.analyticOnNhd isOpen_ne
      exact han.deriv.continuousOn.comp_continuous
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)) hne1
    have hz : Continuous (fun y : ℝ => riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) :=
      differentiableOn_riemannZeta.continuousOn.comp_continuous
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)) hne1
    exact Complex.continuous_re.comp (hdz.div hz hzne)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hcont.intervalIntegrable 0 T)]
  have h1 : |(g T).im| ≤ Real.pi := by
    simp only [g, Complex.log_im]; exact Complex.abs_arg_le_pi _
  have h2 : |(g 0).im| ≤ Real.pi := by
    simp only [g, Complex.log_im]; exact Complex.abs_arg_le_pi _
  calc |(g T).im - (g 0).im| ≤ |(g T).im| + |(g 0).im| := abs_sub _ _
    _ ≤ Real.pi + Real.pi := add_le_add h1 h2
    _ = 2 * Real.pi := by ring

lemma integral_re_digamma_two_main
    (hdigamma : ∀ z : ℂ, (1 / 4 : ℝ) ≤ z.re → ‖logDeriv Complex.Gamma z - Complex.log z‖ ≤ 20 / ‖z‖)
    (T : ℝ) (hT : 2 ≤ T) :
    |(∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
      ((1 / 2 : ℝ) * (T * Real.log (T / 2) - T))| ≤ 50 * Real.log (2 + T) + 10 := by
  have hcont_dig : Continuous (fun y : ℝ => (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
      (Complex.differentiableAt_Gamma z fun m hm => by
        have := congrArg Complex.re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < z.re from hz]).differentiableWithinAt
    have han : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := hdiff.analyticOnNhd hopen
    have hpath : Continuous (fun y : ℝ => (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)) :=
      continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.div_const 2)))
    have hmem : ∀ y : ℝ, (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := fun y => by
      show (0 : ℝ) < ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)).re; simp
    have hGne : ∀ y : ℝ, Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)) ≠ 0 := fun y =>
      Complex.Gamma_ne_zero_of_re_pos (hmem y)
    exact Complex.continuous_re.comp ((han.deriv.continuousOn.comp_continuous hpath hmem).div
      (han.continuousOn.comp_continuous hpath hmem) hGne)
  have hcont_log : Continuous (fun y : ℝ => Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) := by
    have hpath : Continuous (fun y : ℝ => (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)) :=
      continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.div_const 2)))
    refine Real.continuousOn_log.comp_continuous hpath.norm (fun y => ?_)
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ := by
      have := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))
      have hre : ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)).re = 1 := by simp
      rw [hre, abs_one] at this; exact this
    exact ne_of_gt (by linarith)
  -- Step 1: Bound `|∫_0^T (1/2) (Re ψ(1 + iy/2) - log ‖1 + iy/2‖) dy| ≤ 40 log(2 + T)`
  have herr1 : |∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) *
      ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
       Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)| ≤ 40 * Real.log (2 + T) := by
    have hpt : ∀ y ∈ Set.Icc (0 : ℝ) T,
        |(1 / 2 : ℝ) * ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
         Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)| ≤ 40 / (1 + y) := by
      intro y hy
      set z : ℂ := (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)
      have hz_re : (1 / 4 : ℝ) ≤ z.re := by simp [z]; norm_num
      have hbd := hdigamma z hz_re
      have hre_diff : |(logDeriv Complex.Gamma z).re - Real.log ‖z‖| ≤ 20 / ‖z‖ := by
        have h1 : (logDeriv Complex.Gamma z).re - Real.log ‖z‖ = (logDeriv Complex.Gamma z - Complex.log z).re := by
          simp [Complex.log_re]
        rw [h1]
        exact (Complex.abs_re_le_norm _).trans hbd
      have hnorm_lb : (1 + y) / 4 ≤ ‖z‖ := by
        have h1 : (1 : ℝ) ≤ ‖z‖ := by
          have := Complex.abs_re_le_norm z
          have hre : z.re = 1 := by simp [z]
          rw [hre, abs_one] at this; exact this
        have h2 : y / 2 ≤ ‖z‖ := by
          have := Complex.abs_im_le_norm z
          have him : z.im = y / 2 := by simp [z]
          rw [him, abs_of_nonneg (by linarith [hy.1] : 0 ≤ y / 2)] at this; exact this
        linarith
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc (1 / 2 : ℝ) * |(logDeriv Complex.Gamma z).re - Real.log ‖z‖|
          ≤ (1 / 2 : ℝ) * (20 / ‖z‖) := by gcongr
        _ ≤ (1 / 2 : ℝ) * (20 / ((1 + y) / 4)) := by
            gcongr
            exact div_pos (by linarith [hy.1]) (by norm_num)
        _ = 40 / (1 + y) := by field_simp [(by linarith [hy.1] : 1 + y ≠ 0)]; ring
    have hint_diff : IntervalIntegrable (fun y : ℝ => |(1 / 2 : ℝ) *
        ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
         Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)|) volume 0 T :=
      ((continuous_const.mul (hcont_dig.sub hcont_log)).abs).intervalIntegrable 0 T
    have hint_rhs : IntervalIntegrable (fun y : ℝ => 40 / (1 + y)) volume 0 T :=
      (continuousOn_const.div (continuousOn_const.add continuousOn_id) fun y hy => by
        rw [Set.uIcc_of_le (by linarith)] at hy; show 1 + y ≠ 0; linarith [hy.1]).intervalIntegrable
    calc |∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) *
            ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
             Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)|
        ≤ ∫ y in (0 : ℝ)..T, |(1 / 2 : ℝ) *
            ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
             Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)| := by
          simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
            (f := fun y : ℝ => (1 / 2 : ℝ) *
              ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
               Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)) (by linarith : (0 : ℝ) ≤ T)
      _ ≤ ∫ y in (0 : ℝ)..T, 40 / (1 + y) :=
          intervalIntegral.integral_mono_on (by linarith) hint_diff hint_rhs hpt
      _ = 40 * Real.log (1 + T) := by
          have hd : ∀ y ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun x : ℝ => 40 * Real.log (1 + x)) (40 / (1 + y)) y := by
            intro y hy
            rw [Set.uIcc_of_le (by linarith)] at hy
            have h0 : HasDerivAt (fun x : ℝ => 1 + x) 1 y := by simpa using (hasDerivAt_id y).const_add (1 : ℝ)
            have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + y)) y := h0.log (by linarith [hy.1])
            convert h1.const_mul 40 using 1; ring
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_rhs]; simp
      _ ≤ 40 * Real.log (2 + T) := by
          gcongr; linarith
  -- Step 2: Evaluate `∫_0^T (1/2) log ‖1 + iy/2‖ dy` against `(1/2)(T log(T/2) - T)`
  have herr2 : |(∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
      (1 / 2 : ℝ) * (T * Real.log (T / 2) - T)| ≤ 10 := by
    have hsplit : ∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ =
        (∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) +
        (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_const.mul hcont_log).intervalIntegrable 0 2)
        ((continuous_const.mul hcont_log).intervalIntegrable 2 T)).symm
    have h02 : |∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖| ≤ 2 := by
      have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 2,
          |(1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖| ≤ 1 := by
        intro y hy
        set z : ℂ := (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)
        have hz_re : z.re = 1 := by simp [z]
        have hz_im : z.im = y / 2 := by simp [z]
        have h1 : (1 : ℝ) ≤ ‖z‖ := by
          have := Complex.abs_re_le_norm z; rw [hz_re, abs_one] at this; exact this
        have h2 : ‖z‖ ≤ 2 := by
          have := Complex.norm_le_abs_re_add_abs_im z
          rw [hz_re, hz_im, abs_one, abs_of_nonneg (by linarith [hy.1] : 0 ≤ y / 2)] at this
          linarith [hy.2]
        have hlog0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
        have hlog2 : Real.log ‖z‖ ≤ 1 := by
          calc Real.log ‖z‖ ≤ ‖z‖ - 1 := Real.log_le_sub_one_of_pos (by linarith)
            _ ≤ 1 := by linarith
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hlog0]
        linarith
      calc |∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖|
          ≤ ∫ y in (0 : ℝ)..2, |(1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun y : ℝ => (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) (by norm_num : (0 : ℝ) ≤ 2)
        _ ≤ ∫ _y in (0 : ℝ)..2, (1 : ℝ) :=
            intervalIntegral.integral_mono_on (by norm_num)
              ((continuous_const.mul hcont_log).abs.intervalIntegrable 0 2)
              (continuous_const.intervalIntegrable 0 2) hpt
        _ = 2 := by simp
    have hmain_int : ∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / 2) =
        (1 / 2 : ℝ) * (T * Real.log (T / 2) - T) + 1 := by
      have hd : ∀ y ∈ Set.uIcc (2 : ℝ) T, HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (x * Real.log (x / 2) - x))
          ((1 / 2 : ℝ) * Real.log (y / 2)) y := by
        intro y hy
        rw [Set.uIcc_of_le hT] at hy
        have hy0 : y ≠ 0 := by linarith [hy.1]
        have hid : HasDerivAt (fun x : ℝ => x) 1 y := hasDerivAt_id y
        have hlog : HasDerivAt (fun x : ℝ => Real.log (x / 2)) (1 / y) y := by
          have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) y := by simpa using hid.div_const 2
          convert h1.log (by positivity : y / 2 ≠ 0) using 1; field_simp [hy0]
        have hmul : HasDerivAt (fun x : ℝ => x * Real.log (x / 2) - x) (1 * Real.log (y / 2) + y * (1 / y) - 1) y :=
          (hid.mul hlog).sub hid
        convert hmul.const_mul (1 / 2 : ℝ) using 1
        field_simp [hy0]; ring
      have hc : ContinuousOn (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y / 2)) (Set.uIcc 2 T) :=
        continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.div_const 2) fun y hy => by
          rw [Set.uIcc_of_le hT] at hy; show y / 2 ≠ 0; linarith [hy.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
      norm_num
    have h2T : |(∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
        (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / 2))| ≤ 2 := by
      have hc2 : ContinuousOn (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y / 2)) (Set.uIcc 2 T) :=
        continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.div_const 2) fun y hy => by
          rw [Set.uIcc_of_le hT] at hy; show y / 2 ≠ 0; linarith [hy.1])
      have hi1 : IntervalIntegrable (fun y : ℝ => (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) volume 2 T :=
        (continuous_const.mul hcont_log).intervalIntegrable 2 T
      rw [← intervalIntegral.integral_sub hi1 hc2.intervalIntegrable]
      have hpt : ∀ y ∈ Set.Icc (2 : ℝ) T,
          |(1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ - (1 / 2 : ℝ) * Real.log (y / 2)| ≤
            2 / y ^ 2 := by
        intro y hy
        have hy0 : 0 < y := by linarith [hy.1]
        set z : ℂ := (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)
        have hnsq : ‖z‖ ^ 2 = 1 + (y / 2) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp [z]; ring
        have hnorm_ge : y / 2 ≤ ‖z‖ := by
          have := Complex.abs_im_le_norm z
          have him : z.im = y / 2 := by simp [z]
          rw [him, abs_of_pos (by positivity : 0 < y / 2)] at this; exact this
        have hdiff_nn : 0 ≤ Real.log ‖z‖ - Real.log (y / 2) :=
          sub_nonneg.mpr (Real.log_le_log (by positivity) hnorm_ge)
        have hdiff_le : Real.log ‖z‖ - Real.log (y / 2) ≤ 2 / y ^ 2 := by
          have h1 : 2 * (Real.log ‖z‖ - Real.log (y / 2)) = Real.log (1 + 4 / y ^ 2) := by
            rw [mul_sub, show (2 : ℝ) * Real.log ‖z‖ = Real.log (‖z‖ ^ 2) by rw [Real.log_pow]; ring,
              show (2 : ℝ) * Real.log (y / 2) = Real.log ((y / 2) ^ 2) by rw [Real.log_pow]; ring,
              hnsq, ← Real.log_div (by positivity) (by positivity)]
            congr 1; field_simp [hy0.ne']; ring
          have h2 : Real.log (1 + 4 / y ^ 2) ≤ 4 / y ^ 2 := by
            linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 4 / y ^ 2)]
          have h4 : 4 / y ^ 2 = 2 * (2 / y ^ 2) := by ring
          linarith
        have hrewrite : (1 / 2 : ℝ) * Real.log ‖z‖ - (1 / 2 : ℝ) * Real.log (y / 2) =
            (1 / 2 : ℝ) * (Real.log ‖z‖ - Real.log (y / 2)) := by ring
        rw [hrewrite, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hdiff_nn]
        linarith
      have hint_rhs : IntervalIntegrable (fun y : ℝ => 2 / y ^ 2) volume 2 T :=
        (continuousOn_const.div (continuousOn_id.pow 2) fun y hy => by
          rw [Set.uIcc_of_le hT] at hy
          show y ^ 2 ≠ 0
          exact pow_ne_zero 2 (ne_of_gt (by linarith [hy.1]))).intervalIntegrable
      calc |∫ y in (2 : ℝ)..T, ((1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ -
              (1 / 2 : ℝ) * Real.log (y / 2))|
          ≤ ∫ y in (2 : ℝ)..T, |(1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ -
              (1 / 2 : ℝ) * Real.log (y / 2)| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun y : ℝ => (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖ -
                (1 / 2 : ℝ) * Real.log (y / 2)) hT
        _ ≤ ∫ y in (2 : ℝ)..T, 2 / y ^ 2 :=
            intervalIntegral.integral_mono_on hT
              ((hi1.sub hc2.intervalIntegrable).norm)
              hint_rhs hpt
        _ = 1 - 2 / T := by
            have hd : ∀ y ∈ Set.uIcc (2 : ℝ) T, HasDerivAt (fun x : ℝ => -2 / x) (2 / y ^ 2) y := by
              intro y hy
              rw [Set.uIcc_of_le hT] at hy
              have hy0 : y ≠ 0 := by linarith [hy.1]
              have h1 : HasDerivAt (fun x : ℝ => (-2 : ℝ) * x⁻¹) ((-2 : ℝ) * (-(y ^ 2)⁻¹)) y :=
                (hasDerivAt_inv hy0).const_mul (-2 : ℝ)
              have heq_f : (fun x : ℝ => -2 / x) = (fun x : ℝ => (-2 : ℝ) * x⁻¹) := by ext x; ring
              rw [heq_f]
              convert h1 using 1; field_simp [hy0]
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_rhs]; ring
        _ ≤ 2 := by
            have : 0 ≤ 2 / T := by positivity
            linarith
    rw [hsplit]
    have hrearr : (∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) +
        (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
        (1 / 2 : ℝ) * (T * Real.log (T / 2) - T) =
        (∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) +
        ((∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
         (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / 2))) + 1 := by
      linarith [hmain_int]
    rw [hrearr]
    calc _ ≤ |(∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) +
            ((∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
             (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / 2)))| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ (|∫ y in (0 : ℝ)..2, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖| +
            |(∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
             (∫ y in (2 : ℝ)..T, (1 / 2 : ℝ) * Real.log (y / 2))|) + 1 := by
            rw [abs_one]; gcongr; exact abs_add_le _ _
      _ ≤ 10 := by linarith
  have hsub : (∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
      (∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) =
      ∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) *
        ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
         Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) := by
    have hi1 : IntervalIntegrable (fun y : ℝ => (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) volume 0 T :=
      (continuous_const.mul hcont_dig).intervalIntegrable 0 T
    have hi2 : IntervalIntegrable (fun y : ℝ => (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) volume 0 T :=
      (continuous_const.mul hcont_log).intervalIntegrable 0 T
    rw [← intervalIntegral.integral_sub hi1 hi2]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have htri : (∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
      (1 / 2 : ℝ) * (T * Real.log (T / 2) - T) =
      ((∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
       (∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)) +
      ((∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
       (1 / 2 : ℝ) * (T * Real.log (T / 2) - T)) := by ring
  rw [htri, hsub]
  have hlog_nn : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  calc _ ≤ |∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) *
            ((logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re -
             Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖)| +
          |(∫ y in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log ‖(1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)‖) -
           (1 / 2 : ℝ) * (T * Real.log (T / 2) - T)| := abs_add_le _ _
    _ ≤ 40 * Real.log (2 + T) + 10 := add_le_add herr1 herr2
    _ ≤ 50 * Real.log (2 + T) + 10 := by linarith

lemma riemann_von_mangoldt_good_height
    (hdigamma : ∀ z : ℂ, (1 / 4 : ℝ) ≤ z.re → ‖logDeriv Complex.Gamma z - Complex.log z‖ ≤ 20 / ‖z‖)
    (hzeta2_re : ∀ t : ℝ, (1 / 4 : ℝ) ≤ (riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ))).re)
    (CS : ℝ) (hCS : 0 ≤ CS)
    (hS_bound : ∀ T : ℝ, 2 ≤ T →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T) →
      |∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im| ≤
        CS * Real.log (2 + T)) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ H : ℝ, 2 ≤ H →
      (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 → riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0) →
      |(∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ H then
          (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) -
        ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi))| ≤
        CG * Real.log (2 + H) := by
  -- Real-axis zero constant `N_real` inside `(0, 1) × {0}` (actually 0, but bounded by a fixed constant!)
  have hxi_an : AnalyticOnNhd ℂ xiFun Set.univ :=
    differentiable_xiFun.differentiableOn.analyticOnNhd isOpen_univ
  have hxi_ntop : ∀ z : ℂ, meromorphicOrderAt xiFun z ≠ ⊤ := by
    intro z htop
    rw [(hxi_an z (Set.mem_univ z)).meromorphicOrderAt_eq] at htop
    have h0 := ENat.map_eq_top_iff.mp htop
    have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hxi_an
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp h0)
    have h1 := heq (Set.mem_univ 1)
    rw [xiFun_one] at h1; exact one_ne_zero h1
  set Nreal : ℝ := ∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = 0 then (analyticOrderNatAt xiFun ρ : ℝ) else 0
  have hNreal_nn : 0 ≤ Nreal := finsum_nonneg fun ρ => by split_ifs <;> positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨(CS + 50 + 2 * (10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal)) / Real.pi,
    by positivity, fun H hH hseg => ?_⟩
  have hno_H := riemannZeta_no_zero_im_of_good_height hH hseg
  -- Apply `rectIntegral_logDeriv_mul` to `F = xiFun`, `W = 1` on `[-1, 2] × [-H, H]`
  have hxi_ne_bdy : ∀ z ∈ Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc (-H) H,
      (z.re = -1 ∨ z.re = 2 ∨ z.im = -H ∨ z.im = H) → AnalyticAt ℂ xiFun z ∧ xiFun z ≠ 0 := by
    intro z _ hb
    refine ⟨hxi_an z (Set.mem_univ z), ?_⟩
    rcases hb with h | h | h | h
    · exact xiFun_ne_zero_of_re_nonpos (by linarith)
    · exact xiFun_ne_zero_of_one_le_re (by linarith)
    · intro h0
      have hconj : xiFun (starRingEnd ℂ z) = 0 := by rw [xiFun_conj, h0, map_zero]
      have hre_pos : 0 < (starRingEnd ℂ z).re := by
        by_contra hle; push Not at hle; exact xiFun_ne_zero_of_re_nonpos hle hconj
      have hre_lt1 : (starRingEnd ℂ z).re < 1 := by
        by_contra hge; push Not at hge; exact xiFun_ne_zero_of_one_le_re hge hconj
      have hne0 : starRingEnd ℂ z ≠ 0 := by intro he; rw [he] at hre_pos; simp at hre_pos
      have hne1 : starRingEnd ℂ z ≠ 1 := by intro he; rw [he] at hre_lt1; simp at hre_lt1
      rw [xiFun_eq_mul_riemannZeta hne0 hne1 hre_pos] at hconj
      have hpi : (Real.pi : ℂ) ^ (-(starRingEnd ℂ z) / 2) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]; exact Complex.exp_ne_zero _
      have hG : Complex.Gamma ((starRingEnd ℂ z) / 2) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.div_ofNat_re]; linarith)
      have hz0 : riemannZeta (starRingEnd ℂ z) = 0 :=
        (mul_eq_zero.mp hconj).resolve_left (mul_ne_zero (mul_ne_zero hne0 (sub_ne_zero.mpr hne1)) (mul_ne_zero hpi hG))
      exact hno_H (starRingEnd ℂ z) hz0 (by simp [h])
    · intro h0
      have hre_pos : 0 < z.re := by by_contra hle; push Not at hle; exact xiFun_ne_zero_of_re_nonpos hle h0
      have hre_lt1 : z.re < 1 := by by_contra hge; push Not at hge; exact xiFun_ne_zero_of_one_le_re hge h0
      have hne0 : z ≠ 0 := by intro he; rw [he] at hre_pos; simp at hre_pos
      have hne1 : z ≠ 1 := by intro he; rw [he] at hre_lt1; simp at hre_lt1
      rw [xiFun_eq_mul_riemannZeta hne0 hne1 hre_pos] at h0
      have hpi : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]; exact Complex.exp_ne_zero _
      have hG : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
      have hz0 : riemannZeta z = 0 :=
        (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero hne0 (sub_ne_zero.mpr hne1)) (mul_ne_zero hpi hG))
      exact hno_H z hz0 h
  have hrect := rectIntegral_logDeriv_mul isOpen_univ (F := xiFun) (W := fun _ => (1 : ℂ))
    (a := -1) (b := 2) (c := -H) (d := H) (by norm_num) (by linarith) (Set.subset_univ _)
    hxi_an.meromorphicOn (fun z _ => hxi_ntop z) (differentiableOn_const 1) hxi_ne_bdy
  simp only [mul_one] at hrect
  -- Step 1: Simplify the RHS sum `∑ᶠ ρ ∈ (-1, 2) × (-H, H), divisor xiFun ρ` into `2 * N(H) + Nreal`
  have hdiv_xi : ∀ ρ : ℂ, MeromorphicOn.divisor xiFun Set.univ ρ = (analyticOrderNatAt xiFun ρ : ℤ) := by
    intro ρ
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hxi_an (Set.mem_univ ρ)]
    have hntop : analyticOrderAt xiFun ρ ≠ ⊤ := by
      intro h; apply hxi_ntop ρ
      rw [(hxi_an ρ (Set.mem_univ ρ)).meromorphicOrderAt_eq, h]; rfl
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
    have hnat : analyticOrderNatAt xiFun ρ = n := by simp [analyticOrderNatAt, ← hn]
    rw [← hn, hnat]; rfl
  have hfin_box : (Function.support fun ρ : ℂ =>
      if ρ ∈ Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-H) H then (analyticOrderNatAt xiFun ρ : ℝ) else 0).Finite := by
    have hK : IsCompact (Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc (-H) H) := isCompact_Icc.reProdIm isCompact_Icc
    refine ((MeromorphicOn.divisor xiFun (Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc (-H) H)).finiteSupport hK).subset fun ρ hρ => ?_
    rw [Function.mem_support] at hρ ⊢
    split_ifs at hρ with hmem
    · have hρK : ρ ∈ Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc (-H) H :=
        ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hxi_an.mono (Set.subset_univ _)) hρK]
      have hntop : analyticOrderAt xiFun ρ ≠ ⊤ := by
        intro h; apply hxi_ntop ρ
        rw [(hxi_an ρ (Set.mem_univ ρ)).meromorphicOrderAt_eq, h]; rfl
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
      have hnat : analyticOrderNatAt xiFun ρ = n := by simp [analyticOrderNatAt, ← hn]
      rw [hnat] at hρ
      rw [← hn]
      change (n : ℤ) ≠ 0
      exact_mod_cast hρ
    · exact (hρ rfl).elim
  set Zbox : Finset ℂ := hfin_box.toFinset
  have hZbox_mem : ∀ ρ : ℂ, ρ ∈ Zbox ↔ ρ ∈ Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-H) H ∧ analyticOrderNatAt xiFun ρ ≠ 0 := by
    intro ρ; simp only [Zbox, Set.Finite.mem_toFinset, Function.mem_support]
    split_ifs with hmem <;> simp [hmem]
  have hZbox_strip : ∀ ρ ∈ Zbox, 0 < ρ.re ∧ ρ.re < 1 := by
    intro ρ hρ
    have hne0 := ((hZbox_mem ρ).mp hρ).2
    have hxi0 : xiFun ρ = 0 := by
      by_contra hne
      have h0 := (hxi_an ρ (Set.mem_univ ρ)).analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0] at hne0
    constructor
    · by_contra hle; push Not at hle; exact xiFun_ne_zero_of_re_nonpos hle hxi0
    · by_contra hge; push Not at hge; exact xiFun_ne_zero_of_one_le_re hge hxi0
  -- Split `Zbox` by `ρ.im > 0`, `ρ.im < 0`, `ρ.im = 0`
  set NH : ℝ := ∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ H then
      (analyticOrderNatAt riemannZeta ρ : ℝ) else 0
  have hRHS_im : (2 * Real.pi * Complex.I *
      ∑ᶠ ρ : ℂ, if ρ ∈ Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-H) H then (MeromorphicOn.divisor xiFun Set.univ ρ : ℂ) else 0).im =
      2 * Real.pi * (2 * NH + Nreal) := by
    have hsum_cast : (∑ᶠ ρ : ℂ, if ρ ∈ Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-H) H then
        (MeromorphicOn.divisor xiFun Set.univ ρ : ℂ) else 0) =
        ((∑ ρ ∈ Zbox, (analyticOrderNatAt xiFun ρ : ℝ) : ℝ) : ℂ) := by
      rw [finsum_eq_sum_of_support_subset _ (s := Zbox)]
      · push_cast
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hmem := ((hZbox_mem ρ).mp hρ).1
        simp only [hmem, ↓reduceIte, hdiv_xi ρ]; norm_cast
      · intro ρ hρ
        rw [Function.mem_support] at hρ
        split_ifs at hρ with hmem
        · rw [hdiv_xi ρ] at hρ
          exact Finset.mem_coe.mpr ((hZbox_mem ρ).mpr ⟨hmem, by exact_mod_cast hρ⟩)
        · exact (hρ rfl).elim
    rw [hsum_cast]
    have him : (2 * Real.pi * Complex.I * ((∑ ρ ∈ Zbox, (analyticOrderNatAt xiFun ρ : ℝ) : ℝ) : ℂ)).im =
        2 * Real.pi * ∑ ρ ∈ Zbox, (analyticOrderNatAt xiFun ρ : ℝ) := by
      simp [Complex.mul_im, Complex.mul_re]
    rw [him]
    congr 1
    classical
    let Zpos : Finset ℂ := Zbox.filter (fun ρ => 0 < ρ.im)
    let Zneg : Finset ℂ := Zbox.filter (fun ρ => ρ.im < 0)
    let Zzero : Finset ℂ := Zbox.filter (fun ρ => ρ.im = 0)
    have hsplit1 : ∑ ρ ∈ Zbox, (analyticOrderNatAt xiFun ρ : ℝ) =
        (∑ ρ ∈ Zpos, (analyticOrderNatAt xiFun ρ : ℝ)) +
        (∑ ρ ∈ Zneg, (analyticOrderNatAt xiFun ρ : ℝ)) +
        (∑ ρ ∈ Zzero, (analyticOrderNatAt xiFun ρ : ℝ)) := by
      have h1 := (Finset.sum_filter_add_sum_filter_not Zbox (fun ρ : ℂ => 0 < ρ.im)
        (fun ρ => (analyticOrderNatAt xiFun ρ : ℝ))).symm
      rw [h1]
      have h2 := (Finset.sum_filter_add_sum_filter_not (Zbox.filter fun ρ : ℂ => ¬0 < ρ.im)
        (fun ρ : ℂ => ρ.im < 0) (fun ρ => (analyticOrderNatAt xiFun ρ : ℝ))).symm
      rw [h2, ← add_assoc]
      have hZneg_eq : (Zbox.filter fun ρ : ℂ => ¬0 < ρ.im).filter (fun ρ : ℂ => ρ.im < 0) = Zneg := by
        ext ρ; simp only [Zneg, Finset.mem_filter]; constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
      have hZzero_eq : (Zbox.filter fun ρ : ℂ => ¬0 < ρ.im).filter (fun ρ : ℂ => ¬ρ.im < 0) = Zzero := by
        ext ρ; simp only [Zzero, Finset.mem_filter]; constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, by linarith⟩
      rw [hZneg_eq, hZzero_eq]
    have hneg_eq_pos : ∑ ρ ∈ Zneg, (analyticOrderNatAt xiFun ρ : ℝ) =
        ∑ ρ ∈ Zpos, (analyticOrderNatAt xiFun ρ : ℝ) := by
      refine Finset.sum_bij (fun ρ _ => starRingEnd ℂ ρ) ?_ ?_ ?_ ?_
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ ⊢
        have hmem := ((hZbox_mem ρ).mp hρ.1).1
        have hord := ((hZbox_mem ρ).mp hρ.1).2
        have him_neg := hρ.2
        refine ⟨(hZbox_mem _).mpr ⟨⟨by simpa using hmem.1, ⟨by simp; linarith [hmem.2.2], by simp; linarith [hmem.2.1]⟩⟩, ?_⟩,
          by simp; linarith⟩
        rwa [analyticOrderNatAt_xiFun_conj]
      · intro ρ1 _ ρ2 _ heq; exact (starRingEnd ℂ).injective heq
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ
        have hmem := ((hZbox_mem ρ).mp hρ.1).1
        have hord := ((hZbox_mem ρ).mp hρ.1).2
        have him_pos := hρ.2
        refine ⟨starRingEnd ℂ ρ, Finset.mem_filter.mpr ⟨(hZbox_mem _).mpr ⟨⟨by simpa using hmem.1,
          ⟨by simp; linarith [hmem.2.2], by simp; linarith [hmem.2.1]⟩⟩, ?_⟩, by simp; linarith⟩, by simp⟩
        rwa [analyticOrderNatAt_xiFun_conj]
      · intro ρ _; rw [analyticOrderNatAt_xiFun_conj]
    have hpos_eq_NH : ∑ ρ ∈ Zpos, (analyticOrderNatAt xiFun ρ : ℝ) = NH := by
      symm
      dsimp only [NH]
      rw [finsum_eq_sum_of_support_subset _ (s := Zpos)]
      · refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hρB := (Finset.mem_filter.mp hρ).1
        have hst := hZbox_strip ρ hρB
        have him_p := (Finset.mem_filter.mp hρ).2
        have him_lt := ((hZbox_mem ρ).mp hρB).1.2.2
        have hne1 : ρ ≠ 1 := by intro h; rw [h] at hst; simp at hst
        simp only [hst.1, hst.2, him_p, him_lt.le, and_self, ↓reduceIte]
        rw [analyticOrderNatAt_xiFun_eq_riemannZeta hst.1 hne1]
      · intro ρ hρ
        rw [Function.mem_support] at hρ
        split_ifs at hρ with hc
        · obtain ⟨hre0, hre1, him0, himH⟩ := hc
          have hne1 : ρ ≠ 1 := by intro h; rw [h] at hre1; simp at hre1
          have hord_eq := analyticOrderNatAt_xiFun_eq_riemannZeta hre0 hne1
          have hord_ne : analyticOrderNatAt xiFun ρ ≠ 0 := by rw [hord_eq]; exact_mod_cast hρ
          have hz0 : riemannZeta ρ = 0 := by
            by_contra hne
            have h0 := (differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)).analyticOrderAt_eq_zero.mpr hne
            simp [analyticOrderNatAt, h0] at hρ
          have him_lt : ρ.im < H := lt_of_le_of_ne himH (hno_H ρ hz0)
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
            ⟨(hZbox_mem ρ).mpr ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, him_lt⟩⟩, hord_ne⟩, him0⟩)
        · exact (hρ rfl).elim
    have hzero_eq_Nreal : ∑ ρ ∈ Zzero, (analyticOrderNatAt xiFun ρ : ℝ) = Nreal := by
      symm
      dsimp only [Nreal]
      rw [finsum_eq_sum_of_support_subset _ (s := Zzero)]
      · refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hρB := (Finset.mem_filter.mp hρ).1
        have hst := hZbox_strip ρ hρB
        have him0 := (Finset.mem_filter.mp hρ).2
        simp [hst.1, hst.2, him0]
      · intro ρ hρ
        rw [Function.mem_support] at hρ
        split_ifs at hρ with hc
        · obtain ⟨hre0, hre1, him0⟩ := hc
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
            ⟨(hZbox_mem ρ).mpr ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, by exact_mod_cast hρ⟩, him0⟩)
        · exact (hρ rfl).elim
    rw [hsplit1, hneg_eq_pos, hpos_eq_NH, hzero_eq_Nreal]; ring
  -- Step 2: Simplify `(rectIntegral (logDeriv xiFun) (-1) 2 (-H) H).im` by symmetries!
  have hLHS_im : (rectIntegral (logDeriv xiFun) (-1) 2 (-H) H).im =
      4 * (∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
      4 * (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im) := by
    have hxi_ld_cont : ContinuousOn (logDeriv xiFun) {z : ℂ | xiFun z ≠ 0} := by
      show ContinuousOn (fun z => deriv xiFun z / xiFun z) {z : ℂ | xiFun z ≠ 0}
      exact (hxi_an.deriv.continuousOn.mono (Set.subset_univ _)).div
        (hxi_an.continuousOn.mono (Set.subset_univ _)) (fun z hz => hz)
    have hint_top : IntervalIntegrable (fun x : ℝ => logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))) volume (-1) 2 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact hxi_ld_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx =>
        (hxi_ne_bdy ((x : ℂ) + Complex.I * (H : ℂ))
          ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, ⟨by simp; linarith, by simp⟩⟩
          (Or.inr (Or.inr (Or.inr (by simp))))).2
    have hint_bot : IntervalIntegrable (fun x : ℝ => logDeriv xiFun ((x : ℂ) + Complex.I * ((-H : ℝ) : ℂ))) volume (-1) 2 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact hxi_ld_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn fun x hx =>
        (hxi_ne_bdy ((x : ℂ) + Complex.I * ((-H : ℝ) : ℂ))
          ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, ⟨by simp, by simp; linarith⟩⟩
          (Or.inr (Or.inr (Or.inl (by simp))))).2
    have hint_right : IntervalIntegrable (fun y : ℝ => logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))) volume (-H) H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith : -H ≤ H)]
      exact hxi_ld_cont.comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy =>
        (hxi_ne_bdy ((2 : ℂ) + Complex.I * (y : ℂ))
          ⟨⟨by simp; norm_num, by simp⟩, ⟨by simpa using hy.1, by simpa using hy.2⟩⟩
          (Or.inr (Or.inl (by simp)))).2
    have hint_left : IntervalIntegrable (fun y : ℝ => logDeriv xiFun (((-1 : ℝ) : ℂ) + Complex.I * (y : ℂ))) volume (-H) H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith : -H ≤ H)]
      exact hxi_ld_cont.comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn fun y hy =>
        (hxi_ne_bdy (((-1 : ℝ) : ℂ) + Complex.I * (y : ℂ))
          ⟨⟨by simp, by simp; norm_num⟩, ⟨by simpa using hy.1, by simpa using hy.2⟩⟩
          (Or.inl (by simp))).2
    unfold rectIntegral
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add, Complex.ofReal_ofNat]
    have hre_comm : ∀ {f : ℝ → ℂ} {u v : ℝ}, IntervalIntegrable f volume u v →
        (∫ t in u..v, f t).re = ∫ t in u..v, (f t).re := fun hf =>
      (Complex.reCLM.intervalIntegral_comp_comm hf).symm
    have him_comm : ∀ {f : ℝ → ℂ} {u v : ℝ}, IntervalIntegrable f volume u v →
        (∫ t in u..v, f t).im = ∫ t in u..v, (f t).im := fun hf =>
      (Complex.imCLM.intervalIntegral_comp_comm hf).symm
    rw [him_comm hint_bot, him_comm hint_top, hre_comm hint_right, hre_comm hint_left]
    -- Right side: even real part on `[-H, H]` -> `2 * ∫_0^H`
    have hright_even : ∫ y in (-H)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re =
        2 * ∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re := by
      have hint_re_all : IntervalIntegrable (fun y : ℝ => (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) volume (-H) H :=
        ⟨Complex.reCLM.integrable_comp hint_right.1, Complex.reCLM.integrable_comp hint_right.2⟩
      have hsp := (intervalIntegral.integral_add_adjacent_intervals
        (hint_re_all.mono_set (by
          rw [Set.uIcc_of_le (by linarith : -H ≤ 0), Set.uIcc_of_le (by linarith : -H ≤ H)]
          exact Set.Icc_subset_Icc_right (by linarith)))
        (hint_re_all.mono_set (by
          rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ H), Set.uIcc_of_le (by linarith : -H ≤ H)]
          exact Set.Icc_subset_Icc_left (by linarith)))).symm
      rw [hsp]
      have hneg : ∫ y in (-H)..(0 : ℝ), (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re =
          ∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re := by
        have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := H)
          (f := fun y : ℝ => (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re)
        simp only [neg_zero] at hcomp
        rw [← hcomp]
        refine intervalIntegral.integral_congr fun y _ => ?_
        have harg : ((2 : ℂ) + Complex.I * ((-y : ℝ) : ℂ)) = starRingEnd ℂ ((2 : ℂ) + Complex.I * (y : ℂ)) := by
          apply Complex.ext <;> simp
        rw [harg, logDeriv_xiFun_conj, Complex.conj_re]
      rw [hneg]; ring
    -- Left side: `logDeriv xiFun (-1 + iy) = -conj(logDeriv xiFun (2 + iy))`, so `.re` is `-` of right!
    have hleft_eq : ∫ y in (-H)..H, (logDeriv xiFun (((-1 : ℝ) : ℂ) + Complex.I * (y : ℂ))).re =
        -(∫ y in (-H)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun y _ => ?_
      have h1 : (((-1 : ℝ) : ℂ) + Complex.I * (y : ℂ)) = 1 - starRingEnd ℂ ((2 : ℂ) + Complex.I * (y : ℂ)) := by
        apply Complex.ext <;> simp; norm_num
      rw [h1, logDeriv_xiFun_one_sub, logDeriv_xiFun_conj, Complex.neg_re, Complex.conj_re]
    -- Bottom side: `logDeriv xiFun (x - iH) = conj(logDeriv xiFun (x + iH))`, so `.im` is `-` of top!
    have hbot_eq : ∫ x in (-1 : ℝ)..2, (logDeriv xiFun ((x : ℂ) + Complex.I * ((-H : ℝ) : ℂ))).im =
        -(∫ x in (-1 : ℝ)..2, (logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))).im) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      have h1 : ((x : ℂ) + Complex.I * ((-H : ℝ) : ℂ)) = starRingEnd ℂ ((x : ℂ) + Complex.I * (H : ℂ)) := by
        apply Complex.ext <;> simp
      rw [h1, logDeriv_xiFun_conj, Complex.conj_im]
    -- Top side: split `[-1, 2] = [-1, 1/2] + [1/2, 2]`; on `[-1, 1/2]`, `x = 1 - σ` gives same `.im`!
    have htop_symm : ∫ x in (-1 : ℝ)..2, (logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))).im =
        2 * ∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im := by
      have hint_im_all : IntervalIntegrable (fun x : ℝ => (logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))).im) volume (-1) 2 :=
        ⟨Complex.imCLM.integrable_comp hint_top.1, Complex.imCLM.integrable_comp hint_top.2⟩
      have hsp := (intervalIntegral.integral_add_adjacent_intervals
        (hint_im_all.mono_set (by
          rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2), Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
          exact Set.Icc_subset_Icc_right (by norm_num)))
        (hint_im_all.mono_set (by
          rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2), Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
          exact Set.Icc_subset_Icc_left (by norm_num)))).symm
      rw [hsp]
      have hsub : ∫ x in (-1 : ℝ)..(1 / 2 : ℝ), (logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))).im =
          ∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im := by
        have h1 := intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => (logDeriv xiFun ((x : ℂ) + Complex.I * (H : ℂ))).im) (1 : ℝ) (a := (1 / 2 : ℝ)) (b := 2)
        have hlo : (1 : ℝ) - 2 = -1 := by norm_num
        have hhi : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
        rw [hlo, hhi] at h1
        rw [← h1]
        refine intervalIntegral.integral_congr fun σ _ => ?_
        have harg : (((1 - σ : ℝ) : ℂ) + Complex.I * (H : ℂ)) =
            1 - starRingEnd ℂ ((σ : ℂ) + Complex.I * (H : ℂ)) := by
          apply Complex.ext <;> simp
        rw [harg, logDeriv_xiFun_one_sub, logDeriv_xiFun_conj, Complex.neg_im, Complex.conj_im, neg_neg]
      rw [hsub]; ring
    rw [hleft_eq, hright_even, hbot_eq, htop_symm]; ring
  -- Combine: `π * NH + (π/2) * Nreal = ∫_0^H Re(logDeriv ξ(2+iy)) dy - ∫_{1/2}^2 Im(logDeriv ξ(σ+iH)) dσ`
  have hmain_eq : Real.pi * NH + (Real.pi / 2) * Nreal =
      (∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
      (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im) := by
    have him := congrArg Complex.im hrect
    rw [hLHS_im, hRHS_im] at him
    linarith
  -- Step 3: Evaluate right vertical integral `∫_0^H Re(logDeriv ξ(2+iy)) dy`
  have hV_est : |(∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
      ((1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H))| ≤
      50 * Real.log (2 + H) + 10 + 2 * Real.pi + 2 * Real.pi := by
    have hdecomp : ∀ y : ℝ, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re =
        2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2 +
        (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re +
        (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re := by
      intro y
      have hne1 : ((2 : ℂ) + Complex.I * (y : ℂ)) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this
      have hzne : riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simp)
      have hrel := logDeriv_xiFun_eq (s := (2 : ℂ) + Complex.I * (y : ℂ)) (by simp) hne1 hzne
      have hre := congrArg Complex.re hrel
      rw [hre]
      have hhalf : ((2 : ℂ) + Complex.I * (y : ℂ)) / 2 = (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hhalf]
      have h1 : (((2 : ℂ) + Complex.I * (y : ℂ))⁻¹).re = 2 / (4 + y ^ 2) := by
        rw [Complex.inv_re]
        simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
          Complex.im_ofNat, Complex.mul_im, one_mul, zero_add, Complex.ofReal_re, Complex.normSq_apply]
        ring
      have h2 : (((2 : ℂ) + Complex.I * (y : ℂ) - 1)⁻¹).re = 1 / (1 + y ^ 2) := by
        rw [Complex.inv_re]
        simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.one_re, Complex.mul_re,
          Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
          Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.one_im, Complex.mul_im, one_mul,
          zero_add, Complex.ofReal_re, Complex.normSq_apply]
        ring
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
        zero_mul, sub_zero, h1, h2]
    have hc1 : Continuous (fun y : ℝ => 2 / (4 + y ^ 2)) :=
      continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun y => ne_of_gt (by positivity : (0 : ℝ) < 4 + y ^ 2))
    have hc2 : Continuous (fun y : ℝ => 1 / (1 + y ^ 2)) :=
      continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun y => ne_of_gt (by positivity : (0 : ℝ) < 1 + y ^ 2))
    have hc4 : Continuous (fun y : ℝ => (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) := by
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
        (Complex.differentiableAt_Gamma z fun m hm => by
          have := congrArg Complex.re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < z.re from hz]).differentiableWithinAt
      have han : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := hdiff.analyticOnNhd hopen
      have hpath : Continuous (fun y : ℝ => (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)) :=
        continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.div_const 2)))
      have hmem : ∀ y : ℝ, (1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := fun y => by
        show (0 : ℝ) < ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ)).re; simp
      exact continuous_const.mul (Complex.continuous_re.comp ((han.deriv.continuousOn.comp_continuous hpath hmem).div
        (han.continuousOn.comp_continuous hpath hmem) fun y => Complex.Gamma_ne_zero_of_re_pos (hmem y)))
    have hc5 : Continuous (fun y : ℝ => (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re) := by
      have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := differentiableOn_riemannZeta.analyticOnNhd isOpen_ne
      have hne1 : ∀ y : ℝ, ((2 : ℂ) + Complex.I * (y : ℂ)) ≠ 1 := fun y h => by
        have := congrArg Complex.re h; simp at this
      have hpath : Continuous (fun y : ℝ => (2 : ℂ) + Complex.I * (y : ℂ)) :=
        continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      exact Complex.continuous_re.comp ((han.deriv.continuousOn.comp_continuous hpath hne1).div
        (han.continuousOn.comp_continuous hpath hne1) fun y => riemannZeta_ne_zero_of_one_le_re (by simp))
    have hci1 : IntervalIntegrable (fun y : ℝ => 2 / (4 + y ^ 2)) volume 0 H := hc1.intervalIntegrable 0 H
    have hci2 : IntervalIntegrable (fun y : ℝ => 1 / (1 + y ^ 2)) volume 0 H := hc2.intervalIntegrable 0 H
    have hci12 : IntervalIntegrable (fun y : ℝ => 2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)) volume 0 H := hci1.add hci2
    have hci3 : IntervalIntegrable (fun _y : ℝ => Real.log Real.pi / 2) volume 0 H := intervalIntegrable_const
    have hci123 : IntervalIntegrable (fun y : ℝ => 2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2) volume 0 H := hci12.sub hci3
    have hci4 : IntervalIntegrable (fun y : ℝ => (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) volume 0 H := hc4.intervalIntegrable 0 H
    have hci1234 : IntervalIntegrable (fun y : ℝ => 2 / (4 + y ^ 2) + 1 / (1 + y ^ 2) - Real.log Real.pi / 2 +
        (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) volume 0 H := hci123.add hci4
    have hci5 : IntervalIntegrable (fun y : ℝ => (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re) volume 0 H := hc5.intervalIntegrable 0 H
    simp_rw [hdecomp]
    rw [intervalIntegral.integral_add hci1234 hci5,
      intervalIntegral.integral_add hci123 hci4,
      intervalIntegral.integral_sub hci12 hci3,
      intervalIntegral.integral_add hci1 hci2]
    have hi1 : |∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)| ≤ Real.pi := by
      have hd : ∀ y ∈ Set.uIcc (0 : ℝ) H, HasDerivAt (fun x : ℝ => Real.arctan (x / 2)) (2 / (4 + y ^ 2)) y := by
        intro y _
        have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) y := by simpa using (hasDerivAt_id y).div_const 2
        convert h1.arctan using 1; field_simp; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable 0 H),
        zero_div, Real.arctan_zero, sub_zero]
      exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le.trans (by linarith [Real.pi_pos])
    have hi2 : |∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2)| ≤ Real.pi := by
      have hd : ∀ y ∈ Set.uIcc (0 : ℝ) H, HasDerivAt Real.arctan (1 / (1 + y ^ 2)) y := fun y _ => by
        simpa [one_div] using Real.hasDerivAt_arctan y
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc2.intervalIntegrable 0 H),
        Real.arctan_zero, sub_zero]
      exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le.trans (by linarith [Real.pi_pos])
    have hi3 : ∫ _y in (0 : ℝ)..H, Real.log Real.pi / 2 = H * (Real.log Real.pi / 2) := by simp; ring
    have hi4 := integral_re_digamma_two_main hdigamma H hH
    have hi5 := integral_re_logDeriv_zeta_two_bound hzeta2_re H (by linarith)
    have hlog_eq : (1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H) =
        (1 / 2 : ℝ) * (H * Real.log (H / 2) - H) - H * (Real.log Real.pi / 2) := by
      have : H / (2 * Real.pi) = (H / 2) / Real.pi := by ring
      rw [this, Real.log_div (by positivity) Real.pi_pos.ne']; ring
    rw [hi3, hlog_eq]
    have hrearr :
        ((∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)) + (∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2)) -
          H * (Real.log Real.pi / 2) +
          (∫ y in (0 : ℝ)..H, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) +
          (∫ y in (0 : ℝ)..H, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re)) -
        ((1 / 2 : ℝ) * (H * Real.log (H / 2) - H) - H * (Real.log Real.pi / 2)) =
        (∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)) + (∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2)) +
        ((∫ y in (0 : ℝ)..H, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
          (1 / 2 : ℝ) * (H * Real.log (H / 2) - H)) +
        (∫ y in (0 : ℝ)..H, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re) := by ring
    rw [hrearr]
    calc _ ≤ |(∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)) + (∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2)) +
            ((∫ y in (0 : ℝ)..H, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
              (1 / 2 : ℝ) * (H * Real.log (H / 2) - H))| +
          |∫ y in (0 : ℝ)..H, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re| := abs_add_le _ _
      _ ≤ (|(∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)) + (∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2))| +
            |(∫ y in (0 : ℝ)..H, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
              (1 / 2 : ℝ) * (H * Real.log (H / 2) - H)|) +
          |∫ y in (0 : ℝ)..H, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re| := by
            gcongr; exact abs_add_le _ _
      _ ≤ ((|∫ y in (0 : ℝ)..H, 2 / (4 + y ^ 2)| + |∫ y in (0 : ℝ)..H, 1 / (1 + y ^ 2)|) +
            |(∫ y in (0 : ℝ)..H, (1 / 2 : ℝ) * (logDeriv Complex.Gamma ((1 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))).re) -
              (1 / 2 : ℝ) * (H * Real.log (H / 2) - H)|) +
          |∫ y in (0 : ℝ)..H, (logDeriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))).re| := by
            gcongr; exact abs_add_le _ _
      _ ≤ 50 * Real.log (2 + H) + 10 + 2 * Real.pi + 2 * Real.pi := by linarith
  -- Step 4: Bound horizontal integral `|∫_{1/2}^2 Im(logDeriv ξ(σ+iH)) dσ| ≤ CS * log(2+H) + 40 + 4*π`
  have hH_est : |∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im| ≤
      CS * Real.log (2 + H) + 40 + 4 * Real.pi := by
    have hdecomp : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im =
        ((((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
          (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im) +
        (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))).im := by
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      have hne1 : ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 1 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      have hzne : riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 := hseg σ (by linarith [hσ.1]) (by linarith [hσ.2])
      have hrel := logDeriv_xiFun_eq (s := (σ : ℂ) + Complex.I * (H : ℂ)) (by simp; linarith [hσ.1]) hne1 hzne
      have him := congrArg Complex.im hrel
      rw [him]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im,
        Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
        zero_mul, add_zero]
    rw [intervalIntegral.integral_congr hdecomp]
    have hpath : Continuous (fun σ : ℝ => (σ : ℂ) + Complex.I * (H : ℂ)) :=
      Complex.continuous_ofReal.add continuous_const
    have hc_rest : ContinuousOn (fun σ : ℝ =>
        (((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
          (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im)
        (Set.Icc (1 / 2 : ℝ) 2) := by
      have hc1 : ContinuousOn (fun σ : ℝ => (((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im) (Set.Icc (1 / 2 : ℝ) 2) :=
        Complex.continuous_im.comp_continuousOn (hpath.continuousOn.inv₀ fun σ _ h0 => by
          have := congrArg Complex.im h0; simp at this; linarith)
      have hc2 : ContinuousOn (fun σ : ℝ => (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im) (Set.Icc (1 / 2 : ℝ) 2) :=
        Complex.continuous_im.comp_continuousOn ((hpath.continuousOn.sub continuousOn_const).inv₀ fun σ _ h0 => by
          have := congrArg Complex.im h0; simp at this; linarith)
      have hc3 : ContinuousOn (fun σ : ℝ => (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im)
          (Set.Icc (1 / 2 : ℝ) 2) := by
        have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
        have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
          (Complex.differentiableAt_Gamma z fun m hm => by
            have := congrArg Complex.re hm; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < z.re from hz]).differentiableWithinAt
        have han : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := hdiff.analyticOnNhd hopen
        have hp2 : ContinuousOn (fun σ : ℝ => ((σ : ℂ) + Complex.I * (H : ℂ)) / 2) (Set.Icc (1 / 2 : ℝ) 2) :=
          hpath.continuousOn.div_const 2
        have hmem : Set.MapsTo (fun σ : ℝ => ((σ : ℂ) + Complex.I * (H : ℂ)) / 2) (Set.Icc (1 / 2 : ℝ) 2) {z : ℂ | 0 < z.re} :=
          fun σ hσ => by show (0 : ℝ) < (((σ : ℂ) + Complex.I * (H : ℂ)) / 2).re; simp; linarith [hσ.1]
        exact continuousOn_const.mul (Complex.continuous_im.comp_continuousOn
          ((han.deriv.continuousOn.comp hp2 hmem).div (han.continuousOn.comp hp2 hmem) fun σ hσ =>
            Complex.Gamma_ne_zero_of_re_pos (hmem hσ)))
      exact (hc1.add hc2).add hc3
    have hc_z : ContinuousOn (fun σ : ℝ => (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))).im)
        (Set.Icc (1 / 2 : ℝ) 2) := by
      have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := differentiableOn_riemannZeta.analyticOnNhd isOpen_ne
      have hne1 : Set.MapsTo (fun σ : ℝ => (σ : ℂ) + Complex.I * (H : ℂ)) (Set.Icc (1 / 2 : ℝ) 2) {s : ℂ | s ≠ 1} :=
        fun σ _ h0 => by have := congrArg Complex.im h0; simp at this; linarith
      exact Complex.continuous_im.comp_continuousOn
        ((han.deriv.continuousOn.comp hpath.continuousOn hne1).div
          (han.continuousOn.comp hpath.continuousOn hne1) fun σ hσ => hseg σ (by linarith [hσ.1]) (by linarith [hσ.2]))
    rw [intervalIntegral.integral_add (hc_rest.intervalIntegrable_of_Icc (by norm_num))
        (hc_z.intervalIntegrable_of_Icc (by norm_num))]
    have hrest_bd : |∫ σ in (1 / 2 : ℝ)..2,
        ((((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
          (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im)| ≤ 40 + 4 * Real.pi := by
      have hpt : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
          |(((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
            (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im| ≤ 20 + 2 * Real.pi := by
        intro σ hσ
        set s : ℂ := (σ : ℂ) + Complex.I * (H : ℂ)
        have hsn : 2 ≤ ‖s‖ := by
          have := Complex.abs_im_le_norm s; simp [s, abs_of_pos (by linarith : 0 < H)] at this; linarith
        have hs1n : 2 ≤ ‖s - 1‖ := by
          have := Complex.abs_im_le_norm (s - 1); simp [s, abs_of_pos (by linarith : 0 < H)] at this; linarith
        have hb1 : |(s⁻¹).im| ≤ 1 := by
          calc |(s⁻¹).im| ≤ ‖s⁻¹‖ := Complex.abs_im_le_norm _
            _ = ‖s‖⁻¹ := norm_inv s
            _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have hb2 : |((s - 1)⁻¹).im| ≤ 1 := by
          calc |((s - 1)⁻¹).im| ≤ ‖(s - 1)⁻¹‖ := Complex.abs_im_le_norm _
            _ = ‖s - 1‖⁻¹ := norm_inv _
            _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have hb3 : |(1 / 2 : ℝ) * (logDeriv Complex.Gamma (s / 2)).im| ≤ 15 + Real.pi := by
          have hre_s2 : (1 / 4 : ℝ) ≤ (s / 2).re := by simp [s]; linarith [hσ.1]
          have hnorm_s2 : (1 : ℝ) ≤ ‖s / 2‖ := by
            rw [norm_div, Complex.norm_ofNat]; linarith
          have hdg := hdigamma (s / 2) hre_s2
          have hdiff : |(logDeriv Complex.Gamma (s / 2)).im - (Complex.log (s / 2)).im| ≤ 20 := by
            have h1 : (logDeriv Complex.Gamma (s / 2)).im - (Complex.log (s / 2)).im =
                (logDeriv Complex.Gamma (s / 2) - Complex.log (s / 2)).im := by simp
            rw [h1]
            calc _ ≤ ‖logDeriv Complex.Gamma (s / 2) - Complex.log (s / 2)‖ := Complex.abs_im_le_norm _
              _ ≤ 20 / ‖s / 2‖ := hdg
              _ ≤ 20 / 1 := div_le_div_of_nonneg_left (by norm_num) one_pos hnorm_s2
              _ = 20 := by norm_num
          have harg : |(Complex.log (s / 2)).im| ≤ Real.pi := by
            rw [Complex.log_im]; exact Complex.abs_arg_le_pi _
          have him_le : |(logDeriv Complex.Gamma (s / 2)).im| ≤ 20 + Real.pi := by
            have := abs_sub_abs_le_abs_sub (logDeriv Complex.Gamma (s / 2)).im (Complex.log (s / 2)).im
            linarith
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith [Real.pi_pos]
        calc _ ≤ |((s⁻¹).im) + ((s - 1)⁻¹).im| + |(1 / 2 : ℝ) * (logDeriv Complex.Gamma (s / 2)).im| := abs_add_le _ _
          _ ≤ (|(s⁻¹).im| + |((s - 1)⁻¹).im|) + |(1 / 2 : ℝ) * (logDeriv Complex.Gamma (s / 2)).im| := by
              gcongr; exact abs_add_le _ _
          _ ≤ 20 + 2 * Real.pi := by linarith [Real.pi_pos]
      calc _ ≤ ∫ σ in (1 / 2 : ℝ)..2,
            |(((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
              (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun σ : ℝ => (((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
                (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im)
              (by norm_num : (1 / 2 : ℝ) ≤ 2)
        _ ≤ ∫ _σ in (1 / 2 : ℝ)..2, (20 + 2 * Real.pi : ℝ) :=
            intervalIntegral.integral_mono_on (by norm_num)
              (hc_rest.abs.intervalIntegrable_of_Icc (by norm_num))
              (continuous_const.intervalIntegrable (1 / 2) 2) hpt
        _ = (3 / 2 : ℝ) * (20 + 2 * Real.pi) := by simp; ring
        _ ≤ 40 + 4 * Real.pi := by linarith [Real.pi_pos]
    have hz_bd := hS_bound H hH (fun σ h1 h2 => hseg σ (by linarith) (by linarith)) hno_H
    calc _ ≤ |∫ σ in (1 / 2 : ℝ)..2,
            ((((σ : ℂ) + Complex.I * (H : ℂ))⁻¹).im + (((σ : ℂ) + Complex.I * (H : ℂ) - 1)⁻¹).im +
              (1 / 2 : ℝ) * (logDeriv Complex.Gamma (((σ : ℂ) + Complex.I * (H : ℂ)) / 2)).im)| +
          |∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))).im| := abs_add_le _ _
      _ ≤ (40 + 4 * Real.pi) + CS * Real.log (2 + H) := add_le_add hrest_bd hz_bd
      _ = CS * Real.log (2 + H) + 40 + 4 * Real.pi := by ring
  -- Step 5: Combine everything and divide by `π`!
  have hpi_diff : Real.pi * (NH - ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi))) =
      ((∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
        ((1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H))) -
      (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im) -
      (Real.pi / 2) * Nreal := by
    have h1 : Real.pi * ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi)) =
        (1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H) := by
      field_simp [Real.pi_pos.ne']
    linarith [hmain_eq, h1]
  have hlogH : (1 / 2 : ℝ) ≤ Real.log (2 + H) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpi_abs : Real.pi * |NH - ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi))| ≤
      (CS + 50 + 2 * (10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal)) *
        Real.log (2 + H) := by
    have hmul_abs : Real.pi * |NH - ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi))| =
        |Real.pi * (NH - ((H / (2 * Real.pi)) * Real.log (H / (2 * Real.pi)) - H / (2 * Real.pi)))| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [hmul_abs, hpi_diff]
    calc _ ≤ |((∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
              ((1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H))) -
            (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im)| +
          |(Real.pi / 2) * Nreal| := abs_sub _ _
      _ ≤ (|(∫ y in (0 : ℝ)..H, (logDeriv xiFun ((2 : ℂ) + Complex.I * (y : ℂ))).re) -
              ((1 / 2 : ℝ) * (H * Real.log (H / (2 * Real.pi)) - H))| +
            |∫ σ in (1 / 2 : ℝ)..2, (logDeriv xiFun ((σ : ℂ) + Complex.I * (H : ℂ))).im|) +
          (Real.pi / 2) * Nreal := by
            have hNr : |(Real.pi / 2) * Nreal| = (Real.pi / 2) * Nreal := abs_of_nonneg (by positivity)
            rw [hNr]; gcongr; exact abs_sub _ _
      _ ≤ (50 * Real.log (2 + H) + 10 + 2 * Real.pi + 2 * Real.pi) +
          (CS * Real.log (2 + H) + 40 + 4 * Real.pi) + (Real.pi / 2) * Nreal := by linarith [hV_est, hH_est]
      _ ≤ (CS + 50 + 2 * (10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal)) *
            Real.log (2 + H) := by
            have hK0 : 0 ≤ 10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal := by positivity
            nlinarith [hK0, hlogH]
  rw [show (CS + 50 + 2 * (10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal)) / Real.pi *
      Real.log (2 + H) =
      ((CS + 50 + 2 * (10 + 2 * Real.pi + 2 * Real.pi + 40 + 4 * Real.pi + Real.pi / 2 * Nreal)) *
        Real.log (2 + H)) / Real.pi by ring]
  rw [le_div_iff₀ Real.pi_pos, mul_comm]
  exact hpi_abs

theorem riemann_von_mangoldt
    (hF_diff : Differentiable ℂ zetaExt)
    (hdigamma : ∀ z : ℂ, (1 / 4 : ℝ) ≤ z.re → ‖logDeriv Complex.Gamma z - Complex.log z‖ ≤ 20 / ‖z‖)
    (hzeta2_re : ∀ t : ℝ, (1 / 4 : ℝ) ≤ (riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ))).re)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJ : ∀ t : ℝ,
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 3) u : ℝ)) ≤
        CJ * Real.log (2 + |t|))
    (CH : ℝ) (_hCH : 0 ≤ CH)
    (hH_exists : ∀ k : ℤ, 2 ≤ |k| →
      ∃ H : ℝ, (k : ℝ) ≤ H ∧ H ≤ (k : ℝ) + 1 ∧
        (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
          riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤
            CH * (Real.log (2 + |H|)) ^ 2))
    (CS : ℝ) (hCS : 0 ≤ CS)
    (hS_bound : ∀ T : ℝ, 2 ≤ T →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T) →
      |∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ))).im| ≤
        CS * Real.log (2 + T)) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ T : ℝ, 2 ≤ T →
      |(∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T then
          (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) -
        ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))| ≤
        CR * Real.log (2 + T) := by
  obtain ⟨CG, hCG, hG⟩ := riemann_von_mangoldt_good_height hdigamma hzeta2_re CS hCS hS_bound
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨2 * CG + CJ + 4, by positivity, fun T hT => ?_⟩
  set k : ℤ := ⌊T⌋
  have hk_ge2 : 2 ≤ k := Int.le_floor.mpr (by exact_mod_cast hT)
  have hk_abs : 2 ≤ |k| := by rw [abs_of_nonneg (by omega)]; exact hk_ge2
  obtain ⟨H, hHk_lo, hHk_hi, hH_prop⟩ := hH_exists k hk_abs
  have hH_ge2 : 2 ≤ H := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge2
    linarith
  have hHT_diff : |H - T| ≤ 1 := by
    have h1 : (k : ℝ) ≤ T := Int.floor_le T
    have h2 : T < (k : ℝ) + 1 := Int.lt_floor_add_one T
    rw [abs_le]; constructor <;> linarith
  have hlog_H : Real.log (2 + H) ≤ 2 * Real.log (2 + T) := by
    have hle : 2 + H ≤ (2 + T) ^ 2 := by nlinarith [(abs_le.mp hHT_diff).2]
    calc Real.log (2 + H) ≤ Real.log ((2 + T) ^ 2) := Real.log_le_log (by linarith) hle
      _ = 2 * Real.log (2 + T) := by rw [Real.log_pow]; ring
  -- Step 1: Good-height bound at `H`
  have hgood := hG H hH_ge2 (fun σ h1 h2 => (hH_prop σ h1 h2).1)
  -- Step 2: Compare main terms `M(H)` and `M(T)` by MVT on `[min T H, max T H]`
  let M : ℝ → ℝ := fun x => (x / (2 * Real.pi)) * Real.log (x / (2 * Real.pi)) - x / (2 * Real.pi)
  have hM_diff : |M H - M T| ≤ 4 * Real.log (2 + T) := by
    have hdM : ∀ x ∈ Set.uIcc T H, HasDerivAt M ((1 / (2 * Real.pi)) * Real.log (x / (2 * Real.pi))) x := by
      intro x hx
      have hx_lo : 2 ≤ x := by
        rcases le_total T H with hle | hle
        · rw [Set.uIcc_of_le hle] at hx; linarith [hx.1]
        · rw [Set.uIcc_of_ge hle] at hx; linarith [hx.1]
      have hx0 : x ≠ 0 := by linarith
      have h1 : HasDerivAt (fun t : ℝ => t / (2 * Real.pi)) (1 / (2 * Real.pi)) x := by
        simpa using (hasDerivAt_id x).div_const (2 * Real.pi)
      have h2 : HasDerivAt (fun t : ℝ => Real.log (t / (2 * Real.pi))) (1 / x) x := by
        convert h1.log (by positivity : x / (2 * Real.pi) ≠ 0) using 1
        field_simp [hx0, Real.pi_pos.ne']
      have h3 := (h1.mul h2).sub h1
      convert h3 using 1; field_simp [hx0, Real.pi_pos.ne']; ring
    have hcM : ContinuousOn (fun x : ℝ => (1 / (2 * Real.pi)) * Real.log (x / (2 * Real.pi))) (Set.uIcc T H) :=
      continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.div_const _) fun x hx => by
        rcases le_total T H with hle | hle
        · rw [Set.uIcc_of_le hle] at hx; exact ne_of_gt (div_pos (by linarith [hx.1]) (by positivity))
        · rw [Set.uIcc_of_ge hle] at hx; exact ne_of_gt (div_pos (by linarith [hx.1]) (by positivity)))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hdM hcM.intervalIntegrable
    rw [← hftc]
    have hpt : ∀ x ∈ Set.uIcc T H, |(1 / (2 * Real.pi)) * Real.log (x / (2 * Real.pi))| ≤ 4 * Real.log (2 + T) := by
      intro x hx
      have hx_lo : 2 ≤ x := by
        rcases le_total T H with hle | hle
        · rw [Set.uIcc_of_le hle] at hx; linarith [hx.1]
        · rw [Set.uIcc_of_ge hle] at hx; linarith [hx.1]
      have hx_hi : x ≤ 2 + T := by
        rcases le_total T H with hle | hle
        · rw [Set.uIcc_of_le hle] at hx; linarith [hx.2, (abs_le.mp hHT_diff).2]
        · rw [Set.uIcc_of_ge hle] at hx; linarith [hx.2]
      have hlog_bd : |Real.log (x / (2 * Real.pi))| ≤ Real.log (2 + T) + Real.log (2 * Real.pi) := by
        rw [Real.log_div (by linarith) (by positivity)]
        calc |Real.log x - Real.log (2 * Real.pi)| ≤ |Real.log x| + |Real.log (2 * Real.pi)| := abs_sub _ _
          _ = Real.log x + Real.log (2 * Real.pi) := by
              rw [abs_of_nonneg (Real.log_nonneg (by linarith)),
                abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
          _ ≤ Real.log (2 + T) + Real.log (2 * Real.pi) := by gcongr
      have hlog_2pi : Real.log (2 * Real.pi) ≤ 14 * Real.log (2 + T) := by
        have h1 : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
        have h2 : (1 / 2 : ℝ) ≤ Real.log (2 + T) := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
        nlinarith [Real.pi_lt_four]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
      have h2pi_gt : (6 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (1 / (2 * Real.pi)) * |Real.log (x / (2 * Real.pi))|
          ≤ (1 / 6) * (15 * Real.log (2 + T)) := by
            apply mul_le_mul
            · exact one_div_le_one_div_of_le (by norm_num) h2pi_gt.le
            · linarith
            · exact abs_nonneg _
            · positivity
        _ ≤ 4 * Real.log (2 + T) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + T)]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * Real.log (2 + T)) (f := fun x : ℝ => (1 / (2 * Real.pi)) * Real.log (x / (2 * Real.pi))) (a := T) (b := H)
      (fun x hx => by simpa [Real.norm_eq_abs] using hpt x (Set.uIoc_subset_uIcc hx))
    rw [Real.norm_eq_abs] at hnorm
    have hlog_nn : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
    calc |∫ x in T..H, (1 / (2 * Real.pi)) * Real.log (x / (2 * Real.pi))|
        ≤ 4 * Real.log (2 + T) * |H - T| := hnorm
      _ ≤ 4 * Real.log (2 + T) * 1 := by gcongr
      _ = 4 * Real.log (2 + T) := mul_one _
  -- Step 3: Compare `N(T)` and `N(H)` via Jensen zero count in `closedBall (2 + I * T) 3`
  set NT : ℝ := ∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T then
      (analyticOrderNatAt riemannZeta ρ : ℝ) else 0
  set NH : ℝ := ∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ H then
      (analyticOrderNatAt riemannZeta ρ : ℝ) else 0
  have hNT_NH : |NT - NH| ≤ CJ * Real.log (2 + T) := by
    have hF_an : AnalyticOnNhd ℂ zetaExt Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
    have hF_ntop : ∀ z : ℂ, analyticOrderAt zetaExt z ≠ ⊤ := by
      intro z htop
      have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hF_an
        isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop)
      have h1 := heq (Set.mem_univ 1); simp [zetaExt] at h1
    have hdiv_F : ∀ U : Set ℂ, ∀ z ∈ U,
        MeromorphicOn.divisor zetaExt U z = (analyticOrderNatAt zetaExt z : ℤ) := by
      intro U z hz
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF_an.mono (Set.subset_univ U)) hz]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hF_ntop z)
      have hnat : analyticOrderNatAt zetaExt z = n := by simp [analyticOrderNatAt, ← hn]
      rw [← hn, hnat]; rfl
    have hord_F : ∀ ρ : ℂ, ρ ≠ 1 → analyticOrderNatAt zetaExt ρ = analyticOrderNatAt riemannZeta ρ := by
      intro ρ hρ1
      have hev : zetaExt =ᶠ[𝓝 ρ] fun w => (w - 1) * riemannZeta w := by
        filter_upwards [isOpen_ne.mem_nhds hρ1] with w hw; simp [zetaExt, hw]
      have hza := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hρ1)
      have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) ρ := analyticAt_id.sub analyticAt_const
      have h1 : analyticOrderAt zetaExt ρ = analyticOrderAt ((fun w : ℂ => w - 1) * riemannZeta) ρ :=
        analyticOrderAt_congr hev
      rw [analyticOrderAt_mul hlin hza, hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ1), zero_add] at h1
      simp only [analyticOrderNatAt, h1]
    set B := Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) 3
    have hfin_strip : ∀ Y : ℝ, (Function.support fun ρ : ℂ =>
        if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ Y then (analyticOrderNatAt riemannZeta ρ : ℝ) else 0).Finite := by
      intro Y
      have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) (max Y 0)) := isCompact_Icc.reProdIm isCompact_Icc
      have hmero_K : MeromorphicOn zetaExt (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) (max Y 0)) :=
        (hF_an.mono (Set.subset_univ _)).meromorphicOn
      refine ((MeromorphicOn.divisor zetaExt (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) (max Y 0))).finiteSupport hK).subset fun ρ hρ => ?_
      rw [Function.mem_support] at hρ ⊢
      split_ifs at hρ with hc
      · have hne1 : ρ ≠ 1 := by intro h; rw [h] at hc; simp at hc
        have hρK : ρ ∈ Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) (max Y 0) :=
          ⟨⟨hc.1.le, hc.2.1.le⟩, ⟨hc.2.2.1.le, hc.2.2.2.trans (le_max_left Y 0)⟩⟩
        rw [hdiv_F _ ρ hρK, hord_F ρ hne1]
        exact_mod_cast hρ
      · exact (hρ rfl).elim
    have hfin_B : (Function.support fun ρ : ℂ => (MeromorphicOn.divisor zetaExt B ρ : ℝ)).Finite := by
      refine ((MeromorphicOn.divisor zetaExt B).finiteSupport (isCompact_closedBall _ 3)).subset fun ρ hρ => ?_
      rw [Function.mem_support] at hρ ⊢
      exact_mod_cast hρ
    have hsub_fin : ∀ (f g : ℂ → ℝ), (Function.support f).Finite → (Function.support g).Finite →
        (∀ ρ, |f ρ - g ρ| ≤ (MeromorphicOn.divisor zetaExt B ρ : ℝ)) →
        |(∑ᶠ ρ, f ρ) - (∑ᶠ ρ, g ρ)| ≤ ∑ᶠ ρ, (MeromorphicOn.divisor zetaExt B ρ : ℝ) := by
      intro f g hf hg hpt
      set S := hf.toFinset ∪ hg.toFinset ∪ hfin_B.toFinset
      rw [finsum_eq_sum_of_support_subset f (s := S) (fun x hx => by simp [S, hx]),
        finsum_eq_sum_of_support_subset g (s := S) (fun x hx => by simp [S, hx]),
        finsum_eq_sum_of_support_subset _ (s := S) (fun x hx => by simp [S, hx]),
        ← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ _ => hpt ρ)
    have hbound_B := hJ T
    rw [abs_of_pos (by linarith : 0 < T)] at hbound_B
    refine (hsub_fin _ _ (hfin_strip T) (hfin_strip H) fun ρ => ?_).trans hbound_B
    have hdiv_nn : 0 ≤ (MeromorphicOn.divisor zetaExt B ρ : ℝ) := by
      by_cases hρB : ρ ∈ B
      · rw [hdiv_F B ρ hρB]; positivity
      · have : MeromorphicOn.divisor zetaExt B ρ = 0 := by unfold MeromorphicOn.divisor; simp [hρB]
        simp [this]
    split_ifs with h1 h2 h2
    · simpa using hdiv_nn
    · -- `ρ` has `0 < ρ.re < 1`, `0 < ρ.im ≤ T`, and `H < ρ.im`
      have him_gt : H < ρ.im := by
        by_contra hle; push Not at hle; exact h2 ⟨h1.1, h1.2.1, h1.2.2.1, hle⟩
      have hρB : ρ ∈ B := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hre : |ρ.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith [h1.1, h1.2.1]
        have him : |ρ.im - T| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h1.2.2.2, him_gt, (abs_le.mp hHT_diff).1]
        have hsq : ‖ρ - ((2 : ℂ) + Complex.I * (T : ℂ))‖ ^ 2 ≤ 9 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.I_re,
            zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
            Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, one_mul, zero_add, Complex.ofReal_re]
          have h1s : (ρ.re - 2) ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (ρ.re - 2)]
          have h2s : (ρ.im - T) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (ρ.im - T)]
          linarith
        nlinarith [norm_nonneg (ρ - ((2 : ℂ) + Complex.I * (T : ℂ)))]
      have hne1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
      rw [sub_zero, abs_of_nonneg (Nat.cast_nonneg _), hdiv_F B ρ hρB, hord_F ρ hne1]
      norm_cast
    · -- `ρ` has `0 < ρ.re < 1`, `0 < ρ.im ≤ H`, and `T < ρ.im`
      have him_gt : T < ρ.im := by
        by_contra hle; push Not at hle; exact h1 ⟨h2.1, h2.2.1, h2.2.2.1, hle⟩
      have hρB : ρ ∈ B := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hre : |ρ.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith [h2.1, h2.2.1]
        have him : |ρ.im - T| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h2.2.2.2, him_gt, (abs_le.mp hHT_diff).2]
        have hsq : ‖ρ - ((2 : ℂ) + Complex.I * (T : ℂ))‖ ^ 2 ≤ 9 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.I_re,
            zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
            Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, one_mul, zero_add, Complex.ofReal_re]
          have h1s : (ρ.re - 2) ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (ρ.re - 2)]
          have h2s : (ρ.im - T) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (ρ.im - T)]
          linarith
        nlinarith [norm_nonneg (ρ - ((2 : ℂ) + Complex.I * (T : ℂ)))]
      have hne1 : ρ ≠ 1 := by intro h; rw [h] at h2; simp at h2
      rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hdiv_F B ρ hρB, hord_F ρ hne1]
      norm_cast
    · simpa using hdiv_nn
  -- Final triangle inequality
  have hrearr : NT - M T = (NT - NH) + (NH - M H) + (M H - M T) := by ring
  show |NT - M T| ≤ (2 * CG + CJ + 4) * Real.log (2 + T)
  rw [hrearr]
  calc _ ≤ |(NT - NH) + (NH - M H)| + |M H - M T| := abs_add_le _ _
    _ ≤ (|NT - NH| + |NH - M H|) + |M H - M T| := by gcongr; exact abs_add_le _ _
    _ ≤ (CJ * Real.log (2 + T) + CG * Real.log (2 + H)) + 4 * Real.log (2 + T) := by
        linarith [hNT_NH, hgood, hM_diff]
    _ ≤ (CJ * Real.log (2 + T) + CG * (2 * Real.log (2 + T))) + 4 * Real.log (2 + T) := by
        have := mul_le_mul_of_nonneg_left hlog_H hCG; linarith
    _ = (2 * CG + CJ + 4) * Real.log (2 + T) := by ring

end SpectralMod5

end Mod5Section

section Mod6Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace SpectralMod6

/-! ### Module 6: Smooth Explicit Formula for `P(X, t)` under RH -/

noncomputable def bump (a b t : ℝ) : ℝ :=
  if a < t ∧ t < b then Real.exp (-1 / ((t - a) * (b - t))) else 0

noncomputable def Wfun (t : ℝ) : ℝ := bump 1 (51 / 50) t

noncomputable def phiW (y : ℝ) : ℝ := Wfun (Real.exp y)

noncomputable def Wtilde (s : ℂ) : ℂ :=
  ∫ y : ℝ, (phiW y : ℂ) * Complex.exp (s * (y : ℂ))

noncomputable def Mfun (v : ℝ) : ℂ :=
  ∫ u : ℝ, ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * ((v * Real.log u : ℝ) : ℂ))

noncomputable def zCrit (g : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (g : ℂ)

noncomputable def mZero (g : ℝ) : ℕ := analyticOrderNatAt riemannZeta (zCrit g)

def wFinset (X : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)

noncomputable def uTerm (X n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Wfun ((n : ℝ) / X) / Real.sqrt n

noncomputable def Pfun (X : ℕ) (t : ℝ) : ℂ :=
  (wFinset X).sum (fun n => (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))

noncomputable def zetaExt (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

noncomputable def rectIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + Complex.I * (c : ℂ))) -
  (∫ x in a..b, f ((x : ℂ) + Complex.I * (d : ℂ))) +
  Complex.I * (∫ y in c..d, f ((b : ℂ) + Complex.I * (y : ℂ))) -
  Complex.I * (∫ y in c..d, f ((a : ℂ) + Complex.I * (y : ℂ)))

noncomputable def Gweight (X : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  Wtilde (w - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
    Complex.exp ((w - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ))

noncomputable def Eleft (X : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
      Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))

/-! #### Part 6A: Right-Line Mellin Representation of `Pfun X t` -/

lemma integrable_div_one_add_abs_pow' (C : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => C / (1 + |t|) ^ k) := by
  have hcont : Continuous (fun t : ℝ => C / (1 + |t|) ^ k) :=
    continuous_const.div ((continuous_const.add continuous_abs).pow k)
      (fun t => pow_ne_zero k (by linarith [abs_nonneg t]))
  have h1 : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hdom : Integrable (fun t : ℝ => (2 * |C|) * (1 + t ^ 2)⁻¹) := h1.const_mul (2 * |C|)
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (1 + |t|) ^ k := by positivity
  have h2 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ k := pow_le_pow_right₀ (by linarith [abs_nonneg t]) hk
  have hsq : 1 + t ^ 2 ≤ 2 * (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [this]; nlinarith [abs_nonneg t]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |C| = (2 * |C|) * (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) / 2) := by
        have h1t : 1 + t ^ 2 ≠ 0 := by positivity
        field_simp [h1t]
    _ ≤ (2 * |C|) * (1 + t ^ 2)⁻¹ * (1 + |t|) ^ 2 := by
        gcongr; linarith
    _ ≤ (2 * |C|) * (1 + t ^ 2)⁻¹ * (1 + |t|) ^ k := by gcongr

lemma Pfun_eq_tsum {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    Pfun X t = ∑' n : ℕ, (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
  symm
  rw [tsum_eq_sum (s := wFinset X)]
  · rfl
  · intro n hn
    have hW0 : Wfun ((n : ℝ) / X) = 0 := by
      unfold Wfun bump
      split_ifs with h
      · exfalso
        apply hn
        simp only [wFinset, Finset.mem_filter, Finset.mem_range]
        have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
        have h1 : (X : ℝ) < (n : ℝ) := by have h1' := h.1; rwa [one_lt_div hXpos] at h1'
        have h2 : 50 * (n : ℝ) < 51 * (X : ℝ) := by
          have := (div_lt_iff₀ hXpos).mp h.2; linarith
        have h1n : X < n := by exact_mod_cast h1
        have h2n : 50 * n < 51 * X := by exact_mod_cast h2
        exact ⟨by omega, h1n, h2n⟩
      · rfl
    simp [uTerm, hW0]

lemma Pfun_eq_integral_logDeriv_zeta
    (hWtilde_diff : Differentiable ℂ Wtilde)
    (hWtilde_decay : ∀ σ1 σ2 : ℝ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ1 ≤ s.re → s.re ≤ σ2 → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ k)
    (hmellin : ∀ (c : ℝ) {x : ℝ}, 0 < x →
      (Wfun x : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * (x : ℂ) ^ (-((c : ℂ) + Complex.I * (τ : ℂ))))
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    Pfun X t = (1 / (2 * (Real.pi : ℂ))) *
      ∫ y : ℝ, (-logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) *
        Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  -- Step 1: Express each term `n` as an integral over `τ : ℝ`
  let f : ℕ → ℝ → ℂ := fun n τ =>
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) n *
    (Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
      Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ)))
  have hterm_eq : ∀ n : ℕ,
      (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) =
        (1 / (2 * (Real.pi : ℂ))) * ∫ τ : ℝ, f n τ := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [uTerm, f, LSeries.term]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hdiv_pos : (0 : ℝ) < (n : ℝ) / (X : ℝ) := div_pos hn_pos hXpos
      have hm := hmellin 2 hdiv_pos
      simp only [Complex.ofReal_ofNat] at hm
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
      have hu_cast : (uTerm X n : ℂ) =
          (ArithmeticFunction.vonMangoldt n : ℂ) * (Wfun ((n : ℝ) / X) : ℂ) / (Real.sqrt n : ℂ) := by
        unfold uTerm; push_cast; rfl
      rw [hu_cast, hm]
      have hpull : (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ τ : ℝ, Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
              (((n : ℝ) / (X : ℝ) : ℝ) : ℂ) ^ (-((2 : ℂ) + Complex.I * (τ : ℂ)))) /
          (Real.sqrt n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) =
          (1 / (2 * (Real.pi : ℂ))) *
            (((ArithmeticFunction.vonMangoldt n : ℂ) / (Real.sqrt n : ℂ) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))) *
              ∫ τ : ℝ, Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
                (((n : ℝ) / (X : ℝ) : ℝ) : ℂ) ^ (-((2 : ℂ) + Complex.I * (τ : ℂ)))) := by ring
      rw [hpull, ← MeasureTheory.integral_const_mul]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      dsimp only [f]
      rw [LSeries.term_of_ne_zero hn]
      have hcpow_nx : (((n : ℝ) / (X : ℝ) : ℝ) : ℂ) ^ (-((2 : ℂ) + Complex.I * (τ : ℂ))) =
          Complex.exp (-((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log n : ℂ)) *
          Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hdiv_pos.ne'),
          ← Complex.ofReal_log hdiv_pos.le, Real.log_div hn_pos.ne' hXpos.ne',
          ← Complex.exp_add]
        congr 1; push_cast; ring
      have hsqrt_exp : (Real.sqrt n : ℂ) = Complex.exp ((1 / 2 : ℂ) * (Real.log n : ℂ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos, Complex.ofReal_exp]
        congr 1; push_cast; ring
      have hncpow : (n : ℂ) ^ ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) =
          Complex.exp (((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) * (Real.log n : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
          ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
        congr 1; ring
      rw [hcpow_nx, hsqrt_exp, hncpow]
      have hexp_eq :
          (Complex.exp ((1 / 2 : ℂ) * (Real.log n : ℂ)))⁻¹ *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
          Complex.exp (-((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log n : ℂ)) =
          (Complex.exp (((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) * (Real.log n : ℂ)))⁻¹ := by
        rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
      calc (ArithmeticFunction.vonMangoldt n : ℂ) / Complex.exp ((1 / 2 : ℂ) * (Real.log n : ℂ)) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
              (Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
                (Complex.exp (-((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log n : ℂ)) *
                  Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))))
          = (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((Complex.exp ((1 / 2 : ℂ) * (Real.log n : ℂ)))⁻¹ *
                Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
                Complex.exp (-((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log n : ℂ))) *
              (Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
                Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))) := by ring
        _ = (ArithmeticFunction.vonMangoldt n : ℂ) /
              Complex.exp (((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) * (Real.log n : ℂ)) *
              (Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
                Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))) := by
            rw [hexp_eq]; ring
  rw [Pfun_eq_tsum hX t]
  simp_rw [hterm_eq]
  rw [tsum_mul_left]
  congr 1
  -- Step 2: Swap `∑' n` and `∫ τ` using `MeasureTheory.integral_tsum`
  obtain ⟨CW, hCW, hWdec⟩ := hWtilde_decay 2 2 2
  have hWbound : ∀ τ : ℝ, ‖Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
      Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))‖ ≤
      (CW * (X : ℝ) ^ 2) / (1 + |τ|) ^ 2 := by
    intro τ
    rw [norm_mul, Complex.norm_exp]
    have hre : (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ)).re = 2 * Real.log X := by
      simp only [Complex.mul_re, Complex.add_re, Complex.re_ofNat, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.ofReal_re,
        Complex.add_im, Complex.im_ofNat, Complex.mul_im, one_mul, zero_add]
      ring
    rw [hre, show 2 * Real.log X = Real.log ((X : ℝ) ^ 2) by rw [Real.log_pow]; ring,
      Real.exp_log (by positivity)]
    have h1 := hWdec ((2 : ℂ) + Complex.I * (τ : ℂ)) (by simp) (by simp)
    simp only [Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at h1
    calc ‖Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ))‖ * (X : ℝ) ^ 2
        ≤ (CW / (1 + |τ|) ^ 2) * (X : ℝ) ^ 2 := by gcongr
      _ = (CW * (X : ℝ) ^ 2) / (1 + |τ|) ^ 2 := by ring
  have hterm_bound : ∀ (n : ℕ) (τ : ℝ),
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) n‖ ≤ 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n τ
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
      have hre : ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)).re = 5 / 2 := by simp
      rw [hre]
      have hv : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
        (ArithmeticFunction.vonMangoldt_le_log).trans (by linarith [Real.log_le_sub_one_of_pos hn_pos])
      calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)
          ≤ (n : ℝ) / (n : ℝ) ^ (5 / 2 : ℝ) := by gcongr
        _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
            have h1 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
              rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
            rw [h1]; field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos (3 / 2)).ne']
  have hf_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) volume := by
    intro n
    have hcW : Continuous (fun τ : ℝ => Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
        Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))) :=
      (hWtilde_diff.continuous.comp (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))).mul
        (Complex.continuous_exp.comp ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).mul continuous_const))
    by_cases hn : n = 0
    · subst hn; simp only [f, LSeries.term_zero, zero_mul]; exact continuous_const.aestronglyMeasurable
    · have hcL : Continuous (fun τ : ℝ => LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) n) := by
        simp_rw [LSeries.term_of_ne_zero hn]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have heq : (fun τ : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) /
            (n : ℂ) ^ ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ))) =
            (fun τ : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              Complex.exp (-(((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) * (Real.log n : ℂ)))) := by
          funext τ
          rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.ofReal_natCast,
            ← Complex.ofReal_log hn_pos.le, Complex.exp_neg, div_eq_mul_inv]
          congr 2; ring
        rw [heq]
        exact continuous_const.mul (Complex.continuous_exp.comp
          (((continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp
            (continuous_const.add continuous_id)))).mul continuous_const).neg))
      exact (hcL.mul hcW).aestronglyMeasurable
  have hf_sum_lint : ∑' n : ℕ, ∫⁻ τ : ℝ, ‖f n τ‖ₑ ≠ ⊤ := by
    have hint_base : Integrable (fun τ : ℝ => (CW * (X : ℝ) ^ 2) / (1 + |τ|) ^ 2) :=
      integrable_div_one_add_abs_pow' (CW * (X : ℝ) ^ 2) 2 le_rfl
    set I0 : ENNReal := ∫⁻ τ : ℝ, ENNReal.ofReal ((CW * (X : ℝ) ^ 2) / (1 + |τ|) ^ 2)
    have hI0_lt : I0 < ⊤ := by
      have h := hint_base.hasFiniteIntegral
      rw [HasFiniteIntegral] at h
      convert h using 1
      refine lintegral_congr fun τ => ?_
      exact (Real.eNorm_eq_ofReal (by positivity)).symm
    have hle_n : ∀ n : ℕ, ∫⁻ τ : ℝ, ‖f n τ‖ₑ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ (3 / 2 : ℝ)) * I0 := by
      intro n
      rw [← lintegral_const_mul _ (by
        exact (ENNReal.continuous_ofReal.comp
          (continuous_const.div ((continuous_const.add continuous_abs).pow 2)
            fun τ => pow_ne_zero 2 (ne_of_gt (by linarith [abs_nonneg τ] : (0 : ℝ) < 1 + |τ|)))).measurable)]
      refine lintegral_mono fun τ => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul]
      exact mul_le_mul (hterm_bound n τ) (hWbound τ) (norm_nonneg _) (by positivity)
    have hsum_nat : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    have hsum_enn : ∑' n : ℕ, ENNReal.ofReal (1 / (n : ℝ) ^ (3 / 2 : ℝ)) < ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum_nat]
      exact ENNReal.ofReal_lt_top
    have htot : ∑' n : ℕ, ∫⁻ τ : ℝ, ‖f n τ‖ₑ ≤ (∑' n : ℕ, ENNReal.ofReal (1 / (n : ℝ) ^ (3 / 2 : ℝ))) * I0 := by
      rw [← ENNReal.tsum_mul_right]
      exact tsum_le_tsum hle_n
    exact ne_of_lt (lt_of_le_of_lt htot (ENNReal.mul_lt_top hsum_enn hI0_lt))
  rw [← MeasureTheory.integral_tsum hf_meas hf_sum_lint]
  -- Step 3: Evaluate `∑' n, f n τ` using `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, then translate `y = t + τ`
  have hsum_eval : ∀ τ : ℝ, ∑' n : ℕ, f n τ =
      (-logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ))) *
      (Wtilde ((2 : ℂ) + Complex.I * (τ : ℂ)) *
        Complex.exp (((2 : ℂ) + Complex.I * (τ : ℂ)) * (Real.log X : ℂ))) := by
    intro τ
    dsimp only [f]
    rw [tsum_mul_right]
    congr 1
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ)) (by simp; norm_num)
    unfold LSeries at hL
    rw [hL, logDeriv_apply]; ring
  simp_rw [hsum_eval]
  have hshift := MeasureTheory.integral_add_left_eq_self (μ := volume)
    (fun y : ℝ => (-logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) *
      Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) t
  rw [← hshift]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  dsimp only [Gweight]
  have harg : (5 / 2 : ℂ) + Complex.I * ((t + τ : ℝ) : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ) =
      (2 : ℂ) + Complex.I * (τ : ℂ) := by push_cast; ring
  rw [harg]

/-! #### Part 6B: Meromorphicity, Pole Order at 1, and Zero Classification under RH -/

lemma riemannZeta_meromorphicOn (hF_diff : Differentiable ℂ zetaExt) :
    MeromorphicOn riemannZeta Set.univ := by
  have hF_an : AnalyticOnNhd ℂ zetaExt Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
  intro z _
  have hev' : riemannZeta =ᶠ[𝓝[≠] z] fun w => zetaExt w / (w - 1) := by
    by_cases hz1 : z = 1
    · subst hz1
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      simp [zetaExt, hw1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw1)]
    · filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz1)] with w hw
      simp [zetaExt, hw, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw)]
  have hquot : MeromorphicAt (fun w : ℂ => zetaExt w / (w - 1)) z :=
    (hF_an z (Set.mem_univ z)).meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact hquot.congr hev'.symm

lemma meromorphicOrderAt_riemannZeta_ne_top (hF_diff : Differentiable ℂ zetaExt) (z : ℂ) :
    meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  have hF_an : AnalyticOnNhd ℂ zetaExt Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hev : riemannZeta =ᶠ[𝓝[≠] z] fun w => zetaExt w / (w - 1) := by
    by_cases hz1 : z = 1
    · subst hz1
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      simp [zetaExt, hw1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw1)]
    · filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz1)] with w hw
      simp [zetaExt, hw, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hw)]
  rw [meromorphicOrderAt_congr hev]
  intro htop
  rw [meromorphicOrderAt_eq_top_iff] at htop
  have hF0 : ∀ᶠ w in 𝓝[≠] z, zetaExt w = 0 := by
    have hne1 : ∀ᶠ w in 𝓝[≠] z, w ≠ 1 := by
      by_cases hz1 : z = 1
      · subst hz1; exact self_mem_nhdsWithin
      · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz1)
    filter_upwards [htop, hne1] with w hw0 hw1
    exact (div_eq_zero_iff.mp hw0).resolve_right (sub_ne_zero.mpr hw1)
  have hF0_z : zetaExt z = 0 := by
    have h1 : Tendsto zetaExt (𝓝[≠] z) (𝓝 (zetaExt z)) :=
      hF_diff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto zetaExt (𝓝[≠] z) (𝓝 0) := tendsto_const_nhds.congr' (hF0.mono fun _ h => h.symm)
    exact tendsto_nhds_unique h1 h2
  have hF_ev0 : ∀ᶠ w in 𝓝 z, zetaExt w = 0 := by
    rw [eventually_nhdsWithin_iff] at hF0
    filter_upwards [hF0] with w hw
    by_cases h : w = z
    · rwa [h]
    · exact hw h
  have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hF_an
    isPreconnected_univ (Set.mem_univ z) hF_ev0
  have h1 := heq (Set.mem_univ 1); simp [zetaExt] at h1

lemma divisor_riemannZeta_one (hF_diff : Differentiable ℂ zetaExt) :
    MeromorphicOn.divisor riemannZeta Set.univ 1 = -1 := by
  have hmero := riemannZeta_meromorphicOn hF_diff
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ 1)]
  have hF_an : AnalyticAt ℂ zetaExt 1 :=
    (hF_diff.differentiableOn.analyticOnNhd isOpen_univ) 1 (Set.mem_univ 1)
  have hF1 : zetaExt 1 ≠ 0 := by simp [zetaExt]
  have hord : meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff (hmero 1 (Set.mem_univ 1))]
    refine ⟨zetaExt, hF_an, hF1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw1 : w ≠ 1 := hw
    simp [zetaExt, hw1, smul_eq_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr hw1)]
  rw [hord]; rfl

lemma divisor_riemannZeta_of_ne_one (hF_diff : Differentiable ℂ zetaExt) {z : ℂ} (hz : z ≠ 1) :
    MeromorphicOn.divisor riemannZeta Set.univ z = (analyticOrderNatAt riemannZeta z : ℤ) := by
  have hmero := riemannZeta_meromorphicOn hF_diff
  have hzan : AnalyticAt ℂ riemannZeta z := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hz)
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ z), hzan.meromorphicOrderAt_eq]
  have hntop : analyticOrderAt riemannZeta z ≠ ⊤ := by
    intro h; apply meromorphicOrderAt_riemannZeta_ne_top hF_diff z
    rw [hzan.meromorphicOrderAt_eq, h]; rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  have hnat : analyticOrderNatAt riemannZeta z = n := by simp [analyticOrderNatAt, ← hn]
  rw [← hn, hnat]; rfl

lemma riemannZeta_ne_zero_of_neg_half_le_re_nonpos {s : ℂ} (hlo : -(1 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ 0) :
    riemannZeta s ≠ 0 := by
  by_cases hs0 : s = 0
  · rw [hs0, riemannZeta_zero]; norm_num
  · have hne_neg : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
      intro n h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hne1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
    have hfe := riemannZeta_one_sub hne_neg hne1
    rw [sub_sub_cancel] at hfe
    rw [hfe]
    have hpi : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))]
      exact Complex.exp_ne_zero _
    have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
      intro hc
      rw [Complex.cos_eq_zero_iff] at hc
      obtain ⟨k, hk⟩ := hc
      have hre := congrArg Complex.re hk
      have him := congrArg Complex.im hk
      simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_mul, sub_zero,
        Complex.add_re, Complex.intCast_re, Complex.div_ofNat_im, Complex.mul_im, Complex.add_im,
        Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, add_zero, zero_sub] at hre him
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      have hsim : s.im = 0 := by nlinarith
      have hsre : s.re = -2 * (k : ℝ) := by nlinarith
      have hk0 : k = 0 := by
        have h1 : -2 * (k : ℝ) ≤ 0 := by linarith
        have h2 : -(1 / 2 : ℝ) ≤ -2 * (k : ℝ) := by linarith
        have hk_ge : (0 : ℝ) ≤ (k : ℝ) := by linarith
        have hk_lt : (k : ℝ) < 1 := by linarith
        have hk_ge_z : 0 ≤ k := by exact_mod_cast hk_ge
        have hk_lt_z : k < 1 := by exact_mod_cast hk_lt
        omega
      subst hk0
      apply hs0
      apply Complex.ext <;> simp [hsim, hsre]
    have hzr : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hG) hcos) hzr

lemma zero_re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ}
    (hlo : -(1 / 2 : ℝ) ≤ ρ.re) (hρ : riemannZeta ρ = 0) : ρ.re = 1 / 2 := by
  have hlt1 : ρ.re < 1 := by
    by_contra hge; push Not at hge; exact riemannZeta_ne_zero_of_one_le_re hge hρ
  have hgt0 : 0 < ρ.re := by
    by_contra hle; push Not at hle; exact riemannZeta_ne_zero_of_neg_half_le_re_nonpos hlo hle hρ
  have hnt : ¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩; simp at hgt0; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at hlt1; simp at hlt1
  exact hRH ρ hρ hnt hne1

/-! #### Part 6C: Bounds on `Eleft`, Pole Term, Zero Sum Convergence, and Main Explicit Formula -/

lemma norm_pole_term_le
    (hWtilde_decay : ∀ σ1 σ2 : ℝ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ1 ≤ s.re → s.re ≤ σ2 → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ k) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      ‖Gweight X t 1‖ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5 := by
  obtain ⟨C, hC, hdec⟩ := hWtilde_decay (1 / 2) (1 / 2) 5
  refine ⟨C, hC, fun X hX t => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  dsimp only [Gweight]
  rw [norm_mul, Complex.norm_exp]
  have hre : (((1 : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)).re = (1 / 2 : ℝ) * Real.log X := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero,
      Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, zero_div,
      Complex.mul_im, one_mul, zero_add]
    ring
  rw [hre, show (1 / 2 : ℝ) * Real.log X = Real.log (Real.sqrt X) by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hXpos],
    Real.exp_log (Real.sqrt_pos.mpr hXpos)]
  have h1 := hdec ((1 : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) (by simp; norm_num) (by simp; norm_num)
  have him : ((1 : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).im = -t := by simp
  rw [him, abs_neg] at h1
  calc ‖Wtilde ((1 : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ * Real.sqrt X
      ≤ (C / (1 + |t|) ^ 5) * Real.sqrt X := by gcongr
    _ = C * Real.sqrt X / (1 + |t|) ^ 5 := by ring

lemma norm_Eleft_le
    (hWtilde_decay : ∀ σ1 σ2 : ℝ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ1 ≤ s.re → s.re ≤ σ2 → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ k)
    (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hneg_half : ∀ τ : ℝ, ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C2 * Real.log (2 + |τ|)) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      ‖Eleft X t‖ ≤ CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) := by
  obtain ⟨CW, hCW, hdec⟩ := hWtilde_decay (-1) (-1) 4
  have hint_dom : Integrable (fun u : ℝ => (1 + Real.log (2 + |u|)) / (1 + |u|) ^ 4) := by
    have hdom := integrable_div_one_add_abs_pow' (4 : ℝ) 2 le_rfl
    have hcont : Continuous (fun u : ℝ => (1 + Real.log (2 + |u|)) / (1 + |u|) ^ 4) :=
      (continuous_const.add (Real.continuousOn_log.comp_continuous (continuous_const.add continuous_abs)
        (fun u => ne_of_gt (by linarith [abs_nonneg u] : (0 : ℝ) < 2 + |u|)))).div ((continuous_const.add continuous_abs).pow 4)
        (fun u => pow_ne_zero 4 (ne_of_gt (by linarith [abs_nonneg u] : (0 : ℝ) < 1 + |u|)))
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    have hlog_le : Real.log (2 + |u|) ≤ 1 + |u| := by
      linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg u] : 0 < 2 + |u|)]
    have hlog_nn : 0 ≤ Real.log (2 + |u|) := Real.log_nonneg (by linarith [abs_nonneg u])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
    have hpow : (1 + |u|) ^ 4 = (1 + |u|) ^ 2 * (1 + |u|) ^ 2 := by ring
    rw [hpow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : 1 + Real.log (2 + |u|) ≤ 4 * (1 + |u|) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (1 + |u|)]
  set I0 : ℝ := ∫ u : ℝ, (1 + Real.log (2 + |u|)) / (1 + |u|) ^ 4
  have hI0_nn : 0 ≤ I0 := MeasureTheory.integral_nonneg fun u =>
    div_nonneg (by linarith [Real.log_nonneg (by linarith [abs_nonneg u] : (1 : ℝ) ≤ 2 + |u|)]) (by positivity)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨C2 * CW * (2 * I0) / (2 * Real.pi), by positivity, fun X hX t => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  unfold Eleft
  rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hpt : ∀ y : ℝ, ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
      Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ ≤
      (C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|))) * ((1 + Real.log (2 + |y - t|)) / (1 + |y - t|) ^ 4) := by
    intro y
    dsimp only [Gweight]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre_s : (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).re = -1 := by
      simp; norm_num
    have him_s : (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).im = y - t := by
      simp
    have hre_e : ((-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)).re =
        -Real.log X := by
      rw [Complex.mul_re, hre_s, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hre_e, Real.exp_neg, Real.exp_log hXpos]
    have hW := hdec (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))
      (by linarith [hre_s]) (by linarith [hre_s])
    rw [him_s] at hW
    have hlog_y : Real.log (2 + |y|) ≤ Real.log (2 + |t|) + Real.log (2 + |y - t|) := by
      have hle : 2 + |y| ≤ (2 + |t|) * (2 + |y - t|) := by
        have htri : |y| ≤ |t| + |y - t| := by
          have := abs_add_le t (y - t); simpa [add_sub_cancel] using this
        nlinarith [abs_nonneg t, abs_nonneg (y - t)]
      calc Real.log (2 + |y|) ≤ Real.log ((2 + |t|) * (2 + |y - t|)) :=
            Real.log_le_log (by linarith [abs_nonneg y]) hle
        _ = Real.log (2 + |t|) + Real.log (2 + |y - t|) :=
            Real.log_mul (by linarith [abs_nonneg t]) (by linarith [abs_nonneg (y - t)])
    have hlog_t : (1 / 2 : ℝ) ≤ Real.log (2 + |t|) :=
      hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
    have hlu : 0 ≤ Real.log (2 + |y - t|) := Real.log_nonneg (by linarith [abs_nonneg (y - t)])
    have hlt0 : 0 ≤ Real.log (2 + |t|) := by linarith
    have hlog_prod : Real.log (2 + |y|) ≤ (2 * Real.log (2 + |t|)) * (1 + Real.log (2 + |y - t|)) := by
      nlinarith
    have hld := hneg_half y
    calc ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ *
          (‖Wtilde (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ * (X : ℝ)⁻¹)
        ≤ (C2 * ((2 * Real.log (2 + |t|)) * (1 + Real.log (2 + |y - t|)))) *
          ((CW / (1 + |y - t|) ^ 4) * (X : ℝ)⁻¹) := by
            have h1 : ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ ≤
                C2 * ((2 * Real.log (2 + |t|)) * (1 + Real.log (2 + |y - t|))) :=
              hld.trans (mul_le_mul_of_nonneg_left hlog_prod hC2)
            have h2 : ‖Wtilde (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ * (X : ℝ)⁻¹ ≤
                (CW / (1 + |y - t|) ^ 4) * (X : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right hW (by positivity)
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|))) * ((1 + Real.log (2 + |y - t|)) / (1 + |y - t|) ^ 4) := by ring
  have hint_shift : Integrable (fun y : ℝ =>
      (C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|))) * ((1 + Real.log (2 + |y - t|)) / (1 + |y - t|) ^ 4)) :=
    (hint_dom.comp_sub_right t).const_mul _
  have hnorm_le : ‖∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
      Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ ≤
      C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|)) * I0 := by
    calc _ ≤ ∫ y : ℝ, ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
              Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ, (C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|))) *
            ((1 + Real.log (2 + |y - t|)) / (1 + |y - t|) ^ 4) := by
            by_cases hint : Integrable (fun y : ℝ => ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
                Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖)
            · exact MeasureTheory.integral_mono hint hint_shift hpt
            · rw [MeasureTheory.integral_undef hint]
              exact MeasureTheory.integral_nonneg fun y => by
                have h1 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
                have h2 : 0 ≤ Real.log (2 + |y - t|) := Real.log_nonneg (by linarith [abs_nonneg (y - t)])
                positivity
      _ = C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|)) * I0 := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_sub_right_eq_self (fun u : ℝ => (1 + Real.log (2 + |u|)) / (1 + |u|) ^ 4) t]
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
          Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖
      ≤ 1 / (2 * Real.pi) * (C2 * CW * (X : ℝ)⁻¹ * (2 * Real.log (2 + |t|)) * I0) := by gcongr
    _ = C2 * CW * (2 * I0) / (2 * Real.pi) * (X : ℝ)⁻¹ * Real.log (2 + |t|) := by ring

lemma unit_interval_zero_count
    (hF_diff : Differentiable ℂ zetaExt)
    (CJ : ℝ) (_hCJ : 0 ≤ CJ)
    (hJ : ∀ t : ℝ,
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 3) u : ℝ)) ≤
        CJ * Real.log (2 + |t|)) :
    ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|) := by
  intro a
  set B := Metric.closedBall ((2 : ℂ) + Complex.I * (a : ℂ)) 3
  have hF_an : AnalyticOnNhd ℂ zetaExt Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hF_ntop : ∀ z : ℂ, analyticOrderAt zetaExt z ≠ ⊤ := by
    intro z htop
    have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hF_an
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop)
    have h1 := heq (Set.mem_univ 1); simp [zetaExt] at h1
  have hdiv_B : ∀ z ∈ B, MeromorphicOn.divisor zetaExt B z = (analyticOrderNatAt zetaExt z : ℤ) := by
    intro z hz
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF_an.mono (Set.subset_univ B)) hz]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hF_ntop z)
    have hnat : analyticOrderNatAt zetaExt z = n := by simp [analyticOrderNatAt, ← hn]
    rw [← hn, hnat]; rfl
  have hord_z : ∀ g : ℝ, analyticOrderNatAt zetaExt (zCrit g) = mZero g := by
    intro g
    have hne1 : zCrit g ≠ 1 := by intro h; have := congrArg Complex.re h; simp [zCrit] at this
    have hev : zetaExt =ᶠ[𝓝 (zCrit g)] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hne1] with w hw; simp [zetaExt, hw]
    have hza := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)
    have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) (zCrit g) := analyticAt_id.sub analyticAt_const
    have h1 : analyticOrderAt zetaExt (zCrit g) = analyticOrderAt ((fun w : ℂ => w - 1) * riemannZeta) (zCrit g) :=
      analyticOrderAt_congr hev
    rw [analyticOrderAt_mul hlin hza, hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hne1), zero_add] at h1
    simp only [mZero, analyticOrderNatAt, h1]
  have hz_in_B : ∀ g : ℝ, a ≤ g → g < a + 1 → zCrit g ∈ B := by
    intro g h1 h2
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsq : ‖zCrit g - ((2 : ℂ) + Complex.I * (a : ℂ))‖ ^ 2 ≤ 9 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : (zCrit g - ((2 : ℂ) + Complex.I * (a : ℂ))).re = -(3 / 2 : ℝ) := by simp [zCrit]; norm_num
      have him : (zCrit g - ((2 : ℂ) + Complex.I * (a : ℂ))).im = g - a := by simp [zCrit]
      rw [hre, him]
      have hg : (g - a) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith [norm_nonneg (zCrit g - ((2 : ℂ) + Complex.I * (a : ℂ)))]
  have hfin_B : (MeromorphicOn.divisor zetaExt B).support.Finite :=
    (MeromorphicOn.divisor zetaExt B).finiteSupport (isCompact_closedBall _ 3)
  set SB : Finset ℂ := hfin_B.toFinset
  set S : Finset ℝ := (SB.image Complex.im).filter (fun g => a ≤ g ∧ g < a + 1)
  have hfin_S : (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite := by
    refine S.finite_toSet.subset fun g hg => ?_
    rw [Function.mem_support] at hg
    split_ifs at hg with hga
    · have hmemB : zCrit g ∈ B := hz_in_B g hga.1 hga.2
      have hdiv_ne : MeromorphicOn.divisor zetaExt B (zCrit g) ≠ 0 := by
        rw [hdiv_B _ hmemB, hord_z g]; exact_mod_cast hg
      have hmemSB : zCrit g ∈ SB := hfin_B.mem_toFinset.mpr hdiv_ne
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨zCrit g, hmemSB, by simp [zCrit]⟩, hga⟩)
    · exact (hg rfl).elim
  refine ⟨hfin_S, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := S) (fun g hg => by
    rw [Function.mem_support] at hg
    split_ifs at hg with hga
    · have hmemB : zCrit g ∈ B := hz_in_B g hga.1 hga.2
      have hdiv_ne : MeromorphicOn.divisor zetaExt B (zCrit g) ≠ 0 := by
        rw [hdiv_B _ hmemB, hord_z g]; exact_mod_cast hg
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨zCrit g, hfin_B.mem_toFinset.mpr hdiv_ne, by simp [zCrit]⟩, hga⟩)
    · exact (hg rfl).elim)]
  have hsum_B : ∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt B u : ℝ) =
      ∑ u ∈ SB, (MeromorphicOn.divisor zetaExt B u : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun u hu => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0; apply hu; simp [h0]
  have hJ_a := hJ a
  rw [hsum_B] at hJ_a
  refine (le_trans ?_ hJ_a)
  have hsum_eq : ∑ g ∈ S, (if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) =
      ∑ u ∈ S.image zCrit, (MeromorphicOn.divisor zetaExt B u : ℝ) := by
    rw [Finset.sum_image (fun g1 _ g2 _ heq => by simpa [zCrit] using congrArg Complex.im heq)]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hga := (Finset.mem_filter.mp hg).2
    simp only [hga, and_self, ↓reduceIte]
    rw [hdiv_B _ (hz_in_B g hga.1 hga.2), hord_z g]; norm_cast
  rw [hsum_eq]
  -- Every `u ∈ S.image zCrit` with nonzero divisor is in `SB`, and all divisors on `B` are `≥ 0`
  have hsub : (S.image zCrit).filter (fun u => MeromorphicOn.divisor zetaExt B u ≠ 0) ⊆ SB := by
    intro u hu
    exact hfin_B.mem_toFinset.mpr (Finset.mem_filter.mp hu).2
  have hnn : ∀ u ∈ SB, (0 : ℝ) ≤ (MeromorphicOn.divisor zetaExt B u : ℝ) := by
    intro u hu
    have huB : u ∈ B := by
      by_contra hnot
      have : MeromorphicOn.divisor zetaExt B u = 0 := by unfold MeromorphicOn.divisor; simp [hnot]
      exact (hfin_B.mem_toFinset.mp hu) this
    rw [hdiv_B u huB]; positivity
  calc ∑ u ∈ S.image zCrit, (MeromorphicOn.divisor zetaExt B u : ℝ)
      = ∑ u ∈ (S.image zCrit).filter (fun u => MeromorphicOn.divisor zetaExt B u ≠ 0),
          (MeromorphicOn.divisor zetaExt B u : ℝ) := by
          symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun u hu hnot => ?_
          have h0 : MeromorphicOn.divisor zetaExt B u = 0 := by
            by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨hu, hne⟩)
          simp [h0]
    _ ≤ ∑ u ∈ SB, (MeromorphicOn.divisor zetaExt B u : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun u hu _ => hnn u hu

lemma summable_zero_explicit_term
    (hF_diff : Differentiable ℂ zetaExt)
    (hWtilde_decay : ∀ σ1 σ2 : ℝ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ1 ≤ s.re → s.re ≤ σ2 → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ k)
    (hMfun_eq : ∀ v : ℝ, Mfun v = Wtilde (Complex.I * (v : ℂ)))
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJ : ∀ t : ℝ,
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 3) u : ℝ)) ≤
        CJ * Real.log (2 + |t|))
    (X : ℕ) (t : ℝ) :
    Summable (fun g : {g : ℝ // riemannZeta (zCrit g) = 0} =>
      (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) := by
  obtain ⟨CM, hCM, hMdec⟩ := hWtilde_decay 0 0 4
  have hMbd : ∀ v : ℝ, ‖Mfun v‖ ≤ CM / (1 + |v|) ^ 4 := by
    intro v; rw [hMfun_eq v]
    simpa using hMdec (Complex.I * (v : ℂ)) (by simp) (by simp)
  apply Summable.of_norm
  -- Bound finite subsums uniformly by grouping into unit intervals `[k, k + 1)`
  have hunit := unit_interval_zero_count hF_diff CJ hCJ hJ
  have hsum_int : Summable (fun k : ℤ => (CJ * Real.log (2 + |(k : ℝ)|)) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4)) := by
    have hdom : Summable (fun k : ℤ => (CJ * (16 * CM) * (2 + |t|) ^ 4) / (1 + |(k : ℝ)|) ^ 2) := by
      have hnat : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
        have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
          (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective Nat.succ_injective
        exact h1.congr fun n => by push_cast; rfl
      have hpos : Summable (fun k : ℤ => (1 : ℝ) / (1 + |(k : ℝ)|) ^ 2) := by
        rw [summable_int_iff_summable_nat_and_neg]
        constructor
        · exact hnat.congr fun n => by
            rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
        · exact hnat.congr fun n => by
            rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
      have hmul := hpos.mul_left (CJ * (16 * CM) * (2 + |t|) ^ 4)
      exact hmul.congr fun k => by ring
    refine Summable.of_nonneg_of_le (fun k => by
      have : 0 ≤ Real.log (2 + |(k : ℝ)|) := Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])
      positivity) (fun k => ?_) hdom
    have hlog : Real.log (2 + |(k : ℝ)|) ≤ 1 + |(k : ℝ)| := by
      linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg (k : ℝ)] : 0 < 2 + |(k : ℝ)|)]
    have hden : 1 + |(k : ℝ)| ≤ (2 + |t|) * (1 + |(k : ℝ) - t|) := by
      have htri : |(k : ℝ)| ≤ |t| + |(k : ℝ) - t| := by
        have := abs_add_le t ((k : ℝ) - t); simpa [add_sub_cancel] using this
      nlinarith [abs_nonneg t, abs_nonneg ((k : ℝ) - t)]
    have hpow4 : (1 + |(k : ℝ)|) ^ 4 ≤ (2 + |t|) ^ 4 * (1 + |(k : ℝ) - t|) ^ 4 := by
      calc (1 + |(k : ℝ)|) ^ 4 ≤ ((2 + |t|) * (1 + |(k : ℝ) - t|)) ^ 4 :=
            pow_le_pow_left₀ (by linarith [abs_nonneg (k : ℝ)]) hden 4
        _ = (2 + |t|) ^ 4 * (1 + |(k : ℝ) - t|) ^ 4 := by ring
    have h1k : 1 ≤ 1 + |(k : ℝ)| := by linarith [abs_nonneg (k : ℝ)]
    have hden_pos : 0 < (1 + |(k : ℝ) - t|) ^ 4 := by positivity
    have h1k_pos : 0 < (1 + |(k : ℝ)|) ^ 2 := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hden_pos h1k_pos]
    have hlog_le2 : Real.log (2 + |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ 2 ≤ (1 + |(k : ℝ)|) ^ 4 := by
      have h3 : (1 + |(k : ℝ)|) ^ 3 ≤ (1 + |(k : ℝ)|) ^ 4 := pow_le_pow_right₀ h1k (by norm_num)
      nlinarith [sq_nonneg (1 + |(k : ℝ)|)]
    calc CJ * Real.log (2 + |(k : ℝ)|) * (16 * CM) * (1 + |(k : ℝ)|) ^ 2
        = CJ * (16 * CM) * (Real.log (2 + |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ 2) := by ring
      _ ≤ CJ * (16 * CM) * (1 + |(k : ℝ)|) ^ 4 := mul_le_mul_of_nonneg_left hlog_le2 (by positivity)
      _ ≤ CJ * (16 * CM) * ((2 + |t|) ^ 4 * (1 + |(k : ℝ) - t|) ^ 4) :=
          mul_le_mul_of_nonneg_left hpow4 (by positivity)
      _ = CJ * (16 * CM) * (2 + |t|) ^ 4 * (1 + |(k : ℝ) - t|) ^ 4 := by ring
  refine summable_of_sum_le (fun _ => norm_nonneg _) (fun s => ?_) (c := ∑' k : ℤ, (CJ * Real.log (2 + |(k : ℝ)|)) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4))
  -- Group `g ∈ s` by `k = ⌊g.val⌋ : ℤ`
  set ks : Finset ℤ := s.image (fun g => ⌊g.val⌋)
  have hgroup : ∑ g ∈ s, ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖ ≤
      ∑ k ∈ ks, (CJ * Real.log (2 + |(k : ℝ)|)) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4) := by
    have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := ks) (g := fun g => ⌊g.val⌋)
      (fun g hg => Finset.mem_image_of_mem _ hg)
      (f := fun g => ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖)
    rw [← hfib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hpt : ∀ g ∈ s.filter (fun g => ⌊g.val⌋ = k),
        ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖ ≤
          (mZero g.val : ℝ) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4) := by
      intro g hg
      have hfl : ⌊g.val⌋ = k := (Finset.mem_filter.mp hg).2
      have hg1 : (k : ℝ) ≤ g.val := hfl ▸ Int.floor_le g.val
      have hg2 : g.val < (k : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one g.val
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp]
      have hre0 : (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)).re = 0 := by
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_im]; ring
      rw [hre0, Real.exp_zero, mul_one]
      have hdist : 1 + |(k : ℝ) - t| ≤ 2 * (1 + |g.val - t|) := by
        have htri : |(k : ℝ) - t| ≤ |g.val - t| + 1 := by
          have : (k : ℝ) - t = (g.val - t) - (g.val - (k : ℝ)) := by ring
          rw [this]
          have hsub : |g.val - (k : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          linarith [abs_sub (g.val - t) (g.val - (k : ℝ))]
        linarith [abs_nonneg (g.val - t)]
      have hpow4 : (1 + |(k : ℝ) - t|) ^ 4 ≤ 16 * (1 + |g.val - t|) ^ 4 := by
        calc (1 + |(k : ℝ) - t|) ^ 4 ≤ (2 * (1 + |g.val - t|)) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hdist 4
          _ = 16 * (1 + |g.val - t|) ^ 4 := by ring
      have hMle : ‖Mfun (g.val - t)‖ ≤ 16 * CM / (1 + |(k : ℝ) - t|) ^ 4 := by
        refine (hMbd (g.val - t)).trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc CM * (1 + |(k : ℝ) - t|) ^ 4 ≤ CM * (16 * (1 + |g.val - t|) ^ 4) :=
              mul_le_mul_of_nonneg_left hpow4 hCM
          _ = 16 * CM * (1 + |g.val - t|) ^ 4 := by ring
      exact mul_le_mul_of_nonneg_left hMle (Nat.cast_nonneg _)
    calc ∑ g ∈ s.filter (fun g => ⌊g.val⌋ = k),
            ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖
        ≤ ∑ g ∈ s.filter (fun g => ⌊g.val⌋ = k), (mZero g.val : ℝ) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4) :=
          Finset.sum_le_sum hpt
      _ = (∑ g ∈ s.filter (fun g => ⌊g.val⌋ = k), (mZero g.val : ℝ)) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (CJ * Real.log (2 + |(k : ℝ)|)) * (16 * CM / (1 + |(k : ℝ) - t|) ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hfin_k := (hunit (k : ℝ)).1
          have hle_k := (hunit (k : ℝ)).2
          refine le_trans ?_ hle_k
          set Tk := (s.filter (fun g => ⌊g.val⌋ = k)).image Subtype.val ∪ hfin_k.toFinset
          rw [finsum_eq_sum_of_support_subset _ (s := Tk) (fun x hx => Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin_k.mem_toFinset.mpr hx)))]
          have hsum_img : ∑ g ∈ s.filter (fun g => ⌊g.val⌋ = k), (mZero g.val : ℝ) =
              ∑ x ∈ (s.filter (fun g => ⌊g.val⌋ = k)).image Subtype.val,
                (if (k : ℝ) ≤ x ∧ x < (k : ℝ) + 1 then (mZero x : ℝ) else 0) := by
            rw [Finset.sum_image (fun g1 _ g2 _ h => Subtype.ext h)]
            refine Finset.sum_congr rfl fun g hg => ?_
            have hfl : ⌊g.val⌋ = k := (Finset.mem_filter.mp hg).2
            have h1 : (k : ℝ) ≤ g.val := hfl ▸ Int.floor_le g.val
            have h2 : g.val < (k : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one g.val
            simp [h1, h2]
          rw [hsum_img]
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun x _ _ => by split_ifs <;> positivity
  exact hgroup.trans (hsum_int.sum_le_tsum ks fun k _ => by
    have : 0 ≤ Real.log (2 + |(k : ℝ)|) := Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])
    positivity)

set_option maxHeartbeats 400000 in
theorem explicit_formula_Pfun
    (hRH : RiemannHypothesis)
    (hF_diff : Differentiable ℂ zetaExt)
    (hWtilde_diff : Differentiable ℂ Wtilde)
    (hWtilde_decay : ∀ σ1 σ2 : ℝ, ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, σ1 ≤ s.re → s.re ≤ σ2 → ‖Wtilde s‖ ≤ C / (1 + |s.im|) ^ k)
    (hMfun_eq : ∀ v : ℝ, Mfun v = Wtilde (Complex.I * (v : ℂ)))
    (hmellin : ∀ (c : ℝ) {x : ℝ}, 0 < x →
      (Wfun x : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ, Wtilde ((c : ℂ) + Complex.I * (τ : ℂ)) * (x : ℂ) ^ (-((c : ℂ) + Complex.I * (τ : ℂ))))
    (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hneg_half : ∀ τ : ℝ, ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C2 * Real.log (2 + |τ|))
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJ : ∀ t : ℝ,
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor zetaExt (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) 3) u : ℝ)) ≤
        CJ * Real.log (2 + |t|))
    (CH : ℝ) (hCH : 0 ≤ CH)
    (hgood : ∀ k : ℤ, 2 ≤ |k| →
      ∃ H : ℝ, (k : ℝ) ≤ H ∧ H ≤ (k : ℝ) + 1 ∧
        (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
          riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤
            CH * (Real.log (2 + |H|)) ^ 2))
    (hrect_res : ∀ {U : Set ℂ}, IsOpen U → ∀ {F W : ℂ → ℂ} {a b c d : ℝ},
      a < b → c < d → Set.Icc a b ×ℂ Set.Icc c d ⊆ U →
      MeromorphicOn F U → (∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤) →
      DifferentiableOn ℂ W U →
      (∀ z ∈ Set.Icc a b ×ℂ Set.Icc c d,
        (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → AnalyticAt ℂ F z ∧ F z ≠ 0) →
      rectIntegral (fun z => logDeriv F z * W z) a b c d =
        2 * Real.pi * Complex.I *
          ∑ᶠ ρ : ℂ, if ρ ∈ Set.Ioo a b ×ℂ Set.Ioo c d then (MeromorphicOn.divisor F U ρ : ℂ) * W ρ else 0)
    {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    Pfun X t =
      Gweight X t 1 -
      (∑' g : {g : ℝ // riemannZeta (zCrit g) = 0},
        (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
      Eleft X t := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  -- Choose good heights `Hpos n ∈ [n+2, n+3]` and `Hneg n ∈ [-(n+3), -(n+2)]`
  have hpos_ex : ∀ n : ℕ, ∃ H : ℝ, ((n : ℝ) + 2) ≤ H ∧ H ≤ (n : ℝ) + 3 ∧
      (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
        riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
        ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤ CH * (Real.log (2 + |H|)) ^ 2) := by
    intro n
    obtain ⟨H, h1, h2, h3⟩ := hgood ((n : ℤ) + 2) (by rw [abs_of_nonneg (by omega)]; omega)
    exact ⟨H, by exact_mod_cast h1, by push_cast at h2; linarith, h3⟩
  have hneg_ex : ∀ n : ℕ, ∃ H : ℝ, -((n : ℝ) + 3) ≤ H ∧ H ≤ -((n : ℝ) + 2) ∧
      (∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
        riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ)) ≠ 0 ∧
        ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H : ℂ))‖ ≤ CH * (Real.log (2 + |H|)) ^ 2) := by
    intro n
    obtain ⟨H, h1, h2, h3⟩ := hgood (-((n : ℤ) + 3)) (by rw [abs_neg, abs_of_nonneg (by omega)]; omega)
    exact ⟨H, by push_cast at h1; linarith, by push_cast at h2; linarith, h3⟩
  choose Hpos hHpos_lo hHpos_hi hHpos_prop using hpos_ex
  choose Hneg hHneg_lo hHneg_hi hHneg_prop using hneg_ex
  have hHpos_top : Tendsto Hpos atTop atTop :=
    tendsto_atTop_mono hHpos_lo (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hHneg_bot : Tendsto Hneg atTop atBot :=
    tendsto_atBot_mono hHneg_hi (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  -- For each `n`, apply `hrect_res` to `F = riemannZeta`, `W = Gweight X t` on `[-1/2, 5/2] × [Hneg n, Hpos n]`
  have hG_diff : Differentiable ℂ (Gweight X t) := by
    unfold Gweight
    have hlin : Differentiable ℂ (fun w : ℂ => w - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) :=
      (differentiable_id.sub (differentiable_const _)).sub (differentiable_const _)
    exact (hWtilde_diff.comp hlin).mul (Complex.differentiable_exp.comp (hlin.mul (differentiable_const _)))
  have hrect_n : ∀ n : ℕ,
      (1 / (2 * Real.pi * Complex.I)) *
        rectIntegral (fun w => logDeriv riemannZeta w * Gweight X t w) (-(1 / 2)) (5 / 2) (Hneg n) (Hpos n) =
      -Gweight X t 1 +
        ∑ᶠ g : {g : ℝ // riemannZeta (zCrit g) = 0},
          if Hneg n < g.val ∧ g.val < Hpos n then
            (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)
          else 0 := by
    intro n
    have hcd : Hneg n < Hpos n := by linarith [hHneg_hi n, hHpos_lo n, Nat.cast_nonneg (α := ℝ) n]
    have hbdy : ∀ z ∈ Set.Icc (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Icc (Hneg n) (Hpos n),
        (z.re = -(1 / 2) ∨ z.re = 5 / 2 ∨ z.im = Hneg n ∨ z.im = Hpos n) →
        AnalyticAt ℂ riemannZeta z ∧ riemannZeta z ≠ 0 := by
      intro z hz hb
      have hz1 : z ≠ 1 := by
        intro h; rw [h] at hb
        rcases hb with h1 | h1 | h1 | h1
        · simp at h1; norm_num at h1
        · simp at h1; norm_num at h1
        · simp at h1; linarith [hHneg_hi n, Nat.cast_nonneg (α := ℝ) n]
        · simp at h1; linarith [hHpos_lo n, Nat.cast_nonneg (α := ℝ) n]
      refine ⟨differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hz1), ?_⟩
      rcases hb with h1 | h1 | h1 | h1
      · exact riemannZeta_ne_zero_of_neg_half_le_re_nonpos (by linarith) (by linarith)
      · exact riemannZeta_ne_zero_of_one_le_re (by linarith)
      · have hEq : z = ((z.re : ℂ) + Complex.I * (Hneg n : ℂ)) := by apply Complex.ext <;> simp [h1]
        rw [hEq]; exact (hHneg_prop n z.re hz.1.1 hz.1.2).1
      · have hEq : z = ((z.re : ℂ) + Complex.I * (Hpos n : ℂ)) := by apply Complex.ext <;> simp [h1]
        rw [hEq]; exact (hHpos_prop n z.re hz.1.1 hz.1.2).1
    have hres := hrect_res isOpen_univ (by norm_num) hcd (Set.subset_univ _)
      (riemannZeta_meromorphicOn hF_diff) (fun z _ => meromorphicOrderAt_riemannZeta_ne_top hF_diff z)
      hG_diff.differentiableOn hbdy
    rw [hres]
    have h2piI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
    rw [one_div, inv_mul_cancel_left₀ h2piI]
    -- Identify the residue sum on `(-1/2, 5/2) × (Hneg n, Hpos n)` as `-Gweight X t 1 + zero sum`
    have hfin_box : (Function.support fun ρ : ℂ =>
        if ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) then
          (MeromorphicOn.divisor riemannZeta Set.univ ρ : ℂ) * Gweight X t ρ else 0).Finite := by
      have hK : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Icc (Hneg n) (Hpos n)) :=
        isCompact_Icc.reProdIm isCompact_Icc
      have hmero_K : MeromorphicOn riemannZeta (Set.Icc (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Icc (Hneg n) (Hpos n)) :=
        fun z _ => riemannZeta_meromorphicOn hF_diff z (Set.mem_univ z)
      refine ((MeromorphicOn.divisor riemannZeta (Set.Icc (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Icc (Hneg n) (Hpos n))).finiteSupport hK).subset
        fun ρ hρ => ?_
      rw [Function.mem_support] at hρ ⊢
      split_ifs at hρ with hmem
      · have hρK : ρ ∈ Set.Icc (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Icc (Hneg n) (Hpos n) :=
          ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩
        rw [MeromorphicOn.divisor_apply hmero_K hρK, ← MeromorphicOn.divisor_apply (riemannZeta_meromorphicOn hF_diff) (Set.mem_univ ρ)]
        intro h0; simp [h0] at hρ
      · exact (hρ rfl).elim
    have h1_in : (1 : ℂ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) :=
      ⟨⟨by simp; norm_num, by simp; norm_num⟩,
       ⟨by simp; linarith [hHneg_hi n, Nat.cast_nonneg (α := ℝ) n],
        by simp; linarith [hHpos_lo n, Nat.cast_nonneg (α := ℝ) n]⟩⟩
    set Sbox : Finset ℂ := insert 1 hfin_box.toFinset
    rw [finsum_eq_sum_of_support_subset _ (s := Sbox) (fun ρ hρ => Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin_box.mem_toFinset.mpr hρ)))]
    have hSsplit : ∑ ρ ∈ Sbox, (if ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) then
          (MeromorphicOn.divisor riemannZeta Set.univ ρ : ℂ) * Gweight X t ρ else 0) =
        -Gweight X t 1 + ∑ ρ ∈ Sbox.erase 1, (if ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) then
          (MeromorphicOn.divisor riemannZeta Set.univ ρ : ℂ) * Gweight X t ρ else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 1 _)]
      congr 1
      simp only [h1_in, ↓reduceIte, divisor_riemannZeta_one hF_diff]; norm_num
    rw [hSsplit]; congr 1
    -- Biject nonzero terms of `Sbox.erase 1` with `{g : ℝ // riemannZeta (zCrit g) = 0}` having `Hneg n < g < Hpos n`
    set Szero : Finset ℂ := (Sbox.erase 1).filter (fun ρ => ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) ∧ riemannZeta ρ = 0)
    have hSbox_eq : ∑ ρ ∈ Sbox.erase 1, (if ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) then
          (MeromorphicOn.divisor riemannZeta Set.univ ρ : ℂ) * Gweight X t ρ else 0) =
        ∑ ρ ∈ Szero, (MeromorphicOn.divisor riemannZeta Set.univ ρ : ℂ) * Gweight X t ρ := by
      rw [← Finset.sum_subset (Finset.filter_subset
        (fun ρ => ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) ∧ riemannZeta ρ = 0)
        (Sbox.erase 1))]
      · exact Finset.sum_congr rfl fun ρ hρ => by
          have hm : ρ ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) :=
            (Finset.mem_filter.mp hρ).2.1
          simp only [hm, ↓reduceIte]
      · intro ρ hρ hnot
        split_ifs with hmem
        · have hne1 : ρ ≠ 1 := (Finset.mem_erase.mp hρ).1
          have hne0 : riemannZeta ρ ≠ 0 := fun h0 => hnot (Finset.mem_filter.mpr ⟨hρ, hmem, h0⟩)
          have hord0 : analyticOrderNatAt riemannZeta ρ = 0 := by
            have hza := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)
            simp [analyticOrderNatAt, hza.analyticOrderAt_eq_zero.mpr hne0]
          rw [divisor_riemannZeta_of_ne_one hF_diff hne1, hord0]; simp
        · rfl
    rw [hSbox_eq]
    have hSzero_crit : ∀ ρ ∈ Szero, zCrit ρ.im = ρ ∧ riemannZeta (zCrit ρ.im) = 0 := by
      intro ρ hρ
      have hm := (Finset.mem_filter.mp hρ).2
      have hre : ρ.re = 1 / 2 := zero_re_eq_half_of_RH hRH hm.1.1.1.le hm.2
      have heq : zCrit ρ.im = ρ := by apply Complex.ext <;> simp [zCrit, hre]
      exact ⟨heq, heq.symm ▸ hm.2⟩
    let Ssub : Finset {g : ℝ // riemannZeta (zCrit g) = 0} :=
      Szero.attach.image (fun ρ => ⟨ρ.1.im, (hSzero_crit ρ.1 ρ.2).2⟩)
    symm
    rw [finsum_eq_sum_of_support_subset _ (s := Ssub)]
    · rw [Finset.sum_image (by
        rintro ⟨ρ1, h1⟩ _ ⟨ρ2, h2⟩ _ heq
        have him : ρ1.im = ρ2.im := congrArg Subtype.val heq
        apply Subtype.ext
        change ρ1 = ρ2
        rw [← (hSzero_crit ρ1 h1).1, ← (hSzero_crit ρ2 h2).1, him])]
      rw [← Finset.sum_attach Szero]
      refine Finset.sum_congr rfl fun ⟨ρ, hρ⟩ _ => ?_
      have hm := (Finset.mem_filter.mp hρ).2
      have hne1 : ρ ≠ 1 := (Finset.mem_erase.mp (Finset.mem_filter.mp hρ).1).1
      have hcrit := (hSzero_crit ρ hρ).1
      simp only [hm.1.2.1, hm.1.2.2, and_self, ↓reduceIte, divisor_riemannZeta_of_ne_one hF_diff hne1]
      dsimp only [mZero, Gweight]
      rw [hcrit, hMfun_eq (ρ.im - t)]
      have harg : ρ - (1 / 2 : ℂ) - Complex.I * (t : ℂ) = Complex.I * ((ρ.im - t : ℝ) : ℂ) := by
        apply Complex.ext
        · have hre : ρ.re = 1 / 2 := by rw [← hcrit]; simp [zCrit]
          simp [hre]
        · simp
      rw [harg]; push_cast; ring
    · intro g hg
      rw [Function.mem_support] at hg
      split_ifs at hg with hbox
      · have hne0 : mZero g.val ≠ 0 := by intro h0; simp [h0] at hg
        have hne1 : zCrit g.val ≠ 1 := by intro h; have := congrArg Complex.re h; simp [zCrit] at this
        have hmem_box : zCrit g.val ∈ Set.Ioo (-(1 / 2 : ℝ)) (5 / 2) ×ℂ Set.Ioo (Hneg n) (Hpos n) :=
          ⟨⟨by simp only [zCrit, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]; norm_num,
            by simp only [zCrit, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]; norm_num⟩,
           ⟨by simpa [zCrit] using hbox.1, by simpa [zCrit] using hbox.2⟩⟩
        have hsupp : zCrit g.val ∈ Sbox := by
          apply Finset.mem_insert_of_mem
          rw [Set.Finite.mem_toFinset, Function.mem_support]
          simp only [hmem_box, ↓reduceIte, divisor_riemannZeta_of_ne_one hF_diff hne1]
          intro h0
          have harg : zCrit g.val - (1 / 2 : ℂ) - Complex.I * (t : ℂ) = Complex.I * ((g.val - t : ℝ) : ℂ) := by
            dsimp only [zCrit]; push_cast; ring
          dsimp only [Gweight] at h0
          rw [harg, ← hMfun_eq] at h0
          apply hg
          have : (mZero g.val : ℂ) * Mfun (g.val - t) *
              Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) = 0 := by
            simpa [mZero] using h0
          linear_combination this
        have hmem_Sz : zCrit g.val ∈ Szero :=
          Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne1, hsupp⟩, hmem_box, g.2⟩
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨zCrit g.val, hmem_Sz⟩, Finset.mem_attach _ _, ?_⟩)
        apply Subtype.ext; simp [zCrit]
      · exact (hg rfl).elim
  -- Step 2: Take limit as `n → ∞` of both sides!
  -- Horizontal sides → 0
  obtain ⟨CWh, hCWh, hWh_dec⟩ := hWtilde_decay (-1) 2 4
  have hhoriz_lim : ∀ (H : ℕ → ℝ),
      Tendsto (fun n => |H n|) atTop atTop →
      (∀ n, ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 5 / 2 →
        ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H n : ℂ))‖ ≤ CH * (Real.log (2 + |H n|)) ^ 2) →
      Tendsto (fun n => ∫ σ in (-(1 / 2 : ℝ))..(5 / 2),
        logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H n : ℂ)) *
          Gweight X t ((σ : ℂ) + Complex.I * (H n : ℂ))) atTop (𝓝 0) := by
    intro H hHabs hHbd
    refine squeeze_zero_norm' ?_ (show Tendsto (fun n : ℕ =>
        3 * (CH * CWh * (X : ℝ) ^ 2) * (1 / (1 + |H n - t|) ^ 2)) atTop (𝓝 0) by
      have hht : Tendsto (fun n => |H n - t|) atTop atTop := by
        refine tendsto_atTop_mono (fun n => ?_) (hHabs.atTop_add (tendsto_const_nhds (x := -|t|)))
        have := abs_sub_abs_le_abs_sub (H n) t; linarith
      have hsq : Tendsto (fun n => (1 + |H n - t|) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (tendsto_const_nhds.add_atTop hht)
      have h0 : Tendsto (fun n : ℕ => 3 * (CH * CWh * (X : ℝ) ^ 2) * (1 / (1 + |H n - t|) ^ 2)) atTop
          (𝓝 (3 * (CH * CWh * (X : ℝ) ^ 2) * 0)) :=
        (tendsto_const_nhds.div_atTop hsq).const_mul (3 * (CH * CWh * (X : ℝ) ^ 2))
      simpa using h0)
    filter_upwards [hHabs.eventually_ge_atTop (2 * |t| + 4)] with n hn
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (CH * CWh * (X : ℝ) ^ 2) * (1 / (1 + |H n - t|) ^ 2))
      (f := fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H n : ℂ)) *
        Gweight X t ((σ : ℂ) + Complex.I * (H n : ℂ))) (a := -(1 / 2 : ℝ)) (b := 5 / 2)
      (fun σ hσ => by
        rw [Set.uIoc_of_le (by norm_num)] at hσ
        dsimp only [Gweight]
        rw [norm_mul, norm_mul, Complex.norm_exp]
        have hre_s : ((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).re = σ - 1 / 2 := by simp
        have him_s : ((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).im = H n - t := by simp
        have hre_e : (((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)).re =
            (σ - 1 / 2) * Real.log X := by
          rw [Complex.mul_re, hre_s, Complex.ofReal_re, Complex.ofReal_im]; ring
        rw [hre_e]
        have hexp_le : Real.exp ((σ - 1 / 2) * Real.log X) ≤ (X : ℝ) ^ 2 := by
          have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
          have hle : (σ - 1 / 2) * Real.log X ≤ 2 * Real.log X := by nlinarith [hσ.2]
          calc Real.exp ((σ - 1 / 2) * Real.log X) ≤ Real.exp (2 * Real.log X) := Real.exp_le_exp.mpr hle
            _ = (X : ℝ) ^ 2 := by rw [show 2 * Real.log X = Real.log ((X : ℝ) ^ 2) by rw [Real.log_pow]; ring, Real.exp_log (by positivity)]
        have hW := hWh_dec ((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))
          (by rw [hre_s]; linarith [hσ.1]) (by rw [hre_s]; linarith [hσ.2])
        rw [him_s] at hW
        have hlog_le : Real.log (2 + |H n|) ≤ 1 + |H n - t| := by
          have h1 : |H n| ≤ |H n - t| + |t| := by
            have := abs_add_le (H n - t) t; simpa [sub_add_cancel] using this
          have h2 : 2 + |H n| ≤ 2 * (1 + |H n - t|) := by
            have h3 : |t| ≤ |H n - t| := by
              have := abs_sub_abs_le_abs_sub (H n) t; linarith
            linarith
          have h3 : Real.log (2 + |H n|) ≤ 2 + |H n| - 1 := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg (H n)])
          calc Real.log (2 + |H n|) ≤ Real.log (2 * (1 + |H n - t|)) :=
                Real.log_le_log (by linarith [abs_nonneg (H n)]) h2
            _ = Real.log 2 + Real.log (1 + |H n - t|) := Real.log_mul (by norm_num) (by linarith [abs_nonneg (H n - t)])
            _ ≤ 1 + |H n - t| := by
                have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
                have hl3 : Real.log (1 + |H n - t|) ≤ |H n - t| := by
                  linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg (H n - t)] : 0 < 1 + |H n - t|)]
                linarith
        have hlog_sq : (Real.log (2 + |H n|)) ^ 2 ≤ (1 + |H n - t|) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith [abs_nonneg (H n)])) hlog_le 2
        have hld := hHbd n σ hσ.1.le hσ.2
        calc ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H n : ℂ))‖ *
              (‖Wtilde ((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
                Real.exp ((σ - 1 / 2) * Real.log X))
            ≤ (CH * (1 + |H n - t|) ^ 2) * ((CWh / (1 + |H n - t|) ^ 4) * (X : ℝ) ^ 2) := by
              have h1 : ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * (H n : ℂ))‖ ≤ CH * (1 + |H n - t|) ^ 2 :=
                hld.trans (mul_le_mul_of_nonneg_left hlog_sq hCH)
              have h2 : ‖Wtilde ((σ : ℂ) + Complex.I * (H n : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ *
                  Real.exp ((σ - 1 / 2) * Real.log X) ≤ (CWh / (1 + |H n - t|) ^ 4) * (X : ℝ) ^ 2 :=
                mul_le_mul hW hexp_le (Real.exp_pos _).le (by positivity)
              exact mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (CH * CWh * (X : ℝ) ^ 2) * (1 / (1 + |H n - t|) ^ 2) := by
              have hp : (1 + |H n - t|) ≠ 0 := by linarith [abs_nonneg (H n - t)]
              field_simp [hp])
    have hab : |(5 / 2 : ℝ) - -(1 / 2 : ℝ)| = 3 := by norm_num
    rw [hab] at hnorm
    linarith
  have htop_lim := hhoriz_lim Hpos
    (tendsto_atTop_mono (fun n => le_abs_self (Hpos n)) hHpos_top)
    (fun n σ h1 h2 => (hHpos_prop n σ h1 h2).2)
  have hbot_lim := hhoriz_lim Hneg
    (tendsto_atTop_mono (fun n => neg_le_abs (Hneg n)) (tendsto_neg_atBot_atTop.comp hHneg_bot))
    (fun n σ h1 h2 => (hHneg_prop n σ h1 h2).2)
  -- Right vertical side → `-Pfun X t` (integrable by LSeries bound + Wtilde decay)
  have hint_right : Integrable (fun y : ℝ =>
      logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) := by
    obtain ⟨CW, hCW, hWdec⟩ := hWtilde_decay 2 2 2
    have hld_bd : ∀ y : ℝ, ‖logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))‖ ≤
        ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
      intro y
      have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := (5 / 2 : ℂ) + Complex.I * (y : ℂ)) (by simp; norm_num)
      have hld_eq : logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) =
          -LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) := by
        rw [logDeriv_apply, hL]; ring
      rw [hld_eq, norm_neg]
      unfold LSeries
      have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        Real.summable_one_div_nat_rpow.mpr (by norm_num)
      refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum ?_ ?_ hsum)
      · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum
        by_cases hn : n = 0
        · subst hn; simp [LSeries.term]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
          rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
          have hre : ((5 / 2 : ℂ) + Complex.I * (y : ℂ)).re = 5 / 2 := by simp
          rw [hre]
          have hv : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn_pos])
          calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)
              ≤ (n : ℝ) / (n : ℝ) ^ (5 / 2 : ℝ) := by gcongr
            _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
                have h1 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
                  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
                rw [h1]; field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos (3 / 2)).ne']
      · intro n
        by_cases hn : n = 0
        · subst hn; simp [LSeries.term]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
          rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
          have hre : ((5 / 2 : ℂ) + Complex.I * (y : ℂ)).re = 5 / 2 := by simp
          rw [hre]
          have hv : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn_pos])
          calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)
              ≤ (n : ℝ) / (n : ℝ) ^ (5 / 2 : ℝ) := by gcongr
            _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
                have h1 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
                  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
                rw [h1]; field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos (3 / 2)).ne']
      · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum
        by_cases hn : n = 0
        · subst hn; simp [LSeries.term]
        · have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
          rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
          have hre : ((5 / 2 : ℂ) + Complex.I * (y : ℂ)).re = 5 / 2 := by simp
          rw [hre]
          have hv : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn_pos])
          calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)
              ≤ (n : ℝ) / (n : ℝ) ^ (5 / 2 : ℝ) := by gcongr
            _ = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
                have h1 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
                  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hn_pos, Real.rpow_one]
                rw [h1]; field_simp [hn_pos.ne', (Real.rpow_pos_of_pos hn_pos (3 / 2)).ne']
    set CL : ℝ := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
    have hCL : 0 ≤ CL := tsum_nonneg fun n => by positivity
    have hdom : Integrable (fun y : ℝ => (CL * CW * (X : ℝ) ^ 2) / (1 + |y - t|) ^ 2) :=
      (integrable_div_one_add_abs_pow' (CL * CW * (X : ℝ) ^ 2) 2 le_rfl).comp_sub_right t
    have hcont : Continuous (fun y : ℝ =>
        logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
          Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) := by
      have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := differentiableOn_riemannZeta.analyticOnNhd isOpen_ne
      have hpath : Continuous (fun y : ℝ => (5 / 2 : ℂ) + Complex.I * (y : ℂ)) :=
        continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      have hne1 : ∀ y : ℝ, (5 / 2 : ℂ) + Complex.I * (y : ℂ) ≠ 1 := fun y h => by
        have := congrArg Complex.re h; simp at this; norm_num at this
      have hld_c : Continuous (fun y : ℝ => logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) :=
        (han.deriv.continuousOn.comp_continuous hpath hne1).div
          (han.continuousOn.comp_continuous hpath hne1) fun y => riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
      exact hld_c.mul (hG_diff.continuous.comp hpath)
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [Gweight]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre_e : (((5 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)).re =
        2 * Real.log X := by
      have hre_s : ((5 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).re = 2 := by simp; norm_num
      rw [Complex.mul_re, hre_s, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hre_e, show 2 * Real.log X = Real.log ((X : ℝ) ^ 2) by rw [Real.log_pow]; ring,
      Real.exp_log (by positivity)]
    have hW := hWdec ((5 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))
      (by simp; norm_num) (by simp; norm_num)
    have him : ((5 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).im = y - t := by simp
    rw [him] at hW
    calc ‖logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))‖ *
          (‖Wtilde ((5 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ * (X : ℝ) ^ 2)
        ≤ CL * ((CW / (1 + |y - t|) ^ 2) * (X : ℝ) ^ 2) :=
          mul_le_mul (hld_bd y) (mul_le_mul_of_nonneg_right hW (by positivity)) (by positivity) hCL
      _ = (CL * CW * (X : ℝ) ^ 2) / (1 + |y - t|) ^ 2 := by ring
  -- Left vertical side is also integrable!
  have hint_left : Integrable (fun y : ℝ =>
      logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))) := by
    obtain ⟨CW, hCW, hdec⟩ := hWtilde_decay (-1) (-1) 4
    have hcont : Continuous (fun y : ℝ =>
        logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
          Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))) := by
      have han : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := differentiableOn_riemannZeta.analyticOnNhd isOpen_ne
      have hpath : Continuous (fun y : ℝ => -(1 / 2 : ℂ) + Complex.I * (y : ℂ)) :=
        continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      have hne1 : ∀ y : ℝ, -(1 / 2 : ℂ) + Complex.I * (y : ℂ) ≠ 1 := fun y h => by
        have := congrArg Complex.re h; simp at this; norm_num at this
      have hld_c : Continuous (fun y : ℝ => logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))) :=
        (han.deriv.continuousOn.comp_continuous hpath hne1).div
          (han.continuousOn.comp_continuous hpath hne1) fun y =>
            riemannZeta_ne_zero_of_neg_half_le_re_nonpos (by simp) (by simp)
      exact hld_c.mul (hG_diff.continuous.comp hpath)
    have hdom := (integrable_div_one_add_abs_pow' (C2 * CW * (X : ℝ)⁻¹ * (4 * (2 + |t|))) 2 le_rfl).comp_sub_right t
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [Gweight]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre_s : (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).re = -1 := by simp; norm_num
    have him_s : (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)).im = y - t := by simp
    have hre_e : ((-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ)).re =
        -Real.log X := by
      rw [Complex.mul_re, hre_s, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hre_e, Real.exp_neg, Real.exp_log hXpos]
    have hW := hdec (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))
      (by linarith [hre_s]) (by linarith [hre_s])
    rw [him_s] at hW
    have hlog_y : Real.log (2 + |y|) ≤ 4 * (2 + |t|) * (1 + |y - t|) ^ 2 := by
      have h1 : Real.log (2 + |y|) ≤ 2 + |y| := by linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg y] : 0 < 2 + |y|)]
      have h2 : |y| ≤ |t| + |y - t| := by have := abs_add_le t (y - t); simpa [add_sub_cancel] using this
      have h1y : 1 ≤ 1 + |y - t| := by linarith [abs_nonneg (y - t)]
      have hsq : 1 + |y - t| ≤ (1 + |y - t|) ^ 2 := by nlinarith
      nlinarith [abs_nonneg t, abs_nonneg (y - t)]
    calc ‖logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))‖ *
          (‖Wtilde (-(1 / 2 : ℂ) + Complex.I * (y : ℂ) - (1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ * (X : ℝ)⁻¹)
        ≤ (C2 * (4 * (2 + |t|) * (1 + |y - t|) ^ 2)) * ((CW / (1 + |y - t|) ^ 4) * (X : ℝ)⁻¹) :=
          mul_le_mul ((hneg_half y).trans (mul_le_mul_of_nonneg_left hlog_y hC2))
            (mul_le_mul_of_nonneg_right hW (by positivity)) (by positivity) (by positivity)
      _ = (C2 * CW * (X : ℝ)⁻¹ * (4 * (2 + |t|))) / (1 + |y - t|) ^ 2 := by
          have hp : 1 + |y - t| ≠ 0 := by linarith [abs_nonneg (y - t)]
          field_simp [hp]
  have hright_lim : Tendsto (fun n => ∫ y in Hneg n..Hpos n,
      logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) atTop
      (𝓝 (∫ y : ℝ, logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_right hHneg_bot hHpos_top
  have hleft_lim : Tendsto (fun n => ∫ y in Hneg n..Hpos n,
      logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))) atTop
      (𝓝 (∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
        Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_left hHneg_bot hHpos_top
  -- LHS limit: `-Pfun X t - Eleft X t`
  have hLHS_lim : Tendsto (fun n => (1 / (2 * Real.pi * Complex.I)) *
      rectIntegral (fun w => logDeriv riemannZeta w * Gweight X t w) (-(1 / 2)) (5 / 2) (Hneg n) (Hpos n))
      atTop (𝓝 (-Pfun X t - Eleft X t)) := by
    have hcomb := (((hbot_lim.sub htop_lim).add (hright_lim.const_mul Complex.I)).sub
      (hleft_lim.const_mul Complex.I)).const_mul (1 / (2 * (Real.pi : ℂ) * Complex.I))
    have hlim_eq : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (0 - 0 + Complex.I * (∫ y : ℝ, logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
            Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I * (∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
            Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)))) =
        -Pfun X t - Eleft X t := by
      rw [Pfun_eq_integral_logDeriv_zeta hWtilde_diff hWtilde_decay hmellin hX t]
      unfold Eleft
      have hneg_int : ∫ y : ℝ, (-logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) *
          Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) =
          -(∫ y : ℝ, logDeriv riemannZeta ((5 / 2 : ℂ) + Complex.I * (y : ℂ)) *
            Gweight X t ((5 / 2 : ℂ) + Complex.I * (y : ℂ))) := by
        rw [← MeasureTheory.integral_neg]; congr 1; funext y; ring
      rw [hneg_int]
      field_simp [Real.pi_pos.ne', Complex.I_ne_zero]
      ring
    rw [hlim_eq] at hcomb
    refine hcomb.congr fun n => ?_
    unfold rectIntegral
    have hneg_half_c : ((-(1 / 2 : ℝ) : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; ring
    have hfive_half_c : (((5 / 2 : ℝ) : ℝ) : ℂ) = (5 / 2 : ℂ) := by push_cast; ring
    simp only [hneg_half_c, hfive_half_c]
  -- RHS limit: `-Gweight X t 1 + ∑' g, ...`
  have hsumm := summable_zero_explicit_term hF_diff hWtilde_decay hMfun_eq CJ hCJ hJ X t
  let Zterm : {g : ℝ // riemannZeta (zCrit g) = 0} → ℂ := fun g =>
    (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)
  have hzero_lim : Tendsto (fun n : ℕ =>
      ∑ᶠ g : {g : ℝ // riemannZeta (zCrit g) = 0},
        if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0)
      atTop (𝓝 (∑' g : {g : ℝ // riemannZeta (zCrit g) = 0}, Zterm g)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hhs : Tendsto (fun s : Finset {g : ℝ // riemannZeta (zCrit g) = 0} => ∑ b ∈ s, Zterm b)
        atTop (𝓝 (∑' g : {g : ℝ // riemannZeta (zCrit g) = 0}, Zterm g)) := hsumm.hasSum
    obtain ⟨s0, hs0⟩ := Metric.tendsto_atTop.mp hhs ε hε
    -- Choose `N` so all `g ∈ s0` lie in `(Hneg N, Hpos N)`
    have hex_N : ∃ N : ℕ, ∀ n ≥ N, ∀ g ∈ s0, Hneg n < g.val ∧ g.val < Hpos n := by
      have hbd : ∃ M : ℝ, ∀ g ∈ s0, |g.val| < M := by
        by_cases hemp : s0.Nonempty
        · refine ⟨(s0.image (fun g => |g.val|)).max' (hemp.image _) + 1, fun g hg => ?_⟩
          have := Finset.le_max' (s0.image (fun g => |g.val|)) |g.val| (Finset.mem_image_of_mem _ hg)
          linarith
        · refine ⟨1, fun g hg => (hemp ⟨g, hg⟩).elim⟩
      obtain ⟨M, hM⟩ := hbd
      obtain ⟨N, hN⟩ := exists_nat_gt (max M 0)
      refine ⟨N, fun n hn g hg => ?_⟩
      have hMn : M < (n : ℝ) := lt_of_le_of_lt (le_max_left M 0) (lt_of_lt_of_le hN (by exact_mod_cast hn))
      have habs := abs_lt.mp (hM g hg)
      constructor
      · linarith [hHneg_hi n, habs.1]
      · linarith [hHpos_lo n, habs.2]
    obtain ⟨N, hN⟩ := hex_N
    refine ⟨N, fun n hn => ?_⟩
    -- The support of `if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0` is finite (covered by unit intervals)
    have hfin_n : (Function.support fun g : {g : ℝ // riemannZeta (zCrit g) = 0} =>
        if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0).Finite := by
      have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (Hneg n) (Hpos n)) := isCompact_Icc.reProdIm isCompact_Icc
      have hF_an : AnalyticOnNhd ℂ zetaExt Set.univ := hF_diff.differentiableOn.analyticOnNhd isOpen_univ
      have hfin_K : (MeromorphicOn.divisor zetaExt (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (Hneg n) (Hpos n))).support.Finite :=
        (MeromorphicOn.divisor zetaExt _).finiteSupport hK
      have hinj : Function.Injective (fun g : {g : ℝ // riemannZeta (zCrit g) = 0} => zCrit g.val) :=
        fun g1 g2 h => Subtype.ext (by simpa [zCrit] using congrArg Complex.im h)
      refine hfin_K.preimage hinj.injOn |>.subset fun g hg => ?_
      rw [Function.mem_support] at hg
      split_ifs at hg with hbox
      · have hne0 : mZero g.val ≠ 0 := by intro h0; simp [Zterm, h0] at hg
        have hne1 : zCrit g.val ≠ 1 := by intro h; have := congrArg Complex.re h; simp [zCrit] at this
        have hmemK : zCrit g.val ∈ Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (Hneg n) (Hpos n) :=
          ⟨⟨by simp only [zCrit, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]; norm_num,
            by simp only [zCrit, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]; norm_num⟩,
           ⟨by simpa [zCrit] using hbox.1.le, by simpa [zCrit] using hbox.2.le⟩⟩
        rw [Set.mem_preimage, Function.mem_support,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (hF_an.mono (Set.subset_univ _)) hmemK]
        have hF_ntop : analyticOrderAt zetaExt (zCrit g.val) ≠ ⊤ := by
          intro htop
          have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hF_an
            isPreconnected_univ (Set.mem_univ (zCrit g.val)) (analyticOrderAt_eq_top.mp htop)
          have h1 := heq (Set.mem_univ 1); simp [zetaExt] at h1
        have hord_eq : analyticOrderNatAt zetaExt (zCrit g.val) = mZero g.val := by
          have hev : zetaExt =ᶠ[𝓝 (zCrit g.val)] fun w => (w - 1) * riemannZeta w := by
            filter_upwards [isOpen_ne.mem_nhds hne1] with w hw; simp [zetaExt, hw]
          have hza := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)
          have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) (zCrit g.val) := analyticAt_id.sub analyticAt_const
          have h1 : analyticOrderAt zetaExt (zCrit g.val) = analyticOrderAt ((fun w : ℂ => w - 1) * riemannZeta) (zCrit g.val) :=
            analyticOrderAt_congr hev
          rw [analyticOrderAt_mul hlin hza, hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hne1), zero_add] at h1
          simp only [mZero, analyticOrderNatAt, h1]
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hF_ntop
        have hnat : analyticOrderNatAt zetaExt (zCrit g.val) = k := by simp [analyticOrderNatAt, ← hk]
        rw [← hk]
        change (k : ℤ) ≠ 0
        rw [← hnat, hord_eq]; exact_mod_cast hne0
      · exact (hg rfl).elim
    set sn : Finset {g : ℝ // riemannZeta (zCrit g) = 0} := s0 ∪ hfin_n.toFinset
    have hsub : s0 ⊆ sn := Finset.subset_union_left
    have heq_sn : (∑ᶠ g : {g : ℝ // riemannZeta (zCrit g) = 0},
        if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0) =
        ∑ g ∈ sn, Zterm g := by
      rw [finsum_eq_sum_of_support_subset _ (s := sn) (fun g hg => Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin_n.mem_toFinset.mpr hg)))]
      refine Finset.sum_congr rfl fun g hg => ?_
      rcases Finset.mem_union.mp hg with hg0 | hgn
      · simp [hN n hn g hg0]
      · have hsup := hfin_n.mem_toFinset.mp hgn
        rw [Function.mem_support] at hsup
        split_ifs at hsup ⊢ with hc
        · rfl
        · exact (hsup rfl).elim
    rw [heq_sn]
    exact hs0 sn hsub
  have hRHS_lim : Tendsto (fun n => -Gweight X t 1 +
      ∑ᶠ g : {g : ℝ // riemannZeta (zCrit g) = 0},
        if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0)
      atTop (𝓝 (-Gweight X t 1 + ∑' g : {g : ℝ // riemannZeta (zCrit g) = 0}, Zterm g)) :=
    tendsto_const_nhds.add hzero_lim
  have heq_seq : (fun n => (1 / (2 * Real.pi * Complex.I)) *
      rectIntegral (fun w => logDeriv riemannZeta w * Gweight X t w) (-(1 / 2)) (5 / 2) (Hneg n) (Hpos n)) =
      (fun n => -Gweight X t 1 +
        ∑ᶠ g : {g : ℝ // riemannZeta (zCrit g) = 0},
          if Hneg n < g.val ∧ g.val < Hpos n then Zterm g else 0) :=
    funext hrect_n
  rw [heq_seq] at hLHS_lim
  have hfinal := tendsto_nhds_unique hLHS_lim hRHS_lim
  linear_combination -hfinal

end SpectralMod6

end Mod6Section

section Mod7Section

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators Classical

namespace SpectralMod7

/-! ### Module 7: Spectral Comparison, Moving Cutoff, Diagonal Abel Summation, and Final Theorem -/

noncomputable def bump (a b t : ℝ) : ℝ :=
  if a < t ∧ t < b then Real.exp (-1 / ((t - a) * (b - t))) else 0

noncomputable def Wfun : ℝ → ℝ := bump 1 (51 / 50)
noncomputable def bfun : ℝ → ℝ := bump (-1 / 40) (1 / 40)
noncomputable def Kfun (v : ℝ) : ℝ := ∫ u : ℝ, bfun u * bfun (v - u)
noncomputable def kfun (t : ℝ) : ℝ := ∫ v : ℝ, bfun v * Real.cos (2 * Real.pi * v * t)
noncomputable def lfun (t : ℝ) : ℝ := Real.sin (Real.pi * t / 5) * kfun t
noncomputable def omegafun (t : ℝ) : ℝ := (lfun t) ^ 2 * Real.cos (4 * Real.pi * t)
noncomputable def zCrit (g : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (g : ℂ)
noncomputable def mZero (g : ℝ) : ℕ := analyticOrderNatAt riemannZeta (zCrit g)

noncomputable def Mfun (v : ℝ) : ℂ :=
  ∫ u : ℝ, ((Wfun u / u : ℝ) : ℂ) * Complex.exp (Complex.I * ((v * Real.log u : ℝ) : ℂ))

noncomputable def phiW (y : ℝ) : ℝ := Wfun (Real.exp y)
noncomputable def Wtilde (s : ℂ) : ℂ := ∫ y : ℝ, (phiW y : ℂ) * Complex.exp (s * (y : ℂ))

noncomputable def dfun (h : ℝ) : ℝ :=
  (∫ u : ℝ, (Wfun u) ^ 2 / u) / 16 *
    (∫ v : ℝ, Kfun v * (1 / (h + v + 1 / 5) + 1 / (h + v - 1 / 5) - 2 / (h + v)))

noncomputable def Tfun (X : ℕ) : ℝ := 2 * Real.pi * (X : ℝ)
noncomputable def Lfun (X : ℕ) : ℝ := (Real.log (2 + Tfun X)) ^ 2

def wFinset (X : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)

noncomputable def uTerm (X n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Wfun ((n : ℝ) / X) / Real.sqrt n

noncomputable def Pfun (X : ℕ) (t : ℝ) : ℂ :=
  (wFinset X).sum (fun n => (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))

noncomputable def Ifun (X : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (lfun (t / Tfun X)) ^ 2 * (1 + σ * Real.cos (4 * Real.pi * t / Tfun X)) * ‖Pfun X t‖ ^ 2

noncomputable def Gweight (X : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  Wtilde (w - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
    Complex.exp ((w - (1 / 2 : ℂ) - Complex.I * (t : ℂ)) * (Real.log X : ℂ))

noncomputable def Eleft (X : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ y : ℝ, logDeriv riemannZeta (-(1 / 2 : ℂ) + Complex.I * (y : ℂ)) *
      Gweight X t (-(1 / 2 : ℂ) + Complex.I * (y : ℂ))

abbrev ZAll := {g : ℝ // riemannZeta (zCrit g) = 0}
abbrev ZWin (t L : ℝ) := {g : ℝ // |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0}

noncomputable def Swin (X : ℕ) (t L : ℝ) : ℂ :=
  ∑' g : ZWin t L,
    (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)

noncomputable def DiagWin (t L : ℝ) : ℝ :=
  ∑' g : ZWin t L, (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ ^ 2

noncomputable def Rfun (X : ℕ) : ℝ :=
  let T := Tfun X
  let L := Lfun X
  (∫ t in Set.Icc (-T * L) (T * L), omegafun (t / T) * (‖Swin X t L‖ ^ 2 - DiagWin t L)) / (2 * T)

noncomputable def DiagIntegral (X : ℕ) : ℝ :=
  let T := Tfun X
  let L := Lfun X
  (∫ t in Set.Icc (-T * L) (T * L), omegafun (t / T) * DiagWin t L) / (2 * T)

/-! #### Part 7A: Elementary Integrability, Tail Integrals, and `I(X, 1) - I(X, -1)` Folding -/

lemma integrable_div_one_add_abs_pow7 (C : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => C / (1 + |t|) ^ k) := by
  have hcont : Continuous (fun t : ℝ => C / (1 + |t|) ^ k) :=
    continuous_const.div ((continuous_const.add continuous_abs).pow k)
      (fun t => pow_ne_zero k (ne_of_gt (by linarith [abs_nonneg t] : (0 : ℝ) < 1 + |t|)))
  refine ((integrable_inv_one_add_sq.const_mul (2 * |C|))).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by linarith [abs_nonneg t] : 0 < 1 + |t|)]
  have h1t : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsq : 1 + t ^ 2 ≤ 2 * (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [this]; nlinarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ k := pow_le_pow_right₀ h1t hk
  have hdiv : (1 + |t|) ^ k ≥ (1 + t ^ 2) / 2 := by linarith
  rw [div_le_iff₀ (by positivity)]
  calc |C| = (2 * |C|) * ((1 + t ^ 2)⁻¹ * ((1 + t ^ 2) / 2)) := by
        field_simp [(by positivity : (0 : ℝ) < 1 + t ^ 2).ne']
    _ ≤ (2 * |C|) * ((1 + t ^ 2)⁻¹ * (1 + |t|) ^ k) := by gcongr
    _ = 2 * |C| * (1 + t ^ 2)⁻¹ * (1 + |t|) ^ k := by ring

lemma integral_Ioi_inv_one_add_pow {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 2 ≤ k) :
    ∫ u in Set.Ioi a, (1 : ℝ) / (1 + u) ^ k = 1 / (((k : ℝ) - 1) * (1 + a) ^ (k - 1)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  let F : ℝ → ℝ := fun u => -(1 / (((k : ℝ) - 1) * (1 + u) ^ (k - 1)))
  have hderiv : ∀ u ∈ Set.Ioi a, HasDerivAt F (1 / (1 + u) ^ k) u := by
    intro u hu
    have hu_pos : (0 : ℝ) < 1 + u := by linarith [Set.mem_Ioi.mp hu]
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 u := by simpa using (hasDerivAt_id u).const_add (1 : ℝ)
    have hpow : HasDerivAt (fun x : ℝ => (1 + x) ^ (k - 1)) (((k - 1 : ℕ) : ℝ) * (1 + u) ^ (k - 1 - 1) * 1) u :=
      h1.pow (k - 1)
    have hinv : HasDerivAt (fun x : ℝ => ((1 + x) ^ (k - 1))⁻¹)
        (-(((k - 1 : ℕ) : ℝ) * (1 + u) ^ (k - 1 - 1) * 1) / ((1 + u) ^ (k - 1)) ^ 2) u :=
      hpow.inv (pow_ne_zero _ hu_pos.ne')
    have hmul := (hinv.const_mul (1 / ((k : ℝ) - 1))).neg
    have hFeq : F = fun x => -((1 / ((k : ℝ) - 1)) * ((1 + x) ^ (k - 1))⁻¹) := by
      ext x; simp only [F, one_div, mul_inv]
    rw [hFeq]
    convert hmul using 1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hcast]
    have hpow_eq : (1 + u) ^ k = (1 + u) ^ (k - 1) * (1 + u) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hpow_eq2 : (1 + u) ^ (k - 1) = (1 + u) ^ (k - 1 - 1) * (1 + u) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k - 1)]
    have hne1 : (1 + u) ^ (k - 1) ≠ 0 := pow_ne_zero _ hu_pos.ne'
    have hne2 : (1 + u) ^ (k - 1 - 1) ≠ 0 := pow_ne_zero _ hu_pos.ne'
    rw [hpow_eq, hpow_eq2]
    field_simp [hk1_pos.ne', hu_pos.ne', hne2]
  have hcont_F : ContinuousOn F (Set.Ici a) := by
    refine (continuousOn_const.div (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow (k - 1)))
      fun u hu => mul_ne_zero hk1_pos.ne' (pow_ne_zero _ (by show 1 + u ≠ 0; linarith [Set.mem_Ici.mp hu]))).neg
  have htend : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => ((k : ℝ) - 1) * (1 + u) ^ (k - 1)) atTop atTop :=
      ((tendsto_pow_atTop (by omega : k - 1 ≠ 0)).comp
        ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop tendsto_id)).const_mul_atTop hk1_pos
    simpa [F, one_div] using (tendsto_inv_atTop_zero.comp h1).neg
  have hint : IntegrableOn (fun u : ℝ => (1 : ℝ) / (1 + u) ^ k) (Set.Ioi a) := by
    have hfull := (integrable_div_one_add_abs_pow7 1 k hk).integrableOn (s := Set.Ioi a)
    refine hfull.congr_fun (fun u hu => ?_) measurableSet_Ioi
    dsimp only
    rw [abs_of_nonneg (by linarith [Set.mem_Ioi.mp hu])]
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (hcont_F a Set.self_mem_Ici) hderiv hint htend
  rw [hftc]; simp [F]

lemma integral_compl_Icc_inv_one_add_abs_pow {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 2 ≤ k) :
    ∫ u in (Set.Icc (-L) L)ᶜ, (1 : ℝ) / (1 + |u|) ^ k =
      2 / (((k : ℝ) - 1) * (1 + L) ^ (k - 1)) := by
  have hset : (Set.Icc (-L) L)ᶜ = Set.Iio (-L) ∪ Set.Ioi L := by
    ext u; simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-L)) (Set.Ioi L) :=
    Set.disjoint_left.mpr fun u h1 h2 => by linarith [Set.mem_Iio.mp h1, Set.mem_Ioi.mp h2]
  have hint_full : Integrable (fun u : ℝ => (1 : ℝ) / (1 + |u|) ^ k) :=
    integrable_div_one_add_abs_pow7 1 k hk
  rw [hset, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_full.integrableOn hint_full.integrableOn]
  have hpos : ∫ u in Set.Ioi L, (1 : ℝ) / (1 + |u|) ^ k = 1 / (((k : ℝ) - 1) * (1 + L) ^ (k - 1)) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => by
      rw [abs_of_nonneg (by linarith [Set.mem_Ioi.mp hu])]]
    exact integral_Ioi_inv_one_add_pow hL hk
  have hneg : ∫ u in Set.Iio (-L), (1 : ℝ) / (1 + |u|) ^ k = ∫ u in Set.Ioi L, (1 : ℝ) / (1 + |u|) ^ k := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iio, ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_neg_eq_self]
    congr 1; ext u
    by_cases h : L < u
    · have hm1 : -u ∈ Set.Iio (-L) := by simp [Set.mem_Iio]; linarith
      have hm2 : u ∈ Set.Ioi L := h
      rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2, abs_neg]
    · have hm1 : -u ∉ Set.Iio (-L) := by simp [Set.mem_Iio]; linarith
      have hm2 : u ∉ Set.Ioi L := h
      rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
  rw [hneg, hpos]; ring

lemma continuous_Pfun (X : ℕ) : Continuous (Pfun X) := by
  unfold Pfun
  have haux : ∀ (S : Finset ℕ), Continuous (fun t : ℝ => S.sum (fun n => (uTerm X n : ℂ) *
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using continuous_const
    | @insert a s ha ih =>
      have heq : (fun t : ℝ => (insert a s).sum (fun n => (uTerm X n : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
          fun t : ℝ => (uTerm X a : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log a : ℂ)) +
            s.sum (fun n => (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
        ext t; exact Finset.sum_insert ha
      rw [heq]
      exact (continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))).add ih
  exact haux (wFinset X)

lemma norm_Pfun_le_const (X : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Pfun X t‖ ≤ C := by
  refine ⟨∑ n ∈ wFinset X, |uTerm X n|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t => ?_⟩
  unfold Pfun
  calc ‖∑ n ∈ wFinset X, (uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))‖
      ≤ ∑ n ∈ wFinset X, ‖(uTerm X n : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ wFinset X, |uTerm X n| := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
        have hre : (-Complex.I * (t : ℂ) * (Real.log n : ℂ)).re = 0 := by
          simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, neg_zero, zero_mul, mul_zero,
            sub_self, add_zero]
        rw [hre, Real.exp_zero, mul_one]

lemma Pfun_neg (X : ℕ) (t : ℝ) : Pfun X (-t) = starRingEnd ℂ (Pfun X t) := by
  unfold Pfun
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.conj_re, neg_zero,
      zero_mul, mul_zero, sub_self, add_zero]
  · simp only [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im, neg_zero,
      zero_mul, mul_zero, sub_zero, zero_add, one_mul, neg_mul, neg_neg]

lemma norm_Pfun_neg (X : ℕ) (t : ℝ) : ‖Pfun X (-t)‖ = ‖Pfun X t‖ := by
  rw [Pfun_neg, Complex.norm_conj]

lemma Ifun_sub_eq_integral_omegafun
    (hcont_kfun : Continuous kfun)
    (hk_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |kfun t| ≤ C / (1 + |t|) ^ n)
    (homega_even : ∀ t : ℝ, omegafun (-t) = omegafun t)
    {X : ℕ} (hX : 1 ≤ X) :
    Ifun X 1 - Ifun X (-1) = ∫ t : ℝ, omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2 := by
  have hTpos : 0 < Tfun X := by unfold Tfun; positivity
  obtain ⟨Ck, hCk, hk2⟩ := hk_dec 2
  obtain ⟨CP, hCP, hPbd⟩ := norm_Pfun_le_const X
  have hcont_l : Continuous lfun :=
    (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 5)).mul hcont_kfun
  have hint_sigma : ∀ σ : ℝ, IntegrableOn
      (fun t : ℝ => (lfun (t / Tfun X)) ^ 2 * (1 + σ * Real.cos (4 * Real.pi * t / Tfun X)) * ‖Pfun X t‖ ^ 2)
      (Set.Ioi 0) := by
    intro σ
    have hcont : Continuous (fun t : ℝ =>
        (lfun (t / Tfun X)) ^ 2 * (1 + σ * Real.cos (4 * Real.pi * t / Tfun X)) * ‖Pfun X t‖ ^ 2) :=
      ((hcont_l.comp (continuous_id.div_const _)).pow 2 |>.mul
        (continuous_const.add (continuous_const.mul (Real.continuous_cos.comp
          ((continuous_const.mul continuous_id).div_const _))))).mul ((continuous_Pfun X).norm.pow 2)
    have hdom_u : Integrable (fun u : ℝ => (Ck ^ 2 * (1 + |σ|) * CP ^ 2) / (1 + |u|) ^ 4) :=
      integrable_div_one_add_abs_pow7 _ 4 (by norm_num)
    have hdom_t : Integrable (fun t : ℝ => (Ck ^ 2 * (1 + |σ|) * CP ^ 2) / (1 + |t / Tfun X|) ^ 4) := by
      have := hdom_u.comp_div hTpos.ne'
      exact this
    refine hdom_t.integrableOn.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
    have hl : |lfun (t / Tfun X)| ^ 2 ≤ Ck ^ 2 / (1 + |t / Tfun X|) ^ 4 := by
      unfold lfun
      rw [abs_mul]
      have h1 : |Real.sin (Real.pi * (t / Tfun X) / 5)| * |kfun (t / Tfun X)| ≤ Ck / (1 + |t / Tfun X|) ^ 2 := by
        calc _ ≤ 1 * |kfun (t / Tfun X)| := by gcongr; exact Real.abs_sin_le_one _
          _ = |kfun (t / Tfun X)| := one_mul _
          _ ≤ Ck / (1 + |t / Tfun X|) ^ 2 := hk2 _
      calc (|Real.sin (Real.pi * (t / Tfun X) / 5)| * |kfun (t / Tfun X)|) ^ 2
          ≤ (Ck / (1 + |t / Tfun X|) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = Ck ^ 2 / (1 + |t / Tfun X|) ^ 4 := by rw [div_pow, ← pow_mul]
    have hcos : |1 + σ * Real.cos (4 * Real.pi * t / Tfun X)| ≤ 1 + |σ| := by
      calc _ ≤ |1| + |σ * Real.cos (4 * Real.pi * t / Tfun X)| := abs_add_le _ _
        _ = 1 + |σ| * |Real.cos (4 * Real.pi * t / Tfun X)| := by rw [abs_one, abs_mul]
        _ ≤ 1 + |σ| * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ = 1 + |σ| := by ring
    have hP : |‖Pfun X t‖| ^ 2 ≤ CP ^ 2 := by
      rw [abs_of_nonneg (norm_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hPbd t) 2
    calc |lfun (t / Tfun X)| ^ 2 * |1 + σ * Real.cos (4 * Real.pi * t / Tfun X)| * |‖Pfun X t‖| ^ 2
        ≤ (Ck ^ 2 / (1 + |t / Tfun X|) ^ 4) * (1 + |σ|) * CP ^ 2 := by
          have h1 : |lfun (t / Tfun X)| ^ 2 * |1 + σ * Real.cos (4 * Real.pi * t / Tfun X)| ≤
              (Ck ^ 2 / (1 + |t / Tfun X|) ^ 4) * (1 + |σ|) :=
            mul_le_mul hl hcos (abs_nonneg _) (by positivity)
          exact mul_le_mul h1 hP (by positivity) (by positivity)
      _ = (Ck ^ 2 * (1 + |σ|) * CP ^ 2) / (1 + |t / Tfun X|) ^ 4 := by ring
  unfold Ifun
  rw [← MeasureTheory.integral_sub (hint_sigma 1) (hint_sigma (-1))]
  have hsub_eq : ∀ t : ℝ,
      (lfun (t / Tfun X)) ^ 2 * (1 + 1 * Real.cos (4 * Real.pi * t / Tfun X)) * ‖Pfun X t‖ ^ 2 -
      (lfun (t / Tfun X)) ^ 2 * (1 + -1 * Real.cos (4 * Real.pi * t / Tfun X)) * ‖Pfun X t‖ ^ 2 =
      2 * (omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2) := by
    intro t; unfold omegafun
    have : 4 * Real.pi * t / Tfun X = 4 * Real.pi * (t / Tfun X) := by ring
    rw [this]; ring
  simp_rw [hsub_eq, MeasureTheory.integral_const_mul]
  -- Now fold `2 * ∫_{t > 0} f t = ∫ t : ℝ, f t` by evenness of `t ↦ omegafun (t / T) * ‖Pfun X t‖ ^ 2`
  have hint_full : Integrable (fun t : ℝ => omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2) := by
    have hcont : Continuous (fun t : ℝ => omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2) :=
      (((hcont_l.comp (continuous_id.div_const _)).pow 2).mul
        (Real.continuous_cos.comp (continuous_const.mul (continuous_id.div_const _)))).mul
        ((continuous_Pfun X).norm.pow 2)
    have hdom_u : Integrable (fun u : ℝ => (Ck ^ 2 * CP ^ 2) / (1 + |u|) ^ 4) :=
      integrable_div_one_add_abs_pow7 _ 4 (by norm_num)
    refine (hdom_u.comp_div hTpos.ne').mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
    have ho : |omegafun (t / Tfun X)| ≤ Ck ^ 2 / (1 + |t / Tfun X|) ^ 4 := by
      unfold omegafun lfun
      rw [abs_mul, abs_pow, abs_mul]
      have h1 : |Real.sin (Real.pi * (t / Tfun X) / 5)| * |kfun (t / Tfun X)| ≤ Ck / (1 + |t / Tfun X|) ^ 2 := by
        calc _ ≤ 1 * |kfun (t / Tfun X)| := by gcongr; exact Real.abs_sin_le_one _
          _ = |kfun (t / Tfun X)| := one_mul _
          _ ≤ Ck / (1 + |t / Tfun X|) ^ 2 := hk2 _
      calc (|Real.sin (Real.pi * (t / Tfun X) / 5)| * |kfun (t / Tfun X)|) ^ 2 * |Real.cos (4 * Real.pi * (t / Tfun X))|
          ≤ (Ck / (1 + |t / Tfun X|) ^ 2) ^ 2 * 1 :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
        _ = Ck ^ 2 / (1 + |t / Tfun X|) ^ 4 := by rw [mul_one, div_pow, ← pow_mul]
    have hP : ‖Pfun X t‖ ^ 2 ≤ CP ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hPbd t) 2
    calc |omegafun (t / Tfun X)| * ‖Pfun X t‖ ^ 2
        ≤ (Ck ^ 2 / (1 + |t / Tfun X|) ^ 4) * CP ^ 2 := mul_le_mul ho hP (by positivity) (by positivity)
      _ = (Ck ^ 2 * CP ^ 2) / (1 + |t / Tfun X|) ^ 4 := by ring
  have hsplit : ∫ t : ℝ, omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2 =
      (∫ t in Set.Iic (0 : ℝ), omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2) +
      (∫ t in Set.Ioi (0 : ℝ), omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2) := by
    rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint_full.integrableOn hint_full.integrableOn, Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ]
  have hIic : ∫ t in Set.Iic (0 : ℝ), omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2 =
      ∫ t in Set.Ioi (0 : ℝ), omegafun (t / Tfun X) * ‖Pfun X t‖ ^ 2 := by
    rw [MeasureTheory.integral_Iic_eq_integral_Iio (μ := volume),
      ← MeasureTheory.integral_indicator measurableSet_Iio,
      ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_neg_eq_self]
    congr 1; ext t
    by_cases h : (0 : ℝ) < t
    · have hm1 : -t ∈ Set.Iio (0 : ℝ) := by simp [Set.mem_Iio]; linarith
      have hm2 : t ∈ Set.Ioi (0 : ℝ) := h
      rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2, neg_div, homega_even, norm_Pfun_neg]
    · have hm1 : -t ∉ Set.Iio (0 : ℝ) := by simp [Set.mem_Iio]; linarith
      have hm2 : t ∉ Set.Ioi (0 : ℝ) := h
      rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
  linarith

/-! #### Part 7B: Finite Zero Windows, Moving-Height Tail Bounds, and Explicit-Formula Comparison -/

lemma mZero_pos_iff_zero
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    {g : ℝ} : riemannZeta (zCrit g) = 0 ↔ 0 < mZero g := by
  have hne1 : zCrit g ≠ 1 := by intro h; have := congrArg Complex.re h; simp [zCrit] at this
  have han : AnalyticAt ℂ riemannZeta (zCrit g) := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)
  have hntop : analyticOrderAt riemannZeta (zCrit g) ≠ ⊤ := by
    intro h; apply hzeta_ntop (zCrit g); rw [han.meromorphicOrderAt_eq, h]; rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  have hnat : mZero g = n := by simp [mZero, analyticOrderNatAt, ← hn]
  rw [hnat]
  constructor
  · intro hz0
    by_contra h0
    have hn0 : n = 0 := by omega
    rw [hn0, Nat.cast_zero] at hn
    exact han.analyticOrderAt_eq_zero.mp hn.symm hz0
  · intro hpos
    by_contra hne0
    have h0 := han.analyticOrderAt_eq_zero.mpr hne0
    rw [← hn] at h0
    have : n = 0 := by exact_mod_cast h0
    omega

lemma finite_zeros_in_Icc
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (CJ : ℝ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (A B : ℝ) :
    {g : ℝ | A ≤ g ∧ g ≤ B ∧ riemannZeta (zCrit g) = 0}.Finite := by
  set k1 : ℤ := ⌊A⌋
  set k2 : ℤ := ⌊B⌋
  have hfin_u : (⋃ k ∈ (Finset.Icc k1 k2 : Set ℤ),
      Function.support (fun g : ℝ => if (k : ℝ) ≤ g ∧ g < (k : ℝ) + 1 then (mZero g : ℝ) else 0)).Finite :=
    (Finset.finite_toSet (Finset.Icc k1 k2)).biUnion fun k _ => (hunit (k : ℝ)).1
  refine hfin_u.subset fun g ⟨hA, hB, hz⟩ => ?_
  rw [Set.mem_iUnion₂]
  refine ⟨⌊g⌋, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨Int.floor_mono hA, Int.floor_mono hB⟩), ?_⟩
  rw [Function.mem_support]
  have h1 : (⌊g⌋ : ℝ) ≤ g := Int.floor_le g
  have h2 : g < (⌊g⌋ : ℝ) + 1 := Int.lt_floor_add_one g
  have hpos : 0 < mZero g := (mZero_pos_iff_zero hzeta_ntop).mp hz
  simp only [h1, h2, and_self, ↓reduceIte]
  exact_mod_cast hpos.ne'

lemma zero_sum_moving_tail_bounds
    (hM_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|)) :
    ∃ KM : ℝ, 0 ≤ KM ∧
      (∀ t : ℝ, (∑' g : ZAll, (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖) ≤ KM * Real.log (2 + |t|)) ∧
      (∀ t : ℝ, ∀ L : ℝ, 0 ≤ L →
        (∑' g : ZAll, if L < |g.val - t| then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) ≤
          KM * Real.log (2 + |t| + L) / (1 + L) ^ 5) ∧
      (∀ t : ℝ, Summable (fun g : ZAll => (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖)) := by
  obtain ⟨CM6, hCM6, hM6⟩ := hM_dec 6
  obtain ⟨K, hK, hMHT⟩ := Conjectures.TwinPrimes.MovingHeightMellinTail CJ hCJ
  -- Key helper: for any `t : ℝ` and `Lnat : ℕ`, bound finite subsums with `Lnat ≤ (⌊g⌋ - ⌊t⌋).natAbs`
  have hbound_nat : ∀ (t : ℝ) (Lnat : ℕ) (P : ℝ → Prop) [DecidablePred P],
      (∀ g : ℝ, P g → Lnat ≤ (⌊g⌋ - ⌊t⌋).natAbs) →
      (∀ s : Finset ZAll,
        ∑ g ∈ s, (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) ≤
          (64 * CM6 * K) * Real.log (2 + |t| + (Lnat : ℝ)) / (1 + (Lnat : ℝ)) ^ 5) := by
    intro t Lnat P _ hP s
    let m : ℤ → ℝ := fun j =>
      ∑ᶠ g : ℝ, if ((⌊t⌋ : ℝ) + (j : ℝ)) ≤ g ∧ g < ((⌊t⌋ : ℝ) + (j : ℝ)) + 1 then (mZero g : ℝ) else 0
    have hm_spec : ∀ j : ℤ, 0 ≤ m j ∧ m j ≤ CJ * Real.log (2 + |(⌊t⌋ : ℝ) + (j : ℝ)|) := fun j =>
      ⟨finsum_nonneg fun _ => by split_ifs <;> positivity, (hunit ((⌊t⌋ : ℝ) + (j : ℝ))).2⟩
    have hmht_t := hMHT t Lnat m hm_spec
    have hsum_j : Summable (fun j : ℤ => if Lnat ≤ j.natAbs then m j / (1 + (j.natAbs : ℝ)) ^ 6 else 0) := by
      have hdom : Summable (fun j : ℤ => (CJ * (2 + |t| + 1)) / (1 + |(j : ℝ)|) ^ 2) := by
        have hnat : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
          have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
            (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective Nat.succ_injective
          exact h1.congr fun n => by push_cast; rfl
        have hpos : Summable (fun k : ℤ => (1 : ℝ) / (1 + |(k : ℝ)|) ^ 2) := by
          rw [summable_int_iff_summable_nat_and_neg]
          constructor
          · exact hnat.congr fun n => by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
          · exact hnat.congr fun n => by rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
        exact (hpos.mul_left (CJ * (2 + |t| + 1))).congr fun k => by ring
      refine Summable.of_nonneg_of_le
        (fun j => by split_ifs; exact div_nonneg (hm_spec j).1 (by positivity); exact le_rfl)
        (fun j => ?_) hdom
      split_ifs with hL
      · have hmj := (hm_spec j).2
        have hfl : |(⌊t⌋ : ℝ)| ≤ |t| + 1 := by
          rw [abs_le]; constructor <;> linarith [Int.floor_le t, Int.lt_floor_add_one t, neg_abs_le t, le_abs_self t]
        have harg : 2 + |(⌊t⌋ : ℝ) + (j : ℝ)| ≤ (2 + |t| + 1) * (1 + |(j : ℝ)|) := by
          have htri := abs_add_le (⌊t⌋ : ℝ) (j : ℝ)
          nlinarith [abs_nonneg t, abs_nonneg (j : ℝ)]
        have hlog : Real.log (2 + |(⌊t⌋ : ℝ) + (j : ℝ)|) ≤ (2 + |t| + 1) * (1 + |(j : ℝ)|) :=
          (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        have hjabs : (j.natAbs : ℝ) = |(j : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        rw [hjabs]
        have h1j : 1 ≤ 1 + |(j : ℝ)| := by linarith [abs_nonneg (j : ℝ)]
        have hpow : (1 + |(j : ℝ)|) ^ 3 ≤ (1 + |(j : ℝ)|) ^ 6 := pow_le_pow_right₀ h1j (by norm_num)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc m j * (1 + |(j : ℝ)|) ^ 2
            ≤ (CJ * ((2 + |t| + 1) * (1 + |(j : ℝ)|))) * (1 + |(j : ℝ)|) ^ 2 := by
              gcongr; exact hmj.trans (mul_le_mul_of_nonneg_left hlog hCJ)
          _ = CJ * (2 + |t| + 1) * (1 + |(j : ℝ)|) ^ 3 := by ring
          _ ≤ CJ * (2 + |t| + 1) * (1 + |(j : ℝ)|) ^ 6 := by gcongr
      · positivity
    -- Group `s` by `j = ⌊g.val⌋ - ⌊t⌋`
    set js : Finset ℤ := s.image (fun g => ⌊g.val⌋ - ⌊t⌋)
    have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := js) (g := fun g => ⌊g.val⌋ - ⌊t⌋)
      (fun g hg => Finset.mem_image_of_mem _ hg)
      (f := fun g => if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0)
    have hstep1 : ∑ g ∈ s, (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) ≤
        (64 * CM6) * ∑ j ∈ js, (if Lnat ≤ j.natAbs then m j / (1 + (j.natAbs : ℝ)) ^ 6 else 0) := by
      rw [← hfib, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hLj : Lnat ≤ j.natAbs
      · simp only [hLj, ↓reduceIte]
        have hpt : ∀ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j),
            (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) ≤
              (mZero g.val : ℝ) * (64 * CM6 / (1 + (j.natAbs : ℝ)) ^ 6) := by
          intro g hg
          split_ifs with hPg
          · have hj_eq : ⌊g.val⌋ - ⌊t⌋ = j := (Finset.mem_filter.mp hg).2
            have hfl_g1 : (⌊g.val⌋ : ℝ) ≤ g.val := Int.floor_le g.val
            have hfl_g2 : g.val < (⌊g.val⌋ : ℝ) + 1 := Int.lt_floor_add_one g.val
            have hfl_t1 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
            have hfl_t2 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
            have hj_real : (j : ℝ) = (⌊g.val⌋ : ℝ) - (⌊t⌋ : ℝ) := by exact_mod_cast hj_eq.symm
            have hdiff_lt1 : |(g.val - t) - (j : ℝ)| < 1 := by
              rw [hj_real, abs_lt]; constructor <;> linarith
            have hj_le : 1 + (j.natAbs : ℝ) ≤ 2 * (1 + |g.val - t|) := by
              have habs : (j.natAbs : ℝ) = |(j : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
              rw [habs]
              have htri : |(j : ℝ)| ≤ |g.val - t| + 1 := by
                have h1 : (j : ℝ) = (g.val - t) - ((g.val - t) - (j : ℝ)) := by ring
                have h2 := abs_sub (g.val - t) ((g.val - t) - (j : ℝ))
                rw [← h1] at h2; linarith
              linarith [abs_nonneg (g.val - t)]
            have hpow6 : (1 + (j.natAbs : ℝ)) ^ 6 ≤ 64 * (1 + |g.val - t|) ^ 6 := by
              calc (1 + (j.natAbs : ℝ)) ^ 6 ≤ (2 * (1 + |g.val - t|)) ^ 6 :=
                    pow_le_pow_left₀ (by positivity) hj_le 6
                _ = 64 * (1 + |g.val - t|) ^ 6 := by ring
            have hMle : ‖Mfun (g.val - t)‖ ≤ 64 * CM6 / (1 + (j.natAbs : ℝ)) ^ 6 := by
              refine (hM6 (g.val - t)).trans ?_
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              calc CM6 * (1 + (j.natAbs : ℝ)) ^ 6 ≤ CM6 * (64 * (1 + |g.val - t|) ^ 6) :=
                    mul_le_mul_of_nonneg_left hpow6 hCM6
                _ = 64 * CM6 * (1 + |g.val - t|) ^ 6 := by ring
            exact mul_le_mul_of_nonneg_left hMle (Nat.cast_nonneg _)
          · positivity
        calc ∑ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j), (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0)
            ≤ ∑ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j), (mZero g.val : ℝ) * (64 * CM6 / (1 + (j.natAbs : ℝ)) ^ 6) :=
              Finset.sum_le_sum hpt
          _ = (∑ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j), (mZero g.val : ℝ)) * (64 * CM6 / (1 + (j.natAbs : ℝ)) ^ 6) :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ m j * (64 * CM6 / (1 + (j.natAbs : ℝ)) ^ 6) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hfin := (hunit ((⌊t⌋ : ℝ) + (j : ℝ))).1
              set Tj := (s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j)).image Subtype.val ∪ hfin.toFinset
              dsimp only [m]
              rw [finsum_eq_sum_of_support_subset _ (s := Tj)
                (fun x hx => Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr hx)))]
              have himg : ∑ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j), (mZero g.val : ℝ) =
                  ∑ x ∈ (s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j)).image Subtype.val,
                    (if ((⌊t⌋ : ℝ) + (j : ℝ)) ≤ x ∧ x < ((⌊t⌋ : ℝ) + (j : ℝ)) + 1 then (mZero x : ℝ) else 0) := by
                rw [Finset.sum_image (fun g1 _ g2 _ h => Subtype.ext h)]
                refine Finset.sum_congr rfl fun g hg => ?_
                have hj_eq : ⌊g.val⌋ = ⌊t⌋ + j := by have := (Finset.mem_filter.mp hg).2; omega
                have h1 : (⌊t⌋ : ℝ) + (j : ℝ) ≤ g.val := by
                  have := Int.floor_le g.val; rw [hj_eq] at this; exact_mod_cast this
                have h2 : g.val < (⌊t⌋ : ℝ) + (j : ℝ) + 1 := by
                  have := Int.lt_floor_add_one g.val; rw [hj_eq] at this; push_cast at this; linarith
                simp [h1, h2]
              rw [himg]
              exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => by split_ifs <;> positivity
          _ = 64 * CM6 * (m j / (1 + (j.natAbs : ℝ)) ^ 6) := by ring
      · simp only [hLj, ↓reduceIte, mul_zero]
        have hzero : ∀ g ∈ s.filter (fun g => ⌊g.val⌋ - ⌊t⌋ = j),
            (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) = 0 := by
          intro g hg
          rw [if_neg]; intro hPg
          have := hP g.val hPg
          rw [(Finset.mem_filter.mp hg).2] at this
          exact hLj this
        rw [Finset.sum_eq_zero hzero]
    calc ∑ g ∈ s, (if P g.val then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0)
        ≤ (64 * CM6) * ∑ j ∈ js, (if Lnat ≤ j.natAbs then m j / (1 + (j.natAbs : ℝ)) ^ 6 else 0) := hstep1
      _ ≤ (64 * CM6) * ∑' j : ℤ, (if Lnat ≤ j.natAbs then m j / (1 + (j.natAbs : ℝ)) ^ 6 else 0) := by
          gcongr
          exact hsum_j.sum_le_tsum js fun j _ => by
            split_ifs
            · exact div_nonneg (hm_spec j).1 (by positivity)
            · exact le_rfl
      _ ≤ (64 * CM6) * (K * Real.log (2 + |t| + (Lnat : ℝ)) / (1 + (Lnat : ℝ)) ^ 5) := by gcongr
      _ = (64 * CM6 * K) * Real.log (2 + |t| + (Lnat : ℝ)) / (1 + (Lnat : ℝ)) ^ 5 := by ring
  refine ⟨32 * (64 * CM6 * K), by positivity, ?_, ?_, ?_⟩
  · intro t
    have hsum : Summable (fun g : ZAll => (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖) := by
      refine summable_of_sum_le (fun _ => by positivity) (fun s => ?_)
        (c := (64 * CM6 * K) * Real.log (2 + |t| + (0 : ℕ)) / (1 + ((0 : ℕ) : ℝ)) ^ 5)
      simpa using hbound_nat t 0 (fun _ => True) (fun _ _ => Nat.zero_le _) s
    have hle := hsum.tsum_le_of_sum_le (fun s => by
      simpa using hbound_nat t 0 (fun _ => True) (fun _ _ => Nat.zero_le _) s)
    have hlog_nn : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith [mul_nonneg (show 0 ≤ 64 * CM6 * K by positivity) hlog_nn]
  · intro t L hL
    set Lnat : ℕ := Nat.floor L
    have hLnat_le : (Lnat : ℝ) ≤ L := Nat.floor_le hL
    have hL_lt : L < (Lnat : ℝ) + 1 := Nat.lt_floor_add_one L
    have hP : ∀ g : ℝ, L < |g - t| → Lnat ≤ (⌊g⌋ - ⌊t⌋).natAbs := by
      intro g hg
      have hdiff : |(g - t) - ((⌊g⌋ - ⌊t⌋ : ℤ) : ℝ)| < 1 := by
        push_cast; rw [abs_lt]; constructor <;> linarith [Int.floor_le g, Int.lt_floor_add_one g, Int.floor_le t, Int.lt_floor_add_one t]
      have htri : |g - t| < ((⌊g⌋ - ⌊t⌋).natAbs : ℝ) + 1 := by
        have habs : ((⌊g⌋ - ⌊t⌋).natAbs : ℝ) = |((⌊g⌋ - ⌊t⌋ : ℤ) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        rw [habs]
        have := abs_sub_abs_le_abs_sub (g - t) ((⌊g⌋ - ⌊t⌋ : ℤ) : ℝ)
        linarith
      have hlt : (Lnat : ℝ) < ((⌊g⌋ - ⌊t⌋).natAbs : ℝ) + 1 := lt_trans (lt_of_le_of_lt hLnat_le hg) htri
      have hlt_nat : Lnat < (⌊g⌋ - ⌊t⌋).natAbs + 1 := by exact_mod_cast hlt
      omega
    have hsum : Summable (fun g : ZAll => if L < |g.val - t| then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0) :=
      summable_of_sum_le (fun _ => by split_ifs <;> positivity) (fun s => hbound_nat t Lnat (fun g => L < |g - t|) hP s)
    have hle := hsum.tsum_le_of_sum_le (fun s => hbound_nat t Lnat (fun g => L < |g - t|) hP s)
    refine hle.trans ?_
    have hlog_le : Real.log (2 + |t| + (Lnat : ℝ)) ≤ Real.log (2 + |t| + L) :=
      Real.log_le_log (by linarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) Lnat]) (by linarith)
    have hden_le : 1 + L ≤ 2 * (1 + (Lnat : ℝ)) := by linarith [Nat.cast_nonneg (α := ℝ) Lnat]
    have hpow5 : (1 + L) ^ 5 ≤ 32 * (1 + (Lnat : ℝ)) ^ 5 := by
      calc (1 + L) ^ 5 ≤ (2 * (1 + (Lnat : ℝ))) ^ 5 := pow_le_pow_left₀ (by linarith) hden_le 5
        _ = 32 * (1 + (Lnat : ℝ)) ^ 5 := by ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hlog_nn : 0 ≤ Real.log (2 + |t| + (Lnat : ℝ)) :=
      Real.log_nonneg (by linarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) Lnat])
    have hlogL_nn : 0 ≤ Real.log (2 + |t| + L) := Real.log_nonneg (by linarith [abs_nonneg t])
    calc (64 * CM6 * K) * Real.log (2 + |t| + (Lnat : ℝ)) * (1 + L) ^ 5
        ≤ (64 * CM6 * K) * Real.log (2 + |t| + L) * (32 * (1 + (Lnat : ℝ)) ^ 5) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlog_le (by positivity)) hpow5 (by positivity) (by positivity)
      _ = 32 * (64 * CM6 * K) * Real.log (2 + |t| + L) * (1 + (Lnat : ℝ)) ^ 5 := by ring
  · intro t
    refine summable_of_sum_le (fun _ => by positivity) (fun s => ?_)
      (c := (64 * CM6 * K) * Real.log (2 + |t| + (0 : ℕ)) / (1 + ((0 : ℕ) : ℝ)) ^ 5)
    simpa using hbound_nat t 0 (fun _ => True) (fun _ _ => Nat.zero_le _) s

lemma Swin_eq_finset_sum {Gbig : Finset ℝ} {X : ℕ} {t L : ℝ}
    (hG : ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig) :
    Swin X t L = ∑ g ∈ Gbig,
      if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then
        (mZero g : ℂ) * Complex.exp (Complex.I * ((g * Real.log X : ℝ) : ℂ)) * Mfun (g - t)
      else 0 := by
  have hfin : (Set.univ : Set (ZWin t L)).Finite := by
    have hinj : Function.Injective (Subtype.val : ZWin t L → ℝ) := Subtype.val_injective
    refine (Gbig.finite_toSet.preimage hinj.injOn).subset fun g _ => ?_
    exact Finset.mem_coe.mpr (hG g.val g.prop.1 g.prop.2)
  haveI : Finite (ZWin t L) := Set.finite_univ_iff.mp hfin
  haveI : Fintype (ZWin t L) := Fintype.ofFinite (ZWin t L)
  unfold Swin
  rw [tsum_fintype, ← Finset.sum_filter]
  refine Finset.sum_bij (fun g _ => g.val) ?_ ?_ ?_ ?_
  · intro g _; exact Finset.mem_filter.mpr ⟨hG g.val g.prop.1 g.prop.2, g.prop⟩
  · intro g1 _ g2 _ h; exact Subtype.ext h
  · intro g hg
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨⟨g, h1, h2⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

lemma DiagWin_eq_finset_sum {Gbig : Finset ℝ} {t L : ℝ}
    (hG : ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig) :
    DiagWin t L = ∑ g ∈ Gbig,
      if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then
        (mZero g : ℝ) * ‖Mfun (g - t)‖ ^ 2
      else 0 := by
  have hfin : (Set.univ : Set (ZWin t L)).Finite := by
    have hinj : Function.Injective (Subtype.val : ZWin t L → ℝ) := Subtype.val_injective
    refine (Gbig.finite_toSet.preimage hinj.injOn).subset fun g _ => ?_
    exact Finset.mem_coe.mpr (hG g.val g.prop.1 g.prop.2)
  haveI : Finite (ZWin t L) := Set.finite_univ_iff.mp hfin
  haveI : Fintype (ZWin t L) := Fintype.ofFinite (ZWin t L)
  unfold DiagWin
  rw [tsum_fintype, ← Finset.sum_filter]
  refine Finset.sum_bij (fun g _ => g.val) ?_ ?_ ?_ ?_
  · intro g _; exact Finset.mem_filter.mpr ⟨hG g.val g.prop.1 g.prop.2, g.prop⟩
  · intro g1 _ g2 _ h; exact Subtype.ext h
  · intro g hg
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨⟨g, h1, h2⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

lemma measurable_Swin_on_Icc
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hcont_Mfun : Continuous Mfun)
    (CJ : ℝ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (X : ℕ) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    AEStronglyMeasurable (fun t : ℝ => Swin X t L) (volume.restrict (Set.Icc (-B) B)) := by
  have hfin := finite_zeros_in_Icc hzeta_ntop CJ hunit (-(B + L)) (B + L)
  set Gbig : Finset ℝ := hfin.toFinset
  have hG : ∀ t ∈ Set.Icc (-B) B, ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
    intro t ht g hgt hz
    rw [Set.Finite.mem_toFinset]
    have hgt' := abs_le.mp hgt
    exact ⟨by linarith [ht.1, hgt'.1], by linarith [ht.2, hgt'.2], hz⟩
  have hmeas_sum : Measurable (fun t : ℝ => ∑ g ∈ Gbig,
      if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then
        (mZero g : ℂ) * Complex.exp (Complex.I * ((g * Real.log X : ℝ) : ℂ)) * Mfun (g - t)
      else 0) := by
    refine Finset.measurable_sum Gbig fun g _ => ?_
    have hset : MeasurableSet {t : ℝ | |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0} :=
      (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const).inter
        (MeasurableSet.const _)
    exact Measurable.ite hset (measurable_const.mul (hcont_Mfun.measurable.comp (measurable_const.sub measurable_id)))
      measurable_const
  refine hmeas_sum.aestronglyMeasurable.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact (Swin_eq_finset_sum (hG t ht)).symm

lemma measurable_DiagWin_on_Icc
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hcont_Mfun : Continuous Mfun)
    (CJ : ℝ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    AEStronglyMeasurable (fun t : ℝ => DiagWin t L) (volume.restrict (Set.Icc (-B) B)) := by
  have hfin := finite_zeros_in_Icc hzeta_ntop CJ hunit (-(B + L)) (B + L)
  set Gbig : Finset ℝ := hfin.toFinset
  have hG : ∀ t ∈ Set.Icc (-B) B, ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
    intro t ht g hgt hz
    rw [Set.Finite.mem_toFinset]
    have hgt' := abs_le.mp hgt
    exact ⟨by linarith [ht.1, hgt'.1], by linarith [ht.2, hgt'.2], hz⟩
  have hmeas_sum : Measurable (fun t : ℝ => ∑ g ∈ Gbig,
      if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then (mZero g : ℝ) * ‖Mfun (g - t)‖ ^ 2 else 0) := by
    refine Finset.measurable_sum Gbig fun g _ => ?_
    have hset : MeasurableSet {t : ℝ | |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0} :=
      (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const).inter
        (MeasurableSet.const _)
    exact Measurable.ite hset
      (measurable_const.mul ((hcont_Mfun.norm.pow 2).measurable.comp (measurable_const.sub measurable_id)))
      measurable_const
  refine hmeas_sum.aestronglyMeasurable.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  exact (DiagWin_eq_finset_sum (hG t ht)).symm

lemma norm_Swin_le_and_explicit_split
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hM_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hpole : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Gweight X t 1‖ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5)
    (CE : ℝ) (hCE : 0 ≤ CE)
    (heleft : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Eleft X t‖ ≤ CE * (X : ℝ)⁻¹ * Real.log (2 + |t|))
    (hexplicit : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      Pfun X t = Gweight X t 1 -
        (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
        Eleft X t) :
    ∃ KM : ℝ, 0 ≤ KM ∧
      (∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
        ‖Pfun X t‖ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t|) + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|)) ∧
      (∀ X : ℕ, ∀ t L : ℝ, 0 ≤ L → ‖Swin X t L‖ ≤ KM * Real.log (2 + |t|)) ∧
      (∀ X : ℕ, 1 ≤ X → ∀ t L : ℝ, 0 ≤ L →
        |‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2| ≤
          2 * (KM * Real.log (2 + |t|)) *
            (CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|)) +
          (CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|)) ^ 2) := by
  obtain ⟨KM, hKM, htot, htail, hsumm_norm⟩ := zero_sum_moving_tail_bounds hM_dec CJ hCJ hunit
  have hterm_norm : ∀ (X : ℕ) (t : ℝ) (g : ZAll),
      ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)‖ =
      (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ := by
    intro X t g
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp]
    have hre : (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_self]
    rw [hre, Real.exp_zero, mul_one]
  have hterm_norm2 : ∀ (X : ℕ) (t : ℝ) (g : ZAll),
      ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖ =
      (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ := by
    intro X t g
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp]
    have hre : (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
    rw [hre, Real.exp_zero, mul_one]
  have hSwin_bd : ∀ (X : ℕ) (t L : ℝ), 0 ≤ L → ‖Swin X t L‖ ≤ KM * Real.log (2 + |t|) := by
    intro X t L hL
    have hfin := finite_zeros_in_Icc hzeta_ntop CJ hunit (t - L) (t + L)
    set Gbig := hfin.toFinset
    have hG : ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
      intro g hgt hz; rw [Set.Finite.mem_toFinset]; have := abs_le.mp hgt; exact ⟨by linarith, by linarith, hz⟩
    rw [Swin_eq_finset_sum hG]
    set Gfilt : Finset ℝ := Gbig.filter (fun g => |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0)
    set Zfin : Finset ZAll := Gfilt.attach.image (fun g => (⟨g.val, (Finset.mem_filter.mp g.prop).2.2⟩ : ZAll))
    have hsum_eq : ∑ g ∈ Gbig,
        (if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then
          (mZero g : ℂ) * Complex.exp (Complex.I * ((g * Real.log X : ℝ) : ℂ)) * Mfun (g - t)
        else 0) =
        ∑ g ∈ Zfin, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun g hg => (⟨g, (Finset.mem_filter.mp hg).2.2⟩ : ZAll)) ?_ ?_ ?_ ?_
      · intro g hg
        exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
      · intro g1 _ g2 _ h; exact congrArg Subtype.val h
      · intro z hz
        obtain ⟨⟨g, hg⟩, _, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨g, hg, rfl⟩
      · intro _ _; rfl
    rw [hsum_eq]
    calc ‖∑ g ∈ Zfin, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)‖
        ≤ ∑ g ∈ Zfin, ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)‖ :=
          norm_sum_le _ _
      _ = ∑ g ∈ Zfin, (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ := Finset.sum_congr rfl fun g _ => hterm_norm X t g
      _ ≤ ∑' g : ZAll, (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ :=
          (hsumm_norm t).sum_le_tsum Zfin fun _ _ => by positivity
      _ ≤ KM * Real.log (2 + |t|) := htot t
  refine ⟨KM, hKM, ?_, hSwin_bd, ?_⟩
  · intro X hX t
    rw [hexplicit X hX t]
    have hZsumm : Summable (fun g : ZAll =>
        (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) :=
      Summable.of_norm ((hsumm_norm t).congr fun g => (hterm_norm2 X t g).symm)
    have hZbd : ‖∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖ ≤
        KM * Real.log (2 + |t|) := by
      calc _ ≤ ∑' g : ZAll, ‖(mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)‖ :=
            norm_tsum_le_tsum_norm hZsumm.norm
        _ = ∑' g : ZAll, (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ := tsum_congr fun g => hterm_norm2 X t g
        _ ≤ KM * Real.log (2 + |t|) := htot t
    calc ‖Gweight X t 1 - (∑' g : ZAll, _) - Eleft X t‖
        ≤ ‖Gweight X t 1 - (∑' g : ZAll, _)‖ + ‖Eleft X t‖ := norm_sub_le _ _
      _ ≤ (‖Gweight X t 1‖ + ‖∑' g : ZAll, _‖) + ‖Eleft X t‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t|) + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) := by
          linarith [hpole X hX t, hZbd, heleft X hX t]
  · intro X hX t L hL
    -- Rotate by `-cexp (I * t * log X)` (norm 1) to align phases with `Swin X t L`!
    set rot : ℂ := -Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ))
    have hrot_norm : ‖rot‖ = 1 := by
      simp only [rot, norm_neg, Complex.norm_exp]
      have hre : (Complex.I * ((t * Real.log X : ℝ) : ℂ)).re = 0 := by
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, sub_self]
      rw [hre, Real.exp_zero]
    have hZsumm : Summable (fun g : ZAll =>
        (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)) :=
      Summable.of_norm ((hsumm_norm t).congr fun g => (hterm_norm X t g).symm)
    have hZsumm_in : Summable (fun g : ZAll =>
        if |g.val - t| ≤ L then
          (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
        else 0) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun g => by
          split_ifs
          · exact (hterm_norm X t g).le
          · rw [norm_zero]; positivity) (hsumm_norm t))
    have hZsumm_out : Summable (fun g : ZAll =>
        if L < |g.val - t| then
          (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
        else 0) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun g => by
          split_ifs
          · exact (hterm_norm X t g).le
          · rw [norm_zero]; positivity) (hsumm_norm t))
    have hZ_rot : Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) *
        (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) =
        ∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun g => ?_
      have hexp : Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) =
          Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      calc _ = (mZero g.val : ℂ) * (Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ))) * Mfun (g.val - t) := by ring
        _ = _ := by rw [hexp]
    have hZ_split : (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)) =
        Swin X t L +
        ∑' g : ZAll, if L < |g.val - t| then
          (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
        else 0 := by
      have hin_eq : (∑' g : ZAll, if |g.val - t| ≤ L then
          (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
          else 0) = Swin X t L := by
        have hfin := finite_zeros_in_Icc hzeta_ntop CJ hunit (t - L) (t + L)
        set Gbig := hfin.toFinset
        have hG : ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
          intro g hgt hz; rw [Set.Finite.mem_toFinset]; have := abs_le.mp hgt; exact ⟨by linarith, by linarith, hz⟩
        rw [Swin_eq_finset_sum hG]
        set Gfilt : Finset ℝ := Gbig.filter (fun g => |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0)
        set Zfin : Finset ZAll := Gfilt.attach.image (fun g => (⟨g.val, (Finset.mem_filter.mp g.prop).2.2⟩ : ZAll))
        rw [tsum_eq_sum (s := Zfin)]
        · rw [show (∑ g ∈ Gbig, if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then
              (mZero g : ℂ) * Complex.exp (Complex.I * ((g * Real.log X : ℝ) : ℂ)) * Mfun (g - t) else 0) =
              ∑ g ∈ Gfilt, (mZero g : ℂ) * Complex.exp (Complex.I * ((g * Real.log X : ℝ) : ℂ)) * Mfun (g - t) from
              (Finset.sum_filter _ _).symm]
          refine Finset.sum_bij (fun z _ => z.val) ?_ ?_ ?_ ?_
          · intro z hz
            obtain ⟨⟨g, hg⟩, _, rfl⟩ := Finset.mem_image.mp hz
            exact hg
          · intro z1 _ z2 _ h; exact Subtype.ext h
          · intro g hg
            exact ⟨⟨g, (Finset.mem_filter.mp hg).2.2⟩,
              Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
          · intro z hz
            obtain ⟨⟨g, hg⟩, _, rfl⟩ := Finset.mem_image.mp hz
            simp only [(Finset.mem_filter.mp hg).2.1, ↓reduceIte]
        · intro g hg
          split_ifs with hgt
          · exfalso; apply hg
            have hmem : g.val ∈ Gfilt := Finset.mem_filter.mpr ⟨hG g.val hgt g.prop, hgt, g.prop⟩
            exact Finset.mem_image.mpr ⟨⟨g.val, hmem⟩, Finset.mem_attach _ _, rfl⟩
          · rfl
      rw [← hin_eq, ← hZsumm_in.tsum_add hZsumm_out]
      refine tsum_congr fun g => ?_
      by_cases h : |g.val - t| ≤ L
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    let Err : ℂ :=
      (∑' g : ZAll, if L < |g.val - t| then
        (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
      else 0) -
      Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) * Gweight X t 1 +
      Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) * Eleft X t
    have hP_eq : rot * Pfun X t = Swin X t L + Err := by
      rw [hexplicit X hX t]
      dsimp only [rot, Err]
      have h1 : -Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) *
          (Gweight X t 1 -
            (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
            Eleft X t) =
          Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) *
            (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
          Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) * Gweight X t 1 +
          Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ)) * Eleft X t := by ring
      rw [h1, hZ_rot, hZ_split]; ring
    have hP_norm : ‖Pfun X t‖ = ‖Swin X t L + Err‖ := by
      rw [← hP_eq, norm_mul, hrot_norm, one_mul]
    have hErr_bd : ‖Err‖ ≤
        CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 +
        CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) := by
      have hexp1 : ‖Complex.exp (Complex.I * ((t * Real.log X : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        have : (Complex.I * ((t * Real.log X : ℝ) : ℂ)).re = 0 := by
          rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
        rw [this, Real.exp_zero]
      have htail_c : ‖∑' g : ZAll, if L < |g.val - t| then
          (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
          else 0‖ ≤ KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 := by
        calc _ ≤ ∑' g : ZAll, ‖if L < |g.val - t| then
                (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val * Real.log X : ℝ) : ℂ)) * Mfun (g.val - t)
                else 0‖ := norm_tsum_le_tsum_norm hZsumm_out.norm
          _ = ∑' g : ZAll, if L < |g.val - t| then (mZero g.val : ℝ) * ‖Mfun (g.val - t)‖ else 0 :=
              tsum_congr fun g => by
                split_ifs
                · exact hterm_norm X t g
                · exact norm_zero
          _ ≤ KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 := htail t L hL
      dsimp only [Err]
      calc ‖(∑' g : ZAll, _) - Complex.exp _ * Gweight X t 1 + Complex.exp _ * Eleft X t‖
          ≤ ‖(∑' g : ZAll, _) - Complex.exp _ * Gweight X t 1‖ + ‖Complex.exp _ * Eleft X t‖ := norm_add_le _ _
        _ ≤ (‖∑' g : ZAll, _‖ + ‖Complex.exp _ * Gweight X t 1‖) + ‖Complex.exp _ * Eleft X t‖ := by
            gcongr; exact norm_sub_le _ _
        _ = ‖∑' g : ZAll, _‖ + ‖Gweight X t 1‖ + ‖Eleft X t‖ := by
            rw [norm_mul, norm_mul, hexp1, one_mul, one_mul]
        _ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 +
            CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) := by
            linarith [hpole X hX t, htail_c, heleft X hX t]
    set B := CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 +
        CE * (X : ℝ)⁻¹ * Real.log (2 + |t|)
    have hdiff_n : |‖Pfun X t‖ - ‖Swin X t L‖| ≤ ‖Err‖ := by
      rw [hP_norm]
      have h1 := norm_add_le (Swin X t L) Err
      have h2 := norm_sub_norm_le (Swin X t L) (-Err)
      rw [sub_neg_eq_add, norm_neg] at h2
      rw [abs_le]; constructor <;> linarith
    have hsum_n : ‖Pfun X t‖ + ‖Swin X t L‖ ≤ 2 * ‖Swin X t L‖ + ‖Err‖ := by
      rw [hP_norm]; linarith [norm_add_le (Swin X t L) Err]
    have hfact : |‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2| = |‖Pfun X t‖ - ‖Swin X t L‖| * (‖Pfun X t‖ + ‖Swin X t L‖) := by
      rw [show ‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2 = (‖Pfun X t‖ - ‖Swin X t L‖) * (‖Pfun X t‖ + ‖Swin X t L‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg (Pfun X t)) (norm_nonneg (Swin X t L)))]
    rw [hfact]
    have hSbd := hSwin_bd X t L hL
    have hB0 : 0 ≤ B := (norm_nonneg Err).trans hErr_bd
    have hKMlog0 : 0 ≤ KM * Real.log (2 + |t|) := (norm_nonneg _).trans hSbd
    calc |‖Pfun X t‖ - ‖Swin X t L‖| * (‖Pfun X t‖ + ‖Swin X t L‖)
        ≤ ‖Err‖ * (2 * ‖Swin X t L‖ + ‖Err‖) :=
          mul_le_mul hdiff_n hsum_n (by positivity) (norm_nonneg Err)
      _ ≤ B * (2 * (KM * Real.log (2 + |t|)) + B) :=
          mul_le_mul hErr_bd (by linarith) (by positivity) hB0
      _ = 2 * (KM * Real.log (2 + |t|)) * B + B ^ 2 := by ring

/-! #### Part 7C: Asymptotic Growth Helpers and Moment vs Truncated Zero-Sum Comparison -/

lemma Tfun_ge_of_ge {X : ℕ} (hX : 200 ≤ X) : (1200 : ℝ) ≤ Tfun X := by
  unfold Tfun
  have hXr : (200 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  nlinarith [Real.pi_gt_three]

lemma log_Tfun_ge_two {X : ℕ} (hX : 200 ≤ X) : (2 : ℝ) ≤ Real.log (2 + Tfun X) := by
  have hT := Tfun_ge_of_ge hX
  have hexp1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hexp2 : Real.exp 2 < 2 + Tfun X := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h1]; nlinarith [Real.exp_pos 1]
  exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp2.le

lemma log_Tfun_le_four_sqrt_sqrt (X : ℕ) :
    Real.log (2 + Tfun X) ≤ 4 * Real.sqrt (Real.sqrt (2 + Tfun X)) := by
  have hTnn : 0 ≤ Tfun X := by unfold Tfun; positivity
  set y : ℝ := Real.sqrt (Real.sqrt (2 + Tfun X))
  have hy_pos : 0 < y := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hy4 : y ^ 4 = 2 + Tfun X := by
    have h1 : y ^ 2 = Real.sqrt (2 + Tfun X) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (2 + Tfun X)) ^ 2 := by rw [h1]
      _ = 2 + Tfun X := Real.sq_sqrt (by linarith)
  have hlog : Real.log (2 + Tfun X) = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]; ring
  rw [hlog]
  linarith [Real.log_le_sub_one_of_pos hy_pos]

lemma Lfun_bounds {X : ℕ} (hX : 200 ≤ X) :
    4 ≤ Lfun X ∧ Lfun X ≤ 16 * Real.sqrt (2 + Tfun X) ∧ Lfun X ≤ Tfun X / 2 := by
  have hlog := log_Tfun_ge_two hX
  have hT := Tfun_ge_of_ge hX
  have hL_lo : 4 ≤ Lfun X := by unfold Lfun; nlinarith
  have hL_sq : Lfun X ≤ 16 * Real.sqrt (2 + Tfun X) := by
    unfold Lfun
    have h1 := log_Tfun_le_four_sqrt_sqrt X
    have hlog_nn : 0 ≤ Real.log (2 + Tfun X) := by linarith
    calc (Real.log (2 + Tfun X)) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt (2 + Tfun X))) ^ 2 :=
          pow_le_pow_left₀ hlog_nn h1 2
      _ = 16 * (Real.sqrt (Real.sqrt (2 + Tfun X))) ^ 2 := by ring
      _ = 16 * Real.sqrt (2 + Tfun X) := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hL_half : Lfun X ≤ Tfun X / 2 := by
    have hsq : (16 * Real.sqrt (2 + Tfun X)) ^ 2 ≤ (Tfun X / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; nlinarith
    have h1 : 16 * Real.sqrt (2 + Tfun X) ≤ Tfun X / 2 := by
      nlinarith [Real.sqrt_nonneg (2 + Tfun X)]
    linarith
  exact ⟨hL_lo, hL_sq, hL_half⟩

lemma tendsto_eps_zero :
    Tendsto (fun X : ℕ => (Real.log (2 + Tfun X))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) atTop (𝓝 0) := by
  have hT_top : Tendsto (fun X : ℕ => 2 + Tfun X) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi))
  have h1 : Tendsto (fun X : ℕ => (Real.log (2 + Tfun X))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hT_top)
  have h2 : Tendsto (fun X : ℕ => (Real.sqrt (X : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_atTop.mpr fun b => by
      refine ⟨Nat.ceil (max b 0 ^ 2), fun n hn => ?_⟩
      have h1 : max b 0 ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2 : max b 0 ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_sq (le_max_right b 0)]
        exact Real.sqrt_le_sqrt h1
      exact (le_max_left b 0).trans h2)
  simpa using h1.add h2

set_option maxHeartbeats 1200000 in
lemma moment_sub_Rfun_add_diag_tendsto_zero
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hcont_kfun : Continuous kfun)
    (hcont_Mfun : Continuous Mfun)
    (hk_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |kfun t| ≤ C / (1 + |t|) ^ n)
    (hM_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n)
    (homega_even : ∀ t : ℝ, omegafun (-t) = omegafun t)
    (homega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C / (1 + |t|) ^ n)
    (homega_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C * t ^ 2)
    (homega_int : Integrable omegafun)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hpole : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Gweight X t 1‖ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5)
    (CE : ℝ) (hCE : 0 ≤ CE)
    (heleft : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Eleft X t‖ ≤ CE * (X : ℝ)⁻¹ * Real.log (2 + |t|))
    (hexplicit : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      Pfun X t = Gweight X t 1 -
        (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
        Eleft X t) :
    Tendsto (fun X : ℕ => (Ifun X 1 - Ifun X (-1)) / (2 * Tfun X) - (Rfun X + DiagIntegral X)) atTop (𝓝 0) := by
  obtain ⟨KM, hKM, hP_bd, hSwin_bd, hP_split⟩ :=
    norm_Swin_le_and_explicit_split hzeta_ntop hM_dec CJ hCJ hunit CP hCP hpole CE hCE heleft hexplicit
  obtain ⟨Cw6, hCw6, homega6⟩ := homega_dec 6
  obtain ⟨Csq, hCsq, hsq⟩ := homega_sq
  obtain ⟨Ck2, hCk2, hk2⟩ := hk_dec 2
  have hcont_l : Continuous lfun :=
    (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 5)).mul hcont_kfun
  have hcont_omega : Continuous omegafun :=
    (hcont_l.pow 2).mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  set Iom : ℝ := ∫ u : ℝ, |omegafun u|
  have hIom_nn : 0 ≤ Iom := MeasureTheory.integral_nonneg fun _ => abs_nonneg _
  set J3 : ℝ := ∫ t : ℝ, (1 : ℝ) / (1 + |t|) ^ 3
  have hJ3_int : Integrable (fun t : ℝ => (1 : ℝ) / (1 + |t|) ^ 3) :=
    integrable_div_one_add_abs_pow7 1 3 (by norm_num)
  have hJ3_nn : 0 ≤ J3 := MeasureTheory.integral_nonneg fun _ => by positivity
  set C1 : ℝ := 2 * CP + KM + CE
  have hC1_nn : 0 ≤ C1 := by positivity
  set Cout : ℝ := 2 * Cw6 * C1 ^ 2
  set C_R : ℝ := 4 * KM + 4 * CE
  set C_in1 : ℝ := (8 * KM * C_R + 2 * C_R ^ 2) * Iom
  set C_in2 : ℝ := 8 * Csq * KM * CP * J3 + 2 * Csq * CP ^ 2 * J3
  set Ctot : ℝ := Cout + 200 * C_in1 + 200 * C_in2
  have hCtot_nn : 0 ≤ Ctot := by positivity
  refine squeeze_zero_norm' (a := fun X : ℕ => Ctot * ((Real.log (2 + Tfun X))⁻¹ + (Real.sqrt (X : ℝ))⁻¹)) ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨200, fun X hX => ?_⟩
    have hX1 : 1 ≤ X := by omega
    have hXr_pos : (0 : ℝ) < (X : ℝ) := by positivity
    have hT_ge := Tfun_ge_of_ge hX
    have hT_pos : 0 < Tfun X := by linarith
    have hlog_ge := log_Tfun_ge_two hX
    obtain ⟨hL_ge4, hL_sq, hL_half⟩ := Lfun_bounds hX
    set T := Tfun X
    set L := Lfun X
    set TL := T * L
    have hTL_nn : 0 ≤ TL := by positivity
    -- First show `Rfun X + DiagIntegral X = (∫ t in Icc (-TL) TL, ω(t/T) * ‖Swin X t L‖^2) / (2*T)`
    have hSwin_int : IntegrableOn (fun t : ℝ => omegafun (t / T) * ‖Swin X t L‖ ^ 2) (Set.Icc (-TL) TL) := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => omegafun (t / T) * ‖Swin X t L‖ ^ 2)
          (volume.restrict (Set.Icc (-TL) TL)) :=
        ((hcont_omega.comp (continuous_id.div_const T)).aestronglyMeasurable.restrict).mul
          (((measurable_Swin_on_Icc hzeta_ntop hcont_Mfun CJ hunit X TL L hTL_nn (by linarith)).norm).pow 2)
      refine (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := Cw6 * (KM * Real.log (2 + TL)) ^ 2)).mono' hmeas ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
      have ho : |omegafun (t / T)| ≤ Cw6 :=
        (homega6 (t / T)).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg (t / T)])))
      have ht_abs : |t| ≤ TL := abs_le.mpr ht
      have hS : ‖Swin X t L‖ ≤ KM * Real.log (2 + TL) :=
        (hSwin_bd X t L (by linarith)).trans (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)) hKM)
      exact mul_le_mul ho (pow_le_pow_left₀ (norm_nonneg _) hS 2) (by positivity) hCw6
    have hDiag_int : IntegrableOn (fun t : ℝ => omegafun (t / T) * DiagWin t L) (Set.Icc (-TL) TL) := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => omegafun (t / T) * DiagWin t L)
          (volume.restrict (Set.Icc (-TL) TL)) :=
        ((hcont_omega.comp (continuous_id.div_const T)).aestronglyMeasurable.restrict).mul
          (measurable_DiagWin_on_Icc hzeta_ntop hcont_Mfun CJ hunit TL L hTL_nn (by linarith))
      obtain ⟨CM0, hCM0, hM0⟩ := hM_dec 0
      have hfin := finite_zeros_in_Icc hzeta_ntop CJ hunit (-(TL + L)) (TL + L)
      set Gbig := hfin.toFinset
      refine (integrableOn_const (hs := measure_Icc_lt_top.ne)
        (C := Cw6 * (∑ g ∈ Gbig, (mZero g : ℝ) * CM0 ^ 2))).mono' hmeas ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_mul]
      have ho : |omegafun (t / T)| ≤ Cw6 :=
        (homega6 (t / T)).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg (t / T)])))
      have hG : ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
        intro g hgt hz; rw [Set.Finite.mem_toFinset]; have := abs_le.mp hgt
        exact ⟨by linarith [ht.1], by linarith [ht.2], hz⟩
      have hD_nn : 0 ≤ DiagWin t L := by
        rw [DiagWin_eq_finset_sum hG]; exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
      have hD_le : DiagWin t L ≤ ∑ g ∈ Gbig, (mZero g : ℝ) * CM0 ^ 2 := by
        rw [DiagWin_eq_finset_sum hG]
        refine Finset.sum_le_sum fun g _ => ?_
        split_ifs
        · have hMg : ‖Mfun (g - t)‖ ≤ CM0 := by simpa using hM0 (g - t)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hMg 2) (Nat.cast_nonneg _)
        · positivity
      rw [abs_of_nonneg hD_nn]
      exact mul_le_mul ho hD_le hD_nn hCw6
    have hRD_eq : Rfun X + DiagIntegral X =
        (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * ‖Swin X t L‖ ^ 2) / (2 * T) := by
      unfold Rfun DiagIntegral
      dsimp only
      have hnegTL : -Tfun X * Lfun X = -TL := by dsimp only [TL, T, L]; ring
      rw [hnegTL]
      change (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Swin X t L‖ ^ 2 - DiagWin t L)) / (2 * T) +
          (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * DiagWin t L) / (2 * T) = _
      have hsub : (fun t : ℝ => omegafun (t / T) * (‖Swin X t L‖ ^ 2 - DiagWin t L)) =
          (fun t : ℝ => omegafun (t / T) * ‖Swin X t L‖ ^ 2 - omegafun (t / T) * DiagWin t L) := by
        ext t; ring
      rw [hsub, MeasureTheory.integral_sub hSwin_int hDiag_int]
      ring
    -- Integrability of `omegafun (t / T) * ‖Pfun X t‖^2` on `ℝ`
    have hP_int : Integrable (fun t : ℝ => omegafun (t / T) * ‖Pfun X t‖ ^ 2) := by
      obtain ⟨CPc, hCPc, hPc⟩ := norm_Pfun_le_const X
      have hcont : Continuous (fun t : ℝ => omegafun (t / T) * ‖Pfun X t‖ ^ 2) :=
        (hcont_omega.comp (continuous_id.div_const T)).mul ((continuous_Pfun X).norm.pow 2)
      have hdom : Integrable (fun t : ℝ => (Cw6 * CPc ^ 2) / (1 + |t / T|) ^ 6) :=
        (integrable_div_one_add_abs_pow7 (Cw6 * CPc ^ 2) 6 (by norm_num)).comp_div hT_pos.ne'
      refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
      calc |omegafun (t / T)| * ‖Pfun X t‖ ^ 2
          ≤ (Cw6 / (1 + |t / T|) ^ 6) * CPc ^ 2 :=
            mul_le_mul (homega6 (t / T)) (pow_le_pow_left₀ (norm_nonneg _) (hPc t) 2) (by positivity) (by positivity)
        _ = (Cw6 * CPc ^ 2) / (1 + |t / T|) ^ 6 := by ring
    -- Split `∫_ℝ = ∫_{Icc (-TL) TL} + ∫_{(Icc (-TL) TL)ᶜ}`
    have hsplit_eq : (Ifun X 1 - Ifun X (-1)) / (2 * T) - (Rfun X + DiagIntegral X) =
        (∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2) / (2 * T) +
        (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)) / (2 * T) := by
      rw [Ifun_sub_eq_integral_omegafun hcont_kfun hk_dec homega_even hX1, hRD_eq]
      have hsp := (MeasureTheory.integral_add_compl (s := Set.Icc (-TL) TL) measurableSet_Icc hP_int).symm
      rw [hsp]
      have hsub_in : (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * ‖Pfun X t‖ ^ 2) -
          (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * ‖Swin X t L‖ ^ 2) =
          ∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2) := by
        rw [← MeasureTheory.integral_sub hP_int.integrableOn hSwin_int]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => by ring
      linear_combination hsub_in / (2 * T)
    rw [Real.norm_eq_abs, hsplit_eq]
    -- Bound 1: Outer tail `|(∫_{(Icc (-TL) TL)ᶜ} ω(t/T) * ‖Pfun X t‖^2) / (2 * T)| ≤ Cout * (log(2+T))⁻¹`
    have hout_bd : |(∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2) / (2 * T)| ≤
        Cout * (Real.log (2 + T))⁻¹ := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * T)]
      have hdom_u : IntegrableOn (fun u : ℝ =>
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6 + 1 / (1 + |u|) ^ 4))
          (Set.Icc (-L) L)ᶜ :=
        (((integrable_div_one_add_abs_pow7 ((Real.log (2 + T)) ^ 2) 6 (by norm_num)).add
          (integrable_div_one_add_abs_pow7 1 4 (by norm_num))).const_mul (2 * Cw6 * C1 ^ 2)).integrableOn
      have hpt_out : ∀ t ∈ (Set.Icc (-TL) TL)ᶜ,
          ‖omegafun (t / T) * ‖Pfun X t‖ ^ 2‖ ≤
            (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |t / T|) ^ 6 + 1 / (1 + |t / T|) ^ 4) := by
        intro t ht
        have ht_gt : TL < |t| := by
          by_contra hle; push Not at hle; exact ht (abs_le.mp hle)
        have hP_t := hP_bd X hX1 t
        have hpole_le : CP * Real.sqrt X / (1 + |t|) ^ 5 ≤ 2 * CP * Real.log (2 + |t|) := by
          have hX_real : (200 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
          have hsqX : Real.sqrt X ≤ (1 + |t|) ^ 5 := by
            have h1 : Real.sqrt X ≤ (X : ℝ) := by
              calc Real.sqrt X ≤ Real.sqrt ((X : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
                _ = (X : ℝ) := Real.sqrt_sq hXr_pos.le
            have h2 : (X : ℝ) ≤ 1 + |t| := by
              have : (X : ℝ) ≤ T := by unfold T Tfun; nlinarith [Real.pi_gt_three]
              nlinarith
            exact h1.trans (h2.trans (le_self_pow₀ (by linarith [abs_nonneg t]) (by norm_num)))
          have hfrac : Real.sqrt X / (1 + |t|) ^ 5 ≤ 1 := (div_le_one (by positivity)).mpr hsqX
          have hlog_ge1 : (1 / 2 : ℝ) ≤ Real.log (2 + |t|) :=
            (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
              (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
          calc CP * Real.sqrt X / (1 + |t|) ^ 5 = CP * (Real.sqrt X / (1 + |t|) ^ 5) := by ring
            _ ≤ CP * 1 := mul_le_mul_of_nonneg_left hfrac hCP
            _ ≤ 2 * CP * Real.log (2 + |t|) := by nlinarith
        have hXinv : (X : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hX1)
        have hlogt_nn : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
        have hP_log : ‖Pfun X t‖ ≤ C1 * Real.log (2 + |t|) := by
          have hE : CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) ≤ CE * Real.log (2 + |t|) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXinv hCE) hlogt_nn
            linarith
          dsimp only [C1]; linarith
        have hlog_split : Real.log (2 + |t|) ≤ Real.log (2 + T) + (1 + |t / T|) := by
          have hmul : 2 + |t| ≤ (2 + T) * (2 + |t / T|) := by
            have habs : |t| = T * |t / T| := by
              rw [abs_div, abs_of_pos hT_pos, mul_div_cancel₀ _ hT_pos.ne']
            rw [habs]; nlinarith [abs_nonneg (t / T)]
          have h1 : Real.log (2 + |t|) ≤ Real.log (2 + T) + Real.log (2 + |t / T|) := by
            calc Real.log (2 + |t|) ≤ Real.log ((2 + T) * (2 + |t / T|)) :=
                  Real.log_le_log (by linarith [abs_nonneg t]) hmul
              _ = Real.log (2 + T) + Real.log (2 + |t / T|) :=
                  Real.log_mul (by linarith) (by linarith [abs_nonneg (t / T)])
          have h2 : Real.log (2 + |t / T|) ≤ 1 + |t / T| := by
            linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg (t / T)] : 0 < 2 + |t / T|)]
          linarith
        have hP_sq : ‖Pfun X t‖ ^ 2 ≤ 2 * C1 ^ 2 * ((Real.log (2 + T)) ^ 2 + (1 + |t / T|) ^ 2) := by
          have h1 : ‖Pfun X t‖ ^ 2 ≤ (C1 * (Real.log (2 + T) + (1 + |t / T|))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hP_log.trans (mul_le_mul_of_nonneg_left hlog_split hC1_nn)) 2
          nlinarith [sq_nonneg (Real.log (2 + T) - (1 + |t / T|)), sq_nonneg C1]
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
        calc |omegafun (t / T)| * ‖Pfun X t‖ ^ 2
            ≤ (Cw6 / (1 + |t / T|) ^ 6) * (2 * C1 ^ 2 * ((Real.log (2 + T)) ^ 2 + (1 + |t / T|) ^ 2)) :=
              mul_le_mul (homega6 (t / T)) hP_sq (by positivity) (by positivity)
          _ = (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |t / T|) ^ 6 + 1 / (1 + |t / T|) ^ 4) := by
              have hne : 1 + |t / T| ≠ 0 := by linarith [abs_nonneg (t / T)]
              field_simp [hne]
      have hdom_t : IntegrableOn (fun t : ℝ =>
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |t / T|) ^ 6 + 1 / (1 + |t / T|) ^ 4))
          (Set.Icc (-TL) TL)ᶜ :=
        ((((integrable_div_one_add_abs_pow7 ((Real.log (2 + T)) ^ 2) 6 (by norm_num)).add
          (integrable_div_one_add_abs_pow7 1 4 (by norm_num))).const_mul (2 * Cw6 * C1 ^ 2)).comp_div hT_pos.ne').integrableOn
      have hint_chg : ∫ t in (Set.Icc (-TL) TL)ᶜ,
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |t / T|) ^ 6 + 1 / (1 + |t / T|) ^ 4) =
          T * ∫ u in (Set.Icc (-L) L)ᶜ,
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6 + 1 / (1 + |u|) ^ 4) := by
        let g : ℝ → ℝ := fun u =>
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6 + 1 / (1 + |u|) ^ 4)
        have hpre : (fun t : ℝ => t / T) ⁻¹' (Set.Icc (-L) L)ᶜ = (Set.Icc (-TL) TL)ᶜ := by
          ext t; simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, div_le_iff₀ hT_pos, le_div_iff₀ hT_pos]
          constructor <;> intro h h' <;> apply h <;> constructor <;> linarith [h'.1, h'.2]
        rw [← hpre]
        have hchg := MeasureTheory.Measure.integral_comp_mul_left (g := Set.indicator (Set.Icc (-L) L)ᶜ g) T⁻¹
        simp only [abs_inv, inv_inv, abs_of_pos hT_pos, smul_eq_mul] at hchg
        have hmeas_pre : MeasurableSet ((fun t : ℝ => t / T) ⁻¹' (Set.Icc (-L) L)ᶜ) :=
          measurableSet_Icc.compl.preimage (measurable_id.div_const T)
        rw [← MeasureTheory.integral_indicator hmeas_pre,
          ← MeasureTheory.integral_indicator measurableSet_Icc.compl]
        convert hchg using 1
        congr 1; ext t
        have hdiv : T⁻¹ * t = t / T := by rw [div_eq_mul_inv, mul_comm]
        rw [hdiv]; rfl
      have hval_u : ∫ u in (Set.Icc (-L) L)ᶜ,
          (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6 + 1 / (1 + |u|) ^ 4) =
          (2 * Cw6 * C1 ^ 2) *
            ((Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) + 2 / (3 * (1 + L) ^ 3)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add
            ((integrable_div_one_add_abs_pow7 ((Real.log (2 + T)) ^ 2) 6 (by norm_num)).integrableOn)
            ((integrable_div_one_add_abs_pow7 1 4 (by norm_num)).integrableOn)]
        have h1 : ∫ u in (Set.Icc (-L) L)ᶜ, (Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6 =
            (Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) := by
          have : (fun u : ℝ => (Real.log (2 + T)) ^ 2 / (1 + |u|) ^ 6) =
              fun u => (Real.log (2 + T)) ^ 2 * (1 / (1 + |u|) ^ 6) := by ext u; ring
          rw [this, MeasureTheory.integral_const_mul, integral_compl_Icc_inv_one_add_abs_pow (by linarith) (by norm_num)]
          norm_num
        have h2 : ∫ u in (Set.Icc (-L) L)ᶜ, (1 : ℝ) / (1 + |u|) ^ 4 = 2 / (3 * (1 + L) ^ 3) := by
          rw [integral_compl_Icc_inv_one_add_abs_pow (by linarith) (by norm_num)]; norm_num
        rw [h1, h2]
      have hmain : |∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2| ≤
          T * ((2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) + 2 / (3 * (1 + L) ^ 3))) := by
        calc _ ≤ ∫ t in (Set.Icc (-TL) TL)ᶜ, ‖omegafun (t / T) * ‖Pfun X t‖ ^ 2‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ t in (Set.Icc (-TL) TL)ᶜ,
                (2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 / (1 + |t / T|) ^ 6 + 1 / (1 + |t / T|) ^ 4) :=
              MeasureTheory.setIntegral_mono_on hP_int.norm.integrableOn hdom_t measurableSet_Icc.compl hpt_out
          _ = _ := by rw [hint_chg, hval_u]
      rw [div_le_iff₀ (by positivity)]
      have hsmall : (Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) + 2 / (3 * (1 + L) ^ 3) ≤
          2 * (Real.log (2 + T))⁻¹ := by
        have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
        have h1L : L ≤ 1 + L := by linarith
        have hlog1 : (1 : ℝ) ≤ Real.log (2 + T) := by linarith
        have ha : (Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) ≤ (Real.log (2 + T))⁻¹ := by
          have h5 : L ^ 5 ≤ (1 + L) ^ 5 := pow_le_pow_left₀ (by linarith) h1L 5
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          have hge : (Real.log (2 + T)) ^ 3 ≤ (1 + L) ^ 5 := by
            have : (Real.log (2 + T)) ^ 3 ≤ (Real.log (2 + T)) ^ 10 := pow_le_pow_right₀ hlog1 (by norm_num)
            have hL5 : L ^ 5 = (Real.log (2 + T)) ^ 10 := by rw [hL_eq]; ring
            linarith
          have : (Real.log (2 + T)) ^ 2 * 2 * Real.log (2 + T) = 2 * (Real.log (2 + T)) ^ 3 := by ring
          have hinv : (Real.log (2 + T))⁻¹ * (5 * (1 + L) ^ 5) = 5 * (1 + L) ^ 5 / Real.log (2 + T) := by ring
          rw [hinv, le_div_iff₀ (by linarith)]
          nlinarith
        have hb : 2 / (3 * (1 + L) ^ 3) ≤ (Real.log (2 + T))⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          have hinv : (Real.log (2 + T))⁻¹ * (3 * (1 + L) ^ 3) = 3 * (1 + L) ^ 3 / Real.log (2 + T) := by ring
          rw [hinv, le_div_iff₀ (by linarith)]
          have h3 : (Real.log (2 + T)) ^ 6 ≤ (1 + L) ^ 3 := by
            have hL3 : L ^ 3 = (Real.log (2 + T)) ^ 6 := by rw [hL_eq]; ring
            have := pow_le_pow_left₀ (by linarith) h1L 3
            linarith
          have h16 : Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 6 := le_self_pow₀ hlog1 (by norm_num)
          nlinarith
        linarith
      calc |∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2|
          ≤ T * ((2 * Cw6 * C1 ^ 2) * ((Real.log (2 + T)) ^ 2 * (2 / (5 * (1 + L) ^ 5)) + 2 / (3 * (1 + L) ^ 3))) := hmain
        _ ≤ T * ((2 * Cw6 * C1 ^ 2) * (2 * (Real.log (2 + T))⁻¹)) := by gcongr
        _ = Cout * (Real.log (2 + T))⁻¹ * (2 * T) := by dsimp only [Cout]; ring
    -- Bound 2: Inner difference `|(∫_{Icc (-TL) TL} ω(t/T) * (‖P‖^2 - ‖S‖^2)) / (2 * T)| ≤ (200*C_in1 + 200*C_in2) * eps X`
    have hin_bd : |(∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)) / (2 * T)| ≤
        (200 * C_in1 + 200 * C_in2) * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * T)]
      -- Uniform `Rest` bound on `t ∈ [-TL, TL]`
      set Rest : ℝ := C_R * ((Real.log (2 + T))⁻¹ ^ 9 + (Real.log (2 + T)) / (X : ℝ))
      have hRest_nn : 0 ≤ Rest := by positivity
      have hlog_in : ∀ t ∈ Set.Icc (-TL) TL, Real.log (2 + |t| + L) ≤ 4 * Real.log (2 + T) := by
        intro t ht
        have ht_le : |t| ≤ TL := abs_le.mpr ht
        have hle : 2 + |t| + L ≤ (2 + T) ^ 4 := by
          have hL_le : L ≤ 2 + T := by linarith
          have hsq : 2 + |t| + L ≤ (2 + T) ^ 2 := by dsimp only [TL] at ht_le; nlinarith
          exact hsq.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
        calc Real.log (2 + |t| + L) ≤ Real.log ((2 + T) ^ 4) := Real.log_le_log (by linarith [abs_nonneg t]) hle
          _ = 4 * Real.log (2 + T) := by rw [Real.log_pow]; ring
      have hpt_in : ∀ t ∈ Set.Icc (-TL) TL,
          ‖omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)‖ ≤
            (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)| +
            (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
              2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3) := by
        intro t ht
        have hlg := hlog_in t ht
        have hlg0 : Real.log (2 + |t|) ≤ 4 * Real.log (2 + T) :=
          (Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)).trans hlg
        have hRest_pt : KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) ≤ Rest := by
          have h1 : KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 ≤ 4 * KM * (Real.log (2 + T))⁻¹ ^ 9 := by
            have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
            have hpow5 : (Real.log (2 + T)) ^ 10 ≤ (1 + L) ^ 5 := by
              have := pow_le_pow_left₀ (by linarith) (show L ≤ 1 + L by linarith) 5
              rw [show L ^ 5 = (Real.log (2 + T)) ^ 10 by rw [hL_eq]; ring] at this
              exact this
            calc KM * Real.log (2 + |t| + L) / (1 + L) ^ 5
                ≤ KM * (4 * Real.log (2 + T)) / (Real.log (2 + T)) ^ 10 := by
                  apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hpow5
              _ = 4 * KM * (Real.log (2 + T))⁻¹ ^ 9 := by
                  have hne : Real.log (2 + T) ≠ 0 := by linarith
                  field_simp [hne]
          have h2 : CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) ≤ 4 * CE * (Real.log (2 + T) / (X : ℝ)) := by
            have hmul : CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) ≤ CE * (X : ℝ)⁻¹ * (4 * Real.log (2 + T)) := by gcongr
            rw [div_eq_mul_inv]; linarith
          dsimp only [Rest, C_R]
          nlinarith [pow_nonneg (inv_nonneg.mpr (show 0 ≤ Real.log (2 + T) by linarith)) 9,
            div_nonneg (show 0 ≤ Real.log (2 + T) by linarith) hXr_pos.le]
        have hsp := hP_split X hX1 t L (by linarith)
        set A := CP * Real.sqrt X / (1 + |t|) ^ 5
        have hA_nn : 0 ≤ A := by positivity
        have hS_le : KM * Real.log (2 + |t|) ≤ 4 * KM * Real.log (2 + T) := by
          have := mul_le_mul_of_nonneg_left hlg0 hKM; linarith
        have hdiff_le : |‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2| ≤
            (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) +
            (8 * KM * Real.log (2 + T) * A + 2 * A ^ 2) := by
          set E0 := A + (KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 + CE * (X : ℝ)⁻¹ * Real.log (2 + |t|))
          have hE0_le : E0 ≤ A + Rest := by dsimp only [E0]; linarith
          have hE0_nn : 0 ≤ E0 := by
            have : 0 ≤ Real.log (2 + |t| + L) := Real.log_nonneg (by linarith [abs_nonneg t])
            have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
            dsimp only [E0]; positivity
          have hsq_le : E0 ^ 2 ≤ 2 * A ^ 2 + 2 * Rest ^ 2 := by
            have h1 : E0 ^ 2 ≤ (A + Rest) ^ 2 := pow_le_pow_left₀ hE0_nn hE0_le 2
            nlinarith [sq_nonneg (A - Rest)]
          have hlin_le : 2 * (KM * Real.log (2 + |t|)) * E0 ≤
              8 * KM * Real.log (2 + T) * A + 8 * KM * Real.log (2 + T) * Rest := by
            have := mul_le_mul hS_le hE0_le hE0_nn (by positivity)
            linarith
          have hE0_eq : CP * Real.sqrt X / (1 + |t|) ^ 5 + KM * Real.log (2 + |t| + L) / (1 + L) ^ 5 +
              CE * (X : ℝ)⁻¹ * Real.log (2 + |t|) = E0 := by dsimp only [E0, A]; ring
          rw [hE0_eq] at hsp
          linarith
        -- Multiply `A` terms by `|ω(t/T)| ≤ Csq * t^2 / T^2`
        have ho_sq : |omegafun (t / T)| ≤ Csq * (t ^ 2 / T ^ 2) := by
          have := hsq (t / T); rwa [div_pow] at this
        have ht2_le : t ^ 2 ≤ (1 + |t|) ^ 2 := by
          calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
            _ ≤ (1 + |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) (by linarith) 2
        have hA_mul : |omegafun (t / T)| * A ≤ (Csq * CP * Real.sqrt X / T ^ 2) * (1 / (1 + |t|) ^ 3) := by
          calc |omegafun (t / T)| * A
              ≤ (Csq * (t ^ 2 / T ^ 2)) * (CP * Real.sqrt X / (1 + |t|) ^ 5) :=
                mul_le_mul_of_nonneg_right ho_sq hA_nn
            _ ≤ (Csq * ((1 + |t|) ^ 2 / T ^ 2)) * (CP * Real.sqrt X / (1 + |t|) ^ 5) := by gcongr
            _ = (Csq * CP * Real.sqrt X / T ^ 2) * (1 / (1 + |t|) ^ 3) := by
                have hne : 1 + |t| ≠ 0 := by linarith [abs_nonneg t]
                field_simp [hne, hT_pos.ne']
        have hA2_mul : |omegafun (t / T)| * A ^ 2 ≤ (Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3) := by
          have hA2_eq : A ^ 2 = CP ^ 2 * (X : ℝ) / (1 + |t|) ^ 10 := by
            dsimp only [A]; rw [div_pow, mul_pow, Real.sq_sqrt hXr_pos.le]; ring
          rw [hA2_eq]
          have hpow : (1 + |t|) ^ 3 ≤ (1 + |t|) ^ 8 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
          calc |omegafun (t / T)| * (CP ^ 2 * (X : ℝ) / (1 + |t|) ^ 10)
              ≤ (Csq * ((1 + |t|) ^ 2 / T ^ 2)) * (CP ^ 2 * (X : ℝ) / (1 + |t|) ^ 10) := by
                apply mul_le_mul_of_nonneg_right (ho_sq.trans (by gcongr)) (by positivity)
            _ = (Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 8) := by
                have hne : 1 + |t| ≠ 0 := by linarith [abs_nonneg t]
                field_simp [hne, hT_pos.ne']
            _ ≤ (Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3) := by
                gcongr
        rw [Real.norm_eq_abs, abs_mul]
        calc |omegafun (t / T)| * |‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2|
            ≤ |omegafun (t / T)| * ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) +
                (8 * KM * Real.log (2 + T) * A + 2 * A ^ 2)) :=
              mul_le_mul_of_nonneg_left hdiff_le (abs_nonneg _)
          _ = (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)| +
              8 * KM * Real.log (2 + T) * (|omegafun (t / T)| * A) +
              2 * (|omegafun (t / T)| * A ^ 2) := by ring
          _ ≤ (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)| +
              8 * KM * Real.log (2 + T) * ((Csq * CP * Real.sqrt X / T ^ 2) * (1 / (1 + |t|) ^ 3)) +
              2 * ((Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3)) := by gcongr
          _ = _ := by ring
      have hint_diff_in : IntegrableOn (fun t : ℝ => omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2))
          (Set.Icc (-TL) TL) := by
        have heq : (fun t : ℝ => omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)) =
            (fun t : ℝ => omegafun (t / T) * ‖Pfun X t‖ ^ 2 - omegafun (t / T) * ‖Swin X t L‖ ^ 2) := by
          ext t; ring
        rw [heq]; exact hP_int.integrableOn.sub hSwin_int
      have hint_dom1 : Integrable (fun t : ℝ => (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)|) :=
        (((homega_int.norm).comp_div hT_pos.ne').const_mul (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2)).congr
          (Filter.Eventually.of_forall fun t => by simp only [Function.comp_apply, Real.norm_eq_abs])
      have hint_dom2 : Integrable (fun t : ℝ =>
          (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
            2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3)) :=
        hJ3_int.const_mul _
      have hint_om_t : ∫ t : ℝ, |omegafun (t / T)| = T * Iom := by
        have hchg := MeasureTheory.Measure.integral_comp_mul_left (g := fun u : ℝ => |omegafun u|) T⁻¹
        simp only [abs_inv, inv_inv, abs_of_pos hT_pos, smul_eq_mul] at hchg
        have heq : (fun t : ℝ => |omegafun (t / T)|) = fun t : ℝ => |omegafun (T⁻¹ * t)| := by
          ext t; rw [div_eq_mul_inv, mul_comm]
        rw [heq, hchg]
      have htot_in : |∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)| ≤
          (8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * (T * Iom) +
          (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
            2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * J3 := by
        calc _ ≤ ∫ t in Set.Icc (-TL) TL, ‖omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ t in Set.Icc (-TL) TL,
                ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)| +
                (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
                  2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3)) :=
              MeasureTheory.setIntegral_mono_on hint_diff_in.norm
                (hint_dom1.add hint_dom2).integrableOn measurableSet_Icc hpt_in
          _ ≤ ∫ t : ℝ,
                ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * |omegafun (t / T)| +
                (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
                  2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * (1 / (1 + |t|) ^ 3)) :=
              MeasureTheory.setIntegral_le_integral (hint_dom1.add hint_dom2)
                (Filter.Eventually.of_forall fun t => by positivity)
          _ = _ := by
              rw [MeasureTheory.integral_add hint_dom1 hint_dom2,
                MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hint_om_t]
      -- Now simplify each factor into `200 * C_in1 * eps` and `200 * C_in2 * eps`
      have hsq_pos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXr_pos
      have hX200r : (200 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have hsq_div : Real.sqrt (X : ℝ) / (X : ℝ) = (Real.sqrt (X : ℝ))⁻¹ := by
        rw [div_eq_iff hXr_pos.ne']
        calc Real.sqrt (X : ℝ) = (Real.sqrt (X : ℝ))⁻¹ * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ)) := by
              field_simp [hsq_pos.ne']
          _ = (Real.sqrt (X : ℝ))⁻¹ * (X : ℝ) := by rw [Real.mul_self_sqrt hXr_pos.le]
      have hlog_sq_div_X : (Real.log (2 + T)) ^ 2 / (X : ℝ) ≤ 48 * (Real.sqrt (X : ℝ))⁻¹ := by
        have h2T : 2 + T ≤ 9 * (X : ℝ) := by
          unfold T Tfun
          have hpi : 2 * Real.pi * (X : ℝ) ≤ 8 * (X : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hXr_pos.le
          linarith
        have hsq9 : Real.sqrt (2 + T) ≤ 3 * Real.sqrt (X : ℝ) := by
          calc Real.sqrt (2 + T) ≤ Real.sqrt (9 * (X : ℝ)) := Real.sqrt_le_sqrt h2T
            _ = 3 * Real.sqrt (X : ℝ) := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by norm_num]
        have hL_le : (Real.log (2 + T)) ^ 2 ≤ 48 * Real.sqrt (X : ℝ) := by
          have : (Real.log (2 + T)) ^ 2 = L := rfl
          linarith
        calc (Real.log (2 + T)) ^ 2 / (X : ℝ) ≤ (48 * Real.sqrt (X : ℝ)) / (X : ℝ) :=
              div_le_div_of_nonneg_right hL_le hXr_pos.le
          _ = 48 * (Real.sqrt (X : ℝ) / (X : ℝ)) := mul_div_assoc _ _ _
          _ = 48 * (Real.sqrt (X : ℝ))⁻¹ := by rw [hsq_div]
      have hlog_div_X : Real.log (2 + T) / (X : ℝ) ≤ 48 * (Real.sqrt (X : ℝ))⁻¹ := by
        have h1 : Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
        exact (div_le_div_of_nonneg_right h1 hXr_pos.le).trans hlog_sq_div_X
      have hinv9 : (Real.log (2 + T))⁻¹ ^ 9 ≤ (Real.log (2 + T))⁻¹ := by
        have hle1 : (Real.log (2 + T))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have hnn : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
        calc (Real.log (2 + T))⁻¹ ^ 9 = (Real.log (2 + T))⁻¹ * (Real.log (2 + T))⁻¹ ^ 8 := by ring
          _ ≤ (Real.log (2 + T))⁻¹ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hnn hle1) hnn
          _ = (Real.log (2 + T))⁻¹ := mul_one _
      have hlog_inv9 : Real.log (2 + T) * (Real.log (2 + T))⁻¹ ^ 9 ≤ (Real.log (2 + T))⁻¹ := by
        have hne : Real.log (2 + T) ≠ 0 := by linarith
        have heq : Real.log (2 + T) * (Real.log (2 + T))⁻¹ ^ 9 = (Real.log (2 + T))⁻¹ ^ 8 := by
          field_simp [hne]
        rw [heq]
        have hle1 : (Real.log (2 + T))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have hnn : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
        calc (Real.log (2 + T))⁻¹ ^ 8 = (Real.log (2 + T))⁻¹ * (Real.log (2 + T))⁻¹ ^ 7 := by ring
          _ ≤ (Real.log (2 + T))⁻¹ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hnn hle1) hnn
          _ = (Real.log (2 + T))⁻¹ := mul_one _
      have hinv_log_nn : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
      have hRest_sq : Rest ^ 2 ≤ 240 * C_R ^ 2 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        have h1 : (Real.log (2 + T))⁻¹ ^ 9 + Real.log (2 + T) / (X : ℝ) ≤ 5 := by
          have ha : (Real.log (2 + T))⁻¹ ^ 9 ≤ 1 := hinv9.trans (inv_le_one_of_one_le₀ (by linarith))
          have hb : (Real.sqrt (X : ℝ))⁻¹ ≤ 1 / 14 := by
            rw [inv_le_comm₀ hsq_pos (by norm_num), one_div, inv_inv]
            have : (196 : ℝ) ≤ (X : ℝ) := by linarith
            calc (14 : ℝ) = Real.sqrt 196 := by rw [show (196 : ℝ) = 14 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
              _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt this
          linarith [hlog_div_X, ha, hb]
        have h2 : (Real.log (2 + T))⁻¹ ^ 9 + Real.log (2 + T) / (X : ℝ) ≤
            48 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by linarith [hinv9, hlog_div_X, hinv_log_nn]
        have hnn : 0 ≤ (Real.log (2 + T))⁻¹ ^ 9 + Real.log (2 + T) / (X : ℝ) := by positivity
        dsimp only [Rest]
        rw [mul_pow]
        have hsq2 : ((Real.log (2 + T))⁻¹ ^ 9 + Real.log (2 + T) / (X : ℝ)) ^ 2 ≤
            240 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
          rw [sq]
          calc _ ≤ 5 * (48 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹)) := mul_le_mul h1 h2 hnn (by norm_num)
            _ = 240 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by ring
        have := mul_le_mul_of_nonneg_left hsq2 (sq_nonneg C_R)
        linarith
      have hlog_Rest : Real.log (2 + T) * Rest ≤ 48 * C_R * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        dsimp only [Rest]
        have hCR0 : 0 ≤ C_R := by positivity
        have heq : Real.log (2 + T) * (C_R * ((Real.log (2 + T))⁻¹ ^ 9 + Real.log (2 + T) / (X : ℝ))) =
            C_R * (Real.log (2 + T) * (Real.log (2 + T))⁻¹ ^ 9 + (Real.log (2 + T)) ^ 2 / (X : ℝ)) := by ring
        rw [heq]
        have hsum : Real.log (2 + T) * (Real.log (2 + T))⁻¹ ^ 9 + (Real.log (2 + T)) ^ 2 / (X : ℝ) ≤
            48 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by linarith [hlog_inv9, hlog_sq_div_X, hinv_log_nn]
        have := mul_le_mul_of_nonneg_left hsum hCR0
        linarith
      -- First piece (divided by `2 * T`): `((8*KM*log*Rest + 2*Rest^2) * T * Iom) / (2 * T) ≤ 200 * C_in1 * eps`
      have hpiece1 : ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * (T * Iom)) / (2 * T) ≤
          200 * C_in1 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        have hcancel : ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * (T * Iom)) / (2 * T) =
            (4 * KM * (Real.log (2 + T) * Rest) + Rest ^ 2) * Iom := by field_simp [hT_pos.ne']; ring
        rw [hcancel]
        have hinner : 4 * KM * (Real.log (2 + T) * Rest) + Rest ^ 2 ≤
            200 * (8 * KM * C_R + 2 * C_R ^ 2) * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
          have h1 : 4 * KM * (Real.log (2 + T) * Rest) ≤
              192 * KM * C_R * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
            have := mul_le_mul_of_nonneg_left hlog_Rest (by positivity : 0 ≤ 4 * KM); linarith
          have hpad1 : 0 ≤ (1600 - 192) * KM * C_R * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by positivity
          have hpad2 : 0 ≤ (400 - 240) * C_R ^ 2 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by positivity
          linarith [h1, hRest_sq, hpad1, hpad2]
        dsimp only [C_in1]
        have := mul_le_mul_of_nonneg_right hinner hIom_nn
        linarith
      -- Second piece (divided by `2 * T`): `((8*Csq*KM*log*CP*√X/T^2 + 2*Csq*CP^2*X/T^2) * J3) / (2*T) ≤ 200*C_in2*eps`
      have hpiece2 : ((8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
            2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * J3) / (2 * T) ≤
          200 * C_in2 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        have hT_geX : (X : ℝ) ≤ T := by
          unfold T Tfun
          have := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi) hXr_pos.le
          linarith
        have hX_le_sq : (X : ℝ) ≤ (X : ℝ) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_right hXr_pos.le (by linarith)
        have hsq_le_X : Real.sqrt (X : ℝ) ≤ (X : ℝ) :=
          (Real.sqrt_le_sqrt hX_le_sq).trans_eq (Real.sqrt_sq hXr_pos.le)
        have hf1 : Real.log (2 + T) * Real.sqrt X / (2 * T ^ 3) ≤ 48 * (Real.sqrt (X : ℝ))⁻¹ := by
          have hlog_le_X : Real.log (2 + T) ≤ 48 * (X : ℝ) := by
            have h1 : Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 2 := by
              rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
            have h2 := (div_le_iff₀ hXr_pos).mp hlog_sq_div_X
            have h3 : 48 * (Real.sqrt (X : ℝ))⁻¹ * (X : ℝ) = 48 * Real.sqrt (X : ℝ) := by
              calc 48 * (Real.sqrt (X : ℝ))⁻¹ * (X : ℝ)
                  = 48 * ((Real.sqrt (X : ℝ))⁻¹ * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ))) := by
                    rw [Real.mul_self_sqrt hXr_pos.le]; ring
                _ = 48 * Real.sqrt (X : ℝ) := by field_simp [hsq_pos.ne']
            linarith
          have hT3 : (X : ℝ) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hXr_pos.le hT_geX 3
          calc Real.log (2 + T) * Real.sqrt X / (2 * T ^ 3)
              ≤ (48 * (X : ℝ)) * Real.sqrt X / (X : ℝ) ^ 3 := by
                apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (by linarith [pow_nonneg hT_pos.le 3])
            _ = 48 * (Real.sqrt (X : ℝ) / (X : ℝ)) * (X : ℝ)⁻¹ := by
                have hX3 : (X : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hXr_pos.ne'
                field_simp [hXr_pos.ne', hX3]
            _ = 48 * (Real.sqrt (X : ℝ))⁻¹ * (X : ℝ)⁻¹ := by rw [hsq_div]
            _ ≤ 48 * (Real.sqrt (X : ℝ))⁻¹ * 1 := by
                gcongr; exact inv_le_one_of_one_le₀ (by exact_mod_cast hX1)
            _ = 48 * (Real.sqrt (X : ℝ))⁻¹ := mul_one _
        have hf2 : (X : ℝ) / (2 * T ^ 3) ≤ (Real.sqrt (X : ℝ))⁻¹ := by
          have hT3 : (X : ℝ) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hXr_pos.le hT_geX 3
          have hsqX : Real.sqrt (X : ℝ) ≤ (X : ℝ) ^ 2 := hsq_le_X.trans hX_le_sq
          calc (X : ℝ) / (2 * T ^ 3) ≤ (X : ℝ) / (X : ℝ) ^ 3 := by
                apply div_le_div_of_nonneg_left hXr_pos.le (by positivity) (by linarith [pow_nonneg hT_pos.le 3])
            _ = 1 / (X : ℝ) ^ 2 := by
                rw [div_eq_div_iff (pow_ne_zero 3 hXr_pos.ne') (pow_ne_zero 2 hXr_pos.ne')]; ring
            _ ≤ 1 / Real.sqrt (X : ℝ) := div_le_div_of_nonneg_left zero_le_one hsq_pos hsqX
            _ = (Real.sqrt (X : ℝ))⁻¹ := one_div _
        have heq : ((8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
            2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * J3) / (2 * T) =
            (8 * Csq * KM * CP * J3) * (Real.log (2 + T) * Real.sqrt X / (2 * T ^ 3)) +
            (2 * Csq * CP ^ 2 * J3) * ((X : ℝ) / (2 * T ^ 3)) := by field_simp [hT_pos.ne']
        rw [heq]
        have h1 : (8 * Csq * KM * CP * J3) * (Real.log (2 + T) * Real.sqrt X / (2 * T ^ 3)) ≤
            (8 * Csq * KM * CP * J3) * (48 * (Real.sqrt (X : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hf1 (by positivity)
        have h2 : (2 * Csq * CP ^ 2 * J3) * ((X : ℝ) / (2 * T ^ 3)) ≤
            (2 * Csq * CP ^ 2 * J3) * (Real.sqrt (X : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hf2 (by positivity)
        have hpad1 : 0 ≤ 8 * Csq * KM * CP * J3 * (Real.log (2 + T))⁻¹ := by positivity
        have hpad2 : 0 ≤ 2 * Csq * CP ^ 2 * J3 * (Real.log (2 + T))⁻¹ := by positivity
        have hpad3 : 0 ≤ 8 * Csq * KM * CP * J3 * (Real.sqrt (X : ℝ))⁻¹ := by positivity
        have hpad4 : 0 ≤ 2 * Csq * CP ^ 2 * J3 * (Real.sqrt (X : ℝ))⁻¹ := by positivity
        dsimp only [C_in2]
        linarith [h1, h2, hpad1, hpad2, hpad3, hpad4]
      calc |∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)| / (2 * T)
          ≤ ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * (T * Iom) +
              (8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
                2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * J3) / (2 * T) :=
            div_le_div_of_nonneg_right htot_in (by positivity)
        _ = ((8 * KM * Real.log (2 + T) * Rest + 2 * Rest ^ 2) * (T * Iom)) / (2 * T) +
            ((8 * Csq * KM * Real.log (2 + T) * CP * Real.sqrt X / T ^ 2 +
              2 * Csq * CP ^ 2 * (X : ℝ) / T ^ 2) * J3) / (2 * T) := add_div _ _ _
        _ ≤ 200 * C_in1 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) +
            200 * C_in2 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := add_le_add hpiece1 hpiece2
        _ = (200 * C_in1 + 200 * C_in2) * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by ring
    calc |(∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2) / (2 * T) +
          (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)) / (2 * T)|
        ≤ |(∫ t in (Set.Icc (-TL) TL)ᶜ, omegafun (t / T) * ‖Pfun X t‖ ^ 2) / (2 * T)| +
          |(∫ t in Set.Icc (-TL) TL, omegafun (t / T) * (‖Pfun X t‖ ^ 2 - ‖Swin X t L‖ ^ 2)) / (2 * T)| :=
          abs_add_le _ _
      _ ≤ Cout * (Real.log (2 + T))⁻¹ +
          (200 * C_in1 + 200 * C_in2) * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := add_le_add hout_bd hin_bd
      _ ≤ Ctot * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
          have hCout_nn : 0 ≤ Cout := by dsimp only [Cout]; positivity
          have h1 : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
          have h2 : 0 ≤ (Real.sqrt (X : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have hC_le : Cout * (Real.log (2 + T))⁻¹ ≤ Cout * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left (by linarith) hCout_nn
          dsimp only [Ctot]
          linarith
  · simpa using tendsto_eps_zero.const_mul Ctot

/-! #### Part 7D: Diagonal Integral Evaluation (`DiagIntegral X → dfun 2`) -/

lemma sum_mZero_in_Icc_le
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    {Y : ℝ} (hY : 1 ≤ Y) (G : Finset ℝ) (hG : ∀ g ∈ G, |g| ≤ Y) :
    ∑ g ∈ G, (mZero g : ℝ) ≤ 6 * CJ * Y * Real.log (3 + Y) := by
  set ks : Finset ℤ := G.image Int.floor
  have hfib := Finset.sum_fiberwise_of_maps_to (s := G) (t := ks) (g := Int.floor)
    (fun g hg => Finset.mem_image_of_mem _ hg) (f := fun g => (mZero g : ℝ))
  rw [← hfib]
  have hks_sub : ks ⊆ Finset.Icc (-⌈Y⌉ - 1) ⌈Y⌉ := by
    intro k hk
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hk
    have habs := abs_le.mp (hG g hg)
    rw [Finset.mem_Icc]
    constructor
    · have h1 : (-⌈Y⌉ - 1 : ℤ) ≤ ⌊g⌋ := by
        have hY1 : -(⌈Y⌉ : ℝ) ≤ -Y := neg_le_neg (Int.le_ceil Y)
        have hle : ((-⌈Y⌉ - 1 : ℤ) : ℝ) ≤ g := by push_cast; linarith [habs.1]
        exact Int.le_floor.mpr hle
      exact h1
    · have h2 : ⌊g⌋ ≤ ⌈Y⌉ := by
        have hle : (⌊g⌋ : ℝ) ≤ (⌈Y⌉ : ℝ) := (Int.floor_le g).trans (habs.2.trans (Int.le_ceil Y))
        exact_mod_cast hle
      exact h2
  have hstep1 : ∀ k ∈ ks, ∑ g ∈ G.filter (fun g => ⌊g⌋ = k), (mZero g : ℝ) ≤ CJ * Real.log (3 + Y) := by
    intro k hk
    have hmem := Finset.mem_Icc.mp (hks_sub hk)
    have hk_abs : |(k : ℝ)| ≤ Y + 1 := by
      have hceil : (⌈Y⌉ : ℝ) < Y + 1 := Int.ceil_lt_add_one Y
      obtain ⟨g, hg, hgk⟩ := Finset.mem_image.mp hk
      have habs := abs_le.mp (hG g hg)
      have hfl1 : (k : ℝ) ≤ g := hgk ▸ Int.floor_le g
      have hfl2 : g < (k : ℝ) + 1 := hgk ▸ Int.lt_floor_add_one g
      rw [abs_le]; constructor <;> linarith
    have hfin := (hunit (k : ℝ)).1
    have hle := (hunit (k : ℝ)).2
    set Tk := G.filter (fun g => ⌊g⌋ = k) ∪ hfin.toFinset
    have hsub : ∑ g ∈ G.filter (fun g => ⌊g⌋ = k), (mZero g : ℝ) ≤
        ∑ᶠ g : ℝ, if (k : ℝ) ≤ g ∧ g < (k : ℝ) + 1 then (mZero g : ℝ) else 0 := by
      rw [finsum_eq_sum_of_support_subset _ (s := Tk)
        (fun x hx => Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr hx)))]
      have heq : ∑ g ∈ G.filter (fun g => ⌊g⌋ = k), (mZero g : ℝ) =
          ∑ g ∈ G.filter (fun g => ⌊g⌋ = k), if (k : ℝ) ≤ g ∧ g < (k : ℝ) + 1 then (mZero g : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun g hg => ?_
        have hfl := (Finset.mem_filter.mp hg).2
        simp [hfl ▸ Int.floor_le g, hfl ▸ Int.lt_floor_add_one g]
      rw [heq]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => by split_ifs <;> positivity
    refine (hsub.trans hle).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [abs_nonneg (k : ℝ)]) (by linarith)) hCJ
  have hcard : (ks.card : ℝ) ≤ 6 * Y := by
    have h1 : ks.card ≤ (Finset.Icc (-⌈Y⌉ - 1) ⌈Y⌉).card := Finset.card_le_card hks_sub
    have h2 : ((Finset.Icc (-⌈Y⌉ - 1) ⌈Y⌉).card : ℝ) ≤ 6 * Y := by
      rw [Int.card_Icc]
      have hpos_c : 0 ≤ ⌈Y⌉ := Int.ceil_nonneg (by linarith)
      have htoNat : ((⌈Y⌉ + 1 - (-⌈Y⌉ - 1)).toNat : ℝ) = 2 * (⌈Y⌉ : ℝ) + 2 := by
        have hnn : 0 ≤ ⌈Y⌉ + 1 - (-⌈Y⌉ - 1) := by omega
        have := Int.toNat_of_nonneg hnn
        have hcast : ((⌈Y⌉ + 1 - (-⌈Y⌉ - 1)).toNat : ℤ) = 2 * ⌈Y⌉ + 2 := by omega
        exact_mod_cast hcast
      rw [htoNat]
      linarith [Int.ceil_lt_add_one Y]
    exact (by exact_mod_cast h1 : (ks.card : ℝ) ≤ _).trans h2
  calc ∑ k ∈ ks, ∑ g ∈ G.filter (fun g => ⌊g⌋ = k), (mZero g : ℝ)
      ≤ ∑ _k ∈ ks, CJ * Real.log (3 + Y) := Finset.sum_le_sum hstep1
    _ = (ks.card : ℝ) * (CJ * Real.log (3 + Y)) := by simp
    _ ≤ (6 * Y) * (CJ * Real.log (3 + Y)) := by
        have : 0 ≤ Real.log (3 + Y) := Real.log_nonneg (by linarith)
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 6 * CJ * Y * Real.log (3 + Y) := by ring

lemma sum_mZero_div_pow4_le
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    {T : ℝ} (hT : 2 ≤ T) (G : Finset ℝ) :
    ∑ g ∈ G, (mZero g : ℝ) / (1 + |g / T|) ^ 4 ≤ 24 * CJ * T * Real.log (2 + T) * (∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
  -- Group `G` by `j = Nat.floor (|g| / T) : ℕ`
  set js : Finset ℕ := G.image (fun g => Nat.floor (|g| / T))
  have hfib := Finset.sum_fiberwise_of_maps_to (s := G) (t := js) (g := fun g => Nat.floor (|g| / T))
    (fun g hg => Finset.mem_image_of_mem _ hg) (f := fun g => (mZero g : ℝ) / (1 + |g / T|) ^ 4)
  rw [← hfib]
  have hTpos : 0 < T := by linarith
  have hstep : ∀ j ∈ js,
      ∑ g ∈ G.filter (fun g => Nat.floor (|g| / T) = j), (mZero g : ℝ) / (1 + |g / T|) ^ 4 ≤
        (24 * CJ * T * Real.log (2 + T)) * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j _
    set Gj := G.filter (fun g => Nat.floor (|g| / T) = j)
    have hpt : ∀ g ∈ Gj, (mZero g : ℝ) / (1 + |g / T|) ^ 4 ≤ (mZero g : ℝ) / ((j : ℝ) + 1) ^ 4 := by
      intro g hg
      have hfl : Nat.floor (|g| / T) = j := (Finset.mem_filter.mp hg).2
      have hj_le : (j : ℝ) ≤ |g| / T := hfl ▸ Nat.floor_le (by positivity)
      have habs : |g / T| = |g| / T := by rw [abs_div, abs_of_pos hTpos]
      rw [habs]
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hGj_bd : ∀ g ∈ Gj, |g| ≤ ((j : ℝ) + 1) * T := by
      intro g hg
      have hfl : Nat.floor (|g| / T) = j := (Finset.mem_filter.mp hg).2
      have hj_lt : |g| / T < (j : ℝ) + 1 := hfl ▸ Nat.lt_floor_add_one (|g| / T)
      exact ((div_lt_iff₀ hTpos).mp hj_lt).le
    have hsum_Gj := sum_mZero_in_Icc_le CJ hCJ hunit
      (Y := ((j : ℝ) + 1) * T) (by nlinarith [Nat.cast_nonneg (α := ℝ) j]) Gj hGj_bd
    have hlog_le : Real.log (3 + ((j : ℝ) + 1) * T) ≤ 4 * ((j : ℝ) + 1) * Real.log (2 + T) := by
      have hmul : 3 + ((j : ℝ) + 1) * T ≤ (2 + T) * (2 * ((j : ℝ) + 1)) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) j]
      have h1 : Real.log (3 + ((j : ℝ) + 1) * T) ≤ Real.log (2 + T) + Real.log (2 * ((j : ℝ) + 1)) := by
        calc Real.log (3 + ((j : ℝ) + 1) * T) ≤ Real.log ((2 + T) * (2 * ((j : ℝ) + 1))) :=
              Real.log_le_log (by positivity) hmul
          _ = Real.log (2 + T) + Real.log (2 * ((j : ℝ) + 1)) :=
              Real.log_mul (by linarith) (by positivity)
      have h2 : Real.log (2 * ((j : ℝ) + 1)) ≤ 2 * ((j : ℝ) + 1) := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * ((j : ℝ) + 1))]
      have hlogT : (1 : ℝ) ≤ Real.log (2 + T) := by
        have h4 : (1 : ℝ) ≤ Real.log 4 := by
          have : Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
          rw [this, Real.log_pow]; push_cast; linarith [Real.log_two_gt_d9]
        exact h4.trans (Real.log_le_log (by norm_num) (by linarith))
      nlinarith [Nat.cast_nonneg (α := ℝ) j, hlogT]
    calc ∑ g ∈ Gj, (mZero g : ℝ) / (1 + |g / T|) ^ 4
        ≤ ∑ g ∈ Gj, (mZero g : ℝ) / ((j : ℝ) + 1) ^ 4 := Finset.sum_le_sum hpt
      _ = (∑ g ∈ Gj, (mZero g : ℝ)) / ((j : ℝ) + 1) ^ 4 := (Finset.sum_div _ _ _).symm
      _ ≤ (6 * CJ * (((j : ℝ) + 1) * T) * Real.log (3 + ((j : ℝ) + 1) * T)) / ((j : ℝ) + 1) ^ 4 :=
          div_le_div_of_nonneg_right hsum_Gj (by positivity)
      _ ≤ (6 * CJ * (((j : ℝ) + 1) * T) * (4 * ((j : ℝ) + 1) * Real.log (2 + T))) / ((j : ℝ) + 1) ^ 4 := by
          gcongr
      _ = (24 * CJ * T * Real.log (2 + T)) * (1 / ((j : ℝ) + 1) ^ 2) := by
          have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hj1]; ring
  have hsum_nat : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective Nat.succ_injective
    exact h1.congr fun j => by push_cast; rfl
  calc ∑ j ∈ js, ∑ g ∈ G.filter (fun g => Nat.floor (|g| / T) = j), (mZero g : ℝ) / (1 + |g / T|) ^ 4
      ≤ ∑ j ∈ js, (24 * CJ * T * Real.log (2 + T)) * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum hstep
    _ = (24 * CJ * T * Real.log (2 + T)) * ∑ j ∈ js, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (24 * CJ * T * Real.log (2 + T)) * ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
        have hlogT : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
        gcongr
        exact hsum_nat.sum_le_tsum js fun _ _ => by positivity

noncomputable def DiagApprox (X : ℕ) : ℝ :=
  let T := Tfun X
  let L := Lfun X
  (1 / (2 * T)) * (∫ v : ℝ, ‖Mfun v‖ ^ 2) *
    ∑ᶠ g : ℝ, if |g| ≤ T * L ∧ riemannZeta (zCrit g) = 0 then (mZero g : ℝ) * omegafun (g / T) else 0

set_option maxHeartbeats 1200000 in
lemma diagIntegral_sub_diagApprox_tendsto_zero
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hcont_kfun : Continuous kfun)
    (hcont_Mfun : Continuous Mfun)
    (hM_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n)
    (homega_diff : Differentiable ℝ omegafun)
    (homega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C / (1 + |t|) ^ n)
    (hdomega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv omegafun t| ≤ C / (1 + |t|) ^ n)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|)) :
    Tendsto (fun X : ℕ => DiagIntegral X - DiagApprox X) atTop (𝓝 0) := by
  obtain ⟨CM2, hCM2, hM2⟩ := hM_dec 2
  obtain ⟨Cw6, hCw6, homega6⟩ := homega_dec 6
  obtain ⟨Cd4, hCd4, hdomega4⟩ := hdomega_dec 4
  have hcont_omega : Continuous omegafun := homega_diff.continuous
  have hint_M2 : Integrable (fun v : ℝ => ‖Mfun v‖ ^ 2) := by
    refine (integrable_div_one_add_abs_pow7 (CM2 ^ 2) 4 (by norm_num)).mono'
      (hcont_Mfun.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖Mfun v‖ ^ 2 ≤ (CM2 / (1 + |v|) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM2 v) 2
      _ = CM2 ^ 2 / (1 + |v|) ^ 4 := by rw [div_pow, ← pow_mul]
  have hint_vM2 : Integrable (fun v : ℝ => |v| * ‖Mfun v‖ ^ 2) := by
    refine (integrable_div_one_add_abs_pow7 (CM2 ^ 2) 3 (by norm_num)).mono'
      (continuous_abs.mul (hcont_Mfun.norm.pow 2)).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hv : |v| ≤ 1 + |v| := by linarith
    calc |v| * ‖Mfun v‖ ^ 2 ≤ (1 + |v|) * (CM2 / (1 + |v|) ^ 2) ^ 2 :=
          mul_le_mul hv (pow_le_pow_left₀ (norm_nonneg _) (hM2 v) 2) (sq_nonneg _) (by positivity)
      _ = CM2 ^ 2 / (1 + |v|) ^ 3 := by
          have hne : 1 + |v| ≠ 0 := by linarith [abs_nonneg v]
          rw [div_pow, ← pow_mul]; field_simp [hne]; ring
  set IM0 : ℝ := ∫ v : ℝ, ‖Mfun v‖ ^ 2
  set IM1 : ℝ := ∫ v : ℝ, |v| * ‖Mfun v‖ ^ 2
  set Z2 : ℝ := ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 1) ^ 2
  have hIM0_nn : 0 ≤ IM0 := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hIM1_nn : 0 ≤ IM1 := MeasureTheory.integral_nonneg fun _ => by positivity
  have hZ2_nn : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  set C1 : ℝ := 192 * Cd4 * IM1 * CJ * Z2
  set C2 : ℝ := 24 * Cw6 * CM2 ^ 2 * CJ * Z2
  set C3 : ℝ := 3072 * Cw6 * IM0 * CJ
  set Ctot : ℝ := 50 * (C1 + C2 + C3)
  refine squeeze_zero_norm' (a := fun X : ℕ => Ctot * ((Real.log (2 + Tfun X))⁻¹ + (Real.sqrt (X : ℝ))⁻¹)) ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨200, fun X hX => ?_⟩
    have hXr_pos : (0 : ℝ) < (X : ℝ) := by positivity
    have hT_ge := Tfun_ge_of_ge hX
    have hT_pos : 0 < Tfun X := by linarith
    have hlog_ge := log_Tfun_ge_two hX
    obtain ⟨hL_ge4, hL_sq, hL_half⟩ := Lfun_bounds hX
    set T := Tfun X
    set L := Lfun X
    set TL := T * L
    have hTL_nn : 0 ≤ TL := by positivity
    have hfin_big := finite_zeros_in_Icc hzeta_ntop CJ hunit (-(TL + L)) (TL + L)
    set Gbig : Finset ℝ := hfin_big.toFinset
    have hGbig_mem : ∀ g : ℝ, g ∈ Gbig ↔ -(TL + L) ≤ g ∧ g ≤ TL + L ∧ riemannZeta (zCrit g) = 0 := by
      intro g; simp [Gbig]
    have hG_win : ∀ t ∈ Set.Icc (-TL) TL, ∀ g : ℝ, |g - t| ≤ L → riemannZeta (zCrit g) = 0 → g ∈ Gbig := by
      intro t ht g hgt hz
      rw [hGbig_mem]; have := abs_le.mp hgt
      exact ⟨by linarith [ht.1], by linarith [ht.2], hz⟩
    -- Express `DiagIntegral X` as a finite sum over `g ∈ Gbig`
    have hterm_int : ∀ g ∈ Gbig, IntegrableOn
        (fun t : ℝ => if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then omegafun (t / T) * ((mZero g : ℝ) * ‖Mfun (g - t)‖ ^ 2) else 0)
        (Set.Icc (-TL) TL) := by
      intro g _
      have hset : MeasurableSet {t : ℝ | |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0} :=
        (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const).inter (MeasurableSet.const _)
      have hmeas : Measurable (fun t : ℝ =>
          if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then omegafun (t / T) * ((mZero g : ℝ) * ‖Mfun (g - t)‖ ^ 2) else 0) :=
        Measurable.ite hset
          ((hcont_omega.comp (continuous_id.div_const T)).measurable.mul
            (measurable_const.mul ((hcont_Mfun.norm.pow 2).measurable.comp (measurable_const.sub measurable_id))))
          measurable_const
      refine (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := Cw6 * ((mZero g : ℝ) * CM2 ^ 2))).mono'
        hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) (mZero g)) (sq_nonneg ‖Mfun (g - t)‖))]
        have ho : |omegafun (t / T)| ≤ Cw6 :=
          (homega6 (t / T)).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg (t / T)])))
        have hM : ‖Mfun (g - t)‖ ^ 2 ≤ CM2 ^ 2 := by
          have h1 : ‖Mfun (g - t)‖ ≤ CM2 :=
            (hM2 (g - t)).trans (div_le_self hCM2 (one_le_pow₀ (by linarith [abs_nonneg (g - t)])))
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        exact mul_le_mul ho (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)) (by positivity) hCw6
      · simp; positivity
    have hDiag_eq : DiagIntegral X = (1 / (2 * T)) * ∑ g ∈ Gbig, (mZero g : ℝ) *
        ∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0 := by
      unfold DiagIntegral; dsimp only
      have hnegTL : -Tfun X * Lfun X = -TL := by dsimp only [TL, T, L]; ring
      rw [hnegTL]
      change (∫ t in Set.Icc (-TL) TL, omegafun (t / T) * DiagWin t L) / (2 * T) = _
      rw [div_eq_mul_inv, mul_comm, ← one_div]
      congr 1
      have hcongr : ∫ t in Set.Icc (-TL) TL, omegafun (t / T) * DiagWin t L =
          ∫ t in Set.Icc (-TL) TL, ∑ g ∈ Gbig,
            if |g - t| ≤ L ∧ riemannZeta (zCrit g) = 0 then omegafun (t / T) * ((mZero g : ℝ) * ‖Mfun (g - t)‖ ^ 2) else 0 := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [DiagWin_eq_finset_sum (hG_win t ht), Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        split_ifs <;> ring
      have hint_sum_aux : ∀ (S : Finset ℝ) (f : ℝ → ℝ → ℝ),
          (∀ g ∈ S, IntegrableOn (f g) (Set.Icc (-TL) TL)) →
          ∫ t in Set.Icc (-TL) TL, ∑ g ∈ S, f g t = ∑ g ∈ S, ∫ t in Set.Icc (-TL) TL, f g t := by
        intro S f hf
        induction S using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          simp_rw [Finset.sum_insert ha]
          have hs : IntegrableOn (fun t => ∑ g ∈ s, f g t) (Set.Icc (-TL) TL) := by
            have hAux : ∀ (u : Finset ℝ), (∀ g ∈ u, IntegrableOn (f g) (Set.Icc (-TL) TL)) →
                IntegrableOn (fun t => ∑ g ∈ u, f g t) (Set.Icc (-TL) TL) := by
              intro u hu
              induction u using Finset.induction_on with
              | empty => simpa using integrableOn_zero
              | @insert b v hb ihv =>
                simp_rw [Finset.sum_insert hb]
                exact (hu b (Finset.mem_insert_self b v)).add (ihv fun g hg => hu g (Finset.mem_insert_of_mem hg))
            exact hAux s fun g hg => hf g (Finset.mem_insert_of_mem hg)
          rw [MeasureTheory.integral_add (hf a (Finset.mem_insert_self a s)) hs,
            ih fun g hg => hf g (Finset.mem_insert_of_mem hg)]
      rw [hcongr, hint_sum_aux Gbig _ hterm_int]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hgz : riemannZeta (zCrit g) = 0 := ((hGbig_mem g).mp hg).2.2
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      simp only [hgz, and_true]; split_ifs <;> ring
    -- Express `DiagApprox X` as a finite sum over `Gbig` (with `if |g| ≤ TL` indicator)
    have hApprox_eq : DiagApprox X = (1 / (2 * T)) * ∑ g ∈ Gbig,
        if |g| ≤ TL then (mZero g : ℝ) * (omegafun (g / T) * IM0) else 0 := by
      unfold DiagApprox; dsimp only
      have hsupp : (Function.support fun g : ℝ =>
          if |g| ≤ TL ∧ riemannZeta (zCrit g) = 0 then (mZero g : ℝ) * omegafun (g / T) else 0) ⊆ (Gbig : Set ℝ) := by
        intro g hg
        rw [Function.mem_support] at hg
        split_ifs at hg with hc
        · rw [Finset.mem_coe, hGbig_mem]
          have := abs_le.mp hc.1
          exact ⟨by linarith, by linarith, hc.2⟩
        · exact (hg rfl).elim
      rw [finsum_eq_sum_of_support_subset _ (s := Gbig) hsupp, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun g hg => ?_
      have hgz : riemannZeta (zCrit g) = 0 := ((hGbig_mem g).mp hg).2.2
      simp only [hgz, and_true]; split_ifs <;> ring
    rw [Real.norm_eq_abs, hDiag_eq, hApprox_eq, ← mul_sub, ← Finset.sum_sub_distrib,
      abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    -- Bound each `g ∈ Gbig` term!
    have hsum_diff : |∑ g ∈ Gbig, ((mZero g : ℝ) *
          (∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
          (if |g| ≤ TL then (mZero g : ℝ) * (omegafun (g / T) * IM0) else 0))| ≤
        (16 * Cd4 * IM1 / T) * (∑ g ∈ Gbig, (mZero g : ℝ) / (1 + |g / T|) ^ 4) +
        (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * (∑ g ∈ Gbig, (mZero g : ℝ) / (1 + |g / T|) ^ 4) +
        (Cw6 * IM0 / (1 + L / 2) ^ 6) * (∑ g ∈ Gbig, (mZero g : ℝ)) := by
      -- For each `g ∈ Gbig`, first bound the MVT error `|∫ (ω(t/T) - ω(g/T)) * ‖M(g-t)‖^2|`, then the domain truncation!
      have hterm_bd : ∀ g ∈ Gbig,
          |(mZero g : ℝ) * (∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
            (if |g| ≤ TL then (mZero g : ℝ) * (omegafun (g / T) * IM0) else 0)| ≤
          (16 * Cd4 * IM1 / T) * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
          (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
          (Cw6 * IM0 / (1 + L / 2) ^ 6) * (mZero g : ℝ) := by
        intro g hg
        -- Step A: Freeze `ω(t/T) → ω(g/T)` on `|g - t| ≤ L` using MVT + `hdomega4`
        have hmvt : ∀ t : ℝ, |g - t| ≤ L → |omegafun (t / T) - omegafun (g / T)| ≤
            (16 * Cd4 / (1 + |g / T|) ^ 4) * (|g - t| / T) := by
          intro t hgt
          have hball_bd : ∀ u ∈ Set.uIcc (g / T) (t / T), ‖deriv omegafun u‖ ≤ 16 * Cd4 / (1 + |g / T|) ^ 4 := by
            intro u hu
            rw [Real.norm_eq_abs]
            have hudiff : |u - g / T| ≤ 1 / 2 := by
              have h1 : |t / T - g / T| ≤ 1 / 2 := by
                rw [← sub_div, abs_div, abs_of_pos hT_pos, abs_sub_comm]
                exact (div_le_iff₀ hT_pos).mpr (by linarith)
              rcases le_total (g / T) (t / T) with hle | hle
              · rw [Set.uIcc_of_le hle] at hu
                rw [abs_of_nonneg (by linarith [hu.1])]
                have := (abs_le.mp h1).2; linarith [hu.2]
              · rw [Set.uIcc_of_ge hle] at hu
                rw [abs_of_nonpos (by linarith [hu.2])]
                have := (abs_le.mp h1).1; linarith [hu.1]
            have h1g : 1 + |g / T| ≤ 2 * (1 + |u|) := by
              have htri : |g / T| ≤ |u| + |u - g / T| := by
                have := abs_add_le u (g / T - u); rw [add_sub_cancel, abs_sub_comm] at this; exact this
              linarith [abs_nonneg u]
            have hpow4 : (1 + |g / T|) ^ 4 ≤ 16 * (1 + |u|) ^ 4 := by
              calc (1 + |g / T|) ^ 4 ≤ (2 * (1 + |u|)) ^ 4 := pow_le_pow_left₀ (by positivity) h1g 4
                _ = 16 * (1 + |u|) ^ 4 := by ring
            refine (hdomega4 u).trans ?_
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            calc Cd4 * (1 + |g / T|) ^ 4 ≤ Cd4 * (16 * (1 + |u|) ^ 4) := mul_le_mul_of_nonneg_left hpow4 hCd4
              _ = 16 * Cd4 * (1 + |u|) ^ 4 := by ring
          have hconv := Convex.norm_image_sub_le_of_norm_deriv_le (f := omegafun)
            (s := Set.uIcc (g / T) (t / T)) (x := g / T) (y := t / T)
            (fun u _ => homega_diff u) hball_bd (convex_uIcc _ _) Set.left_mem_uIcc Set.right_mem_uIcc
          rw [Real.norm_eq_abs, Real.norm_eq_abs, ← sub_div, abs_div (t - g) T, abs_of_pos hT_pos, abs_sub_comm t g] at hconv
          exact hconv
        have hint_a : IntegrableOn (fun t : ℝ => if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) (Set.Icc (-TL) TL) := by
          have hmeas : Measurable (fun t : ℝ => if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) :=
            Measurable.ite (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const)
              ((hcont_omega.comp (continuous_id.div_const T)).measurable.mul
                ((hcont_Mfun.norm.pow 2).measurable.comp (measurable_const.sub measurable_id)))
              measurable_const
          refine (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := Cw6 * CM2 ^ 2)).mono'
            hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
          split_ifs
          · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Mfun (g - t)‖)]
            have ho : |omegafun (t / T)| ≤ Cw6 :=
              (homega6 (t / T)).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg (t / T)])))
            have hM : ‖Mfun (g - t)‖ ^ 2 ≤ CM2 ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((hM2 (g - t)).trans (div_le_self hCM2 (one_le_pow₀ (by linarith [abs_nonneg (g - t)])))) 2
            exact mul_le_mul ho hM (sq_nonneg _) hCw6
          · simp; positivity
        have hint_b : IntegrableOn (fun t : ℝ => if |g - t| ≤ L then omegafun (g / T) * ‖Mfun (g - t)‖ ^ 2 else 0) (Set.Icc (-TL) TL) := by
          have hmeas : Measurable (fun t : ℝ => if |g - t| ≤ L then omegafun (g / T) * ‖Mfun (g - t)‖ ^ 2 else 0) :=
            Measurable.ite (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const)
              (measurable_const.mul ((hcont_Mfun.norm.pow 2).measurable.comp (measurable_const.sub measurable_id)))
              measurable_const
          refine (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := |omegafun (g / T)| * CM2 ^ 2)).mono'
            hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
          split_ifs
          · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Mfun (g - t)‖)]
            have hM : ‖Mfun (g - t)‖ ^ 2 ≤ CM2 ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((hM2 (g - t)).trans (div_le_self hCM2 (one_le_pow₀ (by linarith [abs_nonneg (g - t)])))) 2
            exact mul_le_mul_of_nonneg_left hM (abs_nonneg _)
          · simp; positivity
        have hfreeze : |(∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
            omegafun (g / T) * (∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0)| ≤
            (16 * Cd4 * IM1 / T) / (1 + |g / T|) ^ 4 := by
          have hpull : omegafun (g / T) * (∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0) =
              ∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (g / T) * ‖Mfun (g - t)‖ ^ 2 else 0 := by
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => by split_ifs <;> ring
          rw [hpull, ← MeasureTheory.integral_sub hint_a hint_b]
          have hdom_v : Integrable (fun t : ℝ => (16 * Cd4 / (T * (1 + |g / T|) ^ 4)) * (|g - t| * ‖Mfun (g - t)‖ ^ 2)) :=
            (hint_vM2.comp_sub_left g).const_mul _
          have hdom_eq : ∫ t : ℝ, (16 * Cd4 / (T * (1 + |g / T|) ^ 4)) * (|g - t| * ‖Mfun (g - t)‖ ^ 2) =
              (16 * Cd4 * IM1 / T) / (1 + |g / T|) ^ 4 := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub_left_eq_self (fun v : ℝ => |v| * ‖Mfun v‖ ^ 2) (μ := volume) g]
            dsimp only [IM1]
            have hne : (1 + |g / T|) ^ 4 ≠ 0 := pow_ne_zero 4 (by linarith [abs_nonneg (g / T)])
            field_simp [hT_pos.ne', hne]
          calc _ ≤ ∫ t in Set.Icc (-TL) TL,
                ‖(if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
                 (if |g - t| ≤ L then omegafun (g / T) * ‖Mfun (g - t)‖ ^ 2 else 0)‖ :=
                MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t in Set.Icc (-TL) TL,
                  (16 * Cd4 / (T * (1 + |g / T|) ^ 4)) * (|g - t| * ‖Mfun (g - t)‖ ^ 2) := by
                refine MeasureTheory.setIntegral_mono_on (hint_a.sub hint_b).norm hdom_v.integrableOn
                  measurableSet_Icc fun t _ => ?_
                split_ifs with hgt
                · rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖Mfun (g - t)‖)]
                  calc |omegafun (t / T) - omegafun (g / T)| * ‖Mfun (g - t)‖ ^ 2
                      ≤ ((16 * Cd4 / (1 + |g / T|) ^ 4) * (|g - t| / T)) * ‖Mfun (g - t)‖ ^ 2 :=
                        mul_le_mul_of_nonneg_right (hmvt t hgt) (sq_nonneg _)
                    _ = (16 * Cd4 / (T * (1 + |g / T|) ^ 4)) * (|g - t| * ‖Mfun (g - t)‖ ^ 2) := by
                        have hne : (1 + |g / T|) ^ 4 ≠ 0 := pow_ne_zero 4 (by linarith [abs_nonneg (g / T)])
                        field_simp [hT_pos.ne', hne]
                · simp; positivity
            _ ≤ ∫ t : ℝ, (16 * Cd4 / (T * (1 + |g / T|) ^ 4)) * (|g - t| * ‖Mfun (g - t)‖ ^ 2) :=
                MeasureTheory.setIntegral_le_integral hdom_v (Filter.Eventually.of_forall fun _ => by positivity)
            _ = (16 * Cd4 * IM1 / T) / (1 + |g / T|) ^ 4 := hdom_eq
        -- Step B: Bound `|omegafun (g / T) * (∫_{Icc (-TL) TL} if |g-t|≤L then ‖M(g-t)‖^2 - (if |g|≤TL then IM0 else 0))|`
        set Ig : ℝ := ∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0
        have hIg_nn : 0 ≤ Ig := MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ => by split_ifs <;> positivity
        have hIg_le_IM0 : Ig ≤ IM0 := by
          have hint_g : IntegrableOn (fun t : ℝ => if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0) (Set.Icc (-TL) TL) := by
            have hmeas : Measurable (fun t : ℝ => if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0) :=
              Measurable.ite (measurableSet_le (continuous_const.sub continuous_id).abs.measurable measurable_const)
                ((hcont_Mfun.norm.pow 2).measurable.comp (measurable_const.sub measurable_id)) measurable_const
            exact (hint_M2.comp_sub_left g).integrableOn.mono' hmeas.aestronglyMeasurable
              (Filter.Eventually.of_forall fun t => by split_ifs <;> simp [abs_of_nonneg, sq_nonneg])
          calc Ig ≤ ∫ t in Set.Icc (-TL) TL, ‖Mfun (g - t)‖ ^ 2 :=
                MeasureTheory.setIntegral_mono_on hint_g (hint_M2.comp_sub_left g).integrableOn measurableSet_Icc
                  fun t _ => by split_ifs; exact le_rfl; exact sq_nonneg _
            _ ≤ ∫ t : ℝ, ‖Mfun (g - t)‖ ^ 2 :=
                MeasureTheory.setIntegral_le_integral (hint_M2.comp_sub_left g) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            _ = IM0 := MeasureTheory.integral_sub_left_eq_self (fun v : ℝ => ‖Mfun v‖ ^ 2) (μ := volume) g
        have hdom_trunc : |omegafun (g / T) * Ig - (if |g| ≤ TL then omegafun (g / T) * IM0 else 0)| ≤
            (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 / (1 + |g / T|) ^ 4 + Cw6 * IM0 / (1 + L / 2) ^ 6 := by
          by_cases hinner : |g| ≤ TL - L
          · have hle_TL : |g| ≤ TL := by linarith
            simp only [hle_TL, ↓reduceIte, ← mul_sub]
            rw [abs_mul]
            have hIg_eq : Ig = ∫ v in Set.Icc (-L) L, ‖Mfun v‖ ^ 2 := by
              -- On `|g| ≤ TL - L`, `|g - t| ≤ L → t ∈ Icc (-TL) TL`!
              have hsub : (fun t : ℝ => g - t) ⁻¹' Set.Icc (-L) L ⊆ Set.Icc (-TL) TL := by
                intro t ht
                have hgt : |g - t| ≤ L := abs_le.mpr ht
                have hg' := abs_le.mp hinner
                have hgt' := abs_le.mp hgt
                exact ⟨by linarith, by linarith⟩
              have hind_eq : ∫ t in Set.Icc (-TL) TL, (if |g - t| ≤ L then ‖Mfun (g - t)‖ ^ 2 else 0) =
                  ∫ t : ℝ, Set.indicator ((fun t : ℝ => g - t) ⁻¹' Set.Icc (-L) L) (fun t => ‖Mfun (g - t)‖ ^ 2) t := by
                rw [← MeasureTheory.integral_indicator measurableSet_Icc]
                congr 1; ext t
                by_cases h1 : t ∈ (fun t : ℝ => g - t) ⁻¹' Set.Icc (-L) L
                · have htI : t ∈ Set.Icc (-TL) TL := hsub h1
                  have hgt : |g - t| ≤ L := abs_le.mpr h1
                  rw [Set.indicator_of_mem htI, Set.indicator_of_mem h1, if_pos hgt]
                · have hgt : ¬(|g - t| ≤ L) := fun h => h1 (abs_le.mp h)
                  rw [Set.indicator_of_notMem h1]
                  by_cases htI : t ∈ Set.Icc (-TL) TL
                  · rw [Set.indicator_of_mem htI, if_neg hgt]
                  · rw [Set.indicator_of_notMem htI]
              dsimp only [Ig]
              rw [hind_eq]
              have hchg := MeasureTheory.integral_sub_left_eq_self
                (fun v : ℝ => Set.indicator (Set.Icc (-L) L) (fun v => ‖Mfun v‖ ^ 2) v) (μ := volume) g
              rw [← MeasureTheory.integral_indicator measurableSet_Icc]
              exact hchg
            have hdiff_IM : |Ig - IM0| ≤ 2 * CM2 ^ 2 / (3 * (1 + L) ^ 3) := by
              rw [hIg_eq]
              have hsp : IM0 = (∫ v in Set.Icc (-L) L, ‖Mfun v‖ ^ 2) + ∫ v in (Set.Icc (-L) L)ᶜ, ‖Mfun v‖ ^ 2 :=
                (MeasureTheory.integral_add_compl measurableSet_Icc hint_M2).symm
              rw [hsp, sub_add_cancel_left, abs_neg,
                abs_of_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Icc.compl fun _ _ => sq_nonneg _)]
              calc ∫ v in (Set.Icc (-L) L)ᶜ, ‖Mfun v‖ ^ 2
                  ≤ ∫ v in (Set.Icc (-L) L)ᶜ, CM2 ^ 2 * ((1 : ℝ) / (1 + |v|) ^ 4) := by
                    refine MeasureTheory.setIntegral_mono_on hint_M2.integrableOn
                      ((integrable_div_one_add_abs_pow7 1 4 (by norm_num)).const_mul _).integrableOn
                      measurableSet_Icc.compl fun v _ => ?_
                    calc ‖Mfun v‖ ^ 2 ≤ (CM2 / (1 + |v|) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM2 v) 2
                      _ = CM2 ^ 2 * (1 / (1 + |v|) ^ 4) := by rw [div_pow, ← pow_mul, mul_one_div]
                _ = CM2 ^ 2 * (2 / (3 * (1 + L) ^ 3)) := by
                    rw [MeasureTheory.integral_const_mul, integral_compl_Icc_inv_one_add_abs_pow (by linarith) (by norm_num)]
                    norm_num
                _ = 2 * CM2 ^ 2 / (3 * (1 + L) ^ 3) := by ring
            have ho4 : |omegafun (g / T)| ≤ Cw6 / (1 + |g / T|) ^ 4 := by
              refine (homega6 (g / T)).trans ?_
              apply div_le_div_of_nonneg_left hCw6 (by positivity)
              exact pow_le_pow_right₀ (by linarith [abs_nonneg (g / T)]) (by norm_num)
            have h1 := mul_le_mul ho4 hdiff_IM (abs_nonneg _) (by positivity)
            have h2 : 0 ≤ Cw6 * IM0 / (1 + L / 2) ^ 6 := by positivity
            linarith [show Cw6 / (1 + |g / T|) ^ 4 * (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) =
              (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 / (1 + |g / T|) ^ 4 by ring]
          · push Not at hinner
            -- Here `|g| > TL - L`, so `|g / T| ≥ L - L / T ≥ L / 2`!
            have hgt_half : L / 2 ≤ |g / T| := by
              rw [abs_div, abs_of_pos hT_pos, le_div_iff₀ hT_pos]
              nlinarith
            have ho6 : |omegafun (g / T)| ≤ Cw6 / (1 + L / 2) ^ 6 :=
              (homega6 (g / T)).trans (div_le_div_of_nonneg_left hCw6 (by positivity)
                (pow_le_pow_left₀ (by linarith) (by linarith) 6))
            have hbd_b : |omegafun (g / T) * Ig - (if |g| ≤ TL then omegafun (g / T) * IM0 else 0)| ≤
                Cw6 * IM0 / (1 + L / 2) ^ 6 := by
              split_ifs
              · rw [← mul_sub, abs_mul]
                have hdiff : |Ig - IM0| ≤ IM0 := by rw [abs_le]; constructor <;> linarith
                calc |omegafun (g / T)| * |Ig - IM0| ≤ (Cw6 / (1 + L / 2) ^ 6) * IM0 :=
                      mul_le_mul ho6 hdiff (abs_nonneg _) (by positivity)
                  _ = Cw6 * IM0 / (1 + L / 2) ^ 6 := by ring
              · rw [sub_zero, abs_mul, abs_of_nonneg hIg_nn]
                calc |omegafun (g / T)| * Ig ≤ (Cw6 / (1 + L / 2) ^ 6) * IM0 :=
                      mul_le_mul ho6 hIg_le_IM0 hIg_nn (by positivity)
                  _ = Cw6 * IM0 / (1 + L / 2) ^ 6 := by ring
            have hnn : 0 ≤ (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 / (1 + |g / T|) ^ 4 := by positivity
            linarith
        -- Combine Steps A and B!
        have hrearr : (mZero g : ℝ) * (∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
            (if |g| ≤ TL then (mZero g : ℝ) * (omegafun (g / T) * IM0) else 0) =
            (mZero g : ℝ) *
              (((∫ t in Set.Icc (-TL) TL, if |g - t| ≤ L then omegafun (t / T) * ‖Mfun (g - t)‖ ^ 2 else 0) -
                  omegafun (g / T) * Ig) +
               (omegafun (g / T) * Ig - (if |g| ≤ TL then omegafun (g / T) * IM0 else 0))) := by
          split_ifs <;> ring
        rw [hrearr, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have htri := (abs_add_le _ _).trans (add_le_add hfreeze hdom_trunc)
        have := mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg (α := ℝ) (mZero g))
        linarith [show (mZero g : ℝ) * ((16 * Cd4 * IM1 / T) / (1 + |g / T|) ^ 4 +
            ((2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 / (1 + |g / T|) ^ 4 + Cw6 * IM0 / (1 + L / 2) ^ 6)) =
          (16 * Cd4 * IM1 / T) * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
          (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
          (Cw6 * IM0 / (1 + L / 2) ^ 6) * (mZero g : ℝ) by ring]
      calc |∑ g ∈ Gbig, _| ≤ ∑ g ∈ Gbig, |_| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ g ∈ Gbig, ((16 * Cd4 * IM1 / T) * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
              (2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * ((mZero g : ℝ) / (1 + |g / T|) ^ 4) +
              (Cw6 * IM0 / (1 + L / 2) ^ 6) * (mZero g : ℝ)) := Finset.sum_le_sum hterm_bd
        _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    -- Apply `sum_mZero_div_pow4_le` and `sum_mZero_in_Icc_le`!
    have hS4 := sum_mZero_div_pow4_le CJ hCJ hunit (by linarith : 2 ≤ T) Gbig
    have hStot := sum_mZero_in_Icc_le CJ hCJ hunit (Y := TL + L) (by nlinarith) Gbig
      (fun g hg => abs_le.mpr ⟨((hGbig_mem g).mp hg).1, ((hGbig_mem g).mp hg).2.1⟩)
    -- Bound each of the 3 pieces divided by `2 * T`!
    have hX_real : (200 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hsq_pos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXr_pos
    have hlog_div_T : Real.log (2 + T) / T ≤ 8 * (Real.sqrt (X : ℝ))⁻¹ := by
      have h2T : 2 + T ≤ 9 * (X : ℝ) := by unfold T Tfun; nlinarith [Real.pi_lt_four]
      have hsq9 : Real.sqrt (2 + T) ≤ 3 * Real.sqrt (X : ℝ) := by
        calc Real.sqrt (2 + T) ≤ Real.sqrt (9 * (X : ℝ)) := Real.sqrt_le_sqrt h2T
          _ = 3 * Real.sqrt (X : ℝ) := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by norm_num]
      have hlog_le : Real.log (2 + T) ≤ 48 * Real.sqrt (X : ℝ) := by
        have h1 : Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 2 := by nlinarith
        have h2 : (Real.log (2 + T)) ^ 2 = L := rfl
        linarith
      have hT_ge6X : 6 * (X : ℝ) ≤ T := by unfold T Tfun; nlinarith [Real.pi_gt_three]
      calc Real.log (2 + T) / T ≤ (48 * Real.sqrt (X : ℝ)) / (6 * (X : ℝ)) :=
            div_le_div₀ (by positivity) hlog_le (by positivity) hT_ge6X
        _ = (48 * Real.sqrt (X : ℝ)) / (6 * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ))) := by
            rw [Real.mul_self_sqrt hXr_pos.le]
        _ = 8 * (Real.sqrt (X : ℝ))⁻¹ := by
            field_simp [hsq_pos.ne']; ring
    have hlog_div_L3 : Real.log (2 + T) / (1 + L) ^ 3 ≤ (Real.log (2 + T))⁻¹ := by
      have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
      have hpow : (Real.log (2 + T)) ^ 6 ≤ (1 + L) ^ 3 := by
        have := pow_le_pow_left₀ (by linarith) (show L ≤ 1 + L by linarith) 3
        rw [show L ^ 3 = (Real.log (2 + T)) ^ 6 by rw [hL_eq]; ring] at this; exact this
      calc Real.log (2 + T) / (1 + L) ^ 3 ≤ Real.log (2 + T) / (Real.log (2 + T)) ^ 6 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity) hpow
        _ ≤ Real.log (2 + T) / (Real.log (2 + T)) ^ 2 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
        _ = (Real.log (2 + T))⁻¹ := by
            have hne : Real.log (2 + T) ≠ 0 := by linarith
            rw [sq, div_mul_eq_div_div, div_self hne, one_div]
    have hlog_big : Real.log (3 + (TL + L)) ≤ 4 * Real.log (2 + T) := by
      have hle : 3 + (TL + L) ≤ (2 + T) ^ 4 := by
        have hL_le : L ≤ 2 + T := by linarith
        have hsq : 3 + (TL + L) ≤ (2 + T) ^ 2 := by dsimp only [TL]; nlinarith
        exact hsq.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
      calc Real.log (3 + (TL + L)) ≤ Real.log ((2 + T) ^ 4) := Real.log_le_log (by positivity) hle
        _ = 4 * Real.log (2 + T) := by rw [Real.log_pow]; ring
    have hL_div_half6 : L * Real.log (2 + T) / (1 + L / 2) ^ 6 ≤ 64 * (Real.log (2 + T))⁻¹ := by
      have hpow : L ^ 6 / 64 ≤ (1 + L / 2) ^ 6 := by
        calc L ^ 6 / 64 = (L / 2) ^ 6 := by ring
          _ ≤ (1 + L / 2) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
      have hL6 : L ^ 6 = (Real.log (2 + T)) ^ 12 := by rw [hL_eq]; ring
      have h12 : (Real.log (2 + T)) ^ 4 ≤ (Real.log (2 + T)) ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
      calc L * Real.log (2 + T) / (1 + L / 2) ^ 6
          ≤ L * Real.log (2 + T) / (L ^ 6 / 64) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = 64 * (Real.log (2 + T)) ^ 3 / (Real.log (2 + T)) ^ 12 := by
            rw [hL6, hL_eq]; field_simp [(by linarith : Real.log (2 + T) ≠ 0)]
        _ ≤ 64 * (Real.log (2 + T)) ^ 3 / (Real.log (2 + T)) ^ 4 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h12
        _ = 64 * (Real.log (2 + T))⁻¹ := by
            have hne : Real.log (2 + T) ≠ 0 := by linarith
            rw [show (Real.log (2 + T)) ^ 4 = (Real.log (2 + T)) ^ 3 * Real.log (2 + T) by ring,
              mul_div_assoc, div_mul_eq_div_div, div_self (pow_ne_zero 3 hne), one_div]
    have hS4_nn : 0 ≤ ∑ g ∈ Gbig, (mZero g : ℝ) / (1 + |g / T|) ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
    have hStot_nn : 0 ≤ ∑ g ∈ Gbig, (mZero g : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hp1 : (1 / (2 * T)) * ((16 * Cd4 * IM1 / T) * (∑ g ∈ Gbig, (mZero g : ℝ) / (1 + |g / T|) ^ 4)) ≤
        8 * C1 * (Real.sqrt (X : ℝ))⁻¹ := by
      calc _ ≤ (1 / (2 * T)) * ((16 * Cd4 * IM1 / T) * (24 * CJ * T * Real.log (2 + T) * Z2)) := by gcongr
        _ = C1 * (Real.log (2 + T) / T) := by dsimp only [C1]; field_simp [hT_pos.ne']; ring
        _ ≤ C1 * (8 * (Real.sqrt (X : ℝ))⁻¹) := mul_le_mul_of_nonneg_left hlog_div_T (by positivity)
        _ = 8 * C1 * (Real.sqrt (X : ℝ))⁻¹ := by ring
    have hp2 : (1 / (2 * T)) * ((2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * (∑ g ∈ Gbig, (mZero g : ℝ) / (1 + |g / T|) ^ 4)) ≤
        C2 * (Real.log (2 + T))⁻¹ := by
      calc _ ≤ (1 / (2 * T)) * ((2 * CM2 ^ 2 / (3 * (1 + L) ^ 3)) * Cw6 * (24 * CJ * T * Real.log (2 + T) * Z2)) := by gcongr
        _ = (1 / 3) * C2 * (Real.log (2 + T) / (1 + L) ^ 3) := by dsimp only [C2]; field_simp [hT_pos.ne']
        _ ≤ (1 / 3) * C2 * (Real.log (2 + T))⁻¹ := mul_le_mul_of_nonneg_left hlog_div_L3 (by positivity)
        _ ≤ C2 * (Real.log (2 + T))⁻¹ := by
            have : 0 ≤ C2 * (Real.log (2 + T))⁻¹ := by positivity
            linarith
    have hp3 : (1 / (2 * T)) * ((Cw6 * IM0 / (1 + L / 2) ^ 6) * (∑ g ∈ Gbig, (mZero g : ℝ))) ≤
        C3 * (Real.log (2 + T))⁻¹ := by
      have hTL_L : TL + L ≤ 2 * T * L := by dsimp only [TL]; nlinarith
      have hStot' : ∑ g ∈ Gbig, (mZero g : ℝ) ≤ 48 * CJ * T * L * Real.log (2 + T) := by
        calc ∑ g ∈ Gbig, (mZero g : ℝ) ≤ 6 * CJ * (TL + L) * Real.log (3 + (TL + L)) := hStot
          _ ≤ 6 * CJ * (2 * T * L) * (4 * Real.log (2 + T)) := by
              have h1 : 0 ≤ Real.log (3 + (TL + L)) := Real.log_nonneg (by linarith)
              have h2 : 6 * CJ * (TL + L) ≤ 6 * CJ * (2 * T * L) := mul_le_mul_of_nonneg_left hTL_L (by positivity)
              exact mul_le_mul h2 hlog_big h1 (by positivity)
          _ = 48 * CJ * T * L * Real.log (2 + T) := by ring
      calc _ ≤ (1 / (2 * T)) * ((Cw6 * IM0 / (1 + L / 2) ^ 6) * (48 * CJ * T * L * Real.log (2 + T))) := by gcongr
        _ = (24 * Cw6 * IM0 * CJ) * (L * Real.log (2 + T) / (1 + L / 2) ^ 6) := by field_simp [hT_pos.ne']; ring
        _ ≤ (24 * Cw6 * IM0 * CJ) * (64 * (Real.log (2 + T))⁻¹) := mul_le_mul_of_nonneg_left hL_div_half6 (by positivity)
        _ ≤ C3 * (Real.log (2 + T))⁻¹ := by
            dsimp only [C3]
            have : 0 ≤ Cw6 * IM0 * CJ * (Real.log (2 + T))⁻¹ := by positivity
            linarith
    have hfinal := mul_le_mul_of_nonneg_left hsum_diff (by positivity : 0 ≤ 1 / (2 * T))
    simp only [mul_add] at hfinal
    refine hfinal.trans ?_
    have h1 : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
    have h2 : 0 ≤ (Real.sqrt (X : ℝ))⁻¹ := inv_nonneg.mpr hsq_pos.le
    have hC1 : 0 ≤ C1 := by positivity
    have hC2 : 0 ≤ C2 := by positivity
    have hC3 : 0 ≤ C3 := by positivity
    dsimp only [Ctot]
    nlinarith [hp1, hp2, hp3]
  · simpa using tendsto_eps_zero.const_mul Ctot

lemma abel_summation_pos_zeros
    (homega_diff : Differentiable ℝ omegafun)
    (hcont_domega : Continuous (deriv omegafun))
    {T Y : ℝ} (hT : 0 < T) (hY : 0 ≤ Y)
    (Gpos : Finset ℝ) (hGpos : ∀ g ∈ Gpos, 0 < g ∧ g ≤ Y) :
    ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T) =
      (∑ g ∈ Gpos, (mZero g : ℝ)) * omegafun (Y / T) -
      ∫ y in (0 : ℝ)..Y, (∑ g ∈ Gpos, if g ≤ y then (mZero g : ℝ) else 0) * (deriv omegafun (y / T) / T) := by
  have hcont_d : Continuous (fun y : ℝ => deriv omegafun (y / T) / T) :=
    (hcont_domega.comp (continuous_id.div_const T)).div_const T
  have hterm_ftc : ∀ g ∈ Gpos,
      omegafun (Y / T) - omegafun (g / T) =
        ∫ y in (0 : ℝ)..Y, if g ≤ y then deriv omegafun (y / T) / T else 0 := by
    intro g hg
    have hg0 : 0 < g := (hGpos g hg).1
    have hgY : g ≤ Y := (hGpos g hg).2
    have hderiv : ∀ y ∈ Set.uIcc g Y,
        HasDerivAt (fun x : ℝ => omegafun (x / T)) (deriv omegafun (y / T) / T) y := by
      intro y _
      have h1 : HasDerivAt (fun x : ℝ => x / T) (1 / T) y := by
        have := (hasDerivAt_id y).div_const T
        simpa [id_eq] using this
      have h2 : HasDerivAt (omegafun ∘ fun x : ℝ => x / T) (deriv omegafun (y / T) * (1 / T)) y :=
        (homega_diff (y / T)).hasDerivAt.comp y h1
      exact h2.congr_deriv (by ring)
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont_d.intervalIntegrable g Y)]
    -- Split `∫_0^Y (if g ≤ y then f y else 0) dy = ∫_0^g 0 + ∫_g^Y f y`
    have hne_ae : ∀ᵐ y : ℝ, y ≠ g := by
      rw [MeasureTheory.ae_iff]; simpa using (Set.finite_singleton g).measure_zero (volume : Measure ℝ)
    have hint1 : IntervalIntegrable (fun y : ℝ => if g ≤ y then deriv omegafun (y / T) / T else 0) volume 0 g := by
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc, MeasureTheory.ae_restrict_of_ae hne_ae] with y hy hne
      rw [Set.uIoc_of_le hg0.le] at hy
      exact (if_neg (not_le.mpr (lt_of_le_of_ne hy.2 hne))).symm
    have hint2 : IntervalIntegrable (fun y : ℝ => if g ≤ y then deriv omegafun (y / T) / T else 0) volume g Y :=
      (hcont_d.intervalIntegrable g Y).congr fun y hy => by
        rw [Set.uIoc_of_le hgY] at hy; exact (if_pos hy.1.le).symm
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hzero : ∫ y in (0 : ℝ)..g, (if g ≤ y then deriv omegafun (y / T) / T else 0) = 0 := by
      have hcongr : ∫ y in (0 : ℝ)..g, (if g ≤ y then deriv omegafun (y / T) / T else 0) = ∫ _y in (0 : ℝ)..g, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hne_ae] with y hne hy
        rw [Set.uIoc_of_le hg0.le] at hy
        exact if_neg (not_le.mpr (lt_of_le_of_ne hy.2 hne))
      rw [hcongr]; simp
    have heq2 : ∫ y in g..Y, (if g ≤ y then deriv omegafun (y / T) / T else 0) =
        ∫ y in g..Y, deriv omegafun (y / T) / T :=
      intervalIntegral.integral_congr fun y hy => by rw [Set.uIcc_of_le hgY] at hy; exact if_pos hy.1
    rw [hzero, zero_add, heq2]
  have hint_g : ∀ g ∈ Gpos, IntervalIntegrable
      (fun y : ℝ => (mZero g : ℝ) * (if g ≤ y then deriv omegafun (y / T) / T else 0)) volume 0 Y := by
    intro g hg
    have hg0 : 0 < g := (hGpos g hg).1
    have hgY : g ≤ Y := (hGpos g hg).2
    have hne_ae : ∀ᵐ y : ℝ, y ≠ g := by
      rw [MeasureTheory.ae_iff]; simpa using (Set.finite_singleton g).measure_zero (volume : Measure ℝ)
    have h1 : IntervalIntegrable (fun y : ℝ => if g ≤ y then deriv omegafun (y / T) / T else 0) volume 0 g := by
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc, MeasureTheory.ae_restrict_of_ae hne_ae] with y hy hne
      rw [Set.uIoc_of_le hg0.le] at hy
      exact (if_neg (not_le.mpr (lt_of_le_of_ne hy.2 hne))).symm
    have h2 : IntervalIntegrable (fun y : ℝ => if g ≤ y then deriv omegafun (y / T) / T else 0) volume g Y :=
      (hcont_d.intervalIntegrable g Y).congr fun y hy => by
        rw [Set.uIoc_of_le hgY] at hy; exact (if_pos hy.1.le).symm
    exact (h1.trans h2).const_mul _
  have hsum_int : ∀ (S : Finset ℝ) (f : ℝ → ℝ → ℝ),
      (∀ g ∈ S, IntervalIntegrable (f g) volume 0 Y) →
      ∫ y in (0 : ℝ)..Y, ∑ g ∈ S, f g y = ∑ g ∈ S, ∫ y in (0 : ℝ)..Y, f g y := by
    intro S f hf
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      have hs : IntervalIntegrable (fun y => ∑ g ∈ s, f g y) volume 0 Y := by
        have heq : (fun y => ∑ g ∈ s, f g y) = ∑ g ∈ s, f g := by ext y; simp [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s (fun g hg => hf g (Finset.mem_insert_of_mem hg))
      rw [intervalIntegral.integral_add (hf a (Finset.mem_insert_self a s)) hs,
        ih (fun g hg => hf g (Finset.mem_insert_of_mem hg))]
  have hstep : (∑ g ∈ Gpos, (mZero g : ℝ)) * omegafun (Y / T) - ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T) =
      ∫ y in (0 : ℝ)..Y, (∑ g ∈ Gpos, if g ≤ y then (mZero g : ℝ) else 0) * (deriv omegafun (y / T) / T) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc ∑ g ∈ Gpos, ((mZero g : ℝ) * omegafun (Y / T) - (mZero g : ℝ) * omegafun (g / T))
        = ∑ g ∈ Gpos, (mZero g : ℝ) * (omegafun (Y / T) - omegafun (g / T)) :=
          Finset.sum_congr rfl fun g _ => by ring
      _ = ∑ g ∈ Gpos, (mZero g : ℝ) * ∫ y in (0 : ℝ)..Y, if g ≤ y then deriv omegafun (y / T) / T else 0 :=
          Finset.sum_congr rfl fun g hg => by rw [hterm_ftc g hg]
      _ = ∑ g ∈ Gpos, ∫ y in (0 : ℝ)..Y, (mZero g : ℝ) * (if g ≤ y then deriv omegafun (y / T) / T else 0) :=
          Finset.sum_congr rfl fun g _ => (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ y in (0 : ℝ)..Y, ∑ g ∈ Gpos, (mZero g : ℝ) * (if g ≤ y then deriv omegafun (y / T) / T else 0) :=
          (hsum_int Gpos _ hint_g).symm
      _ = ∫ y in (0 : ℝ)..Y, (∑ g ∈ Gpos, if g ≤ y then (mZero g : ℝ) else 0) * (deriv omegafun (y / T) / T) := by
          refine intervalIntegral.integral_congr fun y _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun g _ => by split_ifs <;> ring
  linarith

set_option maxHeartbeats 2000000 in
lemma diagApprox_tendsto_dfun_two
    (hRH : RiemannHypothesis)
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hzeta_conj : ∀ {s : ℂ}, s ≠ 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s))
    (hord_conj : ∀ {s : ℂ}, s ≠ 1 → analyticOrderNatAt riemannZeta (starRingEnd ℂ s) = analyticOrderNatAt riemannZeta s)
    (hzero_re : ∀ {ρ : ℂ}, -(1 / 2 : ℝ) ≤ ρ.re → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hM_planch : ∫ v : ℝ, ‖Mfun v‖ ^ 2 = 2 * Real.pi * ∫ u : ℝ, (Wfun u) ^ 2 / u)
    (homega_even : ∀ t : ℝ, omegafun (-t) = omegafun t)
    (homega_diff : Differentiable ℝ omegafun)
    (hcont_domega : Continuous (deriv omegafun))
    (homega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C / (1 + |t|) ^ n)
    (hdomega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv omegafun t| ≤ C / (1 + |t|) ^ n)
    (homega_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C * t ^ 2)
    (homega_int : Integrable omegafun)
    (homega_Ioi_zero : ∫ u in Set.Ioi (0 : ℝ), omegafun u = 0)
    (homega_Ioi_log : ∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u =
      (1 / 16 : ℝ) * ∫ v : ℝ, Kfun v * (1 / (2 + v + 1 / 5) + 1 / (2 + v - 1 / 5) - 2 / (2 + v)))
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRvM : ∀ T : ℝ, 2 ≤ T →
      |(∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T then
          (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) -
        ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))| ≤
        CR * Real.log (2 + T)) :
    Tendsto DiagApprox atTop (𝓝 (dfun 2)) := by
  obtain ⟨Cw6, hCw6, homega6⟩ := homega_dec 6
  obtain ⟨Cd4, hCd4, hdomega4⟩ := hdomega_dec 4
  obtain ⟨Csq, hCsq, hsq⟩ := homega_sq
  have hcont_omega : Continuous omegafun := homega_diff.continuous
  set IM0 : ℝ := ∫ v : ℝ, ‖Mfun v‖ ^ 2
  have hIM0_nn : 0 ≤ IM0 := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hdfun2 : dfun 2 = (IM0 / (2 * Real.pi)) * ∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u := by
    unfold dfun
    rw [homega_Ioi_log, hM_planch]
    field_simp [Real.pi_pos.ne']; ring
  -- Integrability of `omegafun u * Real.log u` on `Set.Ioi 0`
  have hint_omlog : IntegrableOn (fun u : ℝ => omegafun u * Real.log u) (Set.Ioi 0) := by
    have hcont : ContinuousOn (fun u : ℝ => omegafun u * Real.log u) (Set.Ioi 0) :=
      hcont_omega.continuousOn.mul (Real.continuousOn_log.mono fun u hu => ne_of_gt (Set.mem_Ioi.mp hu))
    have hdom : IntegrableOn (fun u : ℝ => (8 * Csq + Cw6) / (1 + |u|) ^ 3) (Set.Ioi 0) :=
      (integrable_div_one_add_abs_pow7 (8 * Csq + Cw6) 3 (by norm_num)).integrableOn
    refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu0]
    by_cases h1 : u ≤ 1
    · have hlog_bd : |Real.log u| ≤ 1 / u := by
        rw [abs_of_nonpos (Real.log_nonpos hu0.le h1), ← Real.log_inv]
        linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hu0), show u⁻¹ = 1 / u from (one_div u).symm]
      have h1u : (1 + u) ^ 3 ≤ 8 := by
        calc (1 + u) ^ 3 ≤ (1 + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
          _ = 8 := by norm_num
      calc |omegafun u| * |Real.log u| ≤ (Csq * u ^ 2) * (1 / u) :=
            mul_le_mul (hsq u) hlog_bd (abs_nonneg _) (by positivity)
        _ = Csq * u := by field_simp [hu0.ne']
        _ ≤ Csq := by nlinarith
        _ = (8 * Csq) / 8 := by ring
        _ ≤ (8 * Csq) / (1 + u) ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) h1u
        _ ≤ (8 * Csq + Cw6) / (1 + u) ^ 3 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    · push Not at h1
      have hlog_bd : |Real.log u| ≤ 1 + u := by
        rw [abs_of_nonneg (Real.log_nonneg h1.le)]
        linarith [Real.log_le_sub_one_of_pos hu0]
      calc |omegafun u| * |Real.log u| ≤ (Cw6 / (1 + |u|) ^ 6) * (1 + u) :=
            mul_le_mul (homega6 u) hlog_bd (abs_nonneg _) (by positivity)
        _ = Cw6 / (1 + u) ^ 5 := by
            rw [abs_of_pos hu0]; have hne : 1 + u ≠ 0 := by linarith
            field_simp [hne]
        _ ≤ (8 * Csq + Cw6) / (1 + u) ^ 3 := by
            have hpow : (1 + u) ^ 3 ≤ (1 + u) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
            exact (div_le_div_of_nonneg_left hCw6 (by positivity) hpow).trans
              (div_le_div_of_nonneg_right (by linarith) (by positivity))
  let M_RvM : ℝ → ℝ := fun y => (y / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) - y / (2 * Real.pi)
  let Nstrip : ℝ → ℝ := fun y => ∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ y then
    (analyticOrderNatAt riemannZeta ρ : ℝ) else 0
  set N2 : ℝ := Nstrip 2
  have hN2_nn : 0 ≤ N2 := finsum_nonneg fun _ => by split_ifs <;> positivity
  have homega_zero : omegafun 0 = 0 := by unfold omegafun lfun; simp
  set Ctot : ℝ := IM0 * (16 * CR * Cw6 + |M_RvM 2| * Cw6 + 2 * N2 * Cd4 + 16 * CR * Cd4 + 18 * Cw6 + 2 * Csq)
  have hsub_zero : Tendsto (fun X : ℕ => DiagApprox X - dfun 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun X : ℕ => Ctot * ((Real.log (2 + Tfun X))⁻¹ + (Real.sqrt (X : ℝ))⁻¹)) ?_ ?_
    · rw [Filter.eventually_atTop]
      refine ⟨200, fun X hX => ?_⟩
      have hXr_pos : (0 : ℝ) < (X : ℝ) := by positivity
      have hT_ge := Tfun_ge_of_ge hX
      have hT_pos : 0 < Tfun X := by linarith
      have hlog_ge := log_Tfun_ge_two hX
      obtain ⟨hL_ge4, hL_sq, hL_half⟩ := Lfun_bounds hX
      set T := Tfun X
      set L := Lfun X
      set Y := T * L
      have hY_ge : 4800 ≤ Y := by dsimp only [Y]; nlinarith
      have hY_pos : 0 < Y := by linarith
      have hX_real : (200 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have hsq_pos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXr_pos
      have hT_ge6X : 6 * (X : ℝ) ≤ T := by unfold T Tfun; nlinarith [Real.pi_gt_three]
      have hsqX_le_T : Real.sqrt (X : ℝ) ≤ T := by
        have h1 : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
          calc Real.sqrt (X : ℝ) ≤ Real.sqrt ((X : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = (X : ℝ) := Real.sqrt_sq hXr_pos.le
        linarith
      have hinvT_le : 1 / T ≤ (Real.sqrt (X : ℝ))⁻¹ := by
        rw [one_div]; exact inv_anti₀ hsq_pos hsqX_le_T
      have hlog_div_T : Real.log (2 + T) / T ≤ 8 * (Real.sqrt (X : ℝ))⁻¹ := by
        have h2T : 2 + T ≤ 9 * (X : ℝ) := by unfold T Tfun; nlinarith [Real.pi_lt_four]
        have hsq9 : Real.sqrt (2 + T) ≤ 3 * Real.sqrt (X : ℝ) := by
          calc Real.sqrt (2 + T) ≤ Real.sqrt (9 * (X : ℝ)) := Real.sqrt_le_sqrt h2T
            _ = 3 * Real.sqrt (X : ℝ) := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by norm_num]
        have hlog_le : Real.log (2 + T) ≤ 48 * Real.sqrt (X : ℝ) := by
          have h1 : Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 2 := by nlinarith
          have h2 : (Real.log (2 + T)) ^ 2 = L := rfl
          linarith
        calc Real.log (2 + T) / T ≤ (48 * Real.sqrt (X : ℝ)) / (6 * (X : ℝ)) :=
              div_le_div₀ (by positivity) hlog_le (by positivity) hT_ge6X
          _ = (48 * Real.sqrt (X : ℝ)) / (6 * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ))) := by
              rw [Real.mul_self_sqrt hXr_pos.le]
          _ = 8 * (Real.sqrt (X : ℝ))⁻¹ := by
              field_simp [hsq_pos.ne']; ring
      have hlog_Y : Real.log (2 + Y) ≤ 2 * Real.log (2 + T) := by
        have hle : 2 + Y ≤ (2 + T) ^ 2 := by dsimp only [Y]; nlinarith
        calc Real.log (2 + Y) ≤ Real.log ((2 + T) ^ 2) := Real.log_le_log (by linarith) hle
          _ = 2 * Real.log (2 + T) := by rw [Real.log_pow]; ring
      -- Step 1: Rewrite `DiagApprox X` as `(IM0 / T) * ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T)`
      have hfin_main := finite_zeros_in_Icc hzeta_ntop CJ hunit (-Y) Y
      set Gmain : Finset ℝ := hfin_main.toFinset
      set Gpos : Finset ℝ := Gmain.filter (fun g => 0 < g)
      set Gneg : Finset ℝ := Gmain.filter (fun g => g < 0)
      have hGmain_mem : ∀ g : ℝ, g ∈ Gmain ↔ -Y ≤ g ∧ g ≤ Y ∧ riemannZeta (zCrit g) = 0 := by
        intro g; simp [Gmain]
      have hconj_crit : ∀ g : ℝ, zCrit (-g) = starRingEnd ℂ (zCrit g) := fun g => by
        apply Complex.ext <;> simp [zCrit]
      have hzCrit_ne1 : ∀ g : ℝ, zCrit g ≠ 1 := fun g h => by
        have := congrArg Complex.re h; simp [zCrit] at this
      have hmZero_neg : ∀ g : ℝ, mZero (-g) = mZero g := fun g => by
        unfold mZero; rw [hconj_crit, hord_conj (hzCrit_ne1 g)]
      have hsum_main : (∑ᶠ g : ℝ, if |g| ≤ Y ∧ riemannZeta (zCrit g) = 0 then (mZero g : ℝ) * omegafun (g / T) else 0) =
          ∑ g ∈ Gmain, (mZero g : ℝ) * omegafun (g / T) := by
        rw [finsum_eq_sum_of_support_subset _ (s := Gmain) (fun g hg => by
          rw [Function.mem_support] at hg
          split_ifs at hg with h
          · rw [Finset.mem_coe, hGmain_mem]; exact ⟨(abs_le.mp h.1).1, (abs_le.mp h.1).2, h.2⟩
          · exact (hg rfl).elim)]
        refine Finset.sum_congr rfl fun g hg => ?_
        have hm := (hGmain_mem g).mp hg
        have hc : |g| ≤ Y ∧ riemannZeta (zCrit g) = 0 := ⟨abs_le.mpr ⟨hm.1, hm.2.1⟩, hm.2.2⟩
        simp only [hc.1, hc.2, and_self, ↓reduceIte]
      have hsum_symm : ∑ g ∈ Gmain, (mZero g : ℝ) * omegafun (g / T) =
          2 * ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T) := by
        rw [← Finset.sum_filter_add_sum_filter_not Gmain (fun g => 0 < g)]
        have hnotpos : ∑ g ∈ Gmain.filter (fun g => ¬ 0 < g), (mZero g : ℝ) * omegafun (g / T) =
            ∑ g ∈ Gneg, (mZero g : ℝ) * omegafun (g / T) := by
          rw [← Finset.sum_filter_add_sum_filter_not (Gmain.filter (fun g => ¬ 0 < g)) (fun g => g < 0)]
          have hzero_part : ∑ g ∈ (Gmain.filter (fun g => ¬ 0 < g)).filter (fun g => ¬ g < 0),
              (mZero g : ℝ) * omegafun (g / T) = 0 := by
            refine Finset.sum_eq_zero fun g hg => ?_
            have h1 := (Finset.mem_filter.mp hg).2
            have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
            have hg0 : g = 0 := by linarith
            rw [hg0, zero_div, homega_zero, mul_zero]
          rw [hzero_part, add_zero]
          congr 1
          ext g; simp only [Gneg, Finset.mem_filter]
          exact ⟨fun ⟨⟨hm, _⟩, hlt⟩ => ⟨hm, hlt⟩, fun ⟨hm, hlt⟩ => ⟨⟨hm, by linarith⟩, hlt⟩⟩
        rw [hnotpos]
        have hneg_eq_pos : ∑ g ∈ Gneg, (mZero g : ℝ) * omegafun (g / T) =
            ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T) := by
          refine Finset.sum_bij (fun g _ => -g) ?_ ?_ ?_ ?_
          · intro g hg
            have hm := (hGmain_mem g).mp (Finset.mem_filter.mp hg).1
            have hlt : g < 0 := (Finset.mem_filter.mp hg).2
            rw [Finset.mem_filter, hGmain_mem]
            refine ⟨⟨by linarith, by linarith, ?_⟩, by linarith⟩
            rw [hconj_crit, hzeta_conj (hzCrit_ne1 g), hm.2.2, map_zero]
          · intro g1 _ g2 _ h; linarith
          · intro g hg
            have hm := (hGmain_mem g).mp (Finset.mem_filter.mp hg).1
            have hgt : 0 < g := (Finset.mem_filter.mp hg).2
            refine ⟨-g, ?_, neg_neg g⟩
            rw [Finset.mem_filter, hGmain_mem]
            refine ⟨⟨by linarith, by linarith, ?_⟩, by linarith⟩
            rw [hconj_crit, hzeta_conj (hzCrit_ne1 g), hm.2.2, map_zero]
          · intro g _
            rw [hmZero_neg, neg_div, homega_even]
        rw [hneg_eq_pos]; ring
      have hDiag_pos : DiagApprox X = (IM0 / T) * ∑ g ∈ Gpos, (mZero g : ℝ) * omegafun (g / T) := by
        unfold DiagApprox; dsimp only
        change (1 / (2 * T)) * IM0 *
            (∑ᶠ g : ℝ, if |g| ≤ Y ∧ riemannZeta (zCrit g) = 0 then (mZero g : ℝ) * omegafun (g / T) else 0) = _
        rw [hsum_main, hsum_symm]
        field_simp [hT_pos.ne']
      -- Step 2: Abel summation on `Gpos` and identification `Nfin y = Nstrip y` on `[0, Y]`
      let Nfin : ℝ → ℝ := fun y => ∑ g ∈ Gpos, if g ≤ y then (mZero g : ℝ) else 0
      have hGpos_bounds : ∀ g ∈ Gpos, 0 < g ∧ g ≤ Y := fun g hg =>
        ⟨(Finset.mem_filter.mp hg).2, ((hGmain_mem g).mp (Finset.mem_filter.mp hg).1).2.1⟩
      have hAbel := abel_summation_pos_zeros homega_diff hcont_domega hT_pos hY_pos.le Gpos hGpos_bounds
      have hYT : Y / T = L := by dsimp only [Y]; field_simp [hT_pos.ne']
      have hNfin_Y : Nfin Y = ∑ g ∈ Gpos, (mZero g : ℝ) :=
        Finset.sum_congr rfl fun g hg => by simp only [(hGpos_bounds g hg).2, ↓reduceIte]
      have hNfin_eq_Nstrip : ∀ y ∈ Set.Icc (0 : ℝ) Y, Nfin y = Nstrip y := by
        intro y hy
        set Sy : Finset ℂ := (Gpos.filter (fun g => g ≤ y)).image zCrit
        have hsupp : (Function.support fun ρ : ℂ =>
            if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ y then (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) ⊆ Sy := by
          intro ρ hρ
          rw [Function.mem_support] at hρ
          split_ifs at hρ with hc
          · have hord_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by intro h0; exact hρ (by simp [h0])
            have hne1 : ρ ≠ 1 := fun h => by rw [h] at hc; norm_num at hc
            have hζ0 : riemannZeta ρ = 0 := by
              by_contra hne0
              have hza := differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds hne1)
              exact hord_ne (by simp [analyticOrderNatAt, hza.analyticOrderAt_eq_zero.mpr hne0])
            have hre : ρ.re = 1 / 2 := hzero_re (by linarith [hc.1]) hζ0
            have hcrit : zCrit ρ.im = ρ := by apply Complex.ext <;> simp [zCrit, hre]
            rw [Finset.mem_coe]
            refine Finset.mem_image.mpr ⟨ρ.im, ?_, hcrit⟩
            rw [Finset.mem_filter, Finset.mem_filter, hGmain_mem]
            exact ⟨⟨⟨by linarith [hc.2.2.1], hc.2.2.2.trans hy.2, hcrit.symm ▸ hζ0⟩, hc.2.2.1⟩, hc.2.2.2⟩
          · exact (hρ rfl).elim
        dsimp only [Nstrip]
        rw [finsum_eq_sum_of_support_subset _ hsupp]
        rw [Finset.sum_image (fun g1 _ g2 _ h => by simpa [zCrit] using congrArg Complex.im h)]
        have hcongr : ∑ g ∈ Gpos.filter (fun g => g ≤ y),
            (if 0 < (zCrit g).re ∧ (zCrit g).re < 1 ∧ 0 < (zCrit g).im ∧ (zCrit g).im ≤ y then
              (analyticOrderNatAt riemannZeta (zCrit g) : ℝ) else 0) =
            ∑ g ∈ Gpos.filter (fun g => g ≤ y), (mZero g : ℝ) := by
          refine Finset.sum_congr rfl fun g hg => ?_
          have hg_pos : 0 < g := (hGpos_bounds g (Finset.mem_filter.mp hg).1).1
          have hg_le : g ≤ y := (Finset.mem_filter.mp hg).2
          have hc : 0 < (zCrit g).re ∧ (zCrit g).re < 1 ∧ 0 < (zCrit g).im ∧ (zCrit g).im ≤ y :=
            ⟨by simp [zCrit], by simp [zCrit]; norm_num, by simpa [zCrit] using hg_pos, by simpa [zCrit] using hg_le⟩
          simp only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, and_self, ↓reduceIte, mZero]
        rw [hcongr, Finset.sum_filter]
      -- Step 3: Integrability & integration by parts of `M_RvM` on `[2, Y]`
      have hcont_d : Continuous (fun y : ℝ => deriv omegafun (y / T) / T) :=
        (hcont_domega.comp (continuous_id.div_const T)).div_const T
      have hmeas_Nfin : Measurable Nfin := by
        dsimp only [Nfin]
        exact Finset.measurable_sum Gpos fun g _ =>
          Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const
      have hint_Nfin : ∀ a b : ℝ, a ≤ b →
          IntervalIntegrable (fun y : ℝ => Nfin y * (deriv omegafun (y / T) / T)) volume a b := by
        intro a b hab
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
        refine (integrableOn_const (hs := measure_Ioc_lt_top.ne)
          (C := (∑ g ∈ Gpos, (mZero g : ℝ)) * (Cd4 / T))).mono'
          (hmeas_Nfin.mul hcont_d.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have hN_le : |Nfin y| ≤ ∑ g ∈ Gpos, (mZero g : ℝ) := by
          have hnn : 0 ≤ Nfin y := Finset.sum_nonneg fun g _ => by split_ifs <;> positivity
          rw [abs_of_nonneg hnn]
          exact Finset.sum_le_sum fun g _ => by split_ifs; exact le_rfl; exact Nat.cast_nonneg _
        have hd_le : |deriv omegafun (y / T) / T| ≤ Cd4 / T := by
          rw [abs_div, abs_of_pos hT_pos]
          refine div_le_div_of_nonneg_right ?_ hT_pos.le
          exact (hdomega4 (y / T)).trans (div_le_self hCd4 (one_le_pow₀ (by linarith [abs_nonneg (y / T)])))
        exact mul_le_mul hN_le hd_le (abs_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      have hcont_MR : ContinuousOn M_RvM (Set.Icc 2 Y) := by
        have hdiv : ContinuousOn (fun y : ℝ => y / (2 * Real.pi)) (Set.Icc 2 Y) :=
          continuousOn_id.div_const (2 * Real.pi)
        exact (hdiv.mul (Real.continuousOn_log.comp hdiv fun y hy => ne_of_gt (div_pos (by linarith [hy.1]) (by positivity)))).sub hdiv
      have hcont_MR' : ContinuousOn (fun y : ℝ => (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi))) (Set.Icc 2 Y) :=
        continuousOn_const.mul (Real.continuousOn_log.comp (continuousOn_id.div_const (2 * Real.pi))
          fun y hy => ne_of_gt (div_pos (by linarith [hy.1]) (by positivity)))
      have hIBP : M_RvM Y * omegafun L - M_RvM 2 * omegafun (2 / T) =
          (∫ y in (2 : ℝ)..Y, (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T)) +
          (∫ y in (2 : ℝ)..Y, M_RvM y * (deriv omegafun (y / T) / T)) := by
        have hderiv : ∀ y ∈ Set.uIcc (2 : ℝ) Y,
            HasDerivAt (fun x : ℝ => M_RvM x * omegafun (x / T))
              ((1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T) +
                M_RvM y * (deriv omegafun (y / T) / T)) y := by
          intro y hy
          rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Y)] at hy
          have hy_pos : 0 < y := by linarith [hy.1]
          have h2pi_pos : 0 < 2 * Real.pi := by positivity
          have hlin : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) y := by
            simpa using (hasDerivAt_id y).div_const (2 * Real.pi)
          have hlog : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) (1 / y) y := by
            convert hlin.log (div_pos hy_pos h2pi_pos).ne' using 1
            field_simp [hy_pos.ne', h2pi_pos.ne']
          have hM : HasDerivAt M_RvM ((1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi))) y := by
            have h1 := (hlin.mul hlog).sub hlin
            convert h1 using 1
            field_simp [hy_pos.ne', h2pi_pos.ne']; ring
          have hom : HasDerivAt (fun x : ℝ => omegafun (x / T)) (deriv omegafun (y / T) / T) y := by
            have h1 : HasDerivAt (fun x : ℝ => x / T) (1 / T) y := by
              have := (hasDerivAt_id y).div_const T
              simpa [id_eq] using this
            have h2 : HasDerivAt (omegafun ∘ fun x : ℝ => x / T) (deriv omegafun (y / T) * (1 / T)) y :=
              (homega_diff (y / T)).hasDerivAt.comp y h1
            exact h2.congr_deriv (by ring)
          exact hM.mul hom
        have hi1 : IntervalIntegrable (fun y : ℝ => (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T)) volume 2 Y :=
          (hcont_MR'.mul (hcont_omega.comp (continuous_id.div_const T)).continuousOn).intervalIntegrable_of_Icc (by linarith)
        have hi2 : IntervalIntegrable (fun y : ℝ => M_RvM y * (deriv omegafun (y / T) / T)) volume 2 Y :=
          (hcont_MR.mul hcont_d.continuousOn).intervalIntegrable_of_Icc (by linarith)
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
        rw [intervalIntegral.integral_add hi1 hi2, hYT] at hftc
        exact hftc.symm
      -- Step 4: Change variables `y = T * u` in the main integral on `[2, Y]`
      have hmain_chg : (1 / T) * (∫ y in (2 : ℝ)..Y, (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T)) =
          (1 / (2 * Real.pi)) * (∫ u in (2 / T)..L, omegafun u * Real.log u) +
          (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * (∫ u in (2 / T)..L, omegafun u) := by
        have hchg := intervalIntegral.integral_comp_mul_left (a := 2 / T) (b := L) (c := T)
          (f := fun y : ℝ => (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T)) hT_pos.ne'
        have hTa : T * (2 / T) = 2 := mul_div_cancel₀ 2 hT_pos.ne'
        have hTb : T * L = Y := rfl
        rw [hTa, hTb, smul_eq_mul, ← one_div] at hchg
        rw [← hchg]
        have h2T_le_L : 2 / T ≤ L := by
          have : 2 / T ≤ 1 := (div_le_one hT_pos).mpr (by linarith)
          linarith
        have hcongr : ∫ u in (2 / T)..L, (1 / (2 * Real.pi)) * Real.log ((T * u) / (2 * Real.pi)) * omegafun ((T * u) / T) =
            ∫ u in (2 / T)..L, ((1 / (2 * Real.pi)) * (omegafun u * Real.log u) +
              (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * omegafun u) := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le h2T_le_L] at hu
          have hu_pos : 0 < u := lt_of_lt_of_le (div_pos (by norm_num) hT_pos) hu.1
          rw [mul_div_cancel_left₀ u hT_pos.ne',
            show (T * u) / (2 * Real.pi) = (T / (2 * Real.pi)) * u by ring,
            Real.log_mul (div_pos hT_pos (by positivity)).ne' hu_pos.ne']
          ring
        rw [hcongr]
        have hi_a : IntervalIntegrable (fun u : ℝ => (1 / (2 * Real.pi)) * (omegafun u * Real.log u)) volume (2 / T) L :=
          (continuousOn_const.mul (hcont_omega.continuousOn.mul
            (Real.continuousOn_log.mono fun u hu => by
              rw [Set.uIcc_of_le h2T_le_L] at hu; exact ne_of_gt (lt_of_lt_of_le (div_pos (by norm_num) hT_pos) hu.1)))).intervalIntegrable
        have hi_b : IntervalIntegrable (fun u : ℝ => (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * omegafun u) volume (2 / T) L :=
          (continuous_const.mul hcont_omega).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hi_a hi_b, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      -- Assemble exact difference identity for `DiagApprox X - dfun 2`
      have hsplit_0Y : ∫ y in (0 : ℝ)..Y, Nfin y * (deriv omegafun (y / T) / T) =
          (∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)) +
          (∫ y in (2 : ℝ)..Y, Nfin y * (deriv omegafun (y / T) / T)) :=
        (intervalIntegral.integral_add_adjacent_intervals (hint_Nfin 0 2 (by norm_num)) (hint_Nfin 2 Y (by linarith))).symm
      have hi_MR_d : IntervalIntegrable (fun y : ℝ => M_RvM y * (deriv omegafun (y / T) / T)) volume 2 Y :=
        (hcont_MR.mul hcont_d.continuousOn).intervalIntegrable_of_Icc (by linarith)
      have hdiff_2Y : (∫ y in (2 : ℝ)..Y, Nfin y * (deriv omegafun (y / T) / T)) -
          (∫ y in (2 : ℝ)..Y, M_RvM y * (deriv omegafun (y / T) / T)) =
          ∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T) := by
        rw [← intervalIntegral.integral_sub (hint_Nfin 2 Y (by linarith)) hi_MR_d]
        refine intervalIntegral.integral_congr fun y _ => by ring
      have hdiff_eq : DiagApprox X - dfun 2 = IM0 * (
          ((Nfin Y - M_RvM Y) * omegafun L) / T +
          (M_RvM 2 * omegafun (2 / T)) / T -
          (1 / T) * (∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)) -
          (1 / T) * (∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)) +
          (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * (∫ u in (2 / T)..L, omegafun u) +
          (1 / (2 * Real.pi)) * ((∫ u in (2 / T)..L, omegafun u * Real.log u) -
            (∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u))) := by
        rw [hDiag_pos, hdfun2, hAbel, ← hNfin_Y, hYT, hsplit_0Y]
        have hstep : (1 / T) * (Nfin Y * omegafun L - ((∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)) +
            (∫ y in (2 : ℝ)..Y, Nfin y * (deriv omegafun (y / T) / T)))) =
            ((Nfin Y - M_RvM Y) * omegafun L) / T +
            (M_RvM 2 * omegafun (2 / T)) / T -
            (1 / T) * (∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)) -
            (1 / T) * (∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)) +
            (1 / T) * (∫ y in (2 : ℝ)..Y, (1 / (2 * Real.pi)) * Real.log (y / (2 * Real.pi)) * omegafun (y / T)) := by
          linear_combination (1 / T) * hIBP - (1 / T) * hdiff_2Y
        rw [div_eq_mul_inv, ← one_div, mul_assoc, hstep, hmain_chg]
        ring
      -- Step 5: Bound each of the 6 error terms!
      have hb1 : |((Nfin Y - M_RvM Y) * omegafun L) / T| ≤ 16 * CR * Cw6 * (Real.sqrt (X : ℝ))⁻¹ := by
        rw [abs_div, abs_of_pos hT_pos, abs_mul, hNfin_eq_Nstrip Y ⟨hY_pos.le, le_rfl⟩]
        have h1 : |Nstrip Y - M_RvM Y| ≤ 2 * CR * Real.log (2 + T) :=
          (hRvM Y (by linarith)).trans (by nlinarith)
        have h2 : |omegafun L| ≤ Cw6 :=
          (homega6 L).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg L])))
        calc |Nstrip Y - M_RvM Y| * |omegafun L| / T
            ≤ (2 * CR * Real.log (2 + T)) * Cw6 / T := by
              exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hT_pos.le
          _ = (2 * CR * Cw6) * (Real.log (2 + T) / T) := by ring
          _ ≤ (2 * CR * Cw6) * (8 * (Real.sqrt (X : ℝ))⁻¹) := mul_le_mul_of_nonneg_left hlog_div_T (by positivity)
          _ = 16 * CR * Cw6 * (Real.sqrt (X : ℝ))⁻¹ := by ring
      have hb2 : |(M_RvM 2 * omegafun (2 / T)) / T| ≤ |M_RvM 2| * Cw6 * (Real.sqrt (X : ℝ))⁻¹ := by
        rw [abs_div, abs_of_pos hT_pos, abs_mul]
        have h2 : |omegafun (2 / T)| ≤ Cw6 :=
          (homega6 (2 / T)).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg (2 / T)])))
        calc |M_RvM 2| * |omegafun (2 / T)| / T
            = (|M_RvM 2| * |omegafun (2 / T)|) * (1 / T) := by ring
          _ ≤ (|M_RvM 2| * Cw6) * (Real.sqrt (X : ℝ))⁻¹ :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) hinvT_le (by positivity) (by positivity)
          _ = |M_RvM 2| * Cw6 * (Real.sqrt (X : ℝ))⁻¹ := by ring
      have hb3 : |(1 / T) * (∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T))| ≤
          2 * N2 * Cd4 * (Real.sqrt (X : ℝ))⁻¹ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hT_pos)]
        have hpt : ∀ y ∈ Set.Icc (0 : ℝ) 2, |Nfin y * (deriv omegafun (y / T) / T)| ≤ N2 * (Cd4 / T) := by
          intro y hy
          rw [abs_mul]
          have hN_nn : 0 ≤ Nfin y := Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
          have hN_le2 : Nfin y ≤ N2 := by
            have h2eq : Nfin 2 = N2 := hNfin_eq_Nstrip 2 ⟨by norm_num, by linarith⟩
            rw [← h2eq]
            refine Finset.sum_le_sum fun g _ => ?_
            split_ifs with h1 h2
            · exact le_rfl
            · exact (h2 (h1.trans hy.2)).elim
            · positivity
            · exact le_rfl
          have hd_le : |deriv omegafun (y / T) / T| ≤ Cd4 / T := by
            rw [abs_div, abs_of_pos hT_pos]
            exact div_le_div_of_nonneg_right
              ((hdomega4 (y / T)).trans (div_le_self hCd4 (one_le_pow₀ (by linarith [abs_nonneg (y / T)])))) hT_pos.le
          rw [abs_of_nonneg hN_nn]
          exact mul_le_mul hN_le2 hd_le (abs_nonneg _) hN2_nn
        have hint_bd : |∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)| ≤ 2 * (N2 * (Cd4 / T)) := by
          calc _ ≤ ∫ y in (0 : ℝ)..2, |Nfin y * (deriv omegafun (y / T) / T)| := by
                simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
                  (f := fun y : ℝ => Nfin y * (deriv omegafun (y / T) / T)) (by norm_num : (0 : ℝ) ≤ 2)
            _ ≤ ∫ _y in (0 : ℝ)..2, (N2 * (Cd4 / T)) :=
                intervalIntegral.integral_mono_on (by norm_num)
                  (hint_Nfin 0 2 (by norm_num)).norm intervalIntegrable_const hpt
            _ = 2 * (N2 * (Cd4 / T)) := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        have h1T : 1 / T ≤ 1 := (div_le_one hT_pos).mpr (by linarith)
        calc (1 / T) * |∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T)|
            ≤ 1 * (2 * (N2 * (Cd4 / T))) := mul_le_mul h1T hint_bd (abs_nonneg _) zero_le_one
          _ = (2 * N2 * Cd4) * (1 / T) := by ring
          _ ≤ (2 * N2 * Cd4) * (Real.sqrt (X : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hinvT_le (by positivity)
          _ = 2 * N2 * Cd4 * (Real.sqrt (X : ℝ))⁻¹ := by ring
      have hb4 : |(1 / T) * (∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T))| ≤
          16 * CR * Cd4 * (Real.sqrt (X : ℝ))⁻¹ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hT_pos)]
        have hi_diff : IntervalIntegrable (fun y : ℝ => (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)) volume 2 Y := by
          have heq : (fun y : ℝ => (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)) =
              (fun y : ℝ => Nfin y * (deriv omegafun (y / T) / T) - M_RvM y * (deriv omegafun (y / T) / T)) := by
            ext y; ring
          rw [heq]; exact (hint_Nfin 2 Y (by linarith)).sub hi_MR_d
        have hpt : ∀ y ∈ Set.Icc (2 : ℝ) Y,
            |(Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)| ≤
              (2 * CR * Cd4 * Real.log (2 + T) / T) * (1 / (1 + y / T) ^ 4) := by
          intro y hy
          rw [abs_mul, abs_div, abs_of_pos hT_pos, hNfin_eq_Nstrip y ⟨by linarith [hy.1], hy.2⟩]
          have h1 : |Nstrip y - M_RvM y| ≤ 2 * CR * Real.log (2 + T) := by
            have hr := hRvM y hy.1
            have hl : Real.log (2 + y) ≤ Real.log (2 + Y) := Real.log_le_log (by linarith [hy.1]) (by linarith [hy.2])
            calc |Nstrip y - M_RvM y| ≤ CR * Real.log (2 + y) := hr
              _ ≤ CR * Real.log (2 + Y) := mul_le_mul_of_nonneg_left hl hCR
              _ ≤ CR * (2 * Real.log (2 + T)) := mul_le_mul_of_nonneg_left hlog_Y hCR
              _ = 2 * CR * Real.log (2 + T) := by ring
          have h2 : |deriv omegafun (y / T)| / T ≤ (Cd4 / T) * (1 / (1 + y / T) ^ 4) := by
            have hyT_nn : 0 ≤ y / T := div_nonneg (by linarith [hy.1]) hT_pos.le
            have hd := hdomega4 (y / T)
            rw [abs_of_nonneg hyT_nn] at hd
            calc |deriv omegafun (y / T)| / T ≤ (Cd4 / (1 + y / T) ^ 4) / T :=
                  div_le_div_of_nonneg_right hd hT_pos.le
              _ = (Cd4 / T) * (1 / (1 + y / T) ^ 4) := by ring
          calc |Nstrip y - M_RvM y| * (|deriv omegafun (y / T)| / T)
              ≤ (2 * CR * Real.log (2 + T)) * ((Cd4 / T) * (1 / (1 + y / T) ^ 4)) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = (2 * CR * Cd4 * Real.log (2 + T) / T) * (1 / (1 + y / T) ^ 4) := by ring
        have hi_rhs : IntervalIntegrable (fun y : ℝ => (2 * CR * Cd4 * Real.log (2 + T) / T) * (1 / (1 + y / T) ^ 4)) volume 2 Y :=
          (continuousOn_const.mul (continuousOn_const.div
            ((continuousOn_const.add (continuousOn_id.div_const T)).pow 4)
            fun y hy => by
              rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Y)] at hy
              have : 0 ≤ y / T := div_nonneg (by linarith [hy.1]) hT_pos.le
              show (1 + y / T) ^ 4 ≠ 0
              exact pow_ne_zero 4 (by linarith))).intervalIntegrable
        have hchg4 : (1 / T) * (∫ y in (2 : ℝ)..Y, 1 / (1 + y / T) ^ 4) ≤ 1 := by
          have hch := intervalIntegral.integral_comp_mul_left (a := 2 / T) (b := L) (c := T)
            (f := fun y : ℝ => (1 : ℝ) / (1 + y / T) ^ 4) hT_pos.ne'
          rw [mul_div_cancel₀ 2 hT_pos.ne', show T * L = Y from rfl, smul_eq_mul, ← one_div] at hch
          rw [← hch]
          have h2T_le_L : 2 / T ≤ L := by have : 2 / T ≤ 1 := (div_le_one hT_pos).mpr (by linarith); linarith
          have hcongr : ∫ u in (2 / T)..L, (1 : ℝ) / (1 + (T * u) / T) ^ 4 = ∫ u in (2 / T)..L, (1 : ℝ) / (1 + u) ^ 4 :=
            intervalIntegral.integral_congr fun u _ => by rw [mul_div_cancel_left₀ u hT_pos.ne']
          rw [hcongr, intervalIntegral.integral_of_le h2T_le_L]
          have hIoi_int : IntegrableOn (fun u : ℝ => (1 : ℝ) / (1 + u) ^ 4) (Set.Ioi 0) :=
            (integrable_div_one_add_abs_pow7 1 4 (by norm_num)).integrableOn.congr_fun
              (fun u hu => by dsimp only; rw [abs_of_pos (Set.mem_Ioi.mp hu)]) measurableSet_Ioi
          have h2T_pos0 : (0 : ℝ) < 2 / T := div_pos (by norm_num) hT_pos
          have hU1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 (2 / T) ∪ Set.Ioi (2 / T) := by
            ext u; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
            constructor
            · intro h; by_cases h2 : u ≤ 2 / T; exact Or.inl ⟨h, h2⟩; exact Or.inr (lt_of_not_ge h2)
            · rintro (⟨h, _⟩ | h); exact h; linarith
          have hU2 : Set.Ioi (2 / T) = Set.Ioc (2 / T) L ∪ Set.Ioi L := by
            ext u; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
            constructor
            · intro h; by_cases h2 : u ≤ L; exact Or.inl ⟨h, h2⟩; exact Or.inr (lt_of_not_ge h2)
            · rintro (⟨h, _⟩ | h); exact h; linarith
          have hd1 : Disjoint (Set.Ioc (0 : ℝ) (2 / T)) (Set.Ioi (2 / T)) :=
            Set.disjoint_left.mpr fun u h1 h2 => by linarith [h1.2, Set.mem_Ioi.mp h2]
          have hd2 : Disjoint (Set.Ioc (2 / T) L) (Set.Ioi L) :=
            Set.disjoint_left.mpr fun u h1 h2 => by linarith [h1.2, Set.mem_Ioi.mp h2]
          have hsp_I : ∫ u in Set.Ioi (0 : ℝ), (1 : ℝ) / (1 + u) ^ 4 =
              (∫ u in Set.Ioc (0 : ℝ) (2 / T), (1 : ℝ) / (1 + u) ^ 4) +
              (∫ u in Set.Ioc (2 / T) L, (1 : ℝ) / (1 + u) ^ 4) +
              (∫ u in Set.Ioi L, (1 : ℝ) / (1 + u) ^ 4) := by
            have hsub1 : Set.Ioc (0 : ℝ) (2 / T) ⊆ Set.Ioi 0 := fun u hu => hu.1
            have hsub2 : Set.Ioi (2 / T) ⊆ Set.Ioi 0 := fun u hu => lt_trans h2T_pos0 hu
            have hsub3 : Set.Ioc (2 / T) L ⊆ Set.Ioi (2 / T) := fun u hu => hu.1
            have hsub4 : Set.Ioi L ⊆ Set.Ioi (2 / T) := fun u hu => lt_of_le_of_lt h2T_le_L hu
            rw [hU1, MeasureTheory.setIntegral_union hd1 measurableSet_Ioi
              (hIoi_int.mono_set hsub1) (hIoi_int.mono_set hsub2),
              hU2, MeasureTheory.setIntegral_union hd2 measurableSet_Ioi
              ((hIoi_int.mono_set hsub2).mono_set hsub3) ((hIoi_int.mono_set hsub2).mono_set hsub4)]
            ring
          have hnn1 : 0 ≤ ∫ u in Set.Ioc (0 : ℝ) (2 / T), (1 : ℝ) / (1 + u) ^ 4 :=
            MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u hu => by have := hu.1; positivity
          have hnn2 : 0 ≤ ∫ u in Set.Ioi L, (1 : ℝ) / (1 + u) ^ 4 :=
            MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => by
              have hu_pos : 0 < u := by linarith [hL_ge4, Set.mem_Ioi.mp hu]
              positivity
          calc ∫ u in Set.Ioc (2 / T) L, (1 : ℝ) / (1 + u) ^ 4
              ≤ ∫ u in Set.Ioi (0 : ℝ), (1 : ℝ) / (1 + u) ^ 4 := by linarith
            _ = 1 / 3 := by rw [integral_Ioi_inv_one_add_pow le_rfl (by norm_num)]; norm_num
            _ ≤ 1 := by norm_num
        calc (1 / T) * |∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)|
            ≤ (1 / T) * ∫ y in (2 : ℝ)..Y, |(Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)| := by
              gcongr
              simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
                (f := fun y : ℝ => (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T)) (by linarith : (2 : ℝ) ≤ Y)
          _ ≤ (1 / T) * ∫ y in (2 : ℝ)..Y, (2 * CR * Cd4 * Real.log (2 + T) / T) * (1 / (1 + y / T) ^ 4) := by
              gcongr; exact intervalIntegral.integral_mono_on (by linarith) hi_diff.norm hi_rhs hpt
          _ = (2 * CR * Cd4 * (Real.log (2 + T) / T)) * ((1 / T) * ∫ y in (2 : ℝ)..Y, 1 / (1 + y / T) ^ 4) := by
              rw [intervalIntegral.integral_const_mul]; ring
          _ ≤ (2 * CR * Cd4 * (Real.log (2 + T) / T)) * 1 := by gcongr
          _ ≤ (2 * CR * Cd4) * (8 * (Real.sqrt (X : ℝ))⁻¹) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hlog_div_T (by positivity)
          _ = 16 * CR * Cd4 * (Real.sqrt (X : ℝ))⁻¹ := by ring
      -- Helper to split `Set.Ioi 0` at `2 / T` and `L`
      have h2T_pos : (0 : ℝ) < 2 / T := div_pos (by norm_num) hT_pos
      have h2T_le1 : 2 / T ≤ 1 := (div_le_one hT_pos).mpr (by linarith)
      have h2T_lt_L : 2 / T < L := by linarith
      have hsplit_Ioi : ∀ f : ℝ → ℝ, IntegrableOn f (Set.Ioi 0) →
          ∫ u in Set.Ioi (0 : ℝ), f u =
            (∫ u in Set.Ioc (0 : ℝ) (2 / T), f u) + (∫ u in (2 / T)..L, f u) + (∫ u in Set.Ioi L, f u) := by
        intro f hf
        have hU1 : Set.Ioi (0 : ℝ) = Set.Ioc 0 (2 / T) ∪ Set.Ioi (2 / T) := by
          ext u; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
          constructor
          · intro h; by_cases h2 : u ≤ 2 / T; exact Or.inl ⟨h, h2⟩; exact Or.inr (lt_of_not_ge h2)
          · rintro (⟨h, _⟩ | h); exact h; linarith
        have hU2 : Set.Ioi (2 / T) = Set.Ioc (2 / T) L ∪ Set.Ioi L := by
          ext u; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
          constructor
          · intro h; by_cases h2 : u ≤ L; exact Or.inl ⟨h, h2⟩; exact Or.inr (lt_of_not_ge h2)
          · rintro (⟨h, _⟩ | h); exact h; linarith
        have hd1 : Disjoint (Set.Ioc (0 : ℝ) (2 / T)) (Set.Ioi (2 / T)) :=
          Set.disjoint_left.mpr fun u h1 h2 => by linarith [h1.2, Set.mem_Ioi.mp h2]
        have hd2 : Disjoint (Set.Ioc (2 / T) L) (Set.Ioi L) :=
          Set.disjoint_left.mpr fun u h1 h2 => by linarith [h1.2, Set.mem_Ioi.mp h2]
        have hsub1 : Set.Ioc (0 : ℝ) (2 / T) ⊆ Set.Ioi 0 := fun u hu => hu.1
        have hsub2 : Set.Ioi (2 / T) ⊆ Set.Ioi 0 := fun u hu => lt_trans h2T_pos hu
        have hsub3 : Set.Ioc (2 / T) L ⊆ Set.Ioi (2 / T) := fun u hu => hu.1
        have hsub4 : Set.Ioi L ⊆ Set.Ioi (2 / T) := fun u hu => lt_trans h2T_lt_L hu
        rw [hU1, MeasureTheory.setIntegral_union hd1 measurableSet_Ioi (hf.mono_set hsub1) (hf.mono_set hsub2)]
        rw [hU2, MeasureTheory.setIntegral_union hd2 measurableSet_Ioi
          ((hf.mono_set hsub2).mono_set hsub3) ((hf.mono_set hsub2).mono_set hsub4)]
        rw [← intervalIntegral.integral_of_le h2T_lt_L.le]; ring
      have hb5 : |(Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * (∫ u in (2 / T)..L, omegafun u)| ≤
          17 * Cw6 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        have hsp := hsplit_Ioi omegafun homega_int.integrableOn
        rw [homega_Ioi_zero] at hsp
        have hint_eq : ∫ u in (2 / T)..L, omegafun u =
            -(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u) - (∫ u in Set.Ioi L, omegafun u) := by linarith
        have hp_sm : |∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u| ≤ Cw6 * (2 / T) := by
          rw [← intervalIntegral.integral_of_le h2T_pos.le]
          calc _ ≤ ∫ u in (0 : ℝ)..(2 / T), |omegafun u| := by
                simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
                  (f := omegafun) h2T_pos.le
            _ ≤ ∫ _u in (0 : ℝ)..(2 / T), Cw6 :=
                intervalIntegral.integral_mono_on h2T_pos.le
                  (hcont_omega.abs.intervalIntegrable 0 (2 / T)) intervalIntegrable_const
                  fun u _ => (homega6 u).trans (div_le_self hCw6 (one_le_pow₀ (by linarith [abs_nonneg u])))
            _ = Cw6 * (2 / T) := by simp; ring
        have hp_lg : |∫ u in Set.Ioi L, omegafun u| ≤ Cw6 / (1 + L) ^ 5 := by
          have hint_pow : IntegrableOn (fun u : ℝ => Cw6 / (1 + u) ^ 6) (Set.Ioi L) :=
            (integrable_div_one_add_abs_pow7 Cw6 6 (by norm_num)).integrableOn.congr_fun
              (fun u hu => by dsimp only; rw [abs_of_pos (by linarith [hL_ge4, Set.mem_Ioi.mp hu])]) measurableSet_Ioi
          calc |∫ u in Set.Ioi L, omegafun u|
              ≤ ∫ u in Set.Ioi L, |omegafun u| := by
                simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm (f := omegafun)
            _ ≤ ∫ u in Set.Ioi L, Cw6 / (1 + u) ^ 6 :=
                MeasureTheory.setIntegral_mono_on homega_int.integrableOn.norm hint_pow measurableSet_Ioi
                  fun u hu => by
                    have hu_pos : 0 < u := by linarith [hL_ge4, Set.mem_Ioi.mp hu]
                    simpa [abs_of_pos hu_pos] using homega6 u
            _ = Cw6 / (5 * (1 + L) ^ 5) := by
                have heq : (fun u : ℝ => Cw6 / (1 + u) ^ 6) = fun u => Cw6 * ((1 : ℝ) / (1 + u) ^ 6) := by ext u; ring
                rw [heq, MeasureTheory.integral_const_mul, integral_Ioi_inv_one_add_pow (by linarith) (by norm_num)]
                have hne : (1 + L) ^ 5 ≠ 0 := pow_ne_zero 5 (by linarith)
                norm_num; field_simp [hne]
            _ ≤ Cw6 / (1 + L) ^ 5 := by
                have h5 : (1 + L) ^ 5 ≤ 5 * (1 + L) ^ 5 := by
                  have hp : 0 < (1 + L) ^ 5 := pow_pos (by linarith) 5
                  linarith
                exact div_le_div_of_nonneg_left hCw6 (by positivity) h5
        have hlog_bd : |Real.log (T / (2 * Real.pi))| ≤ Real.log (2 + T) := by
          have hT2pi : T / (2 * Real.pi) = (X : ℝ) := by
            unfold T Tfun; field_simp [Real.pi_pos.ne']
          have hge1 : 1 ≤ T / (2 * Real.pi) := by rw [hT2pi]; linarith
          rw [abs_of_nonneg (Real.log_nonneg hge1)]
          exact Real.log_le_log (by linarith) (by
            have hle : T / (2 * Real.pi) ≤ T := div_le_self hT_pos.le (by linarith [Real.pi_gt_three])
            linarith)
        have hinv2pi : 1 / (2 * Real.pi) ≤ 1 := by
          have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          exact (div_le_one h2pi_pos).mpr (by linarith [Real.pi_gt_three])
        have hlog_L5 : Real.log (2 + T) / (1 + L) ^ 5 ≤ (Real.log (2 + T))⁻¹ := by
          have hpow : (Real.log (2 + T)) ^ 2 ≤ (1 + L) ^ 5 := by
            have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
            calc (Real.log (2 + T)) ^ 2 = L := hL_eq.symm
              _ ≤ 1 + L := by linarith
              _ ≤ (1 + L) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
          calc Real.log (2 + T) / (1 + L) ^ 5
              ≤ Real.log (2 + T) / (Real.log (2 + T)) ^ 2 :=
                div_le_div_of_nonneg_left (by linarith) (by positivity) hpow
            _ = (Real.log (2 + T))⁻¹ := by
                have hne : Real.log (2 + T) ≠ 0 := by linarith
                rw [sq, div_mul_eq_div_div, div_self hne, one_div]
        rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), hint_eq]
        have hint_abs : |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u) - ∫ u in Set.Ioi L, omegafun u| ≤
            Cw6 * (2 / T) + Cw6 / (1 + L) ^ 5 := by
          calc _ ≤ |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u)| + |∫ u in Set.Ioi L, omegafun u| := abs_sub _ _
            _ = |∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u| + |∫ u in Set.Ioi L, omegafun u| := by rw [abs_neg]
            _ ≤ Cw6 * (2 / T) + Cw6 / (1 + L) ^ 5 := add_le_add hp_sm hp_lg
        calc (|Real.log (T / (2 * Real.pi))| / (2 * Real.pi)) *
              |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u) - ∫ u in Set.Ioi L, omegafun u|
            = (1 / (2 * Real.pi)) * (|Real.log (T / (2 * Real.pi))| *
                |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u) - ∫ u in Set.Ioi L, omegafun u|) := by ring
          _ ≤ 1 * (Real.log (2 + T) * (Cw6 * (2 / T) + Cw6 / (1 + L) ^ 5)) :=
              mul_le_mul hinv2pi (mul_le_mul hlog_bd hint_abs (abs_nonneg _) (by linarith)) (by positivity) zero_le_one
          _ = 2 * Cw6 * (Real.log (2 + T) / T) + Cw6 * (Real.log (2 + T) / (1 + L) ^ 5) := by ring
          _ ≤ 2 * Cw6 * (8 * (Real.sqrt (X : ℝ))⁻¹) + Cw6 * (Real.log (2 + T))⁻¹ :=
              le_trans (add_le_add (mul_le_mul_of_nonneg_left hlog_div_T (by positivity))
                (mul_le_mul_of_nonneg_left hlog_L5 hCw6)) le_rfl
          _ ≤ 17 * Cw6 * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
              have h1 : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
              have h2 : 0 ≤ (Real.sqrt (X : ℝ))⁻¹ := inv_nonneg.mpr hsq_pos.le
              nlinarith
      have hb6 : |(1 / (2 * Real.pi)) * ((∫ u in (2 / T)..L, omegafun u * Real.log u) -
            (∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u))| ≤
          2 * Csq * (Real.sqrt (X : ℝ))⁻¹ + Cw6 * (Real.log (2 + T))⁻¹ := by
        have hsp := hsplit_Ioi (fun u => omegafun u * Real.log u) hint_omlog
        have hdiff_s : (∫ u in (2 / T)..L, omegafun u * Real.log u) - (∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u) =
            -(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u) - (∫ u in Set.Ioi L, omegafun u * Real.log u) := by
          linarith
        have hp_sm : |∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u| ≤ 2 * Csq * (Real.sqrt (X : ℝ))⁻¹ := by
          have hint_c : IntegrableOn (fun _ : ℝ => Csq) (Set.Ioc 0 (2 / T)) :=
            integrableOn_const (hs := measure_Ioc_lt_top.ne)
          calc |∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u|
              ≤ ∫ u in Set.Ioc (0 : ℝ) (2 / T), |omegafun u * Real.log u| := by
                simpa [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
                  (f := fun u : ℝ => omegafun u * Real.log u)
            _ ≤ ∫ _u in Set.Ioc (0 : ℝ) (2 / T), Csq := by
                have hsub0 : Set.Ioc (0 : ℝ) (2 / T) ⊆ Set.Ioi (0 : ℝ) := fun u hu => hu.1
                refine MeasureTheory.setIntegral_mono_on
                  (hint_omlog.mono_set hsub0).norm hint_c measurableSet_Ioc fun u hu => ?_
                have hu0 : 0 < u := hu.1
                have hu1 : u ≤ 1 := hu.2.trans h2T_le1
                rw [abs_mul]
                have hlog_bd : |Real.log u| ≤ 1 / u := by
                  rw [abs_of_nonpos (Real.log_nonpos hu0.le hu1), ← Real.log_inv]
                  linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hu0), show u⁻¹ = 1 / u from (one_div u).symm]
                calc |omegafun u| * |Real.log u| ≤ (Csq * u ^ 2) * (1 / u) :=
                      mul_le_mul (hsq u) hlog_bd (abs_nonneg _) (by positivity)
                  _ = Csq * u := by field_simp [hu0.ne']
                  _ ≤ Csq := by nlinarith
            _ = Csq * (2 / T) := by
                rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
                  Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring
            _ = (2 * Csq) * (1 / T) := by ring
            _ ≤ 2 * Csq * (Real.sqrt (X : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_left hinvT_le (by positivity)
        have hp_lg : |∫ u in Set.Ioi L, omegafun u * Real.log u| ≤ Cw6 * (Real.log (2 + T))⁻¹ := by
          have hint_pow : IntegrableOn (fun u : ℝ => Cw6 / (1 + u) ^ 5) (Set.Ioi L) :=
            (integrable_div_one_add_abs_pow7 Cw6 5 (by norm_num)).integrableOn.congr_fun
              (fun u hu => by dsimp only; rw [abs_of_pos (by linarith [hL_ge4, Set.mem_Ioi.mp hu])]) measurableSet_Ioi
          have hsubL : Set.Ioi L ⊆ Set.Ioi (0 : ℝ) := fun u hu => Set.mem_Ioi.mpr (by linarith [hL_ge4, Set.mem_Ioi.mp hu])
          have hL4 : Real.log (2 + T) ≤ (1 + L) ^ 4 := by
            have hL_eq : L = (Real.log (2 + T)) ^ 2 := rfl
            calc Real.log (2 + T) ≤ (Real.log (2 + T)) ^ 2 := by nlinarith
              _ = L := hL_eq.symm
              _ ≤ 1 + L := by linarith
              _ ≤ (1 + L) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
          calc |∫ u in Set.Ioi L, omegafun u * Real.log u|
              ≤ ∫ u in Set.Ioi L, |omegafun u * Real.log u| := by
                simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
                  (f := fun u : ℝ => omegafun u * Real.log u)
            _ ≤ ∫ u in Set.Ioi L, Cw6 / (1 + u) ^ 5 := by
                refine MeasureTheory.setIntegral_mono_on (hint_omlog.mono_set hsubL).norm hint_pow measurableSet_Ioi
                  fun u hu => ?_
                have hu0 : 0 < u := by linarith [hL_ge4, Set.mem_Ioi.mp hu]
                have hu1 : 1 ≤ u := by linarith [hL_ge4, Set.mem_Ioi.mp hu]
                rw [abs_mul]
                have hlog_bd : |Real.log u| ≤ 1 + u := by
                  rw [abs_of_nonneg (Real.log_nonneg hu1)]
                  linarith [Real.log_le_sub_one_of_pos hu0]
                calc |omegafun u| * |Real.log u| ≤ (Cw6 / (1 + |u|) ^ 6) * (1 + u) :=
                      mul_le_mul (homega6 u) hlog_bd (abs_nonneg _) (by positivity)
                  _ = Cw6 / (1 + u) ^ 5 := by
                      rw [abs_of_pos hu0]; have hne : 1 + u ≠ 0 := by linarith
                      field_simp [hne]
            _ = Cw6 / (4 * (1 + L) ^ 4) := by
                have heq : (fun u : ℝ => Cw6 / (1 + u) ^ 5) = fun u => Cw6 * ((1 : ℝ) / (1 + u) ^ 5) := by ext u; ring
                rw [heq, MeasureTheory.integral_const_mul, integral_Ioi_inv_one_add_pow (by linarith) (by norm_num)]
                have hne : (1 + L) ^ 4 ≠ 0 := pow_ne_zero 4 (by linarith)
                norm_num; field_simp [hne]
            _ ≤ Cw6 / (1 + L) ^ 4 := by
                have h4 : (1 + L) ^ 4 ≤ 4 * (1 + L) ^ 4 := by
                  have hp : 0 < (1 + L) ^ 4 := pow_pos (by linarith) 4
                  linarith
                exact div_le_div_of_nonneg_left hCw6 (by positivity) h4
            _ ≤ Cw6 / Real.log (2 + T) := div_le_div_of_nonneg_left hCw6 (by linarith) hL4
            _ = Cw6 * (Real.log (2 + T))⁻¹ := div_eq_mul_inv _ _
        have hinv2pi : 1 / (2 * Real.pi) ≤ 1 := by
          have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          exact (div_le_one h2pi_pos).mpr (by linarith [Real.pi_gt_three])
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)), hdiff_s]
        have habs : |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u) -
              ∫ u in Set.Ioi L, omegafun u * Real.log u| ≤
            2 * Csq * (Real.sqrt (X : ℝ))⁻¹ + Cw6 * (Real.log (2 + T))⁻¹ := by
          calc _ ≤ |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u)| +
                |∫ u in Set.Ioi L, omegafun u * Real.log u| := abs_sub _ _
            _ = |∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u| +
                |∫ u in Set.Ioi L, omegafun u * Real.log u| := by rw [abs_neg]
            _ ≤ 2 * Csq * (Real.sqrt (X : ℝ))⁻¹ + Cw6 * (Real.log (2 + T))⁻¹ := add_le_add hp_sm hp_lg
        calc (1 / (2 * Real.pi)) * |-(∫ u in Set.Ioc (0 : ℝ) (2 / T), omegafun u * Real.log u) -
              ∫ u in Set.Ioi L, omegafun u * Real.log u|
            ≤ 1 * (2 * Csq * (Real.sqrt (X : ℝ))⁻¹ + Cw6 * (Real.log (2 + T))⁻¹) :=
              mul_le_mul hinv2pi habs (abs_nonneg _) zero_le_one
          _ = 2 * Csq * (Real.sqrt (X : ℝ))⁻¹ + Cw6 * (Real.log (2 + T))⁻¹ := one_mul _
      -- Combine all 6 bounds!
      rw [Real.norm_eq_abs, hdiff_eq, abs_mul, abs_of_nonneg hIM0_nn]
      set a1 := ((Nfin Y - M_RvM Y) * omegafun L) / T
      set a2 := (M_RvM 2 * omegafun (2 / T)) / T
      set a3 := (1 / T) * (∫ y in (0 : ℝ)..2, Nfin y * (deriv omegafun (y / T) / T))
      set a4 := (1 / T) * (∫ y in (2 : ℝ)..Y, (Nfin y - M_RvM y) * (deriv omegafun (y / T) / T))
      set a5 := (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) * (∫ u in (2 / T)..L, omegafun u)
      set a6 := (1 / (2 * Real.pi)) * ((∫ u in (2 / T)..L, omegafun u * Real.log u) -
          (∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u))
      have htri : |a1 + a2 - a3 - a4 + a5 + a6| ≤ |a1| + |a2| + |a3| + |a4| + |a5| + |a6| := by
        calc |a1 + a2 - a3 - a4 + a5 + a6|
            ≤ |a1 + a2 - a3 - a4 + a5| + |a6| := abs_add_le _ _
          _ ≤ (|a1 + a2 - a3 - a4| + |a5|) + |a6| := by gcongr; exact abs_add_le _ _
          _ ≤ ((|a1 + a2 - a3| + |a4|) + |a5|) + |a6| := by gcongr; exact abs_sub _ _
          _ ≤ (((|a1 + a2| + |a3|) + |a4|) + |a5|) + |a6| := by gcongr; exact abs_sub _ _
          _ ≤ ((((|a1| + |a2|) + |a3|) + |a4|) + |a5|) + |a6| := by gcongr; exact abs_add_le _ _
          _ = |a1| + |a2| + |a3| + |a4| + |a5| + |a6| := by ring
      have hsum6 : |a1| + |a2| + |a3| + |a4| + |a5| + |a6| ≤
          (16 * CR * Cw6 + |M_RvM 2| * Cw6 + 2 * N2 * Cd4 + 16 * CR * Cd4 + 18 * Cw6 + 2 * Csq) *
            ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by
        have h1 : 0 ≤ (Real.log (2 + T))⁻¹ := inv_nonneg.mpr (by linarith)
        have h2 : 0 ≤ (Real.sqrt (X : ℝ))⁻¹ := inv_nonneg.mpr hsq_pos.le
        have hM2_nn : 0 ≤ |M_RvM 2| := abs_nonneg _
        have hk1 : 0 ≤ (16 * CR * Cw6 + |M_RvM 2| * Cw6 + 2 * N2 * Cd4 + 16 * CR * Cd4 + 2 * Csq) * (Real.log (2 + T))⁻¹ := by positivity
        have hk2 : 0 ≤ Cw6 * (Real.sqrt (X : ℝ))⁻¹ := by positivity
        linarith [hb1, hb2, hb3, hb4, hb5, hb6, hk1, hk2]
      calc IM0 * |a1 + a2 - a3 - a4 + a5 + a6|
          ≤ IM0 * ((16 * CR * Cw6 + |M_RvM 2| * Cw6 + 2 * N2 * Cd4 + 16 * CR * Cd4 + 18 * Cw6 + 2 * Csq) *
              ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹)) :=
            mul_le_mul_of_nonneg_left (htri.trans hsum6) hIM0_nn
        _ = Ctot * ((Real.log (2 + T))⁻¹ + (Real.sqrt (X : ℝ))⁻¹) := by dsimp only [Ctot]; ring
    · simpa using tendsto_eps_zero.const_mul Ctot
  simpa using hsub_zero.add_const (dfun 2)

theorem spectral_comparison_from_modules
    (hRH : RiemannHypothesis)
    (hzeta_ntop : ∀ z : ℂ, meromorphicOrderAt riemannZeta z ≠ ⊤)
    (hzeta_conj : ∀ {s : ℂ}, s ≠ 1 → riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s))
    (hord_conj : ∀ {s : ℂ}, s ≠ 1 → analyticOrderNatAt riemannZeta (starRingEnd ℂ s) = analyticOrderNatAt riemannZeta s)
    (hzero_re : ∀ {ρ : ℂ}, -(1 / 2 : ℝ) ≤ ρ.re → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hcont_kfun : Continuous kfun)
    (hcont_Mfun : Continuous Mfun)
    (hk_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |kfun t| ≤ C / (1 + |t|) ^ n)
    (hM_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Mfun v‖ ≤ C / (1 + |v|) ^ n)
    (hM_planch : ∫ v : ℝ, ‖Mfun v‖ ^ 2 = 2 * Real.pi * ∫ u : ℝ, (Wfun u) ^ 2 / u)
    (homega_even : ∀ t : ℝ, omegafun (-t) = omegafun t)
    (homega_diff : Differentiable ℝ omegafun)
    (hcont_domega : Continuous (deriv omegafun))
    (homega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C / (1 + |t|) ^ n)
    (hdomega_dec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv omegafun t| ≤ C / (1 + |t|) ^ n)
    (homega_sq : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |omegafun t| ≤ C * t ^ 2)
    (homega_int : Integrable omegafun)
    (homega_Ioi_zero : ∫ u in Set.Ioi (0 : ℝ), omegafun u = 0)
    (homega_Ioi_log : ∫ u in Set.Ioi (0 : ℝ), omegafun u * Real.log u =
      (1 / 16 : ℝ) * ∫ v : ℝ, Kfun v * (1 / (2 + v + 1 / 5) + 1 / (2 + v - 1 / 5) - 2 / (2 + v)))
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hunit : ∀ a : ℝ,
      (Function.support fun g : ℝ => if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0).Finite ∧
      (∑ᶠ g : ℝ, if a ≤ g ∧ g < a + 1 then (mZero g : ℝ) else 0) ≤ CJ * Real.log (2 + |a|))
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRvM : ∀ T : ℝ, 2 ≤ T →
      |(∑ᶠ ρ : ℂ, if 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T then
          (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) -
        ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))| ≤
        CR * Real.log (2 + T))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hpole : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Gweight X t 1‖ ≤ CP * Real.sqrt X / (1 + |t|) ^ 5)
    (CE : ℝ) (hCE : 0 ≤ CE)
    (heleft : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ, ‖Eleft X t‖ ≤ CE * (X : ℝ)⁻¹ * Real.log (2 + |t|))
    (hexplicit : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      Pfun X t = Gweight X t 1 -
        (∑' g : ZAll, (mZero g.val : ℂ) * Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) * Mfun (g.val - t)) -
        Eleft X t)
    (hmargin : ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ κ < dfun 2 + Rfun X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ * Tfun X < Ifun X 1 - Ifun X (-1) := by
  have h1 := moment_sub_Rfun_add_diag_tendsto_zero hzeta_ntop hcont_kfun hcont_Mfun hk_dec hM_dec
    homega_even homega_dec homega_sq homega_int CJ hCJ hunit CP hCP hpole CE hCE heleft hexplicit
  have h2 := diagIntegral_sub_diagApprox_tendsto_zero hzeta_ntop hcont_kfun hcont_Mfun hM_dec
    homega_diff homega_dec hdomega_dec CJ hCJ hunit
  have h3 := diagApprox_tendsto_dfun_two hRH hzeta_ntop hzeta_conj hord_conj hzero_re hM_planch
    homega_even homega_diff hcont_domega homega_dec hdomega_dec homega_sq homega_int
    homega_Ioi_zero homega_Ioi_log CJ hCJ hunit CR hCR hRvM
  have hdiff : Tendsto (fun X : ℕ => (Ifun X 1 - Ifun X (-1)) / (2 * Tfun X) - (dfun 2 + Rfun X)) atTop (𝓝 0) := by
    have hsum := (h1.add h2).add (h3.sub_const (dfun 2))
    simp only [add_zero, sub_self] at hsum
    refine hsum.congr fun X => by ring
  obtain ⟨κ, hκ, hB⟩ := hmargin
  have hev := (Metric.tendsto_atTop.mp hdiff) (κ / 2) (by linarith)
  obtain ⟨X0, hX0⟩ := hev
  refine ⟨κ, hκ, fun B => ?_⟩
  obtain ⟨X, hBX, hκX⟩ := hB (max B X0)
  refine ⟨X, lt_of_le_of_lt (le_max_left B X0) hBX, ?_⟩
  have hX_ge : X0 ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right B X0) hBX)
  have hX_pos : 0 < X := Nat.lt_of_le_of_lt (Nat.zero_le _) hBX
  have hT_pos : 0 < Tfun X := by unfold Tfun; positivity
  have hd := hX0 X hX_ge
  rw [Real.dist_eq, sub_zero, abs_lt] at hd
  have hdiv : κ / 2 < (Ifun X 1 - Ifun X (-1)) / (2 * Tfun X) := by linarith [hd.1, hκX]
  have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * Tfun X)).mp hdiv
  linarith

end SpectralMod7



end Mod7Section

theorem PEqualNP.Outside.L_twin_primes_spectral_comparison :
    (RiemannHypothesis → (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u); let d := fun (h : ℝ) => (∫ u : ℝ, (W u)^2/u)/16 * (∫ v : ℝ, K v*(1/(h+v+1/5)+1/(h+v-1/5)-2/(h+v))); let k := fun (t : ℝ) => ∫ v : ℝ, b v*Real.cos (2*Real.pi*v*t); let omega := fun (t : ℝ) => (Real.sin (Real.pi*t/5)*k t)^2 * Real.cos (4*Real.pi*t); let z := fun (g : ℝ) => (1/2 : ℂ) + Complex.I*(g:ℂ); let m := fun (g : ℝ) => analyticOrderNatAt riemannZeta (z g); let M := fun (v : ℝ) => ∫ u : ℝ, ((W u/u : ℝ):ℂ)*Complex.exp (Complex.I*(v*Real.log u : ℝ)); let R := fun (X : ℕ) => let T : ℝ := 2*Real.pi*X; let L := (Real.log (2+T))^2; (∫ t in Set.Icc (-T*L) (T*L), omega (t/T) * (‖∑' g : {g : ℝ // |g-t| ≤ L ∧ riemannZeta (z g) = 0}, (m g.val : ℂ)*Complex.exp (Complex.I*(g.val*Real.log X : ℝ))*M (g.val-t)‖^2 - ∑' g : {g : ℝ // |g-t| ≤ L ∧ riemannZeta (z g) = 0}, (m g.val : ℝ)*‖M (g.val-t)‖^2))/(2*T); ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ κ < d 2 + R X) → (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t); let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t; let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ); let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n; let P := fun (X : ℕ) (t : ℝ) => (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ))); let I := fun (X : ℕ) (σ : ℝ) => ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2; ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1))) := by
  intro hRH hmargin
  have hF_diff : Differentiable ℂ SpectralMod3.zetaExt := SpectralMod3.differentiable_zetaExt
  have hF_two : ∀ t : ℝ, (1 / 4 : ℝ) ≤ ‖SpectralMod3.zetaExt ((2 : ℂ) + Complex.I * (t : ℂ))‖ :=
    SpectralMod3.norm_zetaExt_two_add_I_ge
  obtain ⟨C3, _hC3, hF_bound⟩ := SpectralMod3.norm_zetaExt_strip_le
  obtain ⟨C2, hC2, hneg_half⟩ := SpectralMod2.norm_logDeriv_riemannZeta_neg_half_le
  obtain ⟨CJ, hCJ, hJ⟩ := SpectralMod4.jensen_ball_zero_count hF_diff hF_two C3 hF_bound 3 (by norm_num) (by norm_num)
  obtain ⟨CH, hCH, hgood⟩ := SpectralMod4.exists_good_height hF_diff hF_two C3 hF_bound
  obtain ⟨CS, hCS, hS_bound⟩ := SpectralMod4.horizontal_im_logDeriv_riemannZeta_bound hF_diff hF_two C3 hF_bound
  obtain ⟨CR, hCR, hRvM⟩ := SpectralMod5.riemann_von_mangoldt hF_diff
    (fun _ hz => SpectralMod2.norm_digamma_sub_log_le hz)
    (fun t => (SpectralMod3.re_riemannZeta_two_add_I_ge t).1)
    CJ hCJ hJ CH hCH hgood CS hCS hS_bound
  obtain ⟨CP, hCP, hpole⟩ := SpectralMod6.norm_pole_term_le SpectralMod1.Wtilde_rapid_decay
  obtain ⟨CE, hCE, heleft⟩ := SpectralMod6.norm_Eleft_le SpectralMod1.Wtilde_rapid_decay C2 hC2 hneg_half
  have hunit := SpectralMod6.unit_interval_zero_count hF_diff CJ hCJ hJ
  have hexplicit : ∀ X : ℕ, 1 ≤ X → ∀ t : ℝ,
      SpectralMod7.Pfun X t = SpectralMod7.Gweight X t 1 -
        (∑' g : SpectralMod7.ZAll,
          (SpectralMod7.mZero g.val : ℂ) *
            Complex.exp (Complex.I * ((g.val - t : ℝ) : ℂ) * (Real.log X : ℂ)) *
            SpectralMod7.Mfun (g.val - t)) -
        SpectralMod7.Eleft X t :=
    fun _ hX t => SpectralMod6.explicit_formula_Pfun hRH hF_diff
      SpectralMod1.differentiable_Wtilde SpectralMod1.Wtilde_rapid_decay
      SpectralMod1.Mfun_eq_Wtilde SpectralMod1.mellin_inversion_Wfun
      C2 hC2 hneg_half CJ hCJ hJ CH hCH hgood
      SpectralMod5.rectIntegral_logDeriv_mul
      hX t
  exact SpectralMod7.spectral_comparison_from_modules hRH
    (SpectralMod6.meromorphicOrderAt_riemannZeta_ne_top hF_diff)
    (fun hs => SpectralMod5.riemannZeta_conj hF_diff hs)
    (fun hs => SpectralMod5.analyticOrderNatAt_riemannZeta_conj hF_diff hs)
    (fun hlo h0 => SpectralMod6.zero_re_eq_half_of_RH hRH hlo h0)
    SpectralMod1.continuous_kfun
    SpectralMod1.continuous_Mfun
    SpectralMod1.kfun_rapid_decay
    SpectralMod1.Mfun_rapid_decay
    SpectralMod1.integral_norm_sq_Mfun
    SpectralMod1.omegafun_even
    SpectralMod1.differentiable_omegafun
    SpectralMod1.continuous_deriv_omegafun
    SpectralMod1.omegafun_rapid_decay
    SpectralMod1.deriv_omegafun_rapid_decay
    SpectralMod1.omegafun_le_const_mul_sq
    SpectralMod1.integrable_omegafun
    SpectralMod1.integral_Ioi_omegafun_eq_zero
    SpectralMod1.integral_Ioi_omegafun_mul_log
    CJ hCJ hunit CR hCR hRvM CP hCP hpole CE hCE heleft hexplicit hmargin
