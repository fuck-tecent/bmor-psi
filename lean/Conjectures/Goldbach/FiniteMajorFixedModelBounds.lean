import Mathlib

section PartKernel
open MeasureTheory intervalIntegral
open scoped Interval
private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
private noncomputable def polysum (n : ℕ) (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 n, phase (k*x)
private noncomputable def target (t : ℝ) := phase (t/2)*(Real.sinc (Real.pi*t):ℂ)

private theorem phaseNorm (x : ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
private theorem phaseAdd (x y : ℝ) : phase (x+y)=phase x*phase y := by
  simp only [phase, mul_add, Complex.ofReal_add,add_mul,Complex.exp_add]
private theorem phaseLip (x y : ℝ) : ‖phase x-phase y‖ ≤ 2*Real.pi*|x-y| := by
  have h : phase x-phase y = (phase (x-y)-1)*phase y := by
    rw [sub_mul, ← phaseAdd, sub_add_cancel,one_mul]
  rw [h,norm_mul,phaseNorm,mul_one]
  unfold phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  rw [show 2*Real.pi*(x-y)/2=Real.pi*(x-y) by ring]
  have hb : |Real.sin (Real.pi*(x-y))| ≤ |Real.pi*(x-y)| := Real.abs_sin_le_abs
  rw [abs_mul,abs_of_pos Real.pi_pos] at hb
  norm_num
  linarith

private theorem continuousPhase : Continuous phase := by unfold phase; fun_prop
private theorem continuousPoly (n : ℕ) : Continuous (polysum n) := by unfold polysum phase; fun_prop
private theorem continuousTarget : Continuous target := by unfold target phase; fun_prop
private theorem targetNorm (t : ℝ) : ‖target t‖ ≤ 1 := by
  simpa [target,norm_mul,phaseNorm,Complex.norm_real,Real.norm_eq_abs] using Real.abs_sinc_le_one (Real.pi*t)

private theorem kernelInt (t : ℝ) : (∫ x in (0:ℝ)..1, phase (x*t)) = target t := by
  by_cases ht : t=0
  · subst t; simp [phase,target]
  let a := Real.pi*t
  have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  let w := fun z : ℝ => Complex.exp ((z:ℂ)*Complex.I)
  have fac (x : ℝ) : phase (x*t) = phase (t/2)*w ((2*a)*x-a) := by
    simp only [phase,w,← Complex.exp_add]
    congr 1
    dsimp [a]; push_cast; ring
  simp_rw [fac]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=1) w
    (show 2*a ≠ 0 by positivity) (-a)
  simp only [mul_zero,zero_add,mul_one,show 2*a + -a = a by ring] at h
  change _ * (∫ x in (0:ℝ)..1, w (2*a*x + -a)) = _
  rw [h]
  change phase (t/2)* ((2*a)⁻¹ • (∫ z in -a..a, Complex.exp ((z:ℂ)*Complex.I))) = _
  rw [integral_exp_mul_I_eq_sinc,Complex.real_smul]
  change phase (t/2) * _ = phase (t/2) * (Real.sinc a : ℂ)
  congr 1
  push_cast
  field_simp [show (a:ℂ)≠0 by exact_mod_cast ha]

private theorem rangePoly (n : ℕ) (y : ℝ) :
    polysum n y = ∑ k ∈ Finset.range n, phase (((k:ℝ)+1)*y) := by
  unfold polysum
  rw [← Finset.Ico_succ_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem cell (u : ℝ) (j : ℕ) :
    ‖phase (((j:ℝ)+1)*u) - ∫ x in (j:ℝ)..((j:ℝ)+1), phase (x*u)‖ ≤ Real.pi*|u| := by
  let b : ℝ := j+1
  let a : ℝ := j
  let g := fun x : ℝ => phase (x*u)
  have hab : a≤b := by dsimp [a,b]; linarith
  have hg : Continuous g := continuousPhase.comp (continuous_id.mul continuous_const)
  have he : (∫ _x in a..b, g b) = g b := by simp [intervalIntegral.integral_const,a,b]
  change ‖g b - ∫ x in a..b, g x‖ ≤ _
  rw [← he, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  let C := 2*Real.pi*|u|
  calc
    _ ≤ ∫ x in a..b, C*(b-x) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall ?_)
        ((show Continuous (fun x : ℝ => C*(b-x)) by fun_prop).intervalIntegrable _ _)
      intro x hx
      calc ‖g b-g x‖ ≤ 2*Real.pi*|b*u-x*u| := phaseLip _ _
           _ = _ := by rw [← sub_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2)]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (f:=fun _ : ℝ => b) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        integral_id,intervalIntegral.integral_const]
      dsimp [a,b,C]; ring

private theorem approx (n : ℕ) (hn : 0<n) (t : ℝ) :
    ‖polysum n (t/n)/(n:ℂ) - target t‖ ≤ Real.pi*|t|/n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let u := t/n
  let g := fun x : ℝ => phase (x*u)
  have hg : Continuous g := continuousPhase.comp (continuous_id.mul continuous_const)
  have tel := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) (n:=n)
    (fun k _ => hg.intervalIntegrable (μ:=volume) (a:=(k:ℝ)) (b:=((k+1:ℕ):ℝ)))
  have integ : (∫ x in (0:ℝ)..n, g x) = (n:ℂ)*target t := by
    have sm := intervalIntegral.integral_comp_div (a:=(0:ℝ)) (b:=(n:ℝ)) (fun x : ℝ => phase (x*t)) hnR.ne'
    simp only [zero_div,div_self hnR.ne',kernelInt,Complex.real_smul,Complex.ofReal_natCast] at sm
    convert sm using 1
    apply intervalIntegral.integral_congr; intro x _
    unfold g u; congr 1; ring
  have C : ‖polysum n u - (n:ℂ)*target t‖ ≤ (n:ℝ)*(Real.pi*|u|) := by
    rw [rangePoly,← integ]
    simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] at tel
    rw [← tel, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ => cell u k)).trans_eq (by simp))
  change ‖polysum n u/(n:ℂ)-target t‖ ≤ _
  rw [show polysum n u/(n:ℂ)-target t=(polysum n u-(n:ℂ)*target t)/(n:ℂ) by field_simp, norm_div,Complex.norm_natCast]
  rw [div_le_div_iff_of_pos_right hnR]
  apply C.trans_eq
  dsimp [u]; rw [abs_div,abs_of_pos hnR]; field_simp

private theorem avgNorm (n : ℕ) (hn : 0<n) (t : ℝ) : ‖polysum n (t/n)/(n:ℂ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_natCast, div_le_one (by exact_mod_cast hn)]
  unfold polysum
  exact (norm_sum_le _ _).trans (by simp [phaseNorm,Nat.card_Icc])

private theorem targetSq (t : ℝ) : (target t)^2 * phase (-t) = ((Real.sinc (Real.pi*t))^2 : ℝ) := by
  have h : phase (t/2)*phase (t/2)*phase (-t)=1 := by
    rw [← phaseAdd, ← phaseAdd,show t/2+t/2 + -t = 0 by ring]
    simp [phase]
  dsimp [target]; push_cast
  linear_combination (Real.sinc (Real.pi*t):ℂ)^2*h

private theorem scaled {𝕜 : Type*} [RCLike 𝕜] (v : ℝ → 𝕜) (d h : ℝ) (hd : d≠0) :
    (∫ x in -h..h, v (x/d)/(d:𝕜)^2) = (∫ x in -(h/d)..h/d, v x)/(d:𝕜) := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div v hd, neg_div, RCLike.real_smul_eq_coe_mul]
  have hn : (d:𝕜)≠0 := by exact_mod_cast hd
  field_simp

private theorem intBound {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ → 𝕜} (ha : Continuous a) (hb : Continuous b)
    (h C : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hab : ∀ x, ‖a x-b x‖ ≤ C*|x|) :
    ‖(∫ x in -h..h, a x)-(∫ x in -h..h, b x)‖ ≤ 2*C*h^2 := by
  rw [← intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)]
  have step := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := C*h)
    (f := fun x => a x-b x) (fun x hx => (hab x).trans (mul_le_mul_of_nonneg_left (by
      rw [Set.uIoc_of_le (by linarith : -h≤h)] at hx
      exact abs_le.mpr ⟨hx.1.le,hx.2⟩) hC))
  exact step.trans_eq (by rw [abs_of_nonneg (by linarith : 0 ≤ h- -h)]; ring)

private theorem kernel_main : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); ∀ (n : ℕ) (h : ℝ), 0<n → 0≤h → (let f := fun t : ℝ => V n (t/n)/(n:ℂ); (∀ t : ℝ, ‖f t - E (t/2)*(Real.sinc (Real.pi*t):ℂ)‖ ≤ 2*Real.pi*|t|/(n:ℝ)) ∧ |((_J (h/n) (fun β => (V n β)^2*E (-(n:ℝ)*β))).re/(n:ℝ)) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ) ∧ |Jr (h/n) (fun β => ‖V n β‖^2)/(n:ℝ) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ)) := by
  dsimp only
  intro n h hn hh
  have hr : 0 < (n:ℝ) := by exact_mod_cast hn
  let F := fun t : ℝ => polysum n (t/n)/(n:ℂ)
  let sqF := fun t : ℝ => (F t)^2*phase (-t)
  let sqG := fun t : ℝ => (((Real.sinc (Real.pi*t))^2:ℝ):ℂ)
  let M := fun t : ℝ => ‖F t‖^2
  let J := fun t : ℝ => (Real.sinc (Real.pi*t))^2
  have cF : Continuous F := (continuousPoly n |>.comp (continuous_id.div_const _)).div_const _
  have cSq : Continuous sqF := (cF.pow 2).mul (continuousPhase.comp continuous_neg)
  have cJ : Continuous J := by dsimp [J]; fun_prop
  have cG : Continuous sqG := Complex.continuous_ofReal.comp cJ
  have cM : Continuous M := cF.norm.pow 2
  have hp t : ‖F t - target t‖ ≤ Real.pi*|t|/n := approx n hn t
  have hF t : ‖F t‖ ≤ 1 := avgNorm n hn t
  have c : 0 ≤ 2*Real.pi/(n:ℝ) := by positivity
  have pointC t : ‖sqF t-sqG t‖ ≤ 2*Real.pi/n*|t| := by
    change ‖F t^2 * phase (-t) - ((J t : ℝ):ℂ)‖ ≤ _
    rw [show ((J t : ℝ):ℂ) = target t^2*phase (-t) from (targetSq _).symm,
        ← sub_mul,norm_mul,phaseNorm,mul_one, sq_sub_sq,norm_mul]
    have hs : ‖F t + target t‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hF t,targetNorm t])
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs (hp t) (norm_nonneg (F t-target t)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have pointR t : ‖M t-J t‖ ≤ 2*Real.pi/n*|t| := by
    have ht : ‖target t‖^2 = J t := by simp [target,J,norm_mul,phaseNorm,Complex.norm_real, Real.norm_eq_abs,sq_abs]
    change ‖‖F t‖^2-J t‖ ≤ _
    rw [← ht,sq_sub_sq,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤‖F t‖+‖target t‖)]
    have hd := (abs_norm_sub_norm_le (F t) (target t)).trans (hp t)
    have hs : ‖F t‖+‖target t‖ ≤ 2 := by linarith [hF t,targetNorm t]
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs hd (abs_nonneg (‖F t‖-‖target t‖)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have sc : (∫ t in -h..h, sqF t) = (∫ β in -(h/n)..h/n, polysum n β^2*phase (-(n:ℝ)*β))/(n:ℂ) := by
    convert scaled (fun β : ℝ => polysum n β^2*phase (-(n:ℝ)*β)) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : -(n:ℝ)*(t/n) = -t := by field_simp
    change (polysum n (t/n)/(n:ℂ))^2 * phase (-t) = (polysum n (t/n)^2 * phase (-(n:ℝ)*(t/n))) / (((n:ℝ):ℂ)^2)
    rw [he,Complex.ofReal_natCast,div_pow]
    ring
  have sr : (∫ t in -h..h, M t) = (∫ β in -(h/n)..h/n, ‖polysum n β‖^2)/(n:ℝ) := by
    convert scaled (fun β : ℝ => ‖polysum n β‖^2) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr; intro t _
    simp [M,F,norm_div,Complex.norm_natCast,div_pow]
  have hG : (∫ t in -h..h, sqG t) = ((∫ t in -h..h, J t):ℝ) := intervalIntegral.integral_ofReal
  refine ⟨fun t => (hp t).trans (by have := abs_nonneg t; gcongr <;> linarith [Real.pi_pos]),?_,?_⟩
  · have hc := intBound cSq cG h (2*Real.pi/n) hh c pointC
    have hl := (Complex.abs_re_le_norm _).trans hc
    rw [sc,hG,Complex.sub_re,Complex.ofReal_re] at hl
    have hre (z : ℂ) : (z/(n:ℂ)).re = z.re/n := by exact Complex.div_ofReal_re z (n:ℝ)
    rw [hre] at hl
    exact hl.trans_eq (by ring)
  · have hl := intBound cM cJ h (2*Real.pi/n) hh c pointR
    rw [sr,Real.norm_eq_abs] at hl
    exact hl.trans_eq (by ring)

end PartKernel

section PartSinc
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
private theorem sinc_mass : ∀ h : ℝ, 0<h → let k := intervalIntegral (fun t : ℝ => Real.sinc (Real.pi*t)^2) (-h) h MeasureTheory.volume; 0≤k ∧ k≤1 ∧ 1-2/(9*h)≤k := by
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
end PartSinc

section PartFold
open Finset
private def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, phase ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : phase ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

private theorem coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), phase ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_phase_sum m a hm]
  symm
  apply sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold phase
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]


private theorem ramanujan_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [ramanujan_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply sum_congr rfl
      intro d hd
      have hcomp : q / (q / d) = d :=
        Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
      unfold f
      rw [hcomp]
      by_cases ha : q / d ∣ a <;> simp [ha]
      ring
    _ = ∑ d ∈ q.divisors, f d := Nat.sum_div_divisors q f
    _ = ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := rfl

end PartFold

private def ram (q t : ℕ) : ℤ :=
  ∑ d ∈ q.divisors.filter (fun d => d ∣ t), (d : ℤ) * ArithmeticFunction.moebius (q/d)
private def coef (q t : ℕ) : ℚ :=
  (ArithmeticFunction.moebius q : ℚ)^2 / (q.totient : ℚ)^2 * (ram q t : ℚ)
private def leftEnd (q : ℕ) : ℚ := if q ∣ 30 then 1 - 2*(q : ℚ)/(9*105) else 0
private def table : List ℤ := [0, 997883, 995767, 496825, 0, 247354, 493650, -27778, 0, 0, 244708, -10000, 0, -6945, -27778, 121031, 0, -3907, 0, -3087, 0, -13889, -10000, -2067, 0, 0, -6945, 0, 0, -1276, 117063, -1112, 0, -5000, -3907, -6945, 0, -772, -3087, -3473, 0, -625, -13889, -567, 0, 0, -2067, -473, 0, 0, 0, -1954, 0, -370, 0, -2500, 0, -1544, -1276, -298, 0, -278, -1112, 0, 0, -1737, -5000, -230, 0, -1034, -6945, -205, 0, -193, -772, 0, 0, -2778, -3473, -165, 0, 0, -625, -149, 0, -977, -567, -638, 0, -130, 0, -2315, 0, -556, -473, -772, 0, -109, 0, 0, 0, -100, -1954, -97, 0, -3473]
private def minorant (q : ℕ) : ℚ := (table.getD q 0 : ℚ) / 1000000
private def Certified (q : ℕ) : Prop := ∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  minorant q ≤ coef q t * leftEnd q ∧ minorant q ≤ coef q t
private instance (q : ℕ) : Decidable (Certified q) := inferInstanceAs (Decidable (∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  minorant q ≤ coef q t * leftEnd q ∧ minorant q ≤ coef q t))
private theorem cert1 : Certified 1 := by decide +kernel
private theorem cert2 : Certified 2 := by decide +kernel
private theorem cert3 : Certified 3 := by decide +kernel
private theorem cert4 : Certified 4 := by decide +kernel
private theorem cert5 : Certified 5 := by decide +kernel
private theorem cert6 : Certified 6 := by decide +kernel
private theorem cert7 : Certified 7 := by decide +kernel
private theorem cert8 : Certified 8 := by decide +kernel
private theorem cert9 : Certified 9 := by decide +kernel
private theorem cert10 : Certified 10 := by decide +kernel
private theorem cert11 : Certified 11 := by decide +kernel
private theorem cert12 : Certified 12 := by decide +kernel
private theorem cert13 : Certified 13 := by decide +kernel
private theorem cert14 : Certified 14 := by decide +kernel
private theorem cert15 : Certified 15 := by decide +kernel
private theorem cert16 : Certified 16 := by decide +kernel
private theorem cert17 : Certified 17 := by decide +kernel
private theorem cert18 : Certified 18 := by decide +kernel
private theorem cert19 : Certified 19 := by decide +kernel
private theorem cert20 : Certified 20 := by decide +kernel
private theorem cert21 : Certified 21 := by decide +kernel
private theorem cert22 : Certified 22 := by decide +kernel
private theorem cert23 : Certified 23 := by decide +kernel
private theorem cert24 : Certified 24 := by decide +kernel
private theorem cert25 : Certified 25 := by decide +kernel
private theorem cert26 : Certified 26 := by decide +kernel
private theorem cert27 : Certified 27 := by decide +kernel
private theorem cert28 : Certified 28 := by decide +kernel
private theorem cert29 : Certified 29 := by decide +kernel
private theorem cert30 : Certified 30 := by decide +kernel
private theorem cert31 : Certified 31 := by decide +kernel
private theorem cert32 : Certified 32 := by decide +kernel
private theorem cert33 : Certified 33 := by decide +kernel
private theorem cert34 : Certified 34 := by decide +kernel
private theorem cert35 : Certified 35 := by decide +kernel
private theorem cert36 : Certified 36 := by decide +kernel
private theorem cert37 : Certified 37 := by decide +kernel
private theorem cert38 : Certified 38 := by decide +kernel
private theorem cert39 : Certified 39 := by decide +kernel
private theorem cert40 : Certified 40 := by decide +kernel
private theorem cert41 : Certified 41 := by decide +kernel
private theorem cert42 : Certified 42 := by decide +kernel
private theorem cert43 : Certified 43 := by decide +kernel
private theorem cert44 : Certified 44 := by decide +kernel
private theorem cert45 : Certified 45 := by decide +kernel
private theorem cert46 : Certified 46 := by decide +kernel
private theorem cert47 : Certified 47 := by decide +kernel
private theorem cert48 : Certified 48 := by decide +kernel
private theorem cert49 : Certified 49 := by decide +kernel
private theorem cert50 : Certified 50 := by decide +kernel
private theorem cert51 : Certified 51 := by decide +kernel
private theorem cert52 : Certified 52 := by decide +kernel
private theorem cert53 : Certified 53 := by decide +kernel
private theorem cert54 : Certified 54 := by decide +kernel
private theorem cert55 : Certified 55 := by decide +kernel
private theorem cert56 : Certified 56 := by decide +kernel
private theorem cert57 : Certified 57 := by decide +kernel
private theorem cert58 : Certified 58 := by decide +kernel
private theorem cert59 : Certified 59 := by decide +kernel
private theorem cert60 : Certified 60 := by decide +kernel
private theorem cert61 : Certified 61 := by decide +kernel
private theorem cert62 : Certified 62 := by decide +kernel
private theorem cert63 : Certified 63 := by decide +kernel
private theorem cert64 : Certified 64 := by decide +kernel
private theorem cert65 : Certified 65 := by decide +kernel
private theorem cert66 : Certified 66 := by decide +kernel
private theorem cert67 : Certified 67 := by decide +kernel
private theorem cert68 : Certified 68 := by decide +kernel
private theorem cert69 : Certified 69 := by decide +kernel
private theorem cert70 : Certified 70 := by decide +kernel
private theorem cert71 : Certified 71 := by decide +kernel
private theorem cert72 : Certified 72 := by decide +kernel
private theorem cert73 : Certified 73 := by decide +kernel
private theorem cert74 : Certified 74 := by decide +kernel
private theorem cert75 : Certified 75 := by decide +kernel
private theorem cert76 : Certified 76 := by decide +kernel
private theorem cert77 : Certified 77 := by decide +kernel
private theorem cert78 : Certified 78 := by decide +kernel
private theorem cert79 : Certified 79 := by decide +kernel
private theorem cert80 : Certified 80 := by decide +kernel
private theorem cert81 : Certified 81 := by decide +kernel
private theorem cert82 : Certified 82 := by decide +kernel
private theorem cert83 : Certified 83 := by decide +kernel
private theorem cert84 : Certified 84 := by decide +kernel
private theorem cert85 : Certified 85 := by decide +kernel
private theorem cert86 : Certified 86 := by decide +kernel
private theorem cert87 : Certified 87 := by decide +kernel
private theorem cert88 : Certified 88 := by decide +kernel
private theorem cert89 : Certified 89 := by decide +kernel
private theorem cert90 : Certified 90 := by decide +kernel
private theorem cert91 : Certified 91 := by decide +kernel
private theorem cert92 : Certified 92 := by decide +kernel
private theorem cert93 : Certified 93 := by decide +kernel
private theorem cert94 : Certified 94 := by decide +kernel
private theorem cert95 : Certified 95 := by decide +kernel
private theorem cert96 : Certified 96 := by decide +kernel
private theorem cert97 : Certified 97 := by decide +kernel
private theorem cert98 : Certified 98 := by decide +kernel
private theorem cert99 : Certified 99 := by decide +kernel
private theorem cert100 : Certified 100 := by decide +kernel
private theorem cert101 : Certified 101 := by decide +kernel
private theorem cert102 : Certified 102 := by decide +kernel
private theorem cert103 : Certified 103 := by decide +kernel
private theorem cert104 : Certified 104 := by decide +kernel
private theorem cert105 : Certified 105 := by decide +kernel
private theorem lowerTable : (351/100 : ℚ) < ∑ q ∈ Finset.Icc 1 105, minorant q := by decide +kernel

private theorem certified {q : ℕ} (hq : q ∈ Finset.Icc 1 105) : Certified q := by
  obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hq
  interval_cases q
  · exact cert1
  · exact cert2
  · exact cert3
  · exact cert4
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
  · exact cert11
  · exact cert12
  · exact cert13
  · exact cert14
  · exact cert15
  · exact cert16
  · exact cert17
  · exact cert18
  · exact cert19
  · exact cert20
  · exact cert21
  · exact cert22
  · exact cert23
  · exact cert24
  · exact cert25
  · exact cert26
  · exact cert27
  · exact cert28
  · exact cert29
  · exact cert30
  · exact cert31
  · exact cert32
  · exact cert33
  · exact cert34
  · exact cert35
  · exact cert36
  · exact cert37
  · exact cert38
  · exact cert39
  · exact cert40
  · exact cert41
  · exact cert42
  · exact cert43
  · exact cert44
  · exact cert45
  · exact cert46
  · exact cert47
  · exact cert48
  · exact cert49
  · exact cert50
  · exact cert51
  · exact cert52
  · exact cert53
  · exact cert54
  · exact cert55
  · exact cert56
  · exact cert57
  · exact cert58
  · exact cert59
  · exact cert60
  · exact cert61
  · exact cert62
  · exact cert63
  · exact cert64
  · exact cert65
  · exact cert66
  · exact cert67
  · exact cert68
  · exact cert69
  · exact cert70
  · exact cert71
  · exact cert72
  · exact cert73
  · exact cert74
  · exact cert75
  · exact cert76
  · exact cert77
  · exact cert78
  · exact cert79
  · exact cert80
  · exact cert81
  · exact cert82
  · exact cert83
  · exact cert84
  · exact cert85
  · exact cert86
  · exact cert87
  · exact cert88
  · exact cert89
  · exact cert90
  · exact cert91
  · exact cert92
  · exact cert93
  · exact cert94
  · exact cert95
  · exact cert96
  · exact cert97
  · exact cert98
  · exact cert99
  · exact cert100
  · exact cert101
  · exact cert102
  · exact cert103
  · exact cert104
  · exact cert105

set_option maxRecDepth 4096 in
private theorem kernel_table : let R := fun (q n : ℕ) => ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (d:ℝ)*(ArithmeticFunction.moebius (q/d):ℝ); ∀ (n : ℕ) (K : ℕ → ℝ), 30 ∣ n → (∀ q ∈ Finset.Icc (1:ℕ) 105, 0≤K q ∧ K q≤1) → (∀ q ∈ Finset.Icc (1:ℕ) 105, q ∣ 30 → 1-2*(q:ℝ)/(9*105)≤K q) → (351/100:ℝ) < ∑ q ∈ Finset.Icc (1:ℕ) 105, (ArithmeticFunction.moebius q:ℝ)^2/(Nat.totient q:ℝ)^2*R q n*K q := by
  classical
  dsimp only
  intro n K hn hK hleft
  have total : (351/100 : ℝ) < ∑ q ∈ Finset.Icc 1 105, (minorant q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] using (Rat.cast_lt (K := ℝ)).mpr lowerTable
  apply total.trans_le
  apply Finset.sum_le_sum
  intro q hq
  let t := q.gcd n
  have qpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have ht : t ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, qpos.ne'⟩
  have hgt : q.gcd 30 ∣ t := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right q 30).trans hn)
  obtain ⟨hlo,hhi⟩ := certified hq t ht hgt
  have realLo : (minorant q : ℝ) ≤ (coef q t : ℝ) * (leftEnd q : ℝ) := by exact_mod_cast hlo
  have realHi : (minorant q : ℝ) ≤ (coef q t : ℝ) := by exact_mod_cast hhi
  have lowK : (leftEnd q : ℝ) ≤ K q := by
    by_cases hd : q ∣ 30
    · simpa [leftEnd,hd] using hleft q hq hd
    · simpa [leftEnd,hd] using (hK q hq).1
  have mid : (minorant q : ℝ) ≤ (coef q t : ℝ) * K q := by
    by_cases hc : 0 ≤ (coef q t : ℝ)
    · exact realLo.trans (mul_le_mul_of_nonneg_left lowK hc)
    · exact realHi.trans (by simpa using mul_le_mul_of_nonpos_left (hK q hq).2 (le_of_not_ge hc))
  have filterEq : q.divisors.filter (fun d => d ∣ t) = q.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd,hdt⟩; exact ⟨hd,hdt.trans (Nat.gcd_dvd_right q n)⟩
    · rintro ⟨hd,hdn⟩; exact ⟨hd,Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 hdn⟩
  simpa [coef, ram, filterEq] using mid


section PartMain
open Finset MeasureTheory intervalIntegral

private noncomputable def cc (q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ)^2 / (Nat.totient q : ℝ)^2

private noncomputable def Rr (q n : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (d:ℝ) * (ArithmeticFunction.moebius (q/d) : ℝ)

private noncomputable def KK (q : ℕ) : ℝ :=
  intervalIntegral (fun t : ℝ => Real.sinc (Real.pi*t)^2) (-(105/(q:ℝ))) (105/(q:ℝ)) MeasureTheory.volume

private def wq (q : ℕ) : ℚ := (ArithmeticFunction.moebius q : ℚ)^2 / (Nat.totient q : ℚ)

private theorem wq_sum : ∑ q ∈ Finset.Icc 1 105, wq q < 599/100 := by decide +kernel

private theorem cc_nonneg (q : ℕ) : 0 ≤ cc q := by unfold cc; positivity

private theorem cc_le_one (q : ℕ) (hq : 0 < q) : cc q ≤ 1 := by
  unfold cc
  have h1 : (1:ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have h2 : (ArithmeticFunction.moebius q : ℝ)^2 ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := q)
    have h3 : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by exact_mod_cast this
    nlinarith [abs_nonneg (ArithmeticFunction.moebius q : ℝ), sq_abs (ArithmeticFunction.moebius q : ℝ)]
  rw [div_le_one (by positivity)]
  nlinarith

private theorem cc_cast (q : ℕ) : ((cc q : ℝ) : ℂ) =
    ((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ) * (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)) := by
  unfold cc
  push_cast
  ring

private theorem M_sq (n q : ℕ) (β : ℝ) :
    (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β)^2 =
      ((cc q : ℝ) : ℂ) * (polysum n β)^2 := by
  rw [cc_cast]; ring

private theorem M_norm (n q : ℕ) (β : ℝ) :
    ‖((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β‖^2 =
      cc q * ‖polysum n β‖^2 := by
  rw [← norm_pow, M_sq, norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs, abs_of_nonneg (cc_nonneg q)]

private theorem phase_neg_conj (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

private theorem phase_split (n a q : ℕ) (β : ℝ) :
    phase (-(n:ℝ)*((a:ℝ)/q+β)) = phase (-((n:ℝ)*(a:ℝ)/q)) * phase (-(n:ℝ)*β) := by
  rw [← phaseAdd]
  congr 1
  ring

private theorem ram_real (n q : ℕ) (hq : 0 < q) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), phase (-((n:ℝ)*(a:ℝ)/q)) = ((Rr q n : ℝ) : ℂ) := by
  have hr : ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), phase ((n:ℝ)*(a:ℝ)/q) = ((Rr q n : ℝ) : ℂ) := by
    have := ramanujan_divisor_formula q n hq
    unfold units at this
    rw [this, ← sum_filter]
    unfold Rr
    push_cast
    rfl
  simp_rw [phase_neg_conj]
  rw [← map_sum, hr, Complex.conj_ofReal]

private theorem card_A (q : ℕ) : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) = (Nat.totient q : ℝ) := by
  congr 1
  rw [Nat.totient_eq_card_coprime]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact Nat.coprime_comm

private theorem Rr_abs (n q : ℕ) (hq : 0 < q) : |Rr q n| ≤ q := by
  have h := congrArg (fun z : ℂ => ‖z‖) (ram_real n q hq)
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  rw [← h]
  refine (norm_sum_le _ _).trans ?_
  simp only [phaseNorm, sum_const, nsmul_eq_mul, mul_one]
  have : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ q := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  exact this

private theorem gb_inner_sum (n q : ℕ) (hq : 0 < q) (h : ℝ) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (intervalIntegral (fun β : ℝ => (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β)^2 *
          phase (-(n:ℝ)*((a:ℝ)/q+β))) (-h) h MeasureTheory.volume).re
    = cc q * Rr q n * (intervalIntegral (fun β : ℝ => polysum n β^2 * phase (-(n:ℝ)*β)) (-h) h MeasureTheory.volume).re := by
  have step : ∀ a : ℕ, intervalIntegral (fun β : ℝ => (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β)^2 *
          phase (-(n:ℝ)*((a:ℝ)/q+β))) (-h) h MeasureTheory.volume =
      ((cc q : ℝ) : ℂ) * phase (-((n:ℝ)*(a:ℝ)/q)) *
        intervalIntegral (fun β : ℝ => polysum n β^2 * phase (-(n:ℝ)*β)) (-h) h MeasureTheory.volume := by
    intro a
    rw [mul_assoc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro β _
    simp only
    rw [M_sq, phase_split]
    ring
  simp_rw [step]
  rw [← Complex.re_sum, ← Finset.sum_mul, ← Finset.mul_sum, ram_real n q hq, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]

private theorem kern_re (n : ℕ) (h : ℝ) (hn : 0 < n) (hh : 0 ≤ h) :
    |(intervalIntegral (fun β : ℝ => polysum n β^2 * phase (-(n:ℝ)*β)) (-(h/n)) (h/n) MeasureTheory.volume).re / n -
      intervalIntegral (fun t : ℝ => Real.sinc (Real.pi*t)^2) (-h) h MeasureTheory.volume| ≤ 4*Real.pi*h^2/n :=
  (kernel_main n h hn hh).2.1

private theorem kern_norm (n : ℕ) (h : ℝ) (hn : 0 < n) (hh : 0 ≤ h) :
    |intervalIntegral (fun β : ℝ => ‖polysum n β‖^2) (-(h/n)) (h/n) MeasureTheory.volume / n -
      intervalIntegral (fun t : ℝ => Real.sinc (Real.pi*t)^2) (-h) h MeasureTheory.volume| ≤ 4*Real.pi*h^2/n :=
  (kernel_main n h hn hh).2.2

private theorem err_le (q n : ℕ) (hq : 1 ≤ q) :
    4*Real.pi*(105/(q:ℝ))^2/n ≤ 16*105^2/n := by
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (105/(q:ℝ)) ≤ 105 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h0 : 0 ≤ (105/(q:ℝ)) := by positivity
  have h2 : (105/(q:ℝ))^2 ≤ 105^2 := by gcongr
  have h3 : 4*Real.pi*(105/(q:ℝ))^2 ≤ 16*105^2 := by
    nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg (105/(q:ℝ))]
  exact div_le_div_of_nonneg_right h3 (Nat.cast_nonneg n)

private theorem eps_small (n : ℕ) (hn : 4000000000000000000 ≤ n) : 16*105^2/(n:ℝ) ≤ 1/10^9 := by
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private theorem H_eq (q n : ℕ) : (105:ℝ)/((q:ℝ)*(n:ℝ)) = (105/(q:ℝ))/(n:ℝ) := by
  rw [div_div]

set_option maxRecDepth 20000 in
private theorem C_part (n : ℕ) (hn : 4000000000000000000 ≤ n) (h30 : 30 ∣ n) :
    (7/2:ℝ)*(n:ℝ) < ∑ q ∈ Finset.Icc (1:ℕ) 105, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (intervalIntegral (fun β : ℝ => (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β)^2 *
          phase (-(n:ℝ)*((a:ℝ)/q+β))) (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume).re := by
  have hn0 : 0 < n := by omega
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hsinc : ∀ q ∈ Finset.Icc (1:ℕ) 105, 0 ≤ KK q ∧ KK q ≤ 1 ∧ 1 - 2/(9*(105/(q:ℝ))) ≤ KK q := by
    intro q hq
    have hqp : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    exact sinc_mass (105/(q:ℝ)) (by positivity)
  have hK : ∀ q ∈ Finset.Icc (1:ℕ) 105, 0 ≤ KK q ∧ KK q ≤ 1 := fun q hq => ⟨(hsinc q hq).1, (hsinc q hq).2.1⟩
  have hleft : ∀ q ∈ Finset.Icc (1:ℕ) 105, q ∣ 30 → 1 - 2*(q:ℝ)/(9*105) ≤ KK q := by
    intro q hq _
    have hqp : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have h := (hsinc q hq).2.2
    have he : 2/(9*(105/(q:ℝ))) = 2*(q:ℝ)/(9*105) := by field_simp
    rw [he] at h
    exact h
  have tab : (351/100:ℝ) < ∑ q ∈ Finset.Icc (1:ℕ) 105, cc q * Rr q n * KK q :=
    kernel_table n KK h30 hK hleft
  set ee : ℕ → ℝ := fun q => (intervalIntegral (fun β : ℝ => polysum n β^2 * phase (-(n:ℝ)*β)) (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume).re / n - KK q with hee
  have hebound : ∀ q ∈ Finset.Icc (1:ℕ) 105, |ee q| ≤ 1/10^9 := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqp : (0:ℝ) < q := by exact_mod_cast hq1
    have := kern_re n (105/(q:ℝ)) hn0 (by positivity)
    rw [← H_eq] at this
    exact (this.trans (err_le q n hq1)).trans (eps_small n hn)
  have hterm : ∀ q ∈ Finset.Icc (1:ℕ) 105, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (intervalIntegral (fun β : ℝ => (((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β)^2 *
          phase (-(n:ℝ)*((a:ℝ)/q+β))) (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume).re
      = n * (cc q * Rr q n * KK q) + n * (cc q * Rr q n * ee q) := by
    intro q hq
    have hqp : 0 < q := (mem_Icc.mp hq).1
    rw [gb_inner_sum n q hqp]
    simp only [hee]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have herr : |∑ q ∈ Finset.Icc (1:ℕ) 105, cc q * Rr q n * ee q| ≤ 1/10^4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ q ∈ Finset.Icc (1:ℕ) 105, |cc q * Rr q n * ee q| ≤ 105 * (1/10^9) := by
      intro q hq
      have hqp : 0 < q := (mem_Icc.mp hq).1
      have hq105 : (q:ℝ) ≤ 105 := by exact_mod_cast (mem_Icc.mp hq).2
      rw [abs_mul, abs_mul, abs_of_nonneg (cc_nonneg q)]
      have h1 := cc_le_one q hqp
      have h2 : |Rr q n| ≤ 105 := (Rr_abs n q hqp).trans hq105
      have h3 := hebound q hq
      have h4 : |Rr q n| * |ee q| ≤ 105 * (1/10^9) :=
        mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
      calc cc q * |Rr q n| * |ee q| = cc q * (|Rr q n| * |ee q|) := by ring
        _ ≤ 1 * (105 * (1/10^9)) := mul_le_mul h1 h4 (by positivity) (by norm_num)
        _ = _ := one_mul _
    refine (Finset.sum_le_sum this).trans ?_
    simp
    norm_num
  have h1 := (abs_le.mp herr).1
  have h2 : 0 < (∑ q ∈ Finset.Icc (1:ℕ) 105, cc q * Rr q n * KK q) +
      (∑ q ∈ Finset.Icc (1:ℕ) 105, cc q * Rr q n * ee q) - 7/2 := by linarith
  nlinarith [mul_pos hnpos h2]

set_option maxRecDepth 20000 in
private theorem B_part (n : ℕ) (hn : 4000000000000000000 ≤ n) :
    ∑ q ∈ Finset.Icc (1:ℕ) 105, (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
      intervalIntegral (fun β : ℝ => ‖((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β‖^2)
        (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume < 6*(n:ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hK : ∀ q ∈ Finset.Icc (1:ℕ) 105, KK q ≤ 1 := by
    intro q hq
    have hqp : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    exact (sinc_mass (105/(q:ℝ)) (by positivity)).2.1
  have hterm : ∀ q ∈ Finset.Icc (1:ℕ) 105,
      (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
      intervalIntegral (fun β : ℝ => ‖((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β‖^2)
        (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume
      ≤ ((wq q : ℚ) : ℝ) * (n * (1 + 1/10^9)) := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqp : 0 < q := hq1
    have hqR : (0:ℝ) < q := by exact_mod_cast hqp
    have hphi : (0:ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqp
    have hk := kern_norm n (105/(q:ℝ)) hn0 (by positivity)
    rw [← H_eq] at hk
    have he := (hk.trans (err_le q n hq1)).trans (eps_small n hn)
    have he2 := (abs_le.mp he).2
    set J := intervalIntegral (fun β : ℝ => ‖polysum n β‖^2) (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume with hJ
    have hint : intervalIntegral (fun β : ℝ => ‖((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*polysum n β‖^2)
        (-((105:ℝ)/((q:ℝ)*(n:ℝ)))) ((105:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume = cc q * J := by
      rw [hJ, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro β _
      exact M_norm n q β
    rw [hint, card_A]
    have hw : ((wq q : ℚ) : ℝ) = (ArithmeticFunction.moebius q : ℝ)^2 / (Nat.totient q : ℝ) := by
      unfold wq; push_cast; rfl
    have hcw : (Nat.totient q : ℝ) * cc q = ((wq q : ℚ) : ℝ) := by
      rw [hw]; unfold cc; field_simp
    have hw0 : 0 ≤ ((wq q : ℚ) : ℝ) := by rw [hw]; positivity
    have hJle : J ≤ n * (1 + 1/10^9) := by
      have h1 : J / n ≤ 1 + 1/10^9 := by
        have := hK q hq
        unfold KK at this
        linarith [he2]
      rw [div_le_iff₀ hnpos] at h1
      linarith
    calc (Nat.totient q : ℝ) * (cc q * J) = ((Nat.totient q : ℝ) * cc q) * J := by ring
      _ = ((wq q : ℚ) : ℝ) * J := by rw [hcw]
      _ ≤ _ := mul_le_mul_of_nonneg_left hJle hw0
  refine (Finset.sum_le_sum hterm).trans_lt ?_
  rw [← Finset.sum_mul]
  have hs : ∑ q ∈ Finset.Icc (1:ℕ) 105, ((wq q : ℚ) : ℝ) < 599/100 := by
    have := (Rat.cast_lt (K := ℝ)).mpr wq_sum
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using this
  have hpos : 0 < (n:ℝ) * (1 + 1/10^9) := by positivity
  calc (∑ q ∈ Finset.Icc (1:ℕ) 105, ((wq q : ℚ) : ℝ)) * (n * (1 + 1/10^9))
      < (599/100) * (n * (1 + 1/10^9)) := mul_lt_mul_of_pos_right hs hpos
    _ < 6 * n := by nlinarith

end PartMain

set_option maxRecDepth 20000 in
theorem Conjectures.Goldbach.FiniteMajorFixedModelBounds :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); let M := fun (n q : ℕ) (β : ℝ) => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*V n β; let H := fun (n q : ℕ) => (105:ℝ)/((q:ℝ)*(n:ℝ)); let Q := Finset.Icc (1:ℕ) 105; let A := fun (q : ℕ) => (Finset.range q).filter (fun a => Nat.Coprime a q); let B := fun (n : ℕ) => ∑ q ∈ Q, ((A q).card:ℝ) * Jr (H n q) (fun β => ‖M n q β‖^2); let C := fun (n : ℕ) => ∑ q ∈ Q, ∑ a ∈ A q, (_J (H n q) (fun β => (M n q β)^2*E (-(n:ℝ)*((a:ℝ)/q+β)))).re; ∀ n : ℕ, 4000000000000000000≤n → 30 ∣ n → (7/2:ℝ)*(n:ℝ) < C n ∧ B n < 6*(n:ℝ) := by
  intro E _J Jr V M H Q A B C n hn h30
  exact ⟨C_part n hn h30, B_part n hn⟩
