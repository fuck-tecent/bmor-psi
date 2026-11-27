import Mathlib

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

theorem Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); ∀ (n : ℕ) (h : ℝ), 0<n → 0≤h → (let f := fun t : ℝ => V n (t/n)/(n:ℂ); (∀ t : ℝ, ‖f t - E (t/2)*(Real.sinc (Real.pi*t):ℂ)‖ ≤ 2*Real.pi*|t|/(n:ℝ)) ∧ |((_J (h/n) (fun β => (V n β)^2*E (-(n:ℝ)*β))).re/(n:ℝ)) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ) ∧ |Jr (h/n) (fun β => ‖V n β‖^2)/(n:ℝ) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ)) := by
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
