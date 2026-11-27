import Mathlib

open Set MeasureTheory

namespace GoldbachOscillation

/-- The multiplier R(y) = y/(L²+y²) stays finite as the phase slope crosses zero. -/
private noncomputable def D (L y : ℝ) := L^2+y^2
private noncomputable def R (L y : ℝ) := y / D L y
private noncomputable def R' (L y : ℝ) := (L^2-y^2) / (D L y)^2
private noncomputable def J (L y : ℝ) := Real.arctan (y/L) / L
private noncomputable def wave (y : ℝ) := Complex.exp ((y:ℂ)*Complex.I)

private theorem D_pos {L : ℝ} (hL : 0 < L) (y : ℝ) : 0 < D L y := by unfold D; positivity

private theorem R_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (R L) (R' L y) y := by
  have h := (hasDerivAt_id y).div ((hasDerivAt_const y (L^2)).add ((hasDerivAt_id y).pow 2))
    (D_pos hL y).ne'
  convert h using 1
  · rfl
  unfold R' D
  simp
  ring

private theorem J_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (J L) (1 / D L y) y := by
  have h := ((Real.hasDerivAt_arctan (y/L)).comp y ((hasDerivAt_id y).div_const L)).div_const L
  convert h using 1
  · rfl
  unfold D
  field_simp [hL.ne']

private theorem wave_deriv (y : ℝ) :
    HasDerivAt wave (wave y * Complex.I) y := by
  simpa [wave] using! (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).cexp).comp_ofReal

private theorem wave_norm (y : ℝ) : ‖wave y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem R_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R L y| ≤ 1/L := by
  rw [R, abs_div, abs_of_pos (D_pos hL y)]
  apply (div_le_div_iff₀ (D_pos hL y) hL).mpr
  unfold D
  nlinarith only [sq_nonneg (L-|y|), sq_abs y, mul_nonneg hL.le (abs_nonneg y)]

private theorem R'_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R' L y| ≤ 1 / D L y := by
  have hp := D_pos hL y
  rw [R', abs_div, abs_of_pos (sq_pos_of_pos hp)]
  have hab : |L^2-y^2| ≤ D L y := abs_le.mpr ⟨by dsimp [D]; nlinarith [sq_nonneg L],
    by dsimp [D]; nlinarith [sq_nonneg y]⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hab hp.le]

private theorem remainder {L : ℝ} (hL : 0 < L) (y : ℝ) :
    1-y*R L y = L^2 / D L y := by
  unfold R
  field_simp [(D_pos hL y).ne']
  unfold D
  ring

private noncomputable def mainTerm (w f : ℝ → ℝ) (x : ℝ) : ℂ := (w x:ℂ)*wave (f x)
private noncomputable def primitive (L : ℝ) (w f p : ℝ → ℝ) (x : ℝ) : ℂ :=
  -Complex.I*((w x * R L (p x) : ℝ):ℂ)*wave (f x)
private noncomputable def errorTerm (L : ℝ) (w dw f p dp : ℝ → ℝ) (x : ℝ) : ℂ :=
  wave (f x) * (((w x * (1-p x*R L (p x)) : ℝ):ℂ) +
    Complex.I * ((dw x*R L (p x)+w x*R' L (p x)*dp x : ℝ):ℂ))

private theorem primitive_deriv {L x : ℝ} (hL : 0 < L) {w dw f p dp : ℝ → ℝ}
    (hw : HasDerivAt w (dw x) x) (hf : HasDerivAt f (p x) x) (hp : HasDerivAt p (dp x) x) :
    HasDerivAt (primitive L w f p) (mainTerm w f x - errorTerm L w dw f p dp x) x := by
  have hr := (R_deriv hL (p x)).comp x hp
  have hd := (((hw.mul hr).ofReal_comp.const_mul (-Complex.I)).mul ((wave_deriv (f x)).scomp x hf))
  convert hd using 1
  · rfl
  dsimp [mainTerm, errorTerm]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem primitive_bound {L x : ℝ} (hL : 0 < L) (w f p : ℝ → ℝ)
    (hw : |w x| ≤ 1) : ‖primitive L w f p x‖ ≤ 1/L := by
  simp only [primitive, norm_mul, norm_neg, Complex.norm_I, one_mul, wave_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul hw (R_bound hL (p x)) (abs_nonneg _) zero_le_one

private theorem error_bound {L x : ℝ} (hL : 0 < L) (w dw f p dp : ℝ → ℝ)
    (hw : |w x| ≤ 1) (hdw : |dw x| ≤ 1) (hcurv : L^2 ≤ 4*dp x) :
    ‖errorTerm L w dw f p dp x‖ ≤ 1/L + 5 * (dp x / D L (p x)) := by
  have hd := D_pos hL (p x)
  have hp : 0 ≤ dp x := by nlinarith only [sq_nonneg L,hcurv]
  rw [errorTerm, norm_mul, wave_norm, one_mul]
  apply (norm_add_le ..).trans
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    remainder hL, abs_of_nonneg (div_nonneg (sq_nonneg L) hd.le)]
  have hfirst := mul_le_of_le_one_left (div_nonneg (sq_nonneg L) hd.le) hw
  have hsecond : |dw x*R L (p x)| ≤ 1/L := by
    rw [abs_mul]
    simpa using mul_le_mul hdw (R_bound hL _) (abs_nonneg _) zero_le_one
  have hthird : |w x*R' L (p x)*dp x| ≤ dp x/D L (p x) := by
    simp only [abs_mul, abs_of_nonneg hp]
    have hs : |w x| * |R' L (p x)| ≤ 1/D L (p x) := by
      simpa using mul_le_mul hw (R'_bound hL _) (abs_nonneg _) zero_le_one
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hs hp
  have hscale := div_le_div_of_nonneg_right hcurv hd.le
  rw [mul_div_assoc] at hscale
  have htriangle := abs_add_le (dw x*R L (p x)) (w x*R' L (p x)*dp x)
  linarith

/-- A regularized integration by parts works across a possible stationary point.
The arctangent controls the total variation of the multiplier. -/
private theorem regularized {a b L : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 1) (hL : 0 < L)
    (w dw f p dp : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (dw x) x)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hcw : ContinuousOn dw (Icc a b)) (hcp : ContinuousOn dp (Icc a b))
    (hw1 : ∀ x ∈ Icc a b, |w x| ≤ 1) (hdw1 : ∀ x ∈ Icc a b, |dw x| ≤ 1)
    (hcurv : ∀ x ∈ Icc a b, L^2 ≤ 4*dp x) :
    ‖∫ x in a..b, mainTerm w f x‖ ≤ (3+5*Real.pi)/L := by
  have cw := HasDerivAt.continuousOn hw
  have cf := HasDerivAt.continuousOn hf
  have cp := HasDerivAt.continuousOn hp
  have cR : Continuous (R L) := continuous_iff_continuousAt.mpr fun y => (R_deriv hL y).continuousAt
  have cD : Continuous (D L) := by unfold D; fun_prop
  have cR' : Continuous (R' L) := by
    unfold R'
    exact (continuous_const.sub (continuous_id.pow 2)).div (cD.pow 2) (fun y => (sq_pos_of_pos (D_pos hL y)).ne')
  have cWave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwav := cWave.comp_continuousOn cf
  have cr := cR.comp_continuousOn cp
  have cr' := cR'.comp_continuousOn cp
  have mainC : ContinuousOn (mainTerm w f) (Icc a b) := by unfold mainTerm; fun_prop
  have errC : ContinuousOn (errorTerm L w dw f p dp) (Icc a b) := by unfold errorTerm; fun_prop
  have mainI := mainC.intervalIntegrable_of_Icc (μ := volume) hab
  have errI := errC.intervalIntegrable_of_Icc (μ := volume) hab
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := primitive L w f p) (f' := fun x => mainTerm w f x - errorTerm L w dw f p dp x)
    (fun x hx => by rw [uIcc_of_le hab] at hx; exact primitive_deriv hL (hw x hx) (hf x hx) (hp x hx))
    (mainI.sub errI)
  rw [intervalIntegral.integral_sub mainI errI] at identity
  let density := fun x => dp x / D L (p x)
  have denC : ContinuousOn density (Icc a b) :=
    hcp.div (cD.comp_continuousOn cp) (fun x _ => (D_pos hL (p x)).ne')
  have di := denC.intervalIntegrable_of_Icc (μ := volume) hab
  have jd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := J L ∘ p) (f' := density) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      convert (J_deriv hL (p x)).comp x (hp x hx) using 1
      dsimp [density]; ring) di
  -- Integrating the positive density only costs the range of arctan, divided by L.
  have jbound : (∫ x in a..b, density x) ≤ Real.pi/L := by
    rw [jd]
    dsimp [J]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith only [Real.arctan_lt_pi_div_two (p b/L), Real.neg_pi_div_two_lt_arctan (p a/L)]
  have errBound := intervalIntegral.norm_integral_le_of_norm_le hab
    (g := fun x => 1/L + 5 * density x) (Filter.Eventually.of_forall fun x hx =>
      error_bound hL w dw f p dp (hw1 x ⟨hx.1.le,hx.2⟩) (hdw1 x ⟨hx.1.le,hx.2⟩) (hcurv x ⟨hx.1.le,hx.2⟩))
    (intervalIntegrable_const.add (di.const_mul 5))
  rw [intervalIntegral.integral_add intervalIntegrable_const (di.const_mul 5),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at errBound
  have lhs : (∫ x in a..b, mainTerm w f x) =
      (primitive L w f p b - primitive L w f p a) + ∫ x in a..b, errorTerm L w dw f p dp x :=
    sub_eq_iff_eq_add.mp identity
  rw [lhs]
  apply (norm_add_le ..).trans
  have nd := norm_sub_le (primitive L w f p b) (primitive L w f p a)
  have ba := primitive_bound hL w f p (hw1 a (left_mem_Icc.mpr hab))
  have bb := primitive_bound hL w f p (hw1 b (right_mem_Icc.mpr hab))
  have length := mul_le_mul_of_nonneg_right hlen (one_div_nonneg.mpr hL.le)
  rw [add_div, mul_div_assoc]
  rw [show 3/L = 3*(1/L) by ring]
  linarith only [ba,bb,nd,errBound,length,jbound]

private noncomputable def kernel (σ β γ x : ℝ) : ℂ :=
  ((x^(σ-1):ℝ):ℂ) * wave (β*x + γ*Real.log x)

private theorem dyadic_minus {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β (-γ) x‖ ≤ (3+5*Real.pi)/Real.sqrt γ := by
  let w := fun x : ℝ => x^(σ-1)
  let dw := fun x : ℝ => (σ-1)*x^(σ-1-1)
  let f := fun x : ℝ => β*x+(-γ)*Real.log x
  let p := fun x : ℝ => β-γ/x
  let dp := fun x : ℝ => γ/x^2
  have hx {x : ℝ} (h : x ∈ Icc a b) : 1 ≤ x := ha.trans h.1
  have hxp {x : ℝ} (h : x ∈ Icc a b) : 0 < x := zero_lt_one.trans_le (hx h)
  apply regularized hab (by linarith) (Real.sqrt_pos.mpr hγ) w dw f p dp
  · intro x h
    exact Real.hasDerivAt_rpow_const (Or.inl (hxp h).ne')
  · intro x h
    have h' := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (hxp h).ne').const_mul (-γ))
    convert h' using 1
    · rfl
    dsimp [p]; ring
  · intro x h
    have h' := (hasDerivAt_const x β).sub ((hasDerivAt_const x γ).div (hasDerivAt_id x) (hxp h).ne')
    convert h' using 1
    · rfl
    dsimp [dp]; ring
  · unfold dw; fun_prop (disch := solve_by_elim [ne_of_gt, hxp])
  · change ContinuousOn (fun x : ℝ => γ/x^2) (Icc a b)
    fun_prop (disch := intro x hx; exact pow_ne_zero 2 (hxp hx).ne')
  · intro x h
    dsimp [w]
    rw [abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hx h) (by linarith)
  · intro x h
    dsimp [dw]
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hσ'), abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    have h1 : -(σ-1) ≤ 1 := by linarith
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos (hx h) (show σ-1-1 ≤ 0 by linarith)
    simpa using mul_le_mul h1 h2 (Real.rpow_nonneg (hxp h).le _) zero_le_one
  · intro x h
    rw [Real.sq_sqrt hγ.le]
    change γ ≤ 4*(γ/x^2)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos (hxp h))).mpr
    have h2 := pow_le_pow_left₀ (hxp h).le (h.2.trans hb) 2
    nlinarith only [mul_le_mul_of_nonneg_left h2 hγ.le]

open scoped ComplexConjugate

private theorem wave_add (u v : ℝ) : wave (u+v) = wave u * wave v := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem conjugate_kernel (σ β γ x : ℝ) :
    conj (kernel σ (-β) (-γ) x) = kernel σ β γ x := by
  unfold kernel wave
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp
  ring

private theorem dyadic {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : γ ≠ 0) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  apply le_min
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := kernel σ β γ) (C := 1) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have h1 := ha.trans hx.1.le
        rw [kernel, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h1) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
    rw [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] at h
    exact h.trans (by linarith)
  · rcases lt_or_gt_of_ne hγ with hn | hpos
    · simpa [abs_of_neg hn] using dyadic_minus ha hab hb (neg_pos.mpr hn) hσ hσ' β
    · have id : (∫ x in a..b, kernel σ β γ x) = conj (∫ x in a..b, kernel σ (-β) (-γ) x) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        exact intervalIntegral.integral_congr fun x _ => (conjugate_kernel σ β γ x).symm
      rw [id, Complex.norm_conj, abs_of_pos hpos]
      exact dyadic_minus ha hab hb hpos hσ hσ' (-β)

private theorem rescale {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) (σ β γ : ℝ) :
    kernel σ β γ (Y*x) = (((Y^(σ-1):ℝ):ℂ)*wave (γ*Real.log Y)) * kernel σ (β*Y) γ x := by
  unfold kernel
  rw [Real.mul_rpow hY.le hx.le, Real.log_mul hY.ne' hx.ne',
    show β*(Y*x)+γ*(Real.log Y+Real.log x) = γ*Real.log Y + ((β*Y)*x+γ*Real.log x) by ring, wave_add]
  push_cast
  ring

/- Away from a stationary point, integrate with the reciprocal of βx+γ.
Its fixed-sign derivative gives a total variation bound from the endpoints. -/
set_option maxHeartbeats 600000 in
private theorem separated {a b σ γ β H : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hH : 0 < H) (hsep : ∀ x ∈ Icc a b, H ≤ |β*x+γ|) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ 5*b^σ/H := by
  let F := fun x : ℝ => β*x + γ*Real.log x
  let p := fun x : ℝ => β+γ/x
  let W := fun x : ℝ => x^σ
  let dW := fun x : ℝ => σ*x^(σ-1)
  let z := fun x : ℝ => 1/(β*x+γ)
  let dz := fun x : ℝ => -β/(β*x+γ)^2
  let B := fun x : ℝ => -Complex.I*((W x*z x : ℝ):ℂ)*wave (F x)
  let er := fun x : ℝ => Complex.I*((dW x*z x+W x*dz x : ℝ):ℂ)*wave (F x)
  have pos {x : ℝ} (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have nz {x : ℝ} (hx : x ∈ Icc a b) : β*x+γ ≠ 0 := abs_pos.mp (hH.trans_le (hsep x hx))
  have zd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt z (dz x) x := by
    have h := (hasDerivAt_const x (1:ℝ)).div (((hasDerivAt_id x).const_mul β).add_const γ) (nz hx)
    convert h using 1 <;> first | rfl | (dsimp [dz]; ring)
  have wd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt W (dW x) x :=
    Real.hasDerivAt_rpow_const (Or.inl (pos hx).ne')
  have fd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (p x) x := by
    have h := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (pos hx).ne').const_mul γ)
    convert h using 1 <;> first | rfl | (dsimp [p]; ring)
  have hB (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt B (kernel σ β γ x - er x) x := by
    have hv := ((((wd x hx).mul (zd x hx)).ofReal_comp.const_mul (-Complex.I)).mul
      ((wave_deriv (F x)).scomp x (fd x hx)))
    have unit : W x*z x*p x = x^(σ-1) := by
      dsimp [W,z,p]
      rw [Real.rpow_sub_one (pos hx).ne']
      field_simp [(nz hx),(pos hx).ne']
    have hu : (W x:ℂ)*(z x:ℂ)*(p x:ℂ) = ((x^(σ-1):ℝ):ℂ) := by exact_mod_cast unit
    convert hv using 1
    · rfl
    change ((x^(σ-1):ℝ):ℂ)*wave (F x) - er x = _
    dsimp only [er, Pi.mul_apply, Function.comp_apply]
    push_cast
    rw [← hu]
    simp only [Complex.real_smul]
    linear_combination ((W x:ℂ)*(z x:ℂ)*(p x:ℂ)*wave (F x)) * Complex.I_sq
  have cw := HasDerivAt.continuousOn wd
  have cz := HasDerivAt.continuousOn zd
  have cf := HasDerivAt.continuousOn fd
  have cdw : ContinuousOn dW (Icc a b) := by unfold dW; fun_prop (disch := solve_by_elim [ne_of_gt,pos])
  have cdz : ContinuousOn dz (Icc a b) := by unfold dz; fun_prop (disch := intro x hx; exact pow_ne_zero _ (nz hx))
  have cwave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwF := cwave.comp_continuousOn cf
  have ce : ContinuousOn er (Icc a b) := by unfold er; fun_prop
  have ck : ContinuousOn (kernel σ β γ) (Icc a b) := by
    change ContinuousOn (fun x : ℝ => ((x^(σ-1):ℝ):ℂ)*wave (F x)) _
    have hc : ContinuousOn (fun x : ℝ => x^(σ-1)) (Icc a b) :=
      continuousOn_id.rpow_const fun _ hx => Or.inl (pos hx).ne'
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul cwF
  have ei := ce.intervalIntegrable_of_Icc (μ := volume) hab
  have ki := ck.intervalIntegrable_of_Icc (μ := volume) hab
  have fi := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := B)
    (f' := fun x => kernel σ β γ x - er x)
    (fun x hx => hB x ((uIcc_of_le hab) ▸ hx)) (ki.sub ei)
  rw [intervalIntegral.integral_sub ki ei] at fi
  have zi := cdz.intervalIntegrable_of_Icc (μ := volume) hab
  have wi := cdw.intervalIntegrable_of_Icc (μ := volume) hab
  have wint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := dW)
    (fun x hx => wd x ((uIcc_of_le hab) ▸ hx)) wi
  have zint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := z) (f' := dz)
    (fun x hx => zd x ((uIcc_of_le hab) ▸ hx)) zi
  have zmax (x : ℝ) (hx : x ∈ Icc a b) : |z x| ≤ 1/H := by
    simp only [z, abs_div, abs_one]
    exact one_div_le_one_div_of_le hH (hsep x hx)
  have Wmax (x : ℝ) (hx : x ∈ Icc a b) : |W x| ≤ b^σ := by
    rw [abs_of_nonneg (Real.rpow_nonneg (pos hx).le _)]
    exact Real.rpow_le_rpow (pos hx).le hx.2 hσ
  have Bmax (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ b^σ/H := by
    simp only [B, norm_mul, norm_neg, Complex.norm_I, wave_norm, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [div_eq_mul_inv] using mul_le_mul (Wmax x hx) (zmax x hx) (abs_nonneg _) (Real.rpow_nonneg (ha.trans_le hab).le _)
  -- The sign of β determines the monotonicity of the reciprocal on this interval.
  have zvar : (∫ x in a..b, |dz x|) ≤ 2/H := by
    have sign {x : ℝ} : 0 ≤ (β*x+γ)^2 := sq_nonneg _
    have za := abs_le.mp (zmax a (left_mem_Icc.mpr hab))
    have zb := abs_le.mp (zmax b (right_mem_Icc.mpr hab))
    rcases le_total 0 β with hp | hn
    · have he : (∫ x in a..b, |dz x|) = -(z b-z a) := by
        rw [← zint, ← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
    · have he : (∫ x in a..b, |dz x|) = z b-z a := by
        rw [← zint]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonneg (div_nonneg (neg_nonneg.mpr hn) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
  have eBound (x : ℝ) (hx : x ∈ Icc a b) : ‖er x‖ ≤ dW x*(1/H) + b^σ*|dz x| := by
    simp only [er, norm_mul, Complex.norm_I, one_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply (abs_add_le ..).trans
    rw [abs_mul (dW x) (z x), abs_mul (W x) (dz x), abs_of_nonneg (show 0 ≤ dW x from mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _))]
    exact add_le_add (mul_le_mul_of_nonneg_left (zmax x hx) (mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _)))
      (mul_le_mul_of_nonneg_right (Wmax x hx) (abs_nonneg _))
  have ai := cdz.abs.intervalIntegrable_of_Icc (μ := volume) hab
  have eint := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => eBound x ⟨hx.1.le,hx.2⟩)
    ((wi.mul_const (1/H)).add (ai.const_mul (b^σ)))
  rw [intervalIntegral.integral_add (wi.mul_const (1/H)) (ai.const_mul (b^σ)),
    intervalIntegral.integral_mul_const (1/H) dW, intervalIntegral.integral_const_mul (b^σ) (fun x => |dz x|), wint] at eint
  rw [sub_eq_iff_eq_add.mp fi]
  apply (norm_add_le ..).trans
  have bd := norm_sub_le (B b) (B a)
  have bl := Bmax a (left_mem_Icc.mpr hab)
  have br := Bmax b (right_mem_Icc.mpr hab)
  have vb := mul_le_mul_of_nonneg_left zvar (Real.rpow_nonneg (ha.trans_le hab).le σ)
  have wa : 0 ≤ W a := Real.rpow_nonneg ha.le _
  have wb := mul_le_mul_of_nonneg_right (show W b-W a ≤ b^σ from sub_le_self _ wa) (one_div_nonneg.mpr hH.le)
  simp only [div_eq_mul_inv,one_mul] at bl br vb eint wb ⊢
  linarith only [bd,bl,br,vb,eint,wb]

/-- The bound holds through a stationary point and is uniform in the additive
frequency. The factor X^σ comes from scaling the dyadic interval. -/
private theorem uniform_bound :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X →
      0 ≤ σ → σ ≤ 1 → γ ≠ 0 →
      ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖ ≤
        X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  intro X a b σ γ β hX ha hab hb hσ hσ' hγ
  let l := a/X
  let r := b/X
  have h1 : 1 ≤ l := (one_le_div hX).mpr ha
  have hlr : l ≤ r := div_le_div_of_nonneg_right hab hX.le
  have h2 : r ≤ 2 := (div_le_iff₀ hX).mpr hb
  let z : ℂ := ((X^(σ-1):ℝ):ℂ)*wave (γ*Real.log X)
  have hz : ‖z‖ = X^(σ-1) := by
    simp only [z, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hX.le _)]
  have eqn : (∫ x in l..r, kernel σ β γ (X*x)) = z * (∫ x in l..r, kernel σ (β*X) γ x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    exact rescale hX (zero_lt_one.trans_le (h1.trans hx.1)) σ β γ
  have sub := intervalIntegral.integral_comp_mul_left (kernel σ β γ) (a := l) (b := r) hX.ne'
  have hx1 : X*l = a := by dsimp [l]; field_simp
  have hx2 : X*r = b := by dsimp [r]; field_simp
  rw [sub,hx1,hx2] at eqn
  have eqnorm := congrArg norm eqn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hX), norm_mul, hz] at eqnorm
  have hxpow : X * X^(σ-1) = X^σ := by
    calc
      _ = X^(1:ℝ) * X^(σ-1) := by rw [Real.rpow_one]
      _ = X^(1+(σ-1)) := (Real.rpow_add hX _ _).symm
      _ = _ := by rw [show (1:ℝ)+(σ-1)=σ by ring]
  change ‖∫ x in a..b, kernel σ β γ x‖ ≤ _
  calc
    _ = X*(X^(σ-1) * ‖∫ x in l..r, kernel σ (β*X) γ x‖) := by
      rw [← eqnorm, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
    _ ≤ X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
      rw [← mul_assoc, hxpow]
      exact mul_le_mul_of_nonneg_left (dyadic h1 hlr h2 hγ hσ hσ' (β*X)) (Real.rpow_nonneg hX.le _)



/-- A dyadic piece of the additively twisted zero kernel. The curvature bound is
uniform in the frequency, and a lower bound on the absolute phase slope gives
stronger decay when the interval misses the stationary point. -/
private theorem per_ordinate :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      ‖K‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K‖ ≤ X^σ * ((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K‖ ≤ 5*b^σ/H := by
  intro X a b σ γ β hX ha hab hb hσ hσ' K
  refine ⟨?_, ?_, fun H hH hsep => separated (hX.trans_le ha) hab hσ hH hsep⟩
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := kernel σ β γ)
      (C := X^(σ-1)) (a := a) (b := b) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have hxx := ha.trans hx.1.le
        rw [kernel,norm_mul,wave_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (hX.le.trans hxx) _)]
        exact Real.rpow_le_rpow_of_nonpos hX hxx (sub_nonpos.mpr hσ'))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    have hb' : b-a ≤ X := by linarith
    apply h.trans
    calc
      _ ≤ X^(σ-1)*X := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hX.le _)
      _ = _ := by rw [Real.rpow_sub_one hX.ne', div_mul_cancel₀ _ hX.ne']
  · intro hγ
    exact (uniform_bound X a b σ γ β hX ha hab hb hσ hσ' hγ).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.rpow_nonneg hX.le _))

-- Bin zero contributes the trivial bound, bins 1 through J the curvature
-- estimate, and larger bins the reciprocal first-derivative estimate.
private noncomputable def profile (J j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ J then (3+5*Real.pi)/Real.sqrt j else 20/j

private lemma profile_nonneg (J j : ℕ) : 0 ≤ profile J j := by
  unfold profile
  split_ifs <;> positivity

private theorem sqrt_step (j : ℕ) :
    1 / Real.sqrt (j+1:ℝ) ≤ 2*(Real.sqrt (j+1:ℝ)-Real.sqrt j) := by
  have hp : 0 < Real.sqrt (j+1:ℝ) := by positivity
  have hle := Real.sqrt_le_sqrt (show (j:ℝ) ≤ j+1 by linarith)
  have hs1 := Real.sq_sqrt (show 0 ≤ (j+1:ℝ) by positivity)
  have hs0 := Real.sq_sqrt (show 0 ≤ (j:ℝ) by positivity)
  apply (div_le_iff₀ hp).mpr
  nlinarith only [sq_nonneg (Real.sqrt (j+1:ℝ)-Real.sqrt j), hs1, hs0]

private theorem profile_sum (J N : ℕ) :
    (∑ j ∈ Finset.range (N+1), profile J j) ≤
      1+2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ)) := by
  have bound (n : ℕ) :
      (∑ j ∈ Finset.range (n+1), profile J j) ≤
        1+2*(3+5*Real.pi)*Real.sqrt (min n J) + 20*(harmonic n:ℝ) := by
    induction n with
    | zero => simp [profile, harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show profile J (n+1) = (if n+1 ≤ J then (3+5*Real.pi)/Real.sqrt (n+1:ℝ) else 20/(n+1:ℝ)) by simp [profile]]
      rw [harmonic_succ]
      push_cast
      split_ifs with h
      · rw [min_eq_left (show (n:ℝ)+1 ≤ J by exact_mod_cast h)]
        rw [min_eq_left (show (n:ℝ) ≤ J by exact_mod_cast Nat.le_trans (Nat.le_succ n) h)] at ih
        have hs := mul_le_mul_of_nonneg_left (sqrt_step n) (show 0 ≤ 3+5*Real.pi by positivity)
        have hr : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity
        simp only [div_eq_mul_inv, one_mul] at hs ⊢
        linarith only [ih,hs,hr]
      · have hn : J ≤ n := by omega
        rw [min_eq_right (show (J:ℝ) ≤ n by exact_mod_cast hn)] at ih
        rw [min_eq_right (show (J:ℝ) ≤ n+1 by exact_mod_cast hn.trans (Nat.le_succ _))]
        simp only [div_eq_mul_inv]
        linarith only [ih]
  have hs := Real.sqrt_le_sqrt (show min (N:ℝ) J ≤ J by exact min_le_right _ _)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(3+5*Real.pi) by positivity)
  have hn := harmonic_le_one_add_log (N+1)
  have hh : (harmonic N : ℝ) ≤ harmonic (N+1) := by
    rw [harmonic_succ]
    push_cast
    have h : 0 ≤ ((N:ℝ)+1)⁻¹ := by positivity
    linarith
  push_cast at hn
  linarith only [bound N,hs',hn,hh]

end GoldbachOscillation

open GoldbachOscillation
open scoped ComplexConjugate

set_option maxHeartbeats 1200000 in
/-- Dyadic kernel estimates and their sum over a finite indexed family with a unit-height occupancy bound. -/
theorem Conjectures.Goldbach.ZeroAdditiveTwistDyadic :
    ∀ (X a b σ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := fun γ : ℝ => ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      (∀ γ : ℝ, ‖K γ‖ ≤ X^σ ∧
        (γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H) ∧
      ∀ (I : Finset ℕ) (g : ℕ → ℝ) (J N : ℕ) (M : ℝ),
        0 ≤ M → 4*|β| * X ≤ J → (∀ i ∈ I, |g i| < (N:ℝ)+1) →
        (∀ j ≤ N, (((I.filter (fun i => ⌊|g i|⌋₊ = j)).card : ℕ) : ℝ) ≤ M) →
        (∑ i ∈ I, ‖K (g i)‖) ≤
          X^σ*M*(1 + 2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ))) := by
  intro X a b σ β hX ha hab hb hσ hσ' K
  have single (γ : ℝ) : ‖K γ‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H :=
    per_ordinate X a b σ γ β hX ha hab hb hσ hσ'
  refine ⟨single, ?_⟩
  intro I g J N M hM hJ hN hcount
  let bin := fun i : ℕ => ⌊|g i|⌋₊
  have hscale := Real.rpow_pos_of_pos hX σ
  have hpow : b^σ ≤ 2*X^σ := by
    calc
      b^σ ≤ (2*X)^σ := Real.rpow_le_rpow (hX.le.trans (ha.trans hab)) hb hσ
      _ = (2:ℝ)^σ * X^σ := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2*X^σ := by
        apply mul_le_mul_of_nonneg_right _ hscale.le
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hσ'
  have per (i : ℕ) : ‖K (g i)‖ ≤ X^σ * profile J (bin i) := by
    have hfloor : ((bin i):ℝ) ≤ |g i| := Nat.floor_le (abs_nonneg _)
    unfold profile
    split_ifs with hz hj
    · simpa using (single (g i)).1
    · have hbin : 0 < ((bin i):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hg : g i ≠ 0 := abs_pos.mp (hbin.trans_le hfloor)
      apply ((single (g i)).2.1 hg).trans
      apply mul_le_mul_of_nonneg_left _ hscale.le
      exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hbin)
        (Real.sqrt_le_sqrt hfloor)
    · have hbin : 0 < ((bin i):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hcut : (J:ℝ) ≤ bin i := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hj))
      have sep (x : ℝ) (hx : x ∈ Icc a b) : (bin i:ℝ)/2 ≤ |β*x+g i| := by
        have hxx : 0 ≤ x := hX.le.trans (ha.trans hx.1)
        have ht := abs_add_le (β*x+g i) (-(β*x))
        rw [show β*x+g i+ -(β*x) = g i by ring, abs_neg, abs_mul, abs_of_nonneg hxx] at ht
        have hbβ := mul_le_mul_of_nonneg_left (hx.2.trans hb) (abs_nonneg β)
        linarith only [ht,hbβ,hJ,hcut,hfloor]
      have hhalf : 0 < (bin i:ℝ)/2 := by positivity
      apply ((single (g i)).2.2 _ hhalf sep).trans
      apply (div_le_iff₀ hhalf).mpr
      calc
        5*b^σ ≤ 5*(2*X^σ) := by linarith only [hpow]
        _ = X^σ*(20/(bin i:ℝ))*((bin i:ℝ)/2) := by field_simp; norm_num
  have maps : ∀ i ∈ I, bin i ∈ Finset.range (N+1) := by
    intro i hi
    apply Finset.mem_range.mpr
    exact (Nat.floor_lt (abs_nonneg _)).mpr (by simpa using hN i hi)
  calc
    _ ≤ ∑ i ∈ I, X^σ*profile J (bin i) := Finset.sum_le_sum fun i _ => per i
    _ = ∑ j ∈ Finset.range (N+1), ∑ i ∈ I.filter (fun i => bin i = j),
          X^σ*profile J (bin i) := (Finset.sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ j ∈ Finset.range (N+1), M*(X^σ*profile J j) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ = ∑ i ∈ I.filter (fun i => bin i = j), X^σ*profile J j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = ((I.filter (fun i => bin i = j)).card:ℝ)*(X^σ*profile J j) := by
          simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount j (by have := Finset.mem_range.mp hj; omega))
          (mul_nonneg hscale.le (profile_nonneg J j))
    _ = X^σ*M*(∑ j ∈ Finset.range (N+1), profile J j) := by
      simp_rw [← mul_assoc, mul_comm M (X^σ)]
      exact (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (profile_sum J N) (mul_nonneg hscale.le hM)
