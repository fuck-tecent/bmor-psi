import Mathlib

private theorem mellin_transport :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ F : ℝ → ℝ, (∀ j : ℕ, ContDiff ℝ j F) → HasCompactSupport F → ∀ t : ℝ, W (deriv F) t = -((t:ℂ)*Complex.I)*W F t := by
  dsimp only
  intro F hsmooth hs t
  let f : ℝ → ℂ := fun x => (F x : ℂ)
  let fd : ℝ → ℂ := fun x => ((deriv F x : ℝ) : ℂ)
  let c : ℂ := (t:ℂ)*Complex.I
  let g : ℝ → ℂ := fun x => Complex.exp (((t*x:ℝ):ℂ)*Complex.I)
  change (∫ x : ℝ, fd x * g x) = -c * (∫ x : ℝ, f x * g x)
  have hfc : Continuous f := Complex.continuous_ofReal.comp (hsmooth 0).continuous
  have hfdc : Continuous fd := Complex.continuous_ofReal.comp
    ((hsmooth 1).continuous_deriv (by norm_num))
  have hfs : HasCompactSupport f := by
    simpa only [f, Function.comp_def] using
      (hs.comp_left (g := fun r : ℝ => (r:ℂ)) (by simp))
  have hfds : HasCompactSupport fd := by
    simpa only [fd, Function.comp_def] using
      (hs.deriv.comp_left (g := fun r : ℝ => (r:ℂ)) (by simp))
  have hgeq : g = fun x : ℝ => Complex.exp (c*(x:ℂ)) := by
    funext x
    apply congrArg Complex.exp
    dsimp [g, c]
    push_cast
    ring
  have hgc : Continuous g := by rw [hgeq]; fun_prop
  have hdf : ∀ x : ℝ, HasDerivAt f (fd x) x := by
    intro x
    exact ((hsmooth 1).differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp
  have hdg : ∀ x : ℝ, HasDerivAt g (c*g x) x := by
    intro x
    rw [hgeq]
    have he : HasDerivAt (fun y : ℝ => c*(y:ℂ)) c x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul c)
    simpa only [mul_comm] using he.cexp
  have hi₁ : MeasureTheory.Integrable (g * fd) :=
    (hgc.mul hfdc).integrable_of_hasCompactSupport hfds.mul_left
  have hi₂ : MeasureTheory.Integrable ((fun x => c*g x) * f) :=
    ((continuous_const.mul hgc).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₃ : MeasureTheory.Integrable (g * f) :=
    (hgc.mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have H := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hdg x) (fun x _ => hdf x) hi₁ hi₂ hi₃
  have H' : (∫ x : ℝ, fd x * g x) =
      -(∫ x : ℝ, c*(f x*g x)) := by
    simpa only [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using H
  rw [MeasureTheory.integral_const_mul] at H'
  simpa only [neg_mul] using H'


theorem PEqualNP.Outside.L_goldbach_mellin_decay_seminorm :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ (F : ℝ → ℝ) (m : ℕ), (∀ j : ℕ, ContDiff ℝ j F) → HasCompactSupport F → ∀ t : ℝ, |t|^m*‖W F t‖ ≤ ∫ x : ℝ, |iteratedDeriv m F x| := by
  dsimp only
  intro F m hsmooth hs t
  let W : (ℝ → ℝ) → ℝ → ℂ := fun G u =>
    ∫ x : ℝ, (G x:ℂ)*Complex.exp (((u*x:ℝ):ℂ)*Complex.I)
  change |t|^m * ‖W F t‖ ≤ ∫ x : ℝ, |iteratedDeriv m F x|
  have heq : ∀ (k : ℕ) (G : ℝ → ℝ),
      (∀ j : ℕ, ContDiff ℝ j G) → HasCompactSupport G →
      ‖W (iteratedDeriv k G) t‖ = |t|^k * ‖W G t‖ := by
    intro k
    induction k with
    | zero =>
        intro G hG hsG
        simp
    | succ k ih =>
        intro G hG hsG
        have hGd : ∀ j : ℕ, ContDiff ℝ j (deriv G) := by
          intro j
          apply ContDiff.deriv' (n := j)
          simpa using hG (j+1)
        have hd := mellin_transport G hG hsG t
        change W (deriv G) t = -((t:ℂ)*Complex.I)*W G t at hd
        rw [iteratedDeriv_succ', ih (deriv G) hGd hsG.deriv, hd]
        simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I,
          Real.norm_eq_abs, mul_one, pow_succ]
        ring
  rw [← heq m F hsmooth hs]
  have H := MeasureTheory.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
    (fun x : ℝ => ((iteratedDeriv m F x : ℝ):ℂ)*
      Complex.exp (((t*x:ℝ):ℂ)*Complex.I))
  simpa only [W, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one] using H
