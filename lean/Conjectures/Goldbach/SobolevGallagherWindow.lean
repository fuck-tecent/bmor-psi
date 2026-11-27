import Mathlib

open Finset MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Conjectures.Goldbach.SobolevGallagherWindow_aux

theorem sub_le_integral_abs_deriv_right {f f' : ℝ → ℝ} {a x b : ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hcont : Continuous f')
    (hax : a ≤ x) (hxb : x ≤ b) :
    f b - f x ≤ ∫ y in a..b, |f' y| := by
  have hEq : (∫ y in x..b, f' y) = f b - f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hcont.intervalIntegrable x b)
  rw [← hEq]
  exact (le_abs_self _).trans
    ((intervalIntegral.abs_integral_le_integral_abs hxb).trans
      (intervalIntegral.integral_mono_interval hax hxb le_rfl
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hcont.abs.intervalIntegrable a b)))

theorem sub_le_integral_abs_deriv_left {f f' : ℝ → ℝ} {a x b : ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hcont : Continuous f')
    (hax : a ≤ x) (hxb : x ≤ b) :
    f a - f x ≤ ∫ y in a..b, |f' y| := by
  have hEq : (∫ y in a..x, f' y) = f x - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hcont.intervalIntegrable a x)
  rw [show f a - f x = -∫ y in a..x, f' y by rw [hEq]; ring]
  exact (neg_le_abs _).trans
    ((intervalIntegral.abs_integral_le_integral_abs hax).trans
      (intervalIntegral.integral_mono_interval le_rfl hax hxb
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hcont.abs.intervalIntegrable a b)))

theorem right_endpoint_length_mul_le {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hcont : Continuous f')
    (hab : a ≤ b) :
    (b - a) * f b ≤ (∫ x in a..b, f x) +
      (b - a) * ∫ x in a..b, |f' x| := by
  have fDifferentiable : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  let variation : ℝ := ∫ x in a..b, |f' x|
  have pointwise (x : ℝ) (hx : x ∈ Icc a b) : f b ≤ f x + variation := by
    have hsub := sub_le_integral_abs_deriv_right hderiv hcont hx.1 hx.2
    dsimp only [variation]
    linarith
  have integrated :
      (∫ _x in a..b, f b) ≤ ∫ x in a..b, f x + variation := by
    apply intervalIntegral.integral_mono_on hab
    · exact (continuous_const : Continuous fun _ : ℝ => f b).intervalIntegrable a b
    · exact (fContinuous.add
        (continuous_const : Continuous fun _ : ℝ => variation)).intervalIntegrable a b
    · exact pointwise
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (fContinuous.intervalIntegrable a b)
      ((continuous_const : Continuous fun _ : ℝ => variation).intervalIntegrable a b),
    intervalIntegral.integral_const] at integrated
  simpa only [variation, smul_eq_mul] using integrated

theorem left_endpoint_length_mul_le {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hcont : Continuous f')
    (hab : a ≤ b) :
    (b - a) * f a ≤ (∫ x in a..b, f x) +
      (b - a) * ∫ x in a..b, |f' x| := by
  have fDifferentiable : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  let variation : ℝ := ∫ x in a..b, |f' x|
  have pointwise (x : ℝ) (hx : x ∈ Icc a b) : f a ≤ f x + variation := by
    have hsub := sub_le_integral_abs_deriv_left hderiv hcont hx.1 hx.2
    dsimp only [variation]
    linarith
  have integrated :
      (∫ _x in a..b, f a) ≤ ∫ x in a..b, f x + variation := by
    apply intervalIntegral.integral_mono_on hab
    · exact (continuous_const : Continuous fun _ : ℝ => f a).intervalIntegrable a b
    · exact (fContinuous.add
        (continuous_const : Continuous fun _ : ℝ => variation)).intervalIntegrable a b
    · exact pointwise
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (fContinuous.intervalIntegrable a b)
      ((continuous_const : Continuous fun _ : ℝ => variation).intervalIntegrable a b),
    intervalIntegral.integral_const] at integrated
  simpa only [variation, smul_eq_mul] using integrated

theorem split_window_length_mul_le {f f' : ℝ → ℝ} {a centre b : ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hcont : Continuous f')
    (hac : a ≤ centre) (hcb : centre ≤ b) :
    (b - a) * f centre ≤ (∫ x in a..b, f x) +
      (centre - a) * (∫ x in a..centre, |f' x|) +
      (b - centre) * (∫ x in centre..b, |f' x|) := by
  have hleft := right_endpoint_length_mul_le hderiv hcont hac
  have hright := left_endpoint_length_mul_le hderiv hcont hcb
  have fDifferentiable : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  have hadjacent :
      (∫ x in a..centre, f x) + (∫ x in centre..b, f x) = ∫ x in a..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (fContinuous.intervalIntegrable a centre)
      (fContinuous.intervalIntegrable centre b)
  calc
    (b - a) * f centre =
        (centre - a) * f centre + (b - centre) * f centre := by ring
    _ ≤ ((∫ x in a..centre, f x) +
          (centre - a) * (∫ x in a..centre, |f' x|)) +
        ((∫ x in centre..b, f x) +
          (b - centre) * (∫ x in centre..b, |f' x|)) := add_le_add hleft hright
    _ = (∫ x in a..b, f x) +
          (centre - a) * (∫ x in a..centre, |f' x|) +
          (b - centre) * (∫ x in centre..b, |f' x|) := by
      rw [← hadjacent]
      ring

end Conjectures.Goldbach.SobolevGallagherWindow_aux

theorem Conjectures.Goldbach.SobolevGallagherWindow :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N : ℕ) (c : ℕ → ℂ) (a δ : ℝ), 0 < δ → let S (t : ℝ) := ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t); ‖S a‖ ^ 2 ≤ (intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) (a+δ) MeasureTheory.volume) / (2 * δ) + intervalIntegral (fun t => ‖S t‖ * ‖deriv S t‖) (a-δ) (a+δ) MeasureTheory.volume := by
  dsimp only
  intro M N c a δ hδ
  let E : ℝ → ℂ := fun x =>
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let S : ℝ → ℂ := fun t =>
    ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t)
  change ‖S a‖ ^ 2 ≤
    (intervalIntegral (fun t => ‖S t‖ ^ 2) (a - δ) (a + δ) volume) / (2 * δ) +
      intervalIntegral (fun t => ‖S t‖ * ‖deriv S t‖) (a - δ) (a + δ) volume
  have hS : ContDiff ℝ 1 S := by
    unfold S E
    apply ContDiff.sum
    intro k hk
    apply contDiff_const.mul
    apply Complex.contDiff_exp.comp
    apply (Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ 1
        (fun t : ℝ => 2 * Real.pi * ((k : ℝ) * t)))).mul
    exact contDiff_const
  have hScont : Continuous S := hS.continuous
  have hSderivCont : Continuous (deriv S) := hS.continuous_deriv_one
  let g : ℝ → ℝ := fun t => ‖S t‖ ^ 2
  let gradient : ℝ → ℝ := fun t => 2 * inner ℝ (S t) (deriv S t)
  let q : ℝ → ℝ := fun t => ‖S t‖ * ‖deriv S t‖
  have hgderiv : ∀ t, HasDerivAt g (gradient t) t := by
    intro t
    dsimp [g, gradient]
    exact (hS.differentiable (by norm_num) t).hasDerivAt.norm_sq
  have hgradientCont : Continuous gradient := by
    dsimp [gradient]
    exact continuous_const.mul (hScont.inner hSderivCont)
  have hqCont : Continuous q := by
    dsimp [q]
    exact hScont.norm.mul hSderivCont.norm
  have hgradientBound (t : ℝ) : |gradient t| ≤ 2 * q t := by
    dsimp [gradient, q]
    calc
      |2 * inner ℝ (S t) (deriv S t)| =
          2 * |inner ℝ (S t) (deriv S t)| := by
            rw [abs_mul]
            norm_num
      _ ≤ 2 * (‖S t‖ * ‖deriv S t‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  let lower : ℝ := a - δ
  let upper : ℝ := a + δ
  let energyIntegral : ℝ := intervalIntegral g lower upper volume
  let gradientIntegral : ℝ :=
    intervalIntegral (fun t => |gradient t|) lower upper volume
  let productIntegral : ℝ := intervalIntegral q lower upper volume
  change g a ≤ energyIntegral / (2 * δ) + productIntegral
  have hsplit :=
    Conjectures.Goldbach.SobolevGallagherWindow_aux.split_window_length_mul_le
      (f := g) (f' := gradient) (a := lower) (centre := a) (b := upper)
      hgderiv hgradientCont (by dsimp [lower]; linarith) (by dsimp [upper]; linarith)
  have hgradientAdjacent :
      intervalIntegral (fun t => |gradient t|) lower a volume +
          intervalIntegral (fun t => |gradient t|) a upper volume =
        gradientIntegral := by
    dsimp [gradientIntegral]
    change (∫ t in lower..a, |gradient t|) + (∫ t in a..upper, |gradient t|) =
      ∫ t in lower..upper, |gradient t|
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgradientCont.abs.intervalIntegrable lower a)
      (hgradientCont.abs.intervalIntegrable a upper)
  have hmid : (2 * δ) * g a ≤ energyIntegral + δ * gradientIntegral := by
    calc
      (2 * δ) * g a = (upper - lower) * g a := by
        dsimp [lower, upper]
        ring
      _ ≤ energyIntegral +
          (a - lower) * intervalIntegral (fun t => |gradient t|) lower a volume +
          (upper - a) * intervalIntegral (fun t => |gradient t|) a upper volume := by
        simpa only [energyIntegral] using hsplit
      _ = energyIntegral + δ *
          (intervalIntegral (fun t => |gradient t|) lower a volume +
            intervalIntegral (fun t => |gradient t|) a upper volume) := by
        dsimp [lower, upper]
        ring
      _ = energyIntegral + δ * gradientIntegral := by rw [hgradientAdjacent]
  have hgradientIntegralBound : gradientIntegral ≤ 2 * productIntegral := by
    have hbounds : lower ≤ upper := by
      dsimp [lower, upper]
      linarith
    have hleft : IntervalIntegrable (fun t => |gradient t|) volume lower upper :=
      hgradientCont.abs.intervalIntegrable lower upper
    have hright : IntervalIntegrable (fun t => 2 * q t) volume lower upper :=
      (continuous_const.mul hqCont).intervalIntegrable lower upper
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hbounds hleft hright
      (fun t _ => hgradientBound t)
    calc
      gradientIntegral = intervalIntegral (fun t => |gradient t|) lower upper volume := rfl
      _ ≤ intervalIntegral (fun t => 2 * q t) lower upper volume := hmono
      _ = 2 * productIntegral := by
        dsimp [productIntegral]
        rw [intervalIntegral.integral_const_mul]
  have hscaled : (2 * δ) * g a ≤
      energyIntegral + (2 * δ) * productIntegral := by
    calc
      (2 * δ) * g a ≤ energyIntegral + δ * gradientIntegral := hmid
      _ ≤ energyIntegral + δ * (2 * productIntegral) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hgradientIntegralBound hδ.le)
      _ = energyIntegral + (2 * δ) * productIntegral := by ring
  have hpositive : 0 < 2 * δ := mul_pos (by norm_num) hδ
  have hquotient :
      (energyIntegral + (2 * δ) * productIntegral) / (2 * δ) =
        energyIntegral / (2 * δ) + productIntegral := by
    field_simp [ne_of_gt hpositive]
  rw [← hquotient]
  apply (le_div_iff₀ hpositive).2
  simpa only [mul_comm] using hscaled
