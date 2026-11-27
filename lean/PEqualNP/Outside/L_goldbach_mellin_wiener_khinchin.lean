import Mathlib

open MeasureTheory
open scoped ComplexConjugate

theorem PEqualNP.Outside.L_goldbach_mellin_wiener_khinchin :
    let W := fun (f : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (f x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h); ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∀ t : ℝ, (∫ h : ℝ, R f h*Real.cos (t*h)) = ‖W f t‖^2 := by
  intro W R f hf hsupport t
  let g (x : ℝ) : ℂ := (f x : ℂ) * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  let V := ∫ x, g x
  let K (z : ℝ × ℝ) := conj (g z.1) * g (z.1 + z.2)
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg : Integrable g := by
    refine (hf.integrable_of_hasCompactSupport hsupport).norm.mono' hgc.aestronglyMeasurable ?_
    filter_upwards with x
    simp only [g, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, le_refl]
  have hconj : Integrable (fun x => conj (g x)) := by
    refine hg.norm.mono' (Complex.continuous_conj.comp hgc).aestronglyMeasurable ?_
    filter_upwards with x
    simp
  have hK : Integrable K ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_add (volume : Measure ℝ) volume).integrable_comp_of_integrable
      (hconj.mul_prod hg)
  have phase (x h : ℝ) : (K (x, h)).re = (f x * f (x + h)) * Real.cos (t * h) := by
    have hphase : (((t * x : ℝ) : ℂ) * -Complex.I) +
        (((t * (x + h) : ℝ) : ℂ) * Complex.I) = (((t * h : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    simp only [K, g, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    rw [mul_mul_mul_comm, ← Complex.exp_add, hphase, ← Complex.ofReal_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      zero_mul, sub_zero]
  have hiter : (∫ h : ℝ, ∫ x : ℝ, K (x, h)) = conj V * V := by
    rw [← integral_prod_symm K hK, integral_prod K hK]
    simp_rw [K, integral_const_mul, integral_add_left_eq_self g]
    rw [integral_mul_const, integral_conj]
  change (∫ h : ℝ, R f h * Real.cos (t * h)) = ‖V‖ ^ 2
  calc
    _ = ∫ h : ℝ, (∫ x : ℝ, K (x, h)).re := by
      apply integral_congr_ae
      filter_upwards [hK.prod_left_ae] with h hh
      have hre : (∫ x : ℝ, (K (x, h)).re) = (∫ x : ℝ, K (x, h)).re := by
        simpa only [RCLike.re_eq_complex_re] using integral_re hh
      rw [← hre]
      simp_rw [phase, integral_mul_const]
      rfl
    _ = (conj V * V).re := by
      rw [← hiter]
      simpa only [RCLike.re_eq_complex_re] using integral_re hK.integral_prod_right
    _ = _ := by rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
