import Mathlib

open MeasureTheory

theorem PEqualNP.Outside.L_goldbach_mellin_phase_regularity :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ F : ℝ → ℝ, Continuous F → HasCompactSupport F → ∀ t u : ℝ, ‖W F t-W F u‖ ≤ |t-u| * ∫ x : ℝ, |x*F x| := by
  dsimp only
  intro F hF hFs t u
  let phase := fun a : ℝ => Complex.exp ((a : ℂ) * Complex.I)
  have chord (a b : ℝ) : ‖phase a - phase b‖ ≤ |a - b| := by
    have hfactor : phase a - phase b = (phase (a - b) - 1) * phase b := by
      dsimp only [phase]
      rw [sub_mul, one_mul, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
        sub_add_cancel]
    rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simpa [phase, mul_comm, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))
  let f := fun v x : ℝ => (F x : ℂ) * phase (v * x)
  have hFs' : HasCompactSupport (fun x => (F x : ℂ)) :=
    hFs.comp_left Complex.ofReal_zero
  have hf (v : ℝ) : Integrable (f v) := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [f, phase]
      fun_prop
    · exact hFs'.mul_right (f' := fun x => phase (v * x))
  have hm : Integrable (fun x : ℝ => |x * F x|) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact (hFs.mul_left (f := fun x => x)).abs
  change ‖(∫ x, f t x) - (∫ x, f u x)‖ ≤ |t - u| * ∫ x : ℝ, |x * F x|
  rw [← integral_sub (hf t) (hf u), ← integral_const_mul]
  calc
    ‖∫ x, f t x - f u x‖ ≤ ∫ x, ‖f t x - f u x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t - u| * |x * F x| := by
      apply integral_mono ((hf t).sub (hf u)).norm (hm.const_mul _)
      intro x
      change ‖(F x : ℂ) * phase (t * x) - (F x : ℂ) * phase (u * x)‖ ≤
        |t - u| * |x * F x|
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |F x| * ‖phase (t * x) - phase (u * x)‖ ≤ |F x| * |t * x - u * x| :=
          mul_le_mul_of_nonneg_left (chord _ _) (abs_nonneg _)
        _ = |t - u| * |x * F x| := by
          rw [← sub_mul, abs_mul, abs_mul]
          ring
