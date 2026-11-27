import Mathlib

open MeasureTheory Set

theorem PEqualNP.Outside.L_goldbach_mellin_log_identification :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ (φ : ℝ → ℝ) (a b t : ℝ), 0<a → a<b → Continuous φ → (∀ u, u<a ∨ b<u → φ u=0) → W (fun x => Real.exp (x/2)*φ (Real.exp x)) t = intervalIntegral (fun u : ℝ => ((φ u/Real.sqrt u:ℝ):ℂ)*Complex.exp (((t*Real.log u:ℝ):ℂ)*Complex.I)) a b MeasureTheory.volume := by
  intro W φ a b t ha hab _ hsupport
  let g (u : ℝ) : ℂ := ((φ u / Real.sqrt u : ℝ) : ℂ) *
    Complex.exp (((t * Real.log u : ℝ) : ℂ) * Complex.I)
  have weight (x : ℝ) : Real.exp x * (φ (Real.exp x) / Real.sqrt (Real.exp x)) =
      Real.exp (x / 2) * φ (Real.exp x) := by
    rw [Real.exp_half, ← mul_div_assoc]
    apply (div_eq_iff (Real.sqrt_pos.2 (Real.exp_pos x)).ne').2
    calc
      _ = (Real.sqrt (Real.exp x)) ^ 2 * φ (Real.exp x) := by rw [Real.sq_sqrt (Real.exp_pos x).le]
      _ = _ := by ring
  calc
    _ = ∫ x : ℝ, Real.exp x • g (Real.exp x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [g, Complex.real_smul, Real.log_exp, ← mul_assoc, ← Complex.ofReal_mul, weight]
    _ = ∫ u in Ioi 0, g u := integral_comp_exp g
    _ = ∫ u in Icc a b, g u := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      · exact fun u hu => ha.trans_le hu.1
      · intro u hu
        have hout : u < a ∨ b < u := by
          simpa only [mem_Icc, not_and_or, not_le] using hu.2
        simp [g, hsupport u hout]
    _ = _ := by rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
