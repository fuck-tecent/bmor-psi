import Mathlib

theorem PEqualNP.Outside.L_goldbach_mask_split :
    ∀ f : ℝ → ℂ, ∀ u : ℝ → ℝ, Continuous f → Continuous u → intervalIntegral (fun t => (u t:ℂ)*f t) (0:ℝ) 1 MeasureTheory.volume + intervalIntegral (fun t => ((1-u t:ℝ):ℂ)*f t) (0:ℝ) 1 MeasureTheory.volume = intervalIntegral (fun t => f t) (0:ℝ) 1 MeasureTheory.volume := by
  intro f u hf hu
  have hmask : Continuous (fun t => (u t : ℂ) * f t) :=
    (Complex.continuous_ofReal.comp hu).mul hf
  have hcomp : Continuous (fun t => ((1 - u t : ℝ) : ℂ) * f t) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub hu)).mul hf
  rw [← intervalIntegral.integral_add (hmask.intervalIntegrable 0 1)
    (hcomp.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring
