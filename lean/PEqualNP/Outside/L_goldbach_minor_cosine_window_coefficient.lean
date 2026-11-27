import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside

/-- The real Fourier coefficient of the interval with center `a` and half-width `H`. -/
theorem L_goldbach_minor_cosine_window_coefficient :
    ∀ a H u : ℝ, 0 ≤ H → u ≠ 0 → intervalIntegral (fun x => Real.cos (u*x)) (a-H) (a+H) MeasureTheory.volume = 2*Real.cos (u*a)*Real.sin (u*H)/u := by
  intro a H u _ hu
  rw [eq_div_iff hu, mul_comm _ u, intervalIntegral.mul_integral_comp_mul_left, integral_cos,
    mul_add u a H, mul_sub u a H, Real.sin_add, Real.sin_sub]
  ring

end PEqualNP.Outside
