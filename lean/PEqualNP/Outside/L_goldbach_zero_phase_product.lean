import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring.Basic

theorem PEqualNP.Outside.L_goldbach_zero_phase_product :
    ∀ (a b x : ℝ), Complex.exp (((a*x : ℝ) : ℂ)*Complex.I) * Complex.exp (-(((b*x : ℝ) : ℂ)*Complex.I)) = Complex.exp (((((a-b)*x) : ℝ) : ℂ)*Complex.I) := by
  intro a b x
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_sub]
  ring
