import Mathlib

/-- Real and imaginary parts of the square give the cosine and sine coefficients. -/
theorem PEqualNP.Outside.L_goldbach_signed_harmonic :
    ∀ (z : ℂ) (t : ℝ), (z^2 * Complex.exp ((-(t : ℂ)) * Complex.I)).re =
      (z.re^2 - z.im^2) * Real.cos t + 2 * z.re * z.im * Real.sin t := by
  intro z t
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  left
  ring
