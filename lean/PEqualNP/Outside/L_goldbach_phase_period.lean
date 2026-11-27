import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_phase_period :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    ∀ (t : ℝ) (m : ℤ), E (t + (m : ℝ)) = E t := by
  dsimp only
  intro t m
  let E : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  change E (t + (m : ℝ)) = E t
  have harg : (((2 * Real.pi * (t + (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I +
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  dsimp [E]
  rw [harg, Complex.exp_add]
  have hm : Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I m
  rw [hm, mul_one]

end PEqualNP.Outside
