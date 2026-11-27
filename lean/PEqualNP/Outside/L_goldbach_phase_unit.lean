import Mathlib

theorem PEqualNP.Outside.L_goldbach_phase_unit :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ t, ‖E t‖=1 := by
  dsimp only
  intro t
  rw [Complex.norm_exp]
  simp [Complex.mul_re]
