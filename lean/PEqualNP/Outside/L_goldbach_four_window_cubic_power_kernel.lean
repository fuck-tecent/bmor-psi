import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_cubic_power_kernel :
    ∀ (z : ℂ), (1:ℂ)-3*z+3*z^2-z^3=(1-z)^3 ∧ ‖1-3*z+3*z^2-z^3‖=‖1-z‖^3 := by
  intro z
  have h : (1:ℂ) - 3*z + 3*z^2 - z^3 = (1-z)^3 := by ring
  constructor
  · exact h
  · rw [h, norm_pow]
