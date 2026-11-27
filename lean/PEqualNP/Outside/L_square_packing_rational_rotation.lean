import Mathlib

theorem PEqualNP.Outside.L_square_packing_rational_rotation :
    ∀ t:ℝ, ((1-t^2)/(1+t^2))^2+(2*t/(1+t^2))^2=1 := by
  intro t
  have h : (1 + t^2) ≠ 0 := by positivity
  field_simp
  ring
