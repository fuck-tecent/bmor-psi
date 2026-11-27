import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_det_swap :
    ∀ x y u v:ℤ, y*u-x*v= -(x*v-y*u) := by
  intro x y u v
  ring
