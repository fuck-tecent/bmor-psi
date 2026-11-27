import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_det_shear :
    ∀ x y u v t:ℤ, x*(v+t*u)-(y+t*x)*u=x*v-y*u := by
  intro x y u v t
  ring
