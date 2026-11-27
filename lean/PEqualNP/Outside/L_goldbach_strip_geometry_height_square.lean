import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_height_square :
    ∀ s : ℂ, s.re=1/2 → Complex.normSq s = 1/4+s.im^2 := by
  intro s h
  rw [Complex.normSq_apply, h]
  ring
