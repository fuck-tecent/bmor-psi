import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_mirror_re :
    ∀ s : ℂ, 1/2 < s.re → s.re < 1 → 0 < (1-s).re ∧ (1-s).re < 1/2 := by
  intro s h1 h2
  have h : (1 - s).re = 1 - s.re := by simp
  constructor <;> rw [h] <;> linarith