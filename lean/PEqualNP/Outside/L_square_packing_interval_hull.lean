import Mathlib

theorem PEqualNP.Outside.L_square_packing_interval_hull :
    ∀ c r L:ℝ,0≤r → (0≤c-r ∧ c+r≤L ↔ r≤c ∧ c≤L-r) := by
  intro c r L hr
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
