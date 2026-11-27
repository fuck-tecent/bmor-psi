import Mathlib

theorem PEqualNP.Outside.L_square_packing_width_energy :
    ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → (|c| + |s|) ^ 2 ≤ 2 := by
  intro c s h
  nlinarith only [h, sq_abs c, sq_abs s, sq_nonneg (|c| - |s|)]
