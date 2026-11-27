import Mathlib

theorem PEqualNP.Outside.L_square_packing_area_bound :
    ∀ (n : ℕ) (s : ℝ), 0 ≤ s → (n : ℝ) ≤ s ^ 2 → Real.sqrt (n : ℝ) ≤ s := by
  intro n s hs hns
  exact Real.sqrt_le_iff.mpr ⟨hs, hns⟩
