import Mathlib

theorem Conjectures.JoshiAbc.AdjacentUnit :
    ∀ (K : Type) [NormedField K] (r : K) (ξ : ℕ → K) (j : ℕ), 0 < j → r ≠ 0 →
      ‖ξ j‖ = ‖r‖ ^ j → ‖ξ (j - 1)‖ = ‖r‖ ^ (j - 1) → ‖ξ j / ξ (j - 1)‖ = ‖r‖ := by
  intro K _ r ξ j hj hr h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2 ⊢
  rw [norm_div, h1, h2, pow_succ]
  exact (div_eq_iff (pow_ne_zero k (norm_ne_zero_iff.mpr hr))).2 (by ring)
