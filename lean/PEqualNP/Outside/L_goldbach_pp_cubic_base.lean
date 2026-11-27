import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_cubic_base :
    ∀ p a n : ℕ, 1≤p → 3≤a → p^a≤n → p^3≤n := by
  intro p a n hp ha h
  exact le_trans (Nat.pow_le_pow_right hp ha) h
