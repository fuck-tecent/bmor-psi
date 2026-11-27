import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_base_cutoff :
    ∀ p a n : ℕ, 2≤p → 2≤a → p^a≤n → p≤Nat.sqrt n := by
  intro p a n hp ha hn
  have hsquare : p ^ 2 ≤ p ^ a :=
    Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_two hp) ha
  exact Nat.le_sqrt'.2 (hsquare.trans hn)
