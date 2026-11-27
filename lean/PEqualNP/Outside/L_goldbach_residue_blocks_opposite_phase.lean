import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_opposite_phase :
    ∀ (q a n : ℕ), 0<q → a<q → ((n+q-a) % q+a) % q=n % q := by
  intro q a n hq ha
  have hle : a ≤ n + q := le_trans (le_of_lt ha) (Nat.le_add_left q n)
  have h1 : (n + q - a) + a = n + q := Nat.sub_add_cancel hle
  rw [Nat.mod_add_mod (n + q - a) q a, h1, Nat.add_mod_right]
