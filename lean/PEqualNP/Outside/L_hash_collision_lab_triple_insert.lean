import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_triple_insert :
    ∀ m:ℕ, Nat.choose (m+1) 3=Nat.choose m 3+Nat.choose m 2 := by
  intro m
  rw [Nat.choose_succ_succ']
  ring

