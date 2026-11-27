import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_balancing_potential :
    ∀ a b:ℕ,b<a → a^2+(b+1)^2<(a+1)^2+b^2 := by
  intro a b h
  nlinarith
