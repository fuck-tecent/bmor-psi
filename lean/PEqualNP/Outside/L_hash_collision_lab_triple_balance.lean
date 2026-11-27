import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_triple_balance :
    ∀ a b:ℕ, b≤a → Nat.choose a 3+Nat.choose (b+1) 3≤Nat.choose (a+1) 3+Nat.choose b 3 := by
  intro a b hba
  have h1 : Nat.choose (a+1) 3 = Nat.choose a 3 + Nat.choose a 2 := by
    rw [Nat.choose_succ_succ']
    ring
  have h2 : Nat.choose (b+1) 3 = Nat.choose b 3 + Nat.choose b 2 := by
    rw [Nat.choose_succ_succ']
    ring
  have h3 : Nat.choose b 2 ≤ Nat.choose a 2 := Nat.choose_le_choose 2 hba
  omega

