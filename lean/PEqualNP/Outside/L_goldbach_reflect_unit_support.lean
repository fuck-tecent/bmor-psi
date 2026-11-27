import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflect_unit_support :
    ∀ n k : ℕ, k ≤ n → (Nat.Coprime k n ↔ Nat.Coprime (n-k) n) := by
  intro n k hk
  exact (Nat.coprime_self_sub_left hk).symm
