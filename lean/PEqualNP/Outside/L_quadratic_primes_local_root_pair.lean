import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_local_root_pair :
    ∀ (p : ℕ), Nat.Prime p → ∀ (a b : ZMod p), a ^ 2 + 1 = 0 → b ^ 2 + 1 = 0 → a = b ∨ a = -b := by
  intro p hp a b ha hb
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have h : (a - b) * (a + b) = 0 := by
    linear_combination ha - hb
  rcases mul_eq_zero.mp h with hsub | hadd
  · exact Or.inl (sub_eq_zero.mp hsub)
  · right
    linear_combination hadd
