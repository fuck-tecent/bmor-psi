import Mathlib

theorem Conjectures.Goldbach.BeaumontQuotientObstruction :
    ∀ m : ℕ, 1 < m → ∃ a b : ℕ, a ≠ b ∧ a % m = b % m ∧ Nat.Prime a ∧ ¬ Nat.Prime b := by
  intro m hm
  refine ⟨2, 2 * (m + 1), ?_, ?_, Nat.prime_two, ?_⟩
  · intro h
    omega
  · have h : 2 * (m + 1) = 2 + m * 2 := by ring
    rw [h, Nat.add_mul_mod_self_left]
  · exact Nat.not_prime_of_mul_eq (a := 2) (b := m + 1) rfl (by norm_num) (by omega)
