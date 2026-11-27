import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_anti_range :
    ∀ n a b : ℕ, 0 < a → a < n → 0 < b → b < n →
      (n ∣ a + b ↔ a + b = n) := by
  intro n a b ha han hb hbn
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    have hpos : 0 < k := by
      by_contra hk0
      have : k = 0 := by omega
      subst k
      simp at hk
      omega
    have hlt : k < 2 := by
      apply Nat.lt_of_mul_lt_mul_left (a := n)
      calc
        n * k = a + b := hk.symm
        _ < 2 * n := by omega
        _ = n * 2 := by ring
    have hk1 : k = 1 := by omega
    subst k
    simpa using hk
  · intro h
    exact ⟨1, by simpa using h⟩
