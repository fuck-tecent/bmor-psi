import Mathlib

theorem Conjectures.Goldbach.BeaumontResonanceWindow :
    ∀ n p q : ℕ, 0 < n → n ≤ p+q → p+q < 2*n →
      (n ∣ p+q ↔ p+q=n) := by
  intro n p q hn hlower hupper
  constructor
  · intro hdiv
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) hdiv hupper
  · intro heq
    rw [heq]
