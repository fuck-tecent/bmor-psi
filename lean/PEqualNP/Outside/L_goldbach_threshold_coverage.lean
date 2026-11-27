import Mathlib

theorem PEqualNP.Outside.L_goldbach_threshold_coverage :
    ∀ N : ℕ, let G := fun n : ℕ => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; (∀ n, 4≤n → n<N → Even n → G n) → (∀ n, 4≤n → N≤n → Even n → G n) → ∀ n, 4≤n → Even n → G n := by
  intro N
  dsimp only
  intro hbelow habove n hn4 hnEven
  by_cases hnN : n < N
  · exact hbelow n hn4 hnN hnEven
  · exact habove n hn4 (Nat.le_of_not_gt hnN) hnEven
