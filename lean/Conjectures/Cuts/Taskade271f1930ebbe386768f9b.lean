import Mathlib

/-- Termwise mass bound: inside the window, a twin prime pair n, n+2 contributes
`log n * log (n+2)`, which is exactly `Λ n * Λ (n+2)`; every other term is zero on the left
and nonnegative on the right. -/
theorem Conjectures.Cuts.Taskade271f1930ebbe386768f9b :
    ∀ (x1 : ℕ), (∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ)) then Real.log ↑x2 * Real.log ↑(x2 + (2 : ℕ)) else (0 : ℝ)) ≤ ∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) with x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x2 + (2 : ℕ)) := by
  intro x1
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum ?_
  intro x2 _
  by_cases h : x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ))
  · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩,
      ArithmeticFunction.vonMangoldt_apply_prime h.2.2.1,
      ArithmeticFunction.vonMangoldt_apply_prime h.2.2.2]
  · rw [if_neg h]
    by_cases h2 : x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1
    · rw [if_pos h2]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg
    · rw [if_neg h2]
