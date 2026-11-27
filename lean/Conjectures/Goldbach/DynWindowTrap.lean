import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.DynWindowTrap :
    ∀ (A B : Set ℤ), (∀ x ∈ A, 0 < x) → (∀ x ∈ B, x < 0) →
      ∀ i j k : ℤ, i+k ∈ A → j+k ∈ B → -i < k ∧ k < -j := by
  intro A B hA hB i j k hik hjk
  exact ⟨by have := hA (i+k) hik; omega, by have := hB (j+k) hjk; omega⟩
