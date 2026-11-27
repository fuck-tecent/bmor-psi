import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring

namespace Conjectures.Goldbach

theorem DynModularMirage :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ A : Set ℕ, (∀ a ∈ A, Odd a) ∧ (∀ m : ℕ, 0 < m → ∃ a ∈ A, ∃ b ∈ A, (a+b) % m=N % m) ∧ ¬ (∃ a ∈ A, ∃ b ∈ A, a+b=N) := by
  intro N hN _
  refine ⟨{a : ℕ | Odd a ∧ N < a}, fun a ha => ha.1, ?_, ?_⟩
  · intro m hm
    let t := m * (N + 1)
    have ht : N + 1 ≤ t := by dsimp [t]; simpa using Nat.mul_le_mul_right (N+1) hm
    refine ⟨N+1, ⟨?_, by omega⟩, 2*t-1, ⟨?_, by omega⟩, ?_⟩
    · obtain ⟨j, hj⟩ := hN
      exact ⟨j, by omega⟩
    · exact ⟨t-1, by omega⟩
    · rw [show N + 1 + (2*t-1) = N + (2*(N+1))*m from by
        calc
          _ = N + 2*t := by omega
          _ = _ := by dsimp [t]; ring]
      simp
  · rintro ⟨a, ha, b, _, hab⟩
    exact (Nat.not_lt_of_ge (show a ≤ N by omega)) ha.2

end Conjectures.Goldbach
