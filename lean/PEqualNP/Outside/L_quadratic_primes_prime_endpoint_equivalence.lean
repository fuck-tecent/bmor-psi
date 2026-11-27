import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_quadratic_primes_prime_endpoint_equivalence :
    (∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ n ^ 2 < p ^ 1) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < n ∧ Nat.Prime (n ^ 2 + 1)) := by
  constructor
  · intro H B
    obtain ⟨n, p, hBn, hp, hdvd, hlt⟩ := H B
    refine ⟨n, hBn, ?_⟩
    have hlt' : n ^ 2 < p := by simpa using hlt
    have hle : p ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdvd
    have hp_eq : p = n ^ 2 + 1 := by omega
    simpa [hp_eq] using hp
  · intro H B
    obtain ⟨n, hBn, hp⟩ := H B
    exact ⟨n, n ^ 2 + 1, hBn, hp, dvd_rfl, by simpa using Nat.lt_succ_self (n ^ 2)⟩
