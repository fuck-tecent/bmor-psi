import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_quadratic_primes_cert_1009 :
    ∀ n : ℕ, 1009 ∣ n ^ 2 + 1 ↔ n % 1009 = 469 ∨ n % 1009 = 540 := by
  intro n
  have prime : Nat.Prime 1009 := by
    refine Nat.prime_def_le_sqrt.mpr ⟨by decide, ?_⟩
    intro d hd hbound
    have small : Nat.sqrt 1009 < 32 := Nat.sqrt_lt.mpr (by decide)
    have upper : d ≤ 31 := by omega
    interval_cases d <;> decide
  have factor : (n + 540) * (n + 469) = (n ^ 2 + 1) + 1009 * (n + 251) := by
    ring
  have same : 1009 ∣ n ^ 2 + 1 ↔ 1009 ∣ (n + 540) * (n + 469) := by
    rw [factor]
    omega
  rw [same, prime.dvd_mul]
  omega
