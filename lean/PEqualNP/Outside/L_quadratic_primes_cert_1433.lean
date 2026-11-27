import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1433 :
    ∀ n : ℕ, 1433 ∣ n ^ 2 + 1 ↔ n % 1433 = 542 ∨ n % 1433 = 891 := by
  intro n
  have e : (n ^ 2 + 1) % 1433 = ((n % 1433) ^ 2 + 1) % 1433 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.add_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, e]
  have h : n % 1433 < 1433 := Nat.mod_lt _ (by norm_num)
  generalize hh : n % 1433 = r at h ⊢
  interval_cases r <;> norm_num
