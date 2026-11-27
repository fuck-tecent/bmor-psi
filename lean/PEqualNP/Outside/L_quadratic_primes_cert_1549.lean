import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1549 :
    ∀ n : ℕ, 1549 ∣ n ^ 2 + 1 ↔ n % 1549 = 88 ∨ n % 1549 = 1461 := by
  intro n
  have e : (n ^ 2 + 1) % 1549 = ((n % 1549) ^ 2 + 1) % 1549 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.add_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, e]
  have h : n % 1549 < 1549 := Nat.mod_lt _ (by norm_num)
  generalize hh : n % 1549 = r at h ⊢
  interval_cases r <;> norm_num
