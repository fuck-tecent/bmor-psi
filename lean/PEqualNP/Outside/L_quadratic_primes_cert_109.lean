import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_109 :
    ∀ n : ℕ, 109 ∣ n ^ 2 + 1 ↔ n % 109 = 33 ∨ n % 109 = 76 := by
  intro n
  have e : (n ^ 2 + 1) % 109 = ((n % 109) ^ 2 + 1) % 109 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.add_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, e]
  have h : n % 109 < 109 := Nat.mod_lt _ (by norm_num)
  generalize hh : n % 109 = r at h ⊢
  interval_cases r <;> norm_num
