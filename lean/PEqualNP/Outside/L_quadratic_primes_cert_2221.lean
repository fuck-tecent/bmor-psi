import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2221 :
    ∀ n : ℕ, 2221 ∣ n ^ 2 + 1 ↔ n % 2221 = 790 ∨ n % 2221 = 1431 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2221 = (n % 2221) ^ 2 % 2221 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2221 = ((n % 2221) ^ 2 + 1) % 2221 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2221 < 2221 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2221 <;> norm_num
