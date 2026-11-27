import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1901 :
    ∀ n : ℕ, 1901 ∣ n ^ 2 + 1 ↔ n % 1901 = 218 ∨ n % 1901 = 1683 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1901 = (n % 1901) ^ 2 % 1901 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1901 = ((n % 1901) ^ 2 + 1) % 1901 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1901 < 1901 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1901 <;> norm_num
