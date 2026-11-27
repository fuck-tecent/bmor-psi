import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2069 :
    ∀ n : ℕ, 2069 ∣ n ^ 2 + 1 ↔ n % 2069 = 164 ∨ n % 2069 = 1905 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2069 = (n % 2069) ^ 2 % 2069 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2069 = ((n % 2069) ^ 2 + 1) % 2069 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2069 < 2069 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2069 <;> norm_num
