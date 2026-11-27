import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2137 :
    ∀ n : ℕ, 2137 ∣ n ^ 2 + 1 ↔ n % 2137 = 296 ∨ n % 2137 = 1841 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2137 = (n % 2137) ^ 2 % 2137 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2137 = ((n % 2137) ^ 2 + 1) % 2137 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2137 < 2137 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2137 <;> norm_num
