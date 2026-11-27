import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2017 :
    ∀ n : ℕ, 2017 ∣ n ^ 2 + 1 ↔ n % 2017 = 229 ∨ n % 2017 = 1788 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2017 = (n % 2017) ^ 2 % 2017 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2017 = ((n % 2017) ^ 2 + 1) % 2017 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2017 < 2017 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2017 <;> norm_num
