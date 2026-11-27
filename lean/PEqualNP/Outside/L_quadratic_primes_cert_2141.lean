import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2141 :
    ∀ n : ℕ, 2141 ∣ n ^ 2 + 1 ↔ n % 2141 = 419 ∨ n % 2141 = 1722 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2141 = (n % 2141) ^ 2 % 2141 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2141 = ((n % 2141) ^ 2 + 1) % 2141 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2141 < 2141 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2141 <;> norm_num
