import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2281 :
    ∀ n : ℕ, 2281 ∣ n ^ 2 + 1 ↔ n % 2281 = 710 ∨ n % 2281 = 1571 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2281 = (n % 2281) ^ 2 % 2281 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2281 = ((n % 2281) ^ 2 + 1) % 2281 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2281 < 2281 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2281 <;> norm_num
