import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_53 :
    ∀ n : ℕ, 53 ∣ n ^ 2 + 1 ↔ n % 53 = 23 ∨ n % 53 = 30 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 53 = (n % 53) ^ 2 % 53 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 53 = ((n % 53) ^ 2 + 1) % 53 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 53 < 53 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 53 <;> norm_num
