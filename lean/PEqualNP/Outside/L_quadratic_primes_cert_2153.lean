import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2153 :
    ∀ n : ℕ, 2153 ∣ n ^ 2 + 1 ↔ n % 2153 = 232 ∨ n % 2153 = 1921 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2153 = (n % 2153) ^ 2 % 2153 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2153 = ((n % 2153) ^ 2 + 1) % 2153 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2153 < 2153 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2153 <;> norm_num
