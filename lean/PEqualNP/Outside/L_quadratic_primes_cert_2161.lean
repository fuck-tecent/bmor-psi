import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2161 :
    ∀ n : ℕ, 2161 ∣ n ^ 2 + 1 ↔ n % 2161 = 147 ∨ n % 2161 = 2014 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2161 = (n % 2161) ^ 2 % 2161 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2161 = ((n % 2161) ^ 2 + 1) % 2161 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2161 < 2161 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2161 <;> norm_num
