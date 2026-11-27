import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2053 :
    ∀ n : ℕ, 2053 ∣ n ^ 2 + 1 ↔ n % 2053 = 244 ∨ n % 2053 = 1809 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2053 = (n % 2053) ^ 2 % 2053 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2053 = ((n % 2053) ^ 2 + 1) % 2053 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2053 < 2053 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2053 <;> norm_num
