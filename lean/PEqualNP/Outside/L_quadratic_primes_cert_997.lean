import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_997 :
    ∀ n : ℕ, 997 ∣ n ^ 2 + 1 ↔ n % 997 = 161 ∨ n % 997 = 836 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 997 = (n % 997) ^ 2 % 997 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 997 = ((n % 997) ^ 2 + 1) % 997 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 997 < 997 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 997 <;> norm_num
