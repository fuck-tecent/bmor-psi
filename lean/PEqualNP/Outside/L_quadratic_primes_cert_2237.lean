import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2237 :
    ∀ n : ℕ, 2237 ∣ n ^ 2 + 1 ↔ n % 2237 = 1021 ∨ n % 2237 = 1216 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2237 = (n % 2237) ^ 2 % 2237 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2237 = ((n % 2237) ^ 2 + 1) % 2237 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2237 < 2237 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2237 <;> norm_num
