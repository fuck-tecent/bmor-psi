import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2269 :
    ∀ n : ℕ, 2269 ∣ n ^ 2 + 1 ↔ n % 2269 = 982 ∨ n % 2269 = 1287 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2269 = (n % 2269) ^ 2 % 2269 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2269 = ((n % 2269) ^ 2 + 1) % 2269 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2269 < 2269 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2269 <;> norm_num
