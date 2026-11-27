import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2273 :
    ∀ n : ℕ, 2273 ∣ n ^ 2 + 1 ↔ n % 2273 = 290 ∨ n % 2273 = 1983 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2273 = (n % 2273) ^ 2 % 2273 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2273 = ((n % 2273) ^ 2 + 1) % 2273 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2273 < 2273 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2273 <;> norm_num
