import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2113 :
    ∀ n : ℕ, 2113 ∣ n ^ 2 + 1 ↔ n % 2113 = 65 ∨ n % 2113 = 2048 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2113 = (n % 2113) ^ 2 % 2113 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2113 = ((n % 2113) ^ 2 + 1) % 2113 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2113 < 2113 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2113 <;> norm_num
