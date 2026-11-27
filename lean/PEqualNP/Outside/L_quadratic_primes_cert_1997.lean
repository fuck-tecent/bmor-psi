import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1997 :
    ∀ n : ℕ, 1997 ∣ n ^ 2 + 1 ↔ n % 1997 = 412 ∨ n % 1997 = 1585 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1997 = (n % 1997) ^ 2 % 1997 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1997 = ((n % 1997) ^ 2 + 1) % 1997 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1997 < 1997 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1997 <;> norm_num
