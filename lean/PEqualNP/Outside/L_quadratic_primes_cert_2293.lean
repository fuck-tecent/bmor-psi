import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2293 :
    ∀ n : ℕ, 2293 ∣ n ^ 2 + 1 ↔ n % 2293 = 600 ∨ n % 2293 = 1693 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2293 = (n % 2293) ^ 2 % 2293 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2293 = ((n % 2293) ^ 2 + 1) % 2293 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2293 < 2293 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2293 <;> norm_num
