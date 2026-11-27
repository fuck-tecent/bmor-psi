import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1777 :
    ∀ n : ℕ, 1777 ∣ n ^ 2 + 1 ↔ n % 1777 = 775 ∨ n % 1777 = 1002 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1777 = (n % 1777) ^ 2 % 1777 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1777 = ((n % 1777) ^ 2 + 1) % 1777 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1777 < 1777 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1777 <;> norm_num
