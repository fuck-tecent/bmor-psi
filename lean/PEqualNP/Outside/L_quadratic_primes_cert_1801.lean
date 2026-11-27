import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1801 :
    ∀ n : ℕ, 1801 ∣ n ^ 2 + 1 ↔ n % 1801 = 824 ∨ n % 1801 = 977 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1801 = (n % 1801) ^ 2 % 1801 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1801 = ((n % 1801) ^ 2 + 1) % 1801 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1801 < 1801 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1801 <;> norm_num
