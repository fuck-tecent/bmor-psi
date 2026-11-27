import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1789 :
    ∀ n : ℕ, 1789 ∣ n ^ 2 + 1 ↔ n % 1789 = 724 ∨ n % 1789 = 1065 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1789 = (n % 1789) ^ 2 % 1789 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1789 = ((n % 1789) ^ 2 + 1) % 1789 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1789 < 1789 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1789 <;> norm_num
