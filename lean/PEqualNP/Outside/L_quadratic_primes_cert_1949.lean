import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1949 :
    ∀ n : ℕ, 1949 ∣ n ^ 2 + 1 ↔ n % 1949 = 589 ∨ n % 1949 = 1360 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1949 = (n % 1949) ^ 2 % 1949 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1949 = ((n % 1949) ^ 2 + 1) % 1949 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1949 < 1949 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1949 <;> norm_num
