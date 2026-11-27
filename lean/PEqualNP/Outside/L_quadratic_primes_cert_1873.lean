import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1873 :
    ∀ n : ℕ, 1873 ∣ n ^ 2 + 1 ↔ n % 1873 = 737 ∨ n % 1873 = 1136 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1873 = (n % 1873) ^ 2 % 1873 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1873 = ((n % 1873) ^ 2 + 1) % 1873 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1873 < 1873 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1873 <;> norm_num
