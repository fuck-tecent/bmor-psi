import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1861 :
    ∀ n : ℕ, 1861 ∣ n ^ 2 + 1 ↔ n % 1861 = 61 ∨ n % 1861 = 1800 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1861 = (n % 1861) ^ 2 % 1861 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1861 = ((n % 1861) ^ 2 + 1) % 1861 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1861 < 1861 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1861 <;> norm_num
