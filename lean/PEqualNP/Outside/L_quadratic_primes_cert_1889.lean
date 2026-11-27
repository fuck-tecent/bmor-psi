import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1889 :
    ∀ n : ℕ, 1889 ∣ n ^ 2 + 1 ↔ n % 1889 = 331 ∨ n % 1889 = 1558 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1889 = (n % 1889) ^ 2 % 1889 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1889 = ((n % 1889) ^ 2 + 1) % 1889 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1889 < 1889 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1889 <;> norm_num
