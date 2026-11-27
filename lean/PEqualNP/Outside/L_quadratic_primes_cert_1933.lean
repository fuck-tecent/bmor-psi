import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1933 :
    ∀ n : ℕ, 1933 ∣ n ^ 2 + 1 ↔ n % 1933 = 598 ∨ n % 1933 = 1335 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1933 = (n % 1933) ^ 2 % 1933 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1933 = ((n % 1933) ^ 2 + 1) % 1933 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1933 < 1933 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1933 <;> norm_num
