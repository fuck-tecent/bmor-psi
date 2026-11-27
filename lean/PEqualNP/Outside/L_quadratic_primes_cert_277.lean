import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_277 :
    ∀ n : ℕ, 277 ∣ n ^ 2 + 1 ↔ n % 277 = 60 ∨ n % 277 = 217 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 277 = (n % 277) ^ 2 % 277 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 277 = ((n % 277) ^ 2 + 1) % 277 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 277 < 277 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 277 <;> norm_num
