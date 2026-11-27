import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_269 :
    ∀ n : ℕ, 269 ∣ n ^ 2 + 1 ↔ n % 269 = 82 ∨ n % 269 = 187 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 269 = (n % 269) ^ 2 % 269 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 269 = ((n % 269) ^ 2 + 1) % 269 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 269 < 269 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 269 <;> norm_num
