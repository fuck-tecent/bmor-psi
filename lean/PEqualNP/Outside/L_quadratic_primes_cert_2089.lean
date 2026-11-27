import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2089 :
    ∀ n : ℕ, 2089 ∣ n ^ 2 + 1 ↔ n % 2089 = 789 ∨ n % 2089 = 1300 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2089 = (n % 2089) ^ 2 % 2089 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2089 = ((n % 2089) ^ 2 + 1) % 2089 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2089 < 2089 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2089 <;> norm_num
