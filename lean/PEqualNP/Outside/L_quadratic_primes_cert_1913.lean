import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1913 :
    ∀ n : ℕ, 1913 ∣ n ^ 2 + 1 ↔ n % 1913 = 712 ∨ n % 1913 = 1201 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1913 = (n % 1913) ^ 2 % 1913 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1913 = ((n % 1913) ^ 2 + 1) % 1913 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1913 < 1913 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1913 <;> norm_num
