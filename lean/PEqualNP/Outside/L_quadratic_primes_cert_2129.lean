import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_2129 :
    ∀ n : ℕ, 2129 ∣ n ^ 2 + 1 ↔ n % 2129 = 372 ∨ n % 2129 = 1757 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 2129 = (n % 2129) ^ 2 % 2129 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 2129 = ((n % 2129) ^ 2 + 1) % 2129 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 2129 < 2129 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 2129 <;> norm_num
