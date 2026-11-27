import Mathlib

namespace PEqualNP.Outside

/-- Complete sieve roots modulo 29. -/
theorem L_quadratic_primes_cert_29 :
    ∀ n : ℕ, 29 ∣ n ^ 2 + 1 ↔ n % 29 = 12 ∨ n % 29 = 17 := by
  intro n
  set r := n % 29 with hr
  have hrp : r < 29 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  have hmod : (n ^ 2 + 1) % 29 = (r ^ 2 + 1) % 29 := by
    have h1 : n ^ 2 % 29 = r ^ 2 % 29 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 29 = (n ^ 2 % 29 + 1 % 29) % 29 := Nat.add_mod (n ^ 2) 1 29
    have h3 : (r ^ 2 + 1) % 29 = (r ^ 2 % 29 + 1 % 29) % 29 := Nat.add_mod (r ^ 2) 1 29
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside