import Mathlib

namespace PEqualNP.Outside

/-- Complete sieve roots modulo 41. -/
theorem L_quadratic_primes_cert_41 :
    ∀ n : ℕ, 41 ∣ n ^ 2 + 1 ↔ n % 41 = 9 ∨ n % 41 = 32 := by
  intro n
  set r := n % 41 with hr
  have hrp : r < 41 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  have hmod : (n ^ 2 + 1) % 41 = (r ^ 2 + 1) % 41 := by
    have h1 : n ^ 2 % 41 = r ^ 2 % 41 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 41 = (n ^ 2 % 41 + 1 % 41) % 41 := Nat.add_mod (n ^ 2) 1 41
    have h3 : (r ^ 2 + 1) % 41 = (r ^ 2 % 41 + 1 % 41) % 41 := Nat.add_mod (r ^ 2) 1 41
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside