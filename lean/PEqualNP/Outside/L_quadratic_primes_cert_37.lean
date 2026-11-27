import Mathlib

namespace PEqualNP.Outside

/-- Complete sieve roots modulo 37. -/
theorem L_quadratic_primes_cert_37 :
    ∀ n : ℕ, 37 ∣ n ^ 2 + 1 ↔ n % 37 = 6 ∨ n % 37 = 31 := by
  intro n
  set r := n % 37 with hr
  have hrp : r < 37 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  have hmod : (n ^ 2 + 1) % 37 = (r ^ 2 + 1) % 37 := by
    have h1 : n ^ 2 % 37 = r ^ 2 % 37 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 37 = (n ^ 2 % 37 + 1 % 37) % 37 := Nat.add_mod (n ^ 2) 1 37
    have h3 : (r ^ 2 + 1) % 37 = (r ^ 2 % 37 + 1 % 37) % 37 := Nat.add_mod (r ^ 2) 1 37
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside