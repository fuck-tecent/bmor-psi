import Mathlib

namespace PEqualNP.Outside

/-- 模 13 的两条筛根及其完整性：`13 ∣ n ^ 2 + 1` 当且仅当 `n ≡ 5` 或 `n ≡ 8` (mod 13)。 -/
theorem L_quadratic_primes_cert_13 :
    ∀ n : ℕ, 13 ∣ n ^ 2 + 1 ↔ n % 13 = 5 ∨ n % 13 = 8 := by
  intro n
  set r := n % 13 with hr
  have hrp : r < 13 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  have hmod : (n ^ 2 + 1) % 13 = (r ^ 2 + 1) % 13 := by
    have h1 : n ^ 2 % 13 = r ^ 2 % 13 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 13 = (n ^ 2 % 13 + 1 % 13) % 13 := Nat.add_mod (n ^ 2) 1 13
    have h3 : (r ^ 2 + 1) % 13 = (r ^ 2 % 13 + 1 % 13) % 13 := Nat.add_mod (r ^ 2) 1 13
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside
