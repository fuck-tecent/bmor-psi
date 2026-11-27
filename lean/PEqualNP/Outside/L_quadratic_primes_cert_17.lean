import Mathlib

namespace PEqualNP.Outside

/-- 模 17 的两条筛根及其完整性：`17 ∣ n ^ 2 + 1` 当且仅当 `n ≡ 4` 或 `n ≡ 13` (mod 17)。 -/
theorem L_quadratic_primes_cert_17 :
    ∀ n : ℕ, 17 ∣ n ^ 2 + 1 ↔ n % 17 = 4 ∨ n % 17 = 13 := by
  intro n
  set r := n % 17 with hr
  have hrp : r < 17 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  have hmod : (n ^ 2 + 1) % 17 = (r ^ 2 + 1) % 17 := by
    have h1 : n ^ 2 % 17 = r ^ 2 % 17 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 17 = (n ^ 2 % 17 + 1 % 17) % 17 := Nat.add_mod (n ^ 2) 1 17
    have h3 : (r ^ 2 + 1) % 17 = (r ^ 2 % 17 + 1 % 17) % 17 := Nat.add_mod (r ^ 2) 1 17
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside
