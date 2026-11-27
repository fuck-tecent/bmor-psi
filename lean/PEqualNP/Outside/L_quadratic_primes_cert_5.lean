import Mathlib

namespace PEqualNP.Outside

/-- 模 5 的两条筛根及其完整性：`5 ∣ n ^ 2 + 1` 当且仅当 `n ≡ 2` 或 `n ≡ 3` (mod 5)。 -/
theorem L_quadratic_primes_cert_5 :
    ∀ n : ℕ, 5 ∣ n ^ 2 + 1 ↔ n % 5 = 2 ∨ n % 5 = 3 := by
  intro n
  set r := n % 5 with hr
  have hr5 : r < 5 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  -- 把模 5 的余数降到 r 上：两边都用 add_mod 展开后再对上 pow_mod
  have hmod : (n ^ 2 + 1) % 5 = (r ^ 2 + 1) % 5 := by
    have h1 : n ^ 2 % 5 = r ^ 2 % 5 := by
      rw [Nat.pow_mod, ← hr]
    have h2 : (n ^ 2 + 1) % 5 = (n ^ 2 % 5 + 1 % 5) % 5 := Nat.add_mod (n ^ 2) 1 5
    have h3 : (r ^ 2 + 1) % 5 = (r ^ 2 % 5 + 1 % 5) % 5 := Nat.add_mod (r ^ 2) 1 5
    rw [h2, h1, h3]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside
