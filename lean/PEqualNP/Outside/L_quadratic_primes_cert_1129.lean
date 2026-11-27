import Mathlib

/-!
模 1129 的平方剩余判定：1129 是素数且除以 4 余 1 时，一个数的平方加 1 被 1129 整除，
当且仅当这个数除以 1129 的余数是 168 或 961，其中 961 正好等于 1129 减 168。
先用有限枚举确认 0 到 1129 之间的整数里只有 168 与 961 这两个余数让 1129 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1129 :
    ∀ n:ℕ, 1129∣n^2+1 ↔ n % 1129= 168 ∨ n % 1129= 961 := by
  intro n
  have key : ∀ r < 1129, (1129 ∣ r ^ 2 + 1) ↔ (r = 168 ∨ r = 961) := by
    decide
  have hsq : (n ^ 2) % 1129 = ((n % 1129) ^ 2) % 1129 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1129 = ((n % 1129) ^ 2 + 1) % 1129 := by
    calc (n ^ 2 + 1) % 1129
        = (n ^ 2 % 1129 + 1 % 1129) % 1129 := Nat.add_mod _ _ _
      _ = ((n % 1129) ^ 2 % 1129 + 1 % 1129) % 1129 := by rw [hsq]
      _ = ((n % 1129) ^ 2 + 1) % 1129 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1129) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
