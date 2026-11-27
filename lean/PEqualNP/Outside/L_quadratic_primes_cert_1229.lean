import Mathlib

/-!
模 1229 的平方剩余判定：1229 是素数且除以 4 余 1 时，一个数的平方加 1 被 1229 整除，
当且仅当这个数除以 1229 的余数是 597 或 632，其中 632 正好等于 1229 减 597。
先用有限枚举确认 0 到 1229 之间的整数里只有 597 与 632 这两个余数让 1229 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1229 :
    ∀ n:ℕ, 1229∣n^2+1 ↔ n % 1229= 597 ∨ n % 1229= 632 := by
  intro n
  have key : ∀ r < 1229, (1229 ∣ r ^ 2 + 1) ↔ (r = 597 ∨ r = 632) := by
    decide
  have hsq : (n ^ 2) % 1229 = ((n % 1229) ^ 2) % 1229 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1229 = ((n % 1229) ^ 2 + 1) % 1229 := by
    calc (n ^ 2 + 1) % 1229
        = (n ^ 2 % 1229 + 1 % 1229) % 1229 := Nat.add_mod _ _ _
      _ = ((n % 1229) ^ 2 % 1229 + 1 % 1229) % 1229 := by rw [hsq]
      _ = ((n % 1229) ^ 2 + 1) % 1229 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1229) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
