import Mathlib

/-!
模 1277 的平方剩余判定：1277 是素数且除以 4 余 1 时，一个数的平方加 1 被 1277 整除，
当且仅当这个数除以 1277 的余数是 113 或 1164，其中 1164 正好等于 1277 减 113。
先用有限枚举确认 0 到 1277 之间的整数里只有 113 与 1164 这两个余数让 1277 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1277 :
    ∀ n:ℕ, 1277∣n^2+1 ↔ n % 1277= 113 ∨ n % 1277= 1164 := by
  intro n
  have key : ∀ r < 1277, (1277 ∣ r ^ 2 + 1) ↔ (r = 113 ∨ r = 1164) := by
    decide
  have hsq : (n ^ 2) % 1277 = ((n % 1277) ^ 2) % 1277 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1277 = ((n % 1277) ^ 2 + 1) % 1277 := by
    calc (n ^ 2 + 1) % 1277
        = (n ^ 2 % 1277 + 1 % 1277) % 1277 := Nat.add_mod _ _ _
      _ = ((n % 1277) ^ 2 % 1277 + 1 % 1277) % 1277 := by rw [hsq]
      _ = ((n % 1277) ^ 2 + 1) % 1277 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1277) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
