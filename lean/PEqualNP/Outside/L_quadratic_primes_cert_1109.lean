import Mathlib

/-!
模 1109 的平方剩余判定：1109 是素数且除以 4 余 1 时，一个数的平方加 1 被 1109 整除，
当且仅当这个数除以 1109 的余数是 354 或 755，其中 755 正好等于 1109 减 354。
先用有限枚举确认 0 到 1109 之间的整数里只有 354 与 755 这两个余数让 1109 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1109 :
    ∀ n:ℕ, 1109∣n^2+1 ↔ n % 1109= 354 ∨ n % 1109= 755 := by
  intro n
  have key : ∀ r < 1109, (1109 ∣ r ^ 2 + 1) ↔ (r = 354 ∨ r = 755) := by
    decide
  have hsq : (n ^ 2) % 1109 = ((n % 1109) ^ 2) % 1109 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1109 = ((n % 1109) ^ 2 + 1) % 1109 := by
    calc (n ^ 2 + 1) % 1109
        = (n ^ 2 % 1109 + 1 % 1109) % 1109 := Nat.add_mod _ _ _
      _ = ((n % 1109) ^ 2 % 1109 + 1 % 1109) % 1109 := by rw [hsq]
      _ = ((n % 1109) ^ 2 + 1) % 1109 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1109) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
