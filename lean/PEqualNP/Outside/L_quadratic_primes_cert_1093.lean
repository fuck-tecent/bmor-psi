import Mathlib

/-!
模 1093 的平方剩余判定：1093 是素数且除以 4 余 1 时，一个数的平方加 1 被 1093 整除，
当且仅当这个数除以 1093 的余数是 530 或 563，其中 563 正好等于 1093 减 530。
先用有限枚举确认 0 到 1093 之间的整数里只有 530 与 563 这两个余数让 1093 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1093 :
    ∀ n:ℕ, 1093∣n^2+1 ↔ n % 1093= 530 ∨ n % 1093= 563 := by
  intro n
  have key : ∀ r < 1093, (1093 ∣ r ^ 2 + 1) ↔ (r = 530 ∨ r = 563) := by
    decide
  have hsq : (n ^ 2) % 1093 = ((n % 1093) ^ 2) % 1093 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1093 = ((n % 1093) ^ 2 + 1) % 1093 := by
    calc (n ^ 2 + 1) % 1093
        = (n ^ 2 % 1093 + 1 % 1093) % 1093 := Nat.add_mod _ _ _
      _ = ((n % 1093) ^ 2 % 1093 + 1 % 1093) % 1093 := by rw [hsq]
      _ = ((n % 1093) ^ 2 + 1) % 1093 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1093) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
