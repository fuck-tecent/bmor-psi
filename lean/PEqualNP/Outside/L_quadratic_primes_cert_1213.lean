import Mathlib

/-!
模 1213 的平方剩余判定：1213 是素数且除以 4 余 1 时，一个数的平方加 1 被 1213 整除，
当且仅当这个数除以 1213 的余数是 495 或 718，其中 718 正好等于 1213 减 495。
先用有限枚举确认 0 到 1213 之间的整数里只有 495 与 718 这两个余数让 1213 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1213 :
    ∀ n:ℕ, 1213∣n^2+1 ↔ n % 1213= 495 ∨ n % 1213= 718 := by
  intro n
  have key : ∀ r < 1213, (1213 ∣ r ^ 2 + 1) ↔ (r = 495 ∨ r = 718) := by
    decide
  have hsq : (n ^ 2) % 1213 = ((n % 1213) ^ 2) % 1213 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1213 = ((n % 1213) ^ 2 + 1) % 1213 := by
    calc (n ^ 2 + 1) % 1213
        = (n ^ 2 % 1213 + 1 % 1213) % 1213 := Nat.add_mod _ _ _
      _ = ((n % 1213) ^ 2 % 1213 + 1 % 1213) % 1213 := by rw [hsq]
      _ = ((n % 1213) ^ 2 + 1) % 1213 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1213) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
