import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1973 :
    ∀ n:ℕ, 1973∣n^2+1 ↔ n % 1973=259 ∨ n % 1973=1714 := by
  intro n
  let : Fact (Nat.Prime 1973) := ⟨by norm_num⟩
  have hsum : (259 + 1714 : ZMod 1973) = 0 := by decide
  have hprod : (259 * 1714 : ZMod 1973) = 1 := by decide
  have factor (z : ZMod 1973) : (z - 259) * (z - 1714) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (259 + 1714) * z + 259 * 1714 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 1973) = 259) ↔ n % 1973 = 259 :=
    ZMod.natCast_eq_natCast_iff' n 259 1973
  have hb : ((n : ZMod 1973) = 1714) ↔ n % 1973 = 1714 :=
    ZMod.natCast_eq_natCast_iff' n 1714 1973
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
