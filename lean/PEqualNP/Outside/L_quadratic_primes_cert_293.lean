import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_293 :
    ∀ n:ℕ, 293∣n^2+1 ↔ n % 293=138 ∨ n % 293=155 := by
  intro n
  let : Fact (Nat.Prime 293) := ⟨by norm_num⟩
  have hsum : (138 + 155 : ZMod 293) = 0 := by decide
  have hprod : (138 * 155 : ZMod 293) = 1 := by decide
  have factor (z : ZMod 293) : (z - 138) * (z - 155) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (138 + 155) * z + 138 * 155 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 293) = 138) ↔ n % 293 = 138 :=
    ZMod.natCast_eq_natCast_iff' n 138 293
  have hb : ((n : ZMod 293) = 155) ↔ n % 293 = 155 :=
    ZMod.natCast_eq_natCast_iff' n 155 293
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
