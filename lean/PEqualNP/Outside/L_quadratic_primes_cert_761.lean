import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_761 :
    ∀ n:ℕ, 761∣n^2+1 ↔ n % 761=39 ∨ n % 761=722 := by
  intro n
  let : Fact (Nat.Prime 761) := ⟨by norm_num⟩
  have hsum : (39 + 722 : ZMod 761) = 0 := by decide
  have hprod : (39 * 722 : ZMod 761) = 1 := by decide
  have factor (z : ZMod 761) : (z - 39) * (z - 722) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (39 + 722) * z + 39 * 722 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 761) = 39) ↔ n % 761 = 39 :=
    ZMod.natCast_eq_natCast_iff' n 39 761
  have hb : ((n : ZMod 761) = 722) ↔ n % 761 = 722 :=
    ZMod.natCast_eq_natCast_iff' n 722 761
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
