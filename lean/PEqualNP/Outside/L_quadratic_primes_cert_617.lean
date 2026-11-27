import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_617 :
    ∀ n:ℕ, 617∣n^2+1 ↔ n % 617=194 ∨ n % 617=423 := by
  intro n
  let : Fact (Nat.Prime 617) := ⟨by norm_num⟩
  have hsum : (194 + 423 : ZMod 617) = 0 := by decide
  have hprod : (194 * 423 : ZMod 617) = 1 := by decide
  have factor (z : ZMod 617) : (z - 194) * (z - 423) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (194 + 423) * z + 194 * 423 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 617) = 194) ↔ n % 617 = 194 :=
    ZMod.natCast_eq_natCast_iff' n 194 617
  have hb : ((n : ZMod 617) = 423) ↔ n % 617 = 423 :=
    ZMod.natCast_eq_natCast_iff' n 423 617
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
