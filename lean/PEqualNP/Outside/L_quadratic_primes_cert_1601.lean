import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1601 :
    ∀ n:ℕ, 1601∣n^2+1 ↔ n % 1601=40 ∨ n % 1601=1561 := by
  intro n
  let : Fact (Nat.Prime 1601) := ⟨by norm_num⟩
  have hsum : (40 + 1561 : ZMod 1601) = 0 := by decide
  have hprod : (40 * 1561 : ZMod 1601) = 1 := by decide
  have factor (z : ZMod 1601) : (z - 40) * (z - 1561) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (40 + 1561) * z + 40 * 1561 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 1601) = 40) ↔ n % 1601 = 40 :=
    ZMod.natCast_eq_natCast_iff' n 40 1601
  have hb : ((n : ZMod 1601) = 1561) ↔ n % 1601 = 1561 :=
    ZMod.natCast_eq_natCast_iff' n 1561 1601
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
