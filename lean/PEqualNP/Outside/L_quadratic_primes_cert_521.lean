import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_521 :
    ∀ n:ℕ, 521∣n^2+1 ↔ n % 521=235 ∨ n % 521=286 := by
  intro n
  let : Fact (Nat.Prime 521) := ⟨by norm_num⟩
  have hsum : (235 + 286 : ZMod 521) = 0 := by decide
  have hprod : (235 * 286 : ZMod 521) = 1 := by decide
  have factor (z : ZMod 521) : (z - 235) * (z - 286) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (235 + 286) * z + 235 * 286 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 521) = 235) ↔ n % 521 = 235 :=
    ZMod.natCast_eq_natCast_iff' n 235 521
  have hb : ((n : ZMod 521) = 286) ↔ n % 521 = 286 :=
    ZMod.natCast_eq_natCast_iff' n 286 521
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
