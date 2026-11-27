import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_613 :
    ∀ n:ℕ, 613∣n^2+1 ↔ n % 613=35 ∨ n % 613=578 := by
  intro n
  let : Fact (Nat.Prime 613) := ⟨by norm_num⟩
  have hsum : (35 + 578 : ZMod 613) = 0 := by decide
  have hprod : (35 * 578 : ZMod 613) = 1 := by decide
  have factor (z : ZMod 613) : (z - 35) * (z - 578) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (35 + 578) * z + 35 * 578 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 613) = 35) ↔ n % 613 = 35 :=
    ZMod.natCast_eq_natCast_iff' n 35 613
  have hb : ((n : ZMod 613) = 578) ↔ n % 613 = 578 :=
    ZMod.natCast_eq_natCast_iff' n 578 613
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
