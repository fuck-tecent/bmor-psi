import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_541 :
    ∀ n : ℕ, 541 ∣ n ^ 2 + 1 ↔ n % 541 = 52 ∨ n % 541 = 489 := by
  intro n
  letI : Fact (Nat.Prime 541) := ⟨by norm_num⟩
  have ha : ((n : ZMod 541) = 52) ↔ n % 541 = 52 :=
    ZMod.natCast_eq_natCast_iff' n 52 541
  have hb : ((n : ZMod 541) = 489) ↔ n % 541 = 489 :=
    ZMod.natCast_eq_natCast_iff' n 489 541
  have hr : (52 : ZMod 541) ^ 2 = -1 := by decide
  have hs : -(52 : ZMod 541) = 489 := by decide
  have hfac (z : ZMod 541) : z ^ 2 + 1 = (z - 52) * (z - 489) := calc
    z ^ 2 + 1 = z ^ 2 - (52 : ZMod 541) ^ 2 := by rw [hr] <;> ring
    _ = (z - 52) * (z - 489) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
