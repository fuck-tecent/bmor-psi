import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1489 :
    ∀ n : ℕ, 1489 ∣ n ^ 2 + 1 ↔ n % 1489 = 225 ∨ n % 1489 = 1264 := by
  intro n
  letI : Fact (Nat.Prime 1489) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1489) = 225) ↔ n % 1489 = 225 :=
    ZMod.natCast_eq_natCast_iff' n 225 1489
  have hb : ((n : ZMod 1489) = 1264) ↔ n % 1489 = 1264 :=
    ZMod.natCast_eq_natCast_iff' n 1264 1489
  have hr : (225 : ZMod 1489) ^ 2 = -1 := by decide
  have hs : -(225 : ZMod 1489) = 1264 := by decide
  have hfac (z : ZMod 1489) : z ^ 2 + 1 = (z - 225) * (z - 1264) := calc
    z ^ 2 + 1 = z ^ 2 - (225 : ZMod 1489) ^ 2 := by rw [hr] <;> ring
    _ = (z - 225) * (z - 1264) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
