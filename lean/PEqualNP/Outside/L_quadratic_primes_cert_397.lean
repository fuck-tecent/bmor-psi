import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_397 :
    ∀ n : ℕ, 397 ∣ n ^ 2 + 1 ↔ n % 397 = 63 ∨ n % 397 = 334 := by
  intro n
  letI : Fact (Nat.Prime 397) := ⟨by norm_num⟩
  have ha : ((n : ZMod 397) = 63) ↔ n % 397 = 63 :=
    ZMod.natCast_eq_natCast_iff' n 63 397
  have hb : ((n : ZMod 397) = 334) ↔ n % 397 = 334 :=
    ZMod.natCast_eq_natCast_iff' n 334 397
  have hr : (63 : ZMod 397) ^ 2 = -1 := by decide
  have hs : -(63 : ZMod 397) = 334 := by decide
  have hfac (z : ZMod 397) : z ^ 2 + 1 = (z - 63) * (z - 334) := calc
    z ^ 2 + 1 = z ^ 2 - (63 : ZMod 397) ^ 2 := by rw [hr] <;> ring
    _ = (z - 63) * (z - 334) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
