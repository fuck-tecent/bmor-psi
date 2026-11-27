import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1289 :
    ∀ n : ℕ, 1289 ∣ n ^ 2 + 1 ↔ n % 1289 = 479 ∨ n % 1289 = 810 := by
  intro n
  letI : Fact (Nat.Prime 1289) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1289) = 479) ↔ n % 1289 = 479 :=
    ZMod.natCast_eq_natCast_iff' n 479 1289
  have hb : ((n : ZMod 1289) = 810) ↔ n % 1289 = 810 :=
    ZMod.natCast_eq_natCast_iff' n 810 1289
  have hr : (479 : ZMod 1289) ^ 2 = -1 := by decide
  have hs : -(479 : ZMod 1289) = 810 := by decide
  have hfac (z : ZMod 1289) : z ^ 2 + 1 = (z - 479) * (z - 810) := calc
    z ^ 2 + 1 = z ^ 2 - (479 : ZMod 1289) ^ 2 := by rw [hr] <;> ring
    _ = (z - 479) * (z - 810) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
