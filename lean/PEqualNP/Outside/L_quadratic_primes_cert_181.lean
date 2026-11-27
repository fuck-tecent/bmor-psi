import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_181 :
    ∀ n : ℕ, 181 ∣ n ^ 2 + 1 ↔ n % 181 = 19 ∨ n % 181 = 162 := by
  intro n
  letI : Fact (Nat.Prime 181) := ⟨by norm_num⟩
  have ha : ((n : ZMod 181) = 19) ↔ n % 181 = 19 :=
    ZMod.natCast_eq_natCast_iff' n 19 181
  have hb : ((n : ZMod 181) = 162) ↔ n % 181 = 162 :=
    ZMod.natCast_eq_natCast_iff' n 162 181
  have hr : (19 : ZMod 181) ^ 2 = -1 := by decide
  have hs : -(19 : ZMod 181) = 162 := by decide
  have hfac (z : ZMod 181) : z ^ 2 + 1 = (z - 19) * (z - 162) := calc
    z ^ 2 + 1 = z ^ 2 - (19 : ZMod 181) ^ 2 := by rw [hr] <;> ring
    _ = (z - 19) * (z - 162) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
