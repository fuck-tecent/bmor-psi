import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_197 :
    ∀ n : ℕ, 197 ∣ n ^ 2 + 1 ↔ n % 197 = 14 ∨ n % 197 = 183 := by
  intro n
  letI : Fact (Nat.Prime 197) := ⟨by norm_num⟩
  have ha : ((n : ZMod 197) = 14) ↔ n % 197 = 14 :=
    ZMod.natCast_eq_natCast_iff' n 14 197
  have hb : ((n : ZMod 197) = 183) ↔ n % 197 = 183 :=
    ZMod.natCast_eq_natCast_iff' n 183 197
  have hr : (14 : ZMod 197) ^ 2 = -1 := by decide
  have hs : -(14 : ZMod 197) = 183 := by decide
  have hfac (z : ZMod 197) : z ^ 2 + 1 = (z - 14) * (z - 183) := calc
    z ^ 2 + 1 = z ^ 2 - (14 : ZMod 197) ^ 2 := by rw [hr] <;> ring
    _ = (z - 14) * (z - 183) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
