import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_257 :
    ∀ n : ℕ, 257 ∣ n ^ 2 + 1 ↔ n % 257 = 16 ∨ n % 257 = 241 := by
  intro n
  letI : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  have ha : ((n : ZMod 257) = 16) ↔ n % 257 = 16 :=
    ZMod.natCast_eq_natCast_iff' n 16 257
  have hb : ((n : ZMod 257) = 241) ↔ n % 257 = 241 :=
    ZMod.natCast_eq_natCast_iff' n 241 257
  have hr : (16 : ZMod 257) ^ 2 = -1 := by decide
  have hs : -(16 : ZMod 257) = 241 := by decide
  have hfac (z : ZMod 257) : z ^ 2 + 1 = (z - 16) * (z - 241) := calc
    z ^ 2 + 1 = z ^ 2 - (16 : ZMod 257) ^ 2 := by rw [hr] <;> ring
    _ = (z - 16) * (z - 241) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
