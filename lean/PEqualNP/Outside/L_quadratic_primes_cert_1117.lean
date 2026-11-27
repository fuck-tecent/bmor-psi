import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1117 :
    ∀ n : ℕ, 1117 ∣ n ^ 2 + 1 ↔ n % 1117 = 214 ∨ n % 1117 = 903 := by
  intro n
  letI : Fact (Nat.Prime 1117) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1117) = 214) ↔ n % 1117 = 214 :=
    ZMod.natCast_eq_natCast_iff' n 214 1117
  have hb : ((n : ZMod 1117) = 903) ↔ n % 1117 = 903 :=
    ZMod.natCast_eq_natCast_iff' n 903 1117
  have hr : (214 : ZMod 1117) ^ 2 = -1 := by decide
  have hs : -(214 : ZMod 1117) = 903 := by decide
  have hfac (z : ZMod 1117) : z ^ 2 + 1 = (z - 214) * (z - 903) := calc
    z ^ 2 + 1 = z ^ 2 - (214 : ZMod 1117) ^ 2 := by rw [hr] <;> ring
    _ = (z - 214) * (z - 903) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
