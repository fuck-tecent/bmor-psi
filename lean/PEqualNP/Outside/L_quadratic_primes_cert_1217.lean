import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1217 :
    ∀ n : ℕ, 1217 ∣ n ^ 2 + 1 ↔ n % 1217 = 78 ∨ n % 1217 = 1139 := by
  intro n
  letI : Fact (Nat.Prime 1217) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1217) = 78) ↔ n % 1217 = 78 :=
    ZMod.natCast_eq_natCast_iff' n 78 1217
  have hb : ((n : ZMod 1217) = 1139) ↔ n % 1217 = 1139 :=
    ZMod.natCast_eq_natCast_iff' n 1139 1217
  have hr : (78 : ZMod 1217) ^ 2 = -1 := by decide
  have hs : -(78 : ZMod 1217) = 1139 := by decide
  have hfac (z : ZMod 1217) : z ^ 2 + 1 = (z - 78) * (z - 1139) := calc
    z ^ 2 + 1 = z ^ 2 - (78 : ZMod 1217) ^ 2 := by rw [hr] <;> ring
    _ = (z - 78) * (z - 1139) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
