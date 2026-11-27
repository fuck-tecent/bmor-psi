import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1553 :
    ∀ n : ℕ, 1553 ∣ n ^ 2 + 1 ↔ n % 1553 = 339 ∨ n % 1553 = 1214 := by
  intro n
  letI : Fact (Nat.Prime 1553) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1553) = 339) ↔ n % 1553 = 339 :=
    ZMod.natCast_eq_natCast_iff' n 339 1553
  have hb : ((n : ZMod 1553) = 1214) ↔ n % 1553 = 1214 :=
    ZMod.natCast_eq_natCast_iff' n 1214 1553
  have hr : (339 : ZMod 1553) ^ 2 = -1 := by decide
  have hs : -(339 : ZMod 1553) = 1214 := by decide
  have hfac (z : ZMod 1553) : z ^ 2 + 1 = (z - 339) * (z - 1214) := calc
    z ^ 2 + 1 = z ^ 2 - (339 : ZMod 1553) ^ 2 := by rw [hr] <;> ring
    _ = (z - 339) * (z - 1214) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
