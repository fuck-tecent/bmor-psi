import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1013 :
    ∀ n : ℕ, 1013 ∣ n ^ 2 + 1 ↔ n % 1013 = 45 ∨ n % 1013 = 968 := by
  intro n
  letI : Fact (Nat.Prime 1013) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1013) = 45) ↔ n % 1013 = 45 :=
    ZMod.natCast_eq_natCast_iff' n 45 1013
  have hb : ((n : ZMod 1013) = 968) ↔ n % 1013 = 968 :=
    ZMod.natCast_eq_natCast_iff' n 968 1013
  have hr : (45 : ZMod 1013) ^ 2 = -1 := by decide
  have hs : -(45 : ZMod 1013) = 968 := by decide
  have hfac (z : ZMod 1013) : z ^ 2 + 1 = (z - 45) * (z - 968) := calc
    z ^ 2 + 1 = z ^ 2 - (45 : ZMod 1013) ^ 2 := by rw [hr] <;> ring
    _ = (z - 45) * (z - 968) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
