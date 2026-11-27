import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_89 :
    ∀ n : ℕ, 89 ∣ n ^ 2 + 1 ↔ n % 89 = 34 ∨ n % 89 = 55 := by
  intro n
  letI : Fact (Nat.Prime 89) := ⟨by decide⟩
  have ha : ((n : ZMod 89) = 34) ↔ n % 89 = 34 :=
    ZMod.natCast_eq_natCast_iff' n 34 89
  have hb : ((n : ZMod 89) = 55) ↔ n % 89 = 55 :=
    ZMod.natCast_eq_natCast_iff' n 55 89
  have hr : (34 : ZMod 89) ^ 2 = -1 := by decide
  have hs : -(34 : ZMod 89) = 55 := by decide
  have hfac (z : ZMod 89) : z ^ 2 + 1 = (z - 34) * (z - 55) := calc
    z ^ 2 + 1 = z ^ 2 - (34 : ZMod 89) ^ 2 := by rw [hr] <;> ring
    _ = (z - 34) * (z - 55) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
