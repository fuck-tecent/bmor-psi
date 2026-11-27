import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_101 :
    ∀ n : ℕ, 101 ∣ n ^ 2 + 1 ↔ n % 101 = 10 ∨ n % 101 = 91 := by
  intro n
  letI : Fact (Nat.Prime 101) := ⟨by decide⟩
  have ha : ((n : ZMod 101) = 10) ↔ n % 101 = 10 :=
    ZMod.natCast_eq_natCast_iff' n 10 101
  have hb : ((n : ZMod 101) = 91) ↔ n % 101 = 91 :=
    ZMod.natCast_eq_natCast_iff' n 91 101
  have hr : (10 : ZMod 101) ^ 2 = -1 := by decide
  have hs : -(10 : ZMod 101) = 91 := by decide
  have hfac (z : ZMod 101) : z ^ 2 + 1 = (z - 10) * (z - 91) := calc
    z ^ 2 + 1 = z ^ 2 - (10 : ZMod 101) ^ 2 := by rw [hr] <;> ring
    _ = (z - 10) * (z - 91) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
