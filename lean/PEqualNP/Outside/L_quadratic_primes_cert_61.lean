import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_61 :
    ∀ n : ℕ, 61 ∣ n ^ 2 + 1 ↔ n % 61 = 11 ∨ n % 61 = 50 := by
  intro n
  letI : Fact (Nat.Prime 61) := ⟨by decide⟩
  have ha : ((n : ZMod 61) = 11) ↔ n % 61 = 11 :=
    ZMod.natCast_eq_natCast_iff' n 11 61
  have hb : ((n : ZMod 61) = 50) ↔ n % 61 = 50 :=
    ZMod.natCast_eq_natCast_iff' n 50 61
  have hr : (11 : ZMod 61) ^ 2 = -1 := by decide
  have hs : -(11 : ZMod 61) = 50 := by decide
  have hfac (z : ZMod 61) : z ^ 2 + 1 = (z - 11) * (z - 50) := calc
    z ^ 2 + 1 = z ^ 2 - (11 : ZMod 61) ^ 2 := by rw [hr] <;> ring
    _ = (z - 11) * (z - 50) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
