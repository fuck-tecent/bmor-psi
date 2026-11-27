import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_97 :
    ∀ n : ℕ, 97 ∣ n ^ 2 + 1 ↔ n % 97 = 22 ∨ n % 97 = 75 := by
  intro n
  letI : Fact (Nat.Prime 97) := ⟨by decide⟩
  have ha : ((n : ZMod 97) = 22) ↔ n % 97 = 22 :=
    ZMod.natCast_eq_natCast_iff' n 22 97
  have hb : ((n : ZMod 97) = 75) ↔ n % 97 = 75 :=
    ZMod.natCast_eq_natCast_iff' n 75 97
  have hr : (22 : ZMod 97) ^ 2 = -1 := by decide
  have hs : -(22 : ZMod 97) = 75 := by decide
  have hfac (z : ZMod 97) : z ^ 2 + 1 = (z - 22) * (z - 75) := calc
    z ^ 2 + 1 = z ^ 2 - (22 : ZMod 97) ^ 2 := by rw [hr] <;> ring
    _ = (z - 22) * (z - 75) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
