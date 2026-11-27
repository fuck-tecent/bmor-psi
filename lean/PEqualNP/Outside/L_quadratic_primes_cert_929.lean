import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_929 :
    ∀ n : ℕ, 929 ∣ n ^ 2 + 1 ↔ n % 929 = 324 ∨ n % 929 = 605 := by
  intro n
  letI : Fact (Nat.Prime 929) := ⟨by norm_num⟩
  have ha : ((n : ZMod 929) = 324) ↔ n % 929 = 324 :=
    ZMod.natCast_eq_natCast_iff' n 324 929
  have hb : ((n : ZMod 929) = 605) ↔ n % 929 = 605 :=
    ZMod.natCast_eq_natCast_iff' n 605 929
  have hr : (324 : ZMod 929) ^ 2 = -1 := by decide
  have hs : -(324 : ZMod 929) = 605 := by decide
  have hfac (z : ZMod 929) : z ^ 2 + 1 = (z - 324) * (z - 605) := calc
    z ^ 2 + 1 = z ^ 2 - (324 : ZMod 929) ^ 2 := by rw [hr] <;> ring
    _ = (z - 324) * (z - 605) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
