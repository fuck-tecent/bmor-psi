import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1033 :
    ∀ n : ℕ, 1033 ∣ n ^ 2 + 1 ↔ n % 1033 = 355 ∨ n % 1033 = 678 := by
  intro n
  letI : Fact (Nat.Prime 1033) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1033) = 355) ↔ n % 1033 = 355 :=
    ZMod.natCast_eq_natCast_iff' n 355 1033
  have hb : ((n : ZMod 1033) = 678) ↔ n % 1033 = 678 :=
    ZMod.natCast_eq_natCast_iff' n 678 1033
  have hr : (355 : ZMod 1033) ^ 2 = -1 := by decide
  have hs : -(355 : ZMod 1033) = 678 := by decide
  have hfac (z : ZMod 1033) : z ^ 2 + 1 = (z - 355) * (z - 678) := calc
    z ^ 2 + 1 = z ^ 2 - (355 : ZMod 1033) ^ 2 := by rw [hr] <;> ring
    _ = (z - 355) * (z - 678) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
