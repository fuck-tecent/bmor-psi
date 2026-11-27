import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_461 :
    ∀ n : ℕ, 461 ∣ n ^ 2 + 1 ↔ n % 461 = 48 ∨ n % 461 = 413 := by
  intro n
  letI : Fact (Nat.Prime 461) := ⟨by norm_num⟩
  have ha : ((n : ZMod 461) = 48) ↔ n % 461 = 48 :=
    ZMod.natCast_eq_natCast_iff' n 48 461
  have hb : ((n : ZMod 461) = 413) ↔ n % 461 = 413 :=
    ZMod.natCast_eq_natCast_iff' n 413 461
  have hr : (48 : ZMod 461) ^ 2 = -1 := by decide
  have hs : -(48 : ZMod 461) = 413 := by decide
  have hfac (z : ZMod 461) : z ^ 2 + 1 = (z - 48) * (z - 413) := calc
    z ^ 2 + 1 = z ^ 2 - (48 : ZMod 461) ^ 2 := by rw [hr] <;> ring
    _ = (z - 48) * (z - 413) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
