import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_601 :
    ∀ n : ℕ, 601 ∣ n ^ 2 + 1 ↔ n % 601 = 125 ∨ n % 601 = 476 := by
  intro n
  letI : Fact (Nat.Prime 601) := ⟨by norm_num⟩
  have ha : ((n : ZMod 601) = 125) ↔ n % 601 = 125 :=
    ZMod.natCast_eq_natCast_iff' n 125 601
  have hb : ((n : ZMod 601) = 476) ↔ n % 601 = 476 :=
    ZMod.natCast_eq_natCast_iff' n 476 601
  have hr : (125 : ZMod 601) ^ 2 = -1 := by decide
  have hs : -(125 : ZMod 601) = 476 := by decide
  have hfac (z : ZMod 601) : z ^ 2 + 1 = (z - 125) * (z - 476) := calc
    z ^ 2 + 1 = z ^ 2 - (125 : ZMod 601) ^ 2 := by rw [hr] <;> ring
    _ = (z - 125) * (z - 476) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
