import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_449 :
    ∀ n : ℕ, 449 ∣ n ^ 2 + 1 ↔ n % 449 = 67 ∨ n % 449 = 382 := by
  intro n
  letI : Fact (Nat.Prime 449) := ⟨by norm_num⟩
  have ha : ((n : ZMod 449) = 67) ↔ n % 449 = 67 :=
    ZMod.natCast_eq_natCast_iff' n 67 449
  have hb : ((n : ZMod 449) = 382) ↔ n % 449 = 382 :=
    ZMod.natCast_eq_natCast_iff' n 382 449
  have hr : (67 : ZMod 449) ^ 2 = -1 := by decide
  have hs : -(67 : ZMod 449) = 382 := by decide
  have hfac (z : ZMod 449) : z ^ 2 + 1 = (z - 67) * (z - 382) := calc
    z ^ 2 + 1 = z ^ 2 - (67 : ZMod 449) ^ 2 := by rw [hr] <;> ring
    _ = (z - 67) * (z - 382) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
