import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_593 :
    ∀ n : ℕ, 593 ∣ n ^ 2 + 1 ↔ n % 593 = 77 ∨ n % 593 = 516 := by
  intro n
  letI : Fact (Nat.Prime 593) := ⟨by norm_num⟩
  have ha : ((n : ZMod 593) = 77) ↔ n % 593 = 77 :=
    ZMod.natCast_eq_natCast_iff' n 77 593
  have hb : ((n : ZMod 593) = 516) ↔ n % 593 = 516 :=
    ZMod.natCast_eq_natCast_iff' n 516 593
  have hr : (77 : ZMod 593) ^ 2 = -1 := by decide
  have hs : -(77 : ZMod 593) = 516 := by decide
  have hfac (z : ZMod 593) : z ^ 2 + 1 = (z - 77) * (z - 516) := calc
    z ^ 2 + 1 = z ^ 2 - (77 : ZMod 593) ^ 2 := by rw [hr] <;> ring
    _ = (z - 77) * (z - 516) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
