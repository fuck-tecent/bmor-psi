import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_881 :
    ∀ n : ℕ, 881 ∣ n ^ 2 + 1 ↔ n % 881 = 387 ∨ n % 881 = 494 := by
  intro n
  letI : Fact (Nat.Prime 881) := ⟨by norm_num⟩
  have ha : ((n : ZMod 881) = 387) ↔ n % 881 = 387 :=
    ZMod.natCast_eq_natCast_iff' n 387 881
  have hb : ((n : ZMod 881) = 494) ↔ n % 881 = 494 :=
    ZMod.natCast_eq_natCast_iff' n 494 881
  have hr : (387 : ZMod 881) ^ 2 = -1 := by decide
  have hs : -(387 : ZMod 881) = 494 := by decide
  have hfac (z : ZMod 881) : z ^ 2 + 1 = (z - 387) * (z - 494) := calc
    z ^ 2 + 1 = z ^ 2 - (387 : ZMod 881) ^ 2 := by rw [hr] <;> ring
    _ = (z - 387) * (z - 494) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
