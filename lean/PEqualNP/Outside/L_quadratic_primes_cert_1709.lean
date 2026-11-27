import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1709 :
  ∀ n : ℕ, 1709 ∣ n ^ 2 + 1 ↔ n % 1709 = 390 ∨ n % 1709 = 1319 := by
  have h1 : (390 + 1319 : ZMod 1709) = 0 := by decide
  have h2 : (390 * 1319 : ZMod 1709) = 1 := by decide
  have hp : Nat.Prime 1709 := by norm_num
  have : Fact (Nat.Prime 1709) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1709]
  push_cast
  have hfac : (n : ZMod 1709) ^ 2 + 1 = ((n : ZMod 1709) - 390) * ((n : ZMod 1709) - 1319) := by
    calc (n : ZMod 1709) ^ 2 + 1
        = (n : ZMod 1709) ^ 2 - (390 + 1319 : ZMod 1709) * (n : ZMod 1709) + (390 * 1319 : ZMod 1709) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1709) - 390) * ((n : ZMod 1709) - 1319) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1709) = 390) ↔ n % 1709 = 390 := by
    rw [show (390 : ZMod 1709) = ((390 : ℕ) : ZMod 1709) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1709) = 1319) ↔ n % 1709 = 1319 := by
    rw [show (1319 : ZMod 1709) = ((1319 : ℕ) : ZMod 1709) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
