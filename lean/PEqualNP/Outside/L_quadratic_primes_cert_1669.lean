import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1669 :
  ∀ n : ℕ, 1669 ∣ n ^ 2 + 1 ↔ n % 1669 = 220 ∨ n % 1669 = 1449 := by
  have h1 : (220 + 1449 : ZMod 1669) = 0 := by decide
  have h2 : (220 * 1449 : ZMod 1669) = 1 := by decide
  have hp : Nat.Prime 1669 := by norm_num
  have : Fact (Nat.Prime 1669) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1669]
  push_cast
  have hfac : (n : ZMod 1669) ^ 2 + 1 = ((n : ZMod 1669) - 220) * ((n : ZMod 1669) - 1449) := by
    calc (n : ZMod 1669) ^ 2 + 1
        = (n : ZMod 1669) ^ 2 - (220 + 1449 : ZMod 1669) * (n : ZMod 1669) + (220 * 1449 : ZMod 1669) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1669) - 220) * ((n : ZMod 1669) - 1449) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1669) = 220) ↔ n % 1669 = 220 := by
    rw [show (220 : ZMod 1669) = ((220 : ℕ) : ZMod 1669) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1669) = 1449) ↔ n % 1669 = 1449 := by
    rw [show (1449 : ZMod 1669) = ((1449 : ℕ) : ZMod 1669) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
