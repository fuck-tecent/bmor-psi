import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1733 :
  ∀ n : ℕ, 1733 ∣ n ^ 2 + 1 ↔ n % 1733 = 410 ∨ n % 1733 = 1323 := by
  have h1 : (410 + 1323 : ZMod 1733) = 0 := by decide
  have h2 : (410 * 1323 : ZMod 1733) = 1 := by decide
  have hp : Nat.Prime 1733 := by norm_num
  have : Fact (Nat.Prime 1733) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1733]
  push_cast
  have hfac : (n : ZMod 1733) ^ 2 + 1 = ((n : ZMod 1733) - 410) * ((n : ZMod 1733) - 1323) := by
    calc (n : ZMod 1733) ^ 2 + 1
        = (n : ZMod 1733) ^ 2 - (410 + 1323 : ZMod 1733) * (n : ZMod 1733) + (410 * 1323 : ZMod 1733) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1733) - 410) * ((n : ZMod 1733) - 1323) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1733) = 410) ↔ n % 1733 = 410 := by
    rw [show (410 : ZMod 1733) = ((410 : ℕ) : ZMod 1733) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1733) = 1323) ↔ n % 1733 = 1323 := by
    rw [show (1323 : ZMod 1733) = ((1323 : ℕ) : ZMod 1733) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
