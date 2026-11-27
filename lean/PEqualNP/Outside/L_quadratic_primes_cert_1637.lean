import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1637 :
  ∀ n : ℕ, 1637 ∣ n ^ 2 + 1 ↔ n % 1637 = 316 ∨ n % 1637 = 1321 := by
  have h1 : (316 + 1321 : ZMod 1637) = 0 := by decide
  have h2 : (316 * 1321 : ZMod 1637) = 1 := by decide
  have hp : Nat.Prime 1637 := by norm_num
  have : Fact (Nat.Prime 1637) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1637]
  push_cast
  have hfac : (n : ZMod 1637) ^ 2 + 1 = ((n : ZMod 1637) - 316) * ((n : ZMod 1637) - 1321) := by
    calc (n : ZMod 1637) ^ 2 + 1
        = (n : ZMod 1637) ^ 2 - (316 + 1321 : ZMod 1637) * (n : ZMod 1637) + (316 * 1321 : ZMod 1637) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1637) - 316) * ((n : ZMod 1637) - 1321) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1637) = 316) ↔ n % 1637 = 316 := by
    rw [show (316 : ZMod 1637) = ((316 : ℕ) : ZMod 1637) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1637) = 1321) ↔ n % 1637 = 1321 := by
    rw [show (1321 : ZMod 1637) = ((1321 : ℕ) : ZMod 1637) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
