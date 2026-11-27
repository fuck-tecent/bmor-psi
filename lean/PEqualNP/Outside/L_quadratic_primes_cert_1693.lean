import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1693 :
  ∀ n : ℕ, 1693 ∣ n ^ 2 + 1 ↔ n % 1693 = 92 ∨ n % 1693 = 1601 := by
  have h1 : (92 + 1601 : ZMod 1693) = 0 := by decide
  have h2 : (92 * 1601 : ZMod 1693) = 1 := by decide
  have hp : Nat.Prime 1693 := by norm_num
  have : Fact (Nat.Prime 1693) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1693]
  push_cast
  have hfac : (n : ZMod 1693) ^ 2 + 1 = ((n : ZMod 1693) - 92) * ((n : ZMod 1693) - 1601) := by
    calc (n : ZMod 1693) ^ 2 + 1
        = (n : ZMod 1693) ^ 2 - (92 + 1601 : ZMod 1693) * (n : ZMod 1693) + (92 * 1601 : ZMod 1693) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1693) - 92) * ((n : ZMod 1693) - 1601) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1693) = 92) ↔ n % 1693 = 92 := by
    rw [show (92 : ZMod 1693) = ((92 : ℕ) : ZMod 1693) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1693) = 1601) ↔ n % 1693 = 1601 := by
    rw [show (1601 : ZMod 1693) = ((1601 : ℕ) : ZMod 1693) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
