import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1657 :
  ∀ n : ℕ, 1657 ∣ n ^ 2 + 1 ↔ n % 1657 = 783 ∨ n % 1657 = 874 := by
  have h1 : (783 + 874 : ZMod 1657) = 0 := by decide
  have h2 : (783 * 874 : ZMod 1657) = 1 := by decide
  have hp : Nat.Prime 1657 := by norm_num
  have : Fact (Nat.Prime 1657) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1657]
  push_cast
  have hfac : (n : ZMod 1657) ^ 2 + 1 = ((n : ZMod 1657) - 783) * ((n : ZMod 1657) - 874) := by
    calc (n : ZMod 1657) ^ 2 + 1
        = (n : ZMod 1657) ^ 2 - (783 + 874 : ZMod 1657) * (n : ZMod 1657) + (783 * 874 : ZMod 1657) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1657) - 783) * ((n : ZMod 1657) - 874) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1657) = 783) ↔ n % 1657 = 783 := by
    rw [show (783 : ZMod 1657) = ((783 : ℕ) : ZMod 1657) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1657) = 874) ↔ n % 1657 = 874 := by
    rw [show (874 : ZMod 1657) = ((874 : ℕ) : ZMod 1657) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
