import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1741 :
  ∀ n : ℕ, 1741 ∣ n ^ 2 + 1 ↔ n % 1741 = 59 ∨ n % 1741 = 1682 := by
  have h1 : (59 + 1682 : ZMod 1741) = 0 := by decide
  have h2 : (59 * 1682 : ZMod 1741) = 1 := by decide
  have hp : Nat.Prime 1741 := by norm_num
  have : Fact (Nat.Prime 1741) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1741]
  push_cast
  have hfac : (n : ZMod 1741) ^ 2 + 1 = ((n : ZMod 1741) - 59) * ((n : ZMod 1741) - 1682) := by
    calc (n : ZMod 1741) ^ 2 + 1
        = (n : ZMod 1741) ^ 2 - (59 + 1682 : ZMod 1741) * (n : ZMod 1741) + (59 * 1682 : ZMod 1741) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1741) - 59) * ((n : ZMod 1741) - 1682) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1741) = 59) ↔ n % 1741 = 59 := by
    rw [show (59 : ZMod 1741) = ((59 : ℕ) : ZMod 1741) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1741) = 1682) ↔ n % 1741 = 1682 := by
    rw [show (1682 : ZMod 1741) = ((1682 : ℕ) : ZMod 1741) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
