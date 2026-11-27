import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1753 :
  ∀ n : ℕ, 1753 ∣ n ^ 2 + 1 ↔ n % 1753 = 713 ∨ n % 1753 = 1040 := by
  have h1 : (713 + 1040 : ZMod 1753) = 0 := by decide
  have h2 : (713 * 1040 : ZMod 1753) = 1 := by decide
  have hp : Nat.Prime 1753 := by norm_num
  have : Fact (Nat.Prime 1753) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1753]
  push_cast
  have hfac : (n : ZMod 1753) ^ 2 + 1 = ((n : ZMod 1753) - 713) * ((n : ZMod 1753) - 1040) := by
    calc (n : ZMod 1753) ^ 2 + 1
        = (n : ZMod 1753) ^ 2 - (713 + 1040 : ZMod 1753) * (n : ZMod 1753) + (713 * 1040 : ZMod 1753) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1753) - 713) * ((n : ZMod 1753) - 1040) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1753) = 713) ↔ n % 1753 = 713 := by
    rw [show (713 : ZMod 1753) = ((713 : ℕ) : ZMod 1753) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1753) = 1040) ↔ n % 1753 = 1040 := by
    rw [show (1040 : ZMod 1753) = ((1040 : ℕ) : ZMod 1753) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
