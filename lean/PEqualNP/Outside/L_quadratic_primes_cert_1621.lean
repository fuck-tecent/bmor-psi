import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1621 :
  ∀ n : ℕ, 1621 ∣ n ^ 2 + 1 ↔ n % 1621 = 166 ∨ n % 1621 = 1455 := by
  have h1 : (166 + 1455 : ZMod 1621) = 0 := by decide
  have h2 : (166 * 1455 : ZMod 1621) = 1 := by decide
  have hp : Nat.Prime 1621 := by norm_num
  have : Fact (Nat.Prime 1621) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1621]
  push_cast
  have hfac : (n : ZMod 1621) ^ 2 + 1 = ((n : ZMod 1621) - 166) * ((n : ZMod 1621) - 1455) := by
    calc (n : ZMod 1621) ^ 2 + 1
        = (n : ZMod 1621) ^ 2 - (166 + 1455 : ZMod 1621) * (n : ZMod 1621) + (166 * 1455 : ZMod 1621) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1621) - 166) * ((n : ZMod 1621) - 1455) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1621) = 166) ↔ n % 1621 = 166 := by
    rw [show (166 : ZMod 1621) = ((166 : ℕ) : ZMod 1621) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1621) = 1455) ↔ n % 1621 = 1455 := by
    rw [show (1455 : ZMod 1621) = ((1455 : ℕ) : ZMod 1621) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
