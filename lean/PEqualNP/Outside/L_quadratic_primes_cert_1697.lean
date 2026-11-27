import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1697 :
  ∀ n : ℕ, 1697 ∣ n ^ 2 + 1 ↔ n % 1697 = 414 ∨ n % 1697 = 1283 := by
  have h1 : (414 + 1283 : ZMod 1697) = 0 := by decide
  have h2 : (414 * 1283 : ZMod 1697) = 1 := by decide
  have hp : Nat.Prime 1697 := by norm_num
  have : Fact (Nat.Prime 1697) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1697]
  push_cast
  have hfac : (n : ZMod 1697) ^ 2 + 1 = ((n : ZMod 1697) - 414) * ((n : ZMod 1697) - 1283) := by
    calc (n : ZMod 1697) ^ 2 + 1
        = (n : ZMod 1697) ^ 2 - (414 + 1283 : ZMod 1697) * (n : ZMod 1697) + (414 * 1283 : ZMod 1697) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1697) - 414) * ((n : ZMod 1697) - 1283) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1697) = 414) ↔ n % 1697 = 414 := by
    rw [show (414 : ZMod 1697) = ((414 : ℕ) : ZMod 1697) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1697) = 1283) ↔ n % 1697 = 1283 := by
    rw [show (1283 : ZMod 1697) = ((1283 : ℕ) : ZMod 1697) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
