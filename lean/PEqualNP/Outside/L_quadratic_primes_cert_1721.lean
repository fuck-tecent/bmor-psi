import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1721 :
  ∀ n : ℕ, 1721 ∣ n ^ 2 + 1 ↔ n % 1721 = 473 ∨ n % 1721 = 1248 := by
  have h1 : (473 + 1248 : ZMod 1721) = 0 := by decide
  have h2 : (473 * 1248 : ZMod 1721) = 1 := by decide
  have hp : Nat.Prime 1721 := by norm_num
  have : Fact (Nat.Prime 1721) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1721]
  push_cast
  have hfac : (n : ZMod 1721) ^ 2 + 1 = ((n : ZMod 1721) - 473) * ((n : ZMod 1721) - 1248) := by
    calc (n : ZMod 1721) ^ 2 + 1
        = (n : ZMod 1721) ^ 2 - (473 + 1248 : ZMod 1721) * (n : ZMod 1721) + (473 * 1248 : ZMod 1721) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1721) - 473) * ((n : ZMod 1721) - 1248) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1721) = 473) ↔ n % 1721 = 473 := by
    rw [show (473 : ZMod 1721) = ((473 : ℕ) : ZMod 1721) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1721) = 1248) ↔ n % 1721 = 1248 := by
    rw [show (1248 : ZMod 1721) = ((1248 : ℕ) : ZMod 1721) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
