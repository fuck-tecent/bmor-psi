import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_937 :
    ∀ n : ℕ, 937 ∣ n ^ 2 + 1 ↔ n % 937 = 196 ∨ n % 937 = 741 := by
  intro n
  letI : Fact (Nat.Prime 937) := ⟨by norm_num⟩
  have ha : ((n : ZMod 937) = 196) ↔ n % 937 = 196 :=
    ZMod.natCast_eq_natCast_iff' n 196 937
  have hb : ((n : ZMod 937) = 741) ↔ n % 937 = 741 :=
    ZMod.natCast_eq_natCast_iff' n 741 937
  have hr : (196 : ZMod 937) ^ 2 = -1 := by decide
  have hs : -(196 : ZMod 937) = 741 := by decide
  have hfac (z : ZMod 937) : z ^ 2 + 1 = (z - 196) * (z - 741) := calc
    z ^ 2 + 1 = z ^ 2 - (196 : ZMod 937) ^ 2 := by rw [hr] <;> ring
    _ = (z - 196) * (z - 741) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
