import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_641 :
    ∀ n : ℕ, 641 ∣ n ^ 2 + 1 ↔ n % 641 = 154 ∨ n % 641 = 487 := by
  intro n
  letI : Fact (Nat.Prime 641) := ⟨by norm_num⟩
  have ha : ((n : ZMod 641) = 154) ↔ n % 641 = 154 :=
    ZMod.natCast_eq_natCast_iff' n 154 641
  have hb : ((n : ZMod 641) = 487) ↔ n % 641 = 487 :=
    ZMod.natCast_eq_natCast_iff' n 487 641
  have hr : (154 : ZMod 641) ^ 2 = -1 := by decide
  have hs : -(154 : ZMod 641) = 487 := by decide
  have hfac (z : ZMod 641) : z ^ 2 + 1 = (z - 154) * (z - 487) := calc
    z ^ 2 + 1 = z ^ 2 - (154 : ZMod 641) ^ 2 := by rw [hr] <;> ring
    _ = (z - 154) * (z - 487) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
