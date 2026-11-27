import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_661 :
    ∀ n : ℕ, 661 ∣ n ^ 2 + 1 ↔ n % 661 = 106 ∨ n % 661 = 555 := by
  intro n
  letI : Fact (Nat.Prime 661) := ⟨by norm_num⟩
  have ha : ((n : ZMod 661) = 106) ↔ n % 661 = 106 :=
    ZMod.natCast_eq_natCast_iff' n 106 661
  have hb : ((n : ZMod 661) = 555) ↔ n % 661 = 555 :=
    ZMod.natCast_eq_natCast_iff' n 555 661
  have hr : (106 : ZMod 661) ^ 2 = -1 := by decide
  have hs : -(106 : ZMod 661) = 555 := by decide
  have hfac (z : ZMod 661) : z ^ 2 + 1 = (z - 106) * (z - 555) := calc
    z ^ 2 + 1 = z ^ 2 - (106 : ZMod 661) ^ 2 := by rw [hr] <;> ring
    _ = (z - 106) * (z - 555) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
