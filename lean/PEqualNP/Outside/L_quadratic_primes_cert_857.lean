import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_857 :
    ∀ n : ℕ, 857 ∣ n ^ 2 + 1 ↔ n % 857 = 207 ∨ n % 857 = 650 := by
  intro n
  letI : Fact (Nat.Prime 857) := ⟨by norm_num⟩
  have ha : ((n : ZMod 857) = 207) ↔ n % 857 = 207 :=
    ZMod.natCast_eq_natCast_iff' n 207 857
  have hb : ((n : ZMod 857) = 650) ↔ n % 857 = 650 :=
    ZMod.natCast_eq_natCast_iff' n 650 857
  have hr : (207 : ZMod 857) ^ 2 = -1 := by decide
  have hs : -(207 : ZMod 857) = 650 := by decide
  have hfac (z : ZMod 857) : z ^ 2 + 1 = (z - 207) * (z - 650) := calc
    z ^ 2 + 1 = z ^ 2 - (207 : ZMod 857) ^ 2 := by rw [hr] <;> ring
    _ = (z - 207) * (z - 650) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
