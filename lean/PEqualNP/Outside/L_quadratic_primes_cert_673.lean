import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_673 :
    ∀ n : ℕ, 673 ∣ n ^ 2 + 1 ↔ n % 673 = 58 ∨ n % 673 = 615 := by
  intro n
  letI : Fact (Nat.Prime 673) := ⟨by norm_num⟩
  have ha : ((n : ZMod 673) = 58) ↔ n % 673 = 58 :=
    ZMod.natCast_eq_natCast_iff' n 58 673
  have hb : ((n : ZMod 673) = 615) ↔ n % 673 = 615 :=
    ZMod.natCast_eq_natCast_iff' n 615 673
  have hr : (58 : ZMod 673) ^ 2 = -1 := by decide
  have hs : -(58 : ZMod 673) = 615 := by decide
  have hfac (z : ZMod 673) : z ^ 2 + 1 = (z - 58) * (z - 615) := calc
    z ^ 2 + 1 = z ^ 2 - (58 : ZMod 673) ^ 2 := by rw [hr] <;> ring
    _ = (z - 58) * (z - 615) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
