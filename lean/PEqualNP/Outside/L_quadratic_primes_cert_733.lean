import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_733 :
    ∀ n : ℕ, 733 ∣ n ^ 2 + 1 ↔ n % 733 = 353 ∨ n % 733 = 380 := by
  intro n
  letI : Fact (Nat.Prime 733) := ⟨by norm_num⟩
  have ha : ((n : ZMod 733) = 353) ↔ n % 733 = 353 :=
    ZMod.natCast_eq_natCast_iff' n 353 733
  have hb : ((n : ZMod 733) = 380) ↔ n % 733 = 380 :=
    ZMod.natCast_eq_natCast_iff' n 380 733
  have hr : (353 : ZMod 733) ^ 2 = -1 := by decide
  have hs : -(353 : ZMod 733) = 380 := by decide
  have hfac (z : ZMod 733) : z ^ 2 + 1 = (z - 353) * (z - 380) := calc
    z ^ 2 + 1 = z ^ 2 - (353 : ZMod 733) ^ 2 := by rw [hr] <;> ring
    _ = (z - 353) * (z - 380) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
