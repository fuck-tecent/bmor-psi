import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_281 :
    ∀ n : ℕ, 281 ∣ n ^ 2 + 1 ↔ n % 281 = 53 ∨ n % 281 = 228 := by
  intro n
  letI : Fact (Nat.Prime 281) := ⟨by norm_num⟩
  have ha : ((n : ZMod 281) = 53) ↔ n % 281 = 53 :=
    ZMod.natCast_eq_natCast_iff' n 53 281
  have hb : ((n : ZMod 281) = 228) ↔ n % 281 = 228 :=
    ZMod.natCast_eq_natCast_iff' n 228 281
  have hr : (53 : ZMod 281) ^ 2 = -1 := by decide
  have hs : -(53 : ZMod 281) = 228 := by decide
  have hfac (z : ZMod 281) : z ^ 2 + 1 = (z - 53) * (z - 228) := calc
    z ^ 2 + 1 = z ^ 2 - (53 : ZMod 281) ^ 2 := by rw [hr] <;> ring
    _ = (z - 53) * (z - 228) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
