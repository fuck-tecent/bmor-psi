import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1237 :
    ∀ n : ℕ, 1237 ∣ n ^ 2 + 1 ↔ n % 1237 = 546 ∨ n % 1237 = 691 := by
  intro n
  letI : Fact (Nat.Prime 1237) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1237) = 546) ↔ n % 1237 = 546 :=
    ZMod.natCast_eq_natCast_iff' n 546 1237
  have hb : ((n : ZMod 1237) = 691) ↔ n % 1237 = 691 :=
    ZMod.natCast_eq_natCast_iff' n 691 1237
  have hr : (546 : ZMod 1237) ^ 2 = -1 := by decide
  have hs : -(546 : ZMod 1237) = 691 := by decide
  have hfac (z : ZMod 1237) : z ^ 2 + 1 = (z - 546) * (z - 691) := calc
    z ^ 2 + 1 = z ^ 2 - (546 : ZMod 1237) ^ 2 := by rw [hr] <;> ring
    _ = (z - 546) * (z - 691) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
