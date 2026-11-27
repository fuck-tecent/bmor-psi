import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_353 :
    ∀ n : ℕ, 353 ∣ n ^ 2 + 1 ↔ n % 353 = 42 ∨ n % 353 = 311 := by
  intro n
  letI : Fact (Nat.Prime 353) := ⟨by norm_num⟩
  have ha : ((n : ZMod 353) = 42) ↔ n % 353 = 42 :=
    ZMod.natCast_eq_natCast_iff' n 42 353
  have hb : ((n : ZMod 353) = 311) ↔ n % 353 = 311 :=
    ZMod.natCast_eq_natCast_iff' n 311 353
  have hr : (42 : ZMod 353) ^ 2 = -1 := by decide
  have hs : -(42 : ZMod 353) = 311 := by decide
  have hfac (z : ZMod 353) : z ^ 2 + 1 = (z - 42) * (z - 311) := calc
    z ^ 2 + 1 = z ^ 2 - (42 : ZMod 353) ^ 2 := by rw [hr] <;> ring
    _ = (z - 42) * (z - 311) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
