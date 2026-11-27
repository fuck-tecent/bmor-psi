import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_421 :
    ∀ n : ℕ, 421 ∣ n ^ 2 + 1 ↔ n % 421 = 29 ∨ n % 421 = 392 := by
  intro n
  letI : Fact (Nat.Prime 421) := ⟨by norm_num⟩
  have ha : ((n : ZMod 421) = 29) ↔ n % 421 = 29 :=
    ZMod.natCast_eq_natCast_iff' n 29 421
  have hb : ((n : ZMod 421) = 392) ↔ n % 421 = 392 :=
    ZMod.natCast_eq_natCast_iff' n 392 421
  have hr : (29 : ZMod 421) ^ 2 = -1 := by decide
  have hs : -(29 : ZMod 421) = 392 := by decide
  have hfac (z : ZMod 421) : z ^ 2 + 1 = (z - 29) * (z - 392) := calc
    z ^ 2 + 1 = z ^ 2 - (29 : ZMod 421) ^ 2 := by rw [hr] <;> ring
    _ = (z - 29) * (z - 392) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
