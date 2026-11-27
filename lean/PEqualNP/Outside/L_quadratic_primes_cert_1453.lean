import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1453 :
    ∀ n : ℕ, 1453 ∣ n ^ 2 + 1 ↔ n % 1453 = 497 ∨ n % 1453 = 956 := by
  intro n
  letI : Fact (Nat.Prime 1453) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1453) = 497) ↔ n % 1453 = 497 :=
    ZMod.natCast_eq_natCast_iff' n 497 1453
  have hb : ((n : ZMod 1453) = 956) ↔ n % 1453 = 956 :=
    ZMod.natCast_eq_natCast_iff' n 956 1453
  have hr : (497 : ZMod 1453) ^ 2 = -1 := by decide
  have hs : -(497 : ZMod 1453) = 956 := by decide
  have hfac (z : ZMod 1453) : z ^ 2 + 1 = (z - 497) * (z - 956) := calc
    z ^ 2 + 1 = z ^ 2 - (497 : ZMod 1453) ^ 2 := by rw [hr] <;> ring
    _ = (z - 497) * (z - 956) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
