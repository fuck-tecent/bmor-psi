import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1429 :
    ∀ n : ℕ, 1429 ∣ n ^ 2 + 1 ↔ n % 1429 = 620 ∨ n % 1429 = 809 := by
  intro n
  letI : Fact (Nat.Prime 1429) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1429) = 620) ↔ n % 1429 = 620 :=
    ZMod.natCast_eq_natCast_iff' n 620 1429
  have hb : ((n : ZMod 1429) = 809) ↔ n % 1429 = 809 :=
    ZMod.natCast_eq_natCast_iff' n 809 1429
  have hr : (620 : ZMod 1429) ^ 2 = -1 := by decide
  have hs : -(620 : ZMod 1429) = 809 := by decide
  have hfac (z : ZMod 1429) : z ^ 2 + 1 = (z - 620) * (z - 809) := calc
    z ^ 2 + 1 = z ^ 2 - (620 : ZMod 1429) ^ 2 := by rw [hr] <;> ring
    _ = (z - 620) * (z - 809) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
