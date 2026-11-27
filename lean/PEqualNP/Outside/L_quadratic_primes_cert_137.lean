import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_137 :
    ∀ n : ℕ, 137 ∣ n ^ 2 + 1 ↔ n % 137 = 37 ∨ n % 137 = 100 := by
  intro n
  letI : Fact (Nat.Prime 137) := ⟨by decide⟩
  have ha : ((n : ZMod 137) = 37) ↔ n % 137 = 37 :=
    ZMod.natCast_eq_natCast_iff' n 37 137
  have hb : ((n : ZMod 137) = 100) ↔ n % 137 = 100 :=
    ZMod.natCast_eq_natCast_iff' n 100 137
  have hr : (37 : ZMod 137) ^ 2 = -1 := by decide
  have hs : -(37 : ZMod 137) = 100 := by decide
  have hfac (z : ZMod 137) : z ^ 2 + 1 = (z - 37) * (z - 100) := calc
    z ^ 2 + 1 = z ^ 2 - (37 : ZMod 137) ^ 2 := by rw [hr] <;> ring
    _ = (z - 37) * (z - 100) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
