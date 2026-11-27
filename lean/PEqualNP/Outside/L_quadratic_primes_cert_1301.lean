import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1301 :
    ∀ n : ℕ, 1301 ∣ n ^ 2 + 1 ↔ n % 1301 = 51 ∨ n % 1301 = 1250 := by
  intro n
  letI : Fact (Nat.Prime 1301) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1301) = 51) ↔ n % 1301 = 51 :=
    ZMod.natCast_eq_natCast_iff' n 51 1301
  have hb : ((n : ZMod 1301) = 1250) ↔ n % 1301 = 1250 :=
    ZMod.natCast_eq_natCast_iff' n 1250 1301
  have hr : (51 : ZMod 1301) ^ 2 = -1 := by decide
  have hs : -(51 : ZMod 1301) = 1250 := by decide
  have hfac (z : ZMod 1301) : z ^ 2 + 1 = (z - 51) * (z - 1250) := calc
    z ^ 2 + 1 = z ^ 2 - (51 : ZMod 1301) ^ 2 := by rw [hr] <;> ring
    _ = (z - 51) * (z - 1250) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
