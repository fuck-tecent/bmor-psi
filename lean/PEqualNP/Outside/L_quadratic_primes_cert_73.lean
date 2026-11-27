import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_73 :
    ∀ n : ℕ, 73 ∣ n ^ 2 + 1 ↔ n % 73 = 27 ∨ n % 73 = 46 := by
  intro n
  letI : Fact (Nat.Prime 73) := ⟨by decide⟩
  have ha : ((n : ZMod 73) = 27) ↔ n % 73 = 27 :=
    ZMod.natCast_eq_natCast_iff' n 27 73
  have hb : ((n : ZMod 73) = 46) ↔ n % 73 = 46 :=
    ZMod.natCast_eq_natCast_iff' n 46 73
  have hr : (27 : ZMod 73) ^ 2 = -1 := by decide
  have hs : -(27 : ZMod 73) = 46 := by decide
  have hfac (z : ZMod 73) : z ^ 2 + 1 = (z - 27) * (z - 46) := calc
    z ^ 2 + 1 = z ^ 2 - (27 : ZMod 73) ^ 2 := by rw [hr] <;> ring
    _ = (z - 27) * (z - 46) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
