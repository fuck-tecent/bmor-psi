import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_829 :
    ∀ n : ℕ, 829 ∣ n ^ 2 + 1 ↔ n % 829 = 246 ∨ n % 829 = 583 := by
  intro n
  letI : Fact (Nat.Prime 829) := ⟨by norm_num⟩
  have ha : ((n : ZMod 829) = 246) ↔ n % 829 = 246 :=
    ZMod.natCast_eq_natCast_iff' n 246 829
  have hb : ((n : ZMod 829) = 583) ↔ n % 829 = 583 :=
    ZMod.natCast_eq_natCast_iff' n 583 829
  have hr : (246 : ZMod 829) ^ 2 = -1 := by decide
  have hs : -(246 : ZMod 829) = 583 := by decide
  have hfac (z : ZMod 829) : z ^ 2 + 1 = (z - 246) * (z - 583) := calc
    z ^ 2 + 1 = z ^ 2 - (246 : ZMod 829) ^ 2 := by rw [hr] <;> ring
    _ = (z - 246) * (z - 583) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
