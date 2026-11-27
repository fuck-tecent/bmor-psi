import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1361 :
    ∀ n : ℕ, 1361 ∣ n ^ 2 + 1 ↔ n % 1361 = 614 ∨ n % 1361 = 747 := by
  intro n
  letI : Fact (Nat.Prime 1361) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1361) = 614) ↔ n % 1361 = 614 :=
    ZMod.natCast_eq_natCast_iff' n 614 1361
  have hb : ((n : ZMod 1361) = 747) ↔ n % 1361 = 747 :=
    ZMod.natCast_eq_natCast_iff' n 747 1361
  have hr : (614 : ZMod 1361) ^ 2 = -1 := by decide
  have hs : -(614 : ZMod 1361) = 747 := by decide
  have hfac (z : ZMod 1361) : z ^ 2 + 1 = (z - 614) * (z - 747) := calc
    z ^ 2 + 1 = z ^ 2 - (614 : ZMod 1361) ^ 2 := by rw [hr] <;> ring
    _ = (z - 614) * (z - 747) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
