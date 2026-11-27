import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_337 :
    ∀ n : ℕ, 337 ∣ n ^ 2 + 1 ↔ n % 337 = 148 ∨ n % 337 = 189 := by
  intro n
  letI : Fact (Nat.Prime 337) := ⟨by norm_num⟩
  have ha : ((n : ZMod 337) = 148) ↔ n % 337 = 148 :=
    ZMod.natCast_eq_natCast_iff' n 148 337
  have hb : ((n : ZMod 337) = 189) ↔ n % 337 = 189 :=
    ZMod.natCast_eq_natCast_iff' n 189 337
  have hr : (148 : ZMod 337) ^ 2 = -1 := by decide
  have hs : -(148 : ZMod 337) = 189 := by decide
  have hfac (z : ZMod 337) : z ^ 2 + 1 = (z - 148) * (z - 189) := calc
    z ^ 2 + 1 = z ^ 2 - (148 : ZMod 337) ^ 2 := by rw [hr] <;> ring
    _ = (z - 148) * (z - 189) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
