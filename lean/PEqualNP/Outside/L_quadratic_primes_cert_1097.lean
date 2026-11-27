import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1097 :
    ∀ n : ℕ, 1097 ∣ n ^ 2 + 1 ↔ n % 1097 = 341 ∨ n % 1097 = 756 := by
  intro n
  letI : Fact (Nat.Prime 1097) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1097) = 341) ↔ n % 1097 = 341 :=
    ZMod.natCast_eq_natCast_iff' n 341 1097
  have hb : ((n : ZMod 1097) = 756) ↔ n % 1097 = 756 :=
    ZMod.natCast_eq_natCast_iff' n 756 1097
  have hr : (341 : ZMod 1097) ^ 2 = -1 := by decide
  have hs : -(341 : ZMod 1097) = 756 := by decide
  have hfac (z : ZMod 1097) : z ^ 2 + 1 = (z - 341) * (z - 756) := calc
    z ^ 2 + 1 = z ^ 2 - (341 : ZMod 1097) ^ 2 := by rw [hr] <;> ring
    _ = (z - 341) * (z - 756) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
