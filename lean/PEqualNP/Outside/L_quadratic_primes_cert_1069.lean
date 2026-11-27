import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1069 :
    ∀ n : ℕ, 1069 ∣ n ^ 2 + 1 ↔ n % 1069 = 249 ∨ n % 1069 = 820 := by
  intro n
  letI : Fact (Nat.Prime 1069) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1069) = 249) ↔ n % 1069 = 249 :=
    ZMod.natCast_eq_natCast_iff' n 249 1069
  have hb : ((n : ZMod 1069) = 820) ↔ n % 1069 = 820 :=
    ZMod.natCast_eq_natCast_iff' n 820 1069
  have hr : (249 : ZMod 1069) ^ 2 = -1 := by decide
  have hs : -(249 : ZMod 1069) = 820 := by decide
  have hfac (z : ZMod 1069) : z ^ 2 + 1 = (z - 249) * (z - 820) := calc
    z ^ 2 + 1 = z ^ 2 - (249 : ZMod 1069) ^ 2 := by rw [hr] <;> ring
    _ = (z - 249) * (z - 820) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
