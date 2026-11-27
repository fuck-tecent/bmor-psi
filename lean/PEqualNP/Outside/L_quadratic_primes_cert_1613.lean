import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1613 :
    ∀ n : ℕ, 1613 ∣ n ^ 2 + 1 ↔ n % 1613 = 127 ∨ n % 1613 = 1486 := by
  intro n
  letI : Fact (Nat.Prime 1613) := ⟨by norm_num⟩
  have ha : ((n : ZMod 1613) = 127) ↔ n % 1613 = 127 :=
    ZMod.natCast_eq_natCast_iff' n 127 1613
  have hb : ((n : ZMod 1613) = 1486) ↔ n % 1613 = 1486 :=
    ZMod.natCast_eq_natCast_iff' n 1486 1613
  have hr : (127 : ZMod 1613) ^ 2 = -1 := by decide
  have hs : -(127 : ZMod 1613) = 1486 := by decide
  have hfac (z : ZMod 1613) : z ^ 2 + 1 = (z - 127) * (z - 1486) := calc
    z ^ 2 + 1 = z ^ 2 - (127 : ZMod 1613) ^ 2 := by rw [hr] <;> ring
    _ = (z - 127) * (z - 1486) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
