import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_677 :
    ∀ n : ℕ, 677 ∣ n ^ 2 + 1 ↔ n % 677 = 26 ∨ n % 677 = 651 := by
  intro n
  letI : Fact (Nat.Prime 677) := ⟨by norm_num⟩
  have ha : ((n : ZMod 677) = 26) ↔ n % 677 = 26 :=
    ZMod.natCast_eq_natCast_iff' n 26 677
  have hb : ((n : ZMod 677) = 651) ↔ n % 677 = 651 :=
    ZMod.natCast_eq_natCast_iff' n 651 677
  have hr : (26 : ZMod 677) ^ 2 = -1 := by decide
  have hs : -(26 : ZMod 677) = 651 := by decide
  have hfac (z : ZMod 677) : z ^ 2 + 1 = (z - 26) * (z - 651) := calc
    z ^ 2 + 1 = z ^ 2 - (26 : ZMod 677) ^ 2 := by rw [hr] <;> ring
    _ = (z - 26) * (z - 651) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
