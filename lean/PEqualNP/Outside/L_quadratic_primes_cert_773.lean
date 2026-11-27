import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_773 :
    ∀ n : ℕ, 773 ∣ n ^ 2 + 1 ↔ n % 773 = 317 ∨ n % 773 = 456 := by
  intro n
  letI : Fact (Nat.Prime 773) := ⟨by norm_num⟩
  have ha : ((n : ZMod 773) = 317) ↔ n % 773 = 317 :=
    ZMod.natCast_eq_natCast_iff' n 317 773
  have hb : ((n : ZMod 773) = 456) ↔ n % 773 = 456 :=
    ZMod.natCast_eq_natCast_iff' n 456 773
  have hr : (317 : ZMod 773) ^ 2 = -1 := by decide
  have hs : -(317 : ZMod 773) = 456 := by decide
  have hfac (z : ZMod 773) : z ^ 2 + 1 = (z - 317) * (z - 456) := calc
    z ^ 2 + 1 = z ^ 2 - (317 : ZMod 773) ^ 2 := by rw [hr] <;> ring
    _ = (z - 317) * (z - 456) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
