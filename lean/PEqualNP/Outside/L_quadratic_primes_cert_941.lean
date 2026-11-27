import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_941 :
    ∀ n : ℕ, 941 ∣ n ^ 2 + 1 ↔ n % 941 = 97 ∨ n % 941 = 844 := by
  intro n
  letI : Fact (Nat.Prime 941) := ⟨by norm_num⟩
  have ha : ((n : ZMod 941) = 97) ↔ n % 941 = 97 :=
    ZMod.natCast_eq_natCast_iff' n 97 941
  have hb : ((n : ZMod 941) = 844) ↔ n % 941 = 844 :=
    ZMod.natCast_eq_natCast_iff' n 844 941
  have hr : (97 : ZMod 941) ^ 2 = -1 := by decide
  have hs : -(97 : ZMod 941) = 844 := by decide
  have hfac (z : ZMod 941) : z ^ 2 + 1 = (z - 97) * (z - 844) := calc
    z ^ 2 + 1 = z ^ 2 - (97 : ZMod 941) ^ 2 := by rw [hr] <;> ring
    _ = (z - 97) * (z - 844) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
