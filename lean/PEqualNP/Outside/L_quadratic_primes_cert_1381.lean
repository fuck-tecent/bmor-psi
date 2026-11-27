import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1381 :
    ∀ n : ℕ, 1381 ∣ n ^ 2 + 1 ↔ n % 1381 = 366 ∨ n % 1381 = 1015 := by
  intro n
  haveI : Fact (1381).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1381) = (n : ZMod 1381) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (366 : ZMod 1381) ^ 2 + 1 = 0 := by
    rw [show (366 : ZMod 1381) ^ 2 + 1 = ((366 ^ 2 + 1 : ℕ) : ZMod 1381) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (366 ^ 2 + 1) 1381).mpr (by norm_num)
  have hb : (1015 : ZMod 1381) ^ 2 + 1 = 0 := by
    rw [show (1015 : ZMod 1381) ^ 2 + 1 = ((1015 ^ 2 + 1 : ℕ) : ZMod 1381) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1015 ^ 2 + 1) 1381).mpr (by norm_num)
  have hsum : (366 : ZMod 1381) + (1015 : ZMod 1381) = 0 := by
    rw [show (366 : ZMod 1381) + (1015 : ZMod 1381) = ((366 + 1015 : ℕ) : ZMod 1381) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (366 + 1015) 1381).mpr (by norm_num)
  have hprod : (366 : ZMod 1381) * (1015 : ZMod 1381) = 1 := by
    rw [← Nat.cast_one]
    rw [show (366 : ZMod 1381) * (1015 : ZMod 1381) = ((366 * 1015 : ℕ) : ZMod 1381) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (366 * 1015) 1 1381).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1381, r ^ 2 + 1 = 0 ↔ r = (366 : ZMod 1381) ∨ r = (1015 : ZMod 1381) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (366 : ZMod 1381)) * (r - (1015 : ZMod 1381)) = 0 := by
        have hid : (r - (366 : ZMod 1381)) * (r - (1015 : ZMod 1381)) = r ^ 2 + 1 := by
          calc (r - (366 : ZMod 1381)) * (r - (1015 : ZMod 1381))
              = r ^ 2 - ((366 : ZMod 1381) + (1015 : ZMod 1381)) * r
                  + (366 : ZMod 1381) * (1015 : ZMod 1381) := by ring
            _ = r ^ 2 + 1 := by rw [hsum, hprod]; ring
        rw [hid]
        exact h
      rcases mul_eq_zero.mp hfac with h' | h'
      · left
        exact sub_eq_zero.mp h'
      · right
        exact sub_eq_zero.mp h'
    · rintro (h | h)
      · rw [h]
        exact ha
      · rw [h]
        exact hb
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1381, hcast, hroot (n : ZMod 1381)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 366 1381).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 366 < 1381)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1015 1381).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1015 < 1381)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 366 1381).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 366 < 1381)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1015 1381).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1015 < 1381)]
        exact h)
