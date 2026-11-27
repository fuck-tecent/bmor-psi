import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1249 :
    ∀ n : ℕ, 1249 ∣ n ^ 2 + 1 ↔ n % 1249 = 585 ∨ n % 1249 = 664 := by
  intro n
  haveI : Fact (1249).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1249) = (n : ZMod 1249) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (585 : ZMod 1249) ^ 2 + 1 = 0 := by
    rw [show (585 : ZMod 1249) ^ 2 + 1 = ((585 ^ 2 + 1 : ℕ) : ZMod 1249) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (585 ^ 2 + 1) 1249).mpr (by norm_num)
  have hb : (664 : ZMod 1249) ^ 2 + 1 = 0 := by
    rw [show (664 : ZMod 1249) ^ 2 + 1 = ((664 ^ 2 + 1 : ℕ) : ZMod 1249) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (664 ^ 2 + 1) 1249).mpr (by norm_num)
  have hsum : (585 : ZMod 1249) + (664 : ZMod 1249) = 0 := by
    rw [show (585 : ZMod 1249) + (664 : ZMod 1249) = ((585 + 664 : ℕ) : ZMod 1249) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (585 + 664) 1249).mpr (by norm_num)
  have hprod : (585 : ZMod 1249) * (664 : ZMod 1249) = 1 := by
    rw [← Nat.cast_one]
    rw [show (585 : ZMod 1249) * (664 : ZMod 1249) = ((585 * 664 : ℕ) : ZMod 1249) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (585 * 664) 1 1249).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1249, r ^ 2 + 1 = 0 ↔ r = (585 : ZMod 1249) ∨ r = (664 : ZMod 1249) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (585 : ZMod 1249)) * (r - (664 : ZMod 1249)) = 0 := by
        have hid : (r - (585 : ZMod 1249)) * (r - (664 : ZMod 1249)) = r ^ 2 + 1 := by
          calc (r - (585 : ZMod 1249)) * (r - (664 : ZMod 1249))
              = r ^ 2 - ((585 : ZMod 1249) + (664 : ZMod 1249)) * r
                  + (585 : ZMod 1249) * (664 : ZMod 1249) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1249, hcast, hroot (n : ZMod 1249)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 585 1249).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 585 < 1249)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 664 1249).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 664 < 1249)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 585 1249).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 585 < 1249)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 664 1249).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 664 < 1249)]
        exact h)
