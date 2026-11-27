import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_349 :
    ∀ n : ℕ, 349 ∣ n ^ 2 + 1 ↔ n % 349 = 136 ∨ n % 349 = 213 := by
  intro n
  haveI : Fact (349).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 349) = (n : ZMod 349) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (136 : ZMod 349) ^ 2 + 1 = 0 := by
    rw [show (136 : ZMod 349) ^ 2 + 1 = ((136 ^ 2 + 1 : ℕ) : ZMod 349) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (136 ^ 2 + 1) 349).mpr (by norm_num)
  have hb : (213 : ZMod 349) ^ 2 + 1 = 0 := by
    rw [show (213 : ZMod 349) ^ 2 + 1 = ((213 ^ 2 + 1 : ℕ) : ZMod 349) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (213 ^ 2 + 1) 349).mpr (by norm_num)
  have hsum : (136 : ZMod 349) + (213 : ZMod 349) = 0 := by
    rw [show (136 : ZMod 349) + (213 : ZMod 349) = ((136 + 213 : ℕ) : ZMod 349) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (136 + 213) 349).mpr (by norm_num)
  have hprod : (136 : ZMod 349) * (213 : ZMod 349) = 1 := by
    rw [← Nat.cast_one]
    rw [show (136 : ZMod 349) * (213 : ZMod 349) = ((136 * 213 : ℕ) : ZMod 349) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (136 * 213) 1 349).mpr (by norm_num)
  have hroot : ∀ r : ZMod 349, r ^ 2 + 1 = 0 ↔ r = (136 : ZMod 349) ∨ r = (213 : ZMod 349) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (136 : ZMod 349)) * (r - (213 : ZMod 349)) = 0 := by
        have hid : (r - (136 : ZMod 349)) * (r - (213 : ZMod 349)) = r ^ 2 + 1 := by
          calc (r - (136 : ZMod 349)) * (r - (213 : ZMod 349))
              = r ^ 2 - ((136 : ZMod 349) + (213 : ZMod 349)) * r
                  + (136 : ZMod 349) * (213 : ZMod 349) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 349, hcast, hroot (n : ZMod 349)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 136 349).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 136 < 349)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 213 349).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 213 < 349)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 136 349).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 136 < 349)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 213 349).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 213 < 349)]
        exact h)
