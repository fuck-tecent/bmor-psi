import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_953 :
    ∀ n : ℕ, 953 ∣ n ^ 2 + 1 ↔ n % 953 = 442 ∨ n % 953 = 511 := by
  intro n
  haveI : Fact (953).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 953) = (n : ZMod 953) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (442 : ZMod 953) ^ 2 + 1 = 0 := by
    rw [show (442 : ZMod 953) ^ 2 + 1 = ((442 ^ 2 + 1 : ℕ) : ZMod 953) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (442 ^ 2 + 1) 953).mpr (by norm_num)
  have hb : (511 : ZMod 953) ^ 2 + 1 = 0 := by
    rw [show (511 : ZMod 953) ^ 2 + 1 = ((511 ^ 2 + 1 : ℕ) : ZMod 953) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (511 ^ 2 + 1) 953).mpr (by norm_num)
  have hsum : (442 : ZMod 953) + (511 : ZMod 953) = 0 := by
    rw [show (442 : ZMod 953) + (511 : ZMod 953) = ((442 + 511 : ℕ) : ZMod 953) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (442 + 511) 953).mpr (by norm_num)
  have hprod : (442 : ZMod 953) * (511 : ZMod 953) = 1 := by
    rw [← Nat.cast_one]
    rw [show (442 : ZMod 953) * (511 : ZMod 953) = ((442 * 511 : ℕ) : ZMod 953) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (442 * 511) 1 953).mpr (by norm_num)
  have hroot : ∀ r : ZMod 953, r ^ 2 + 1 = 0 ↔ r = (442 : ZMod 953) ∨ r = (511 : ZMod 953) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (442 : ZMod 953)) * (r - (511 : ZMod 953)) = 0 := by
        have hid : (r - (442 : ZMod 953)) * (r - (511 : ZMod 953)) = r ^ 2 + 1 := by
          calc (r - (442 : ZMod 953)) * (r - (511 : ZMod 953))
              = r ^ 2 - ((442 : ZMod 953) + (511 : ZMod 953)) * r
                  + (442 : ZMod 953) * (511 : ZMod 953) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 953, hcast, hroot (n : ZMod 953)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 442 953).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 442 < 953)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 511 953).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 511 < 953)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 442 953).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 442 < 953)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 511 953).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 511 < 953)]
        exact h)
