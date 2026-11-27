import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1181 :
    ∀ n : ℕ, 1181 ∣ n ^ 2 + 1 ↔ n % 1181 = 243 ∨ n % 1181 = 938 := by
  intro n
  haveI : Fact (1181).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1181) = (n : ZMod 1181) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (243 : ZMod 1181) ^ 2 + 1 = 0 := by
    rw [show (243 : ZMod 1181) ^ 2 + 1 = ((243 ^ 2 + 1 : ℕ) : ZMod 1181) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (243 ^ 2 + 1) 1181).mpr (by norm_num)
  have hb : (938 : ZMod 1181) ^ 2 + 1 = 0 := by
    rw [show (938 : ZMod 1181) ^ 2 + 1 = ((938 ^ 2 + 1 : ℕ) : ZMod 1181) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (938 ^ 2 + 1) 1181).mpr (by norm_num)
  have hsum : (243 : ZMod 1181) + (938 : ZMod 1181) = 0 := by
    rw [show (243 : ZMod 1181) + (938 : ZMod 1181) = ((243 + 938 : ℕ) : ZMod 1181) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (243 + 938) 1181).mpr (by norm_num)
  have hprod : (243 : ZMod 1181) * (938 : ZMod 1181) = 1 := by
    rw [← Nat.cast_one]
    rw [show (243 : ZMod 1181) * (938 : ZMod 1181) = ((243 * 938 : ℕ) : ZMod 1181) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (243 * 938) 1 1181).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1181, r ^ 2 + 1 = 0 ↔ r = (243 : ZMod 1181) ∨ r = (938 : ZMod 1181) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (243 : ZMod 1181)) * (r - (938 : ZMod 1181)) = 0 := by
        have hid : (r - (243 : ZMod 1181)) * (r - (938 : ZMod 1181)) = r ^ 2 + 1 := by
          calc (r - (243 : ZMod 1181)) * (r - (938 : ZMod 1181))
              = r ^ 2 - ((243 : ZMod 1181) + (938 : ZMod 1181)) * r
                  + (243 : ZMod 1181) * (938 : ZMod 1181) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1181, hcast, hroot (n : ZMod 1181)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 243 1181).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 243 < 1181)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 938 1181).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 938 < 1181)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 243 1181).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 243 < 1181)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 938 1181).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 938 < 1181)]
        exact h)
