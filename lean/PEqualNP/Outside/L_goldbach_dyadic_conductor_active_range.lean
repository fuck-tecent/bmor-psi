import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_dyadic_conductor_active_range :
    ∀ k j : ℕ, j ≤ k → (2 < (2 : ℕ) ^ k / 2 ^ j ↔ j + 2 ≤ k) := by
  intro k j hj
  have hquot : (2 : ℕ) ^ k / 2 ^ j = 2 ^ (k - j) := by
    calc
      (2 : ℕ) ^ k / 2 ^ j = (2 ^ (k - j) * 2 ^ j) / 2 ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      _ = 2 ^ (k - j) := Nat.mul_div_cancel _ (by positivity)
  rw [hquot]
  constructor
  · intro h
    by_contra hn
    have hm : k - j = 0 ∨ k - j = 1 := by omega
    rcases hm with hm | hm <;> rw [hm] at h <;> norm_num at h
  · intro h
    have hm : 2 ≤ k - j := by omega
    have hp : (2 : ℕ) ^ 2 ≤ 2 ^ (k - j) :=
      Nat.pow_le_pow_right (by decide) hm
    norm_num at hp
    omega

end PEqualNP.Outside
