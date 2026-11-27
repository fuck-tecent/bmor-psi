import Mathlib

theorem PEqualNP.Outside.L_goldbach_farey_separation :
    ∀ a b q r : ℕ, 0<q → 0<r → a*r ≠ b*q → 1/((q:ℝ)*(r:ℝ)) ≤ |(a:ℝ)/(q:ℝ)-(b:ℝ)/(r:ℝ)| := by
  intro a b q r hq hr hne
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hcross : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hstep : (a : ℝ) * r + 1 ≤ (b : ℝ) * q := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (neg_le_abs _)
    · have hstep : (b : ℝ) * q + 1 ≤ (a : ℝ) * r := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (le_abs_self _)
  have hquot : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by
    field_simp
  rw [hquot, abs_div, abs_of_pos (mul_pos hq' hr')]
  exact div_le_div_of_nonneg_right hcross (mul_pos hq' hr').le
