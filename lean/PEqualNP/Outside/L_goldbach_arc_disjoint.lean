import Mathlib

theorem PEqualNP.Outside.L_goldbach_arc_disjoint :
    ∀ (a b q r Q n : ℕ) (t : ℝ), 0<q → 0<r → q≤Q → r≤Q → 2*Q^2<n → a*r ≠ b*q → |t-(a:ℝ)/(q:ℝ)|≤(Q:ℝ)/((q:ℝ)*n) → (Q:ℝ)/((r:ℝ)*n) < |t-(b:ℝ)/(r:ℝ)| := by
  intro a b q r Q n t hq hr hqQ hrQ hn hdistinct ha
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : Q * r + Q * q < n := by
    nlinarith [Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q * n) + Q / (r * n) < 1 / (q * r) := calc
    _ = ((Q : ℝ) * r + Q * q) / (q * r * n) := by field_simp
    _ < (n : ℝ) / (q * r * n) :=
      (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = 1 / (q * r) := by field_simp
  have hsep : 1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - b / r| := by
    have hdiff : (a : ℝ) / q - b / r = (a * r - b * q) / (q * r) := by
      field_simp
    rw [hdiff, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hdistinct with hab | hba
    · have hgap : (a : ℝ) * r + 1 ≤ b * q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a : ℝ) * r - b * q)]
    · have hgap : (b : ℝ) * q + 1 ≤ a * r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a : ℝ) * r - b * q)]
  have htriangle := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) t] at htriangle
  linarith
