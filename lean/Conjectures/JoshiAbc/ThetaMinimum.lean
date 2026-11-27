import Mathlib

noncomputable section

theorem Conjectures.JoshiAbc.ThetaMinimum :
  ∀ (l j : ℚ), 0 < j → j < l → let b := fun (n : ℤ) => (n:ℚ)*(n+1)/2+(2*(n:ℚ)+1)*j/(2*l); ∀ n : ℤ, n ≠ -1 → b (-1) < b n := by
  intro l j hj hjl
  dsimp only
  intro n hn
  have hl : 0 < l := lt_trans hj hjl
  have hncase : n ≤ -2 ∨ 0 ≤ n := by omega
  have hnl : (n : ℚ) ≤ -2 ∨ 0 ≤ (n : ℚ) := by exact_mod_cast hncase
  rcases hnl with hneg | hpos
  · have hn1 : (n : ℚ)+1 < 0 := by linarith
    have hn2 : l*(n : ℚ)+2*j < 0 := by nlinarith [mul_nonneg hl.le (show 0 ≤ -(n : ℚ)-2 by linarith)]
    have hp := mul_pos_of_neg_of_neg hn1 hn2
    field_simp
    push_cast
    nlinarith
  · have hn1 : 0 < (n : ℚ)+1 := by linarith
    have hn2 : 0 < l*(n : ℚ)+2*j := by nlinarith [mul_nonneg hl.le hpos]
    have hp := mul_pos hn1 hn2
    field_simp
    push_cast
    nlinarith
