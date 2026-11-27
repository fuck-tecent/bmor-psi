import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_5_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(21*u-20*v)/29 ∧ x+(21*u-20*v)/29≤L ∧ 0≤y+(20*u+21*v)/29 ∧ y+(20*u+21*v)/29≤L) ↔ (41:ℝ)/(2*29)≤x ∧ x≤L-(41:ℝ)/(2*29) ∧ (41:ℝ)/(2*29)≤y ∧ y≤L-(41:ℝ)/(2*29) := by
  intro x y L
  constructor
  · intro inside
    have posHalf : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have negHalf : |(-(1 / 2) : ℝ)| ≤ 1 / 2 := by norm_num
    have left := (inside (-(1 / 2)) (1 / 2) negHalf posHalf).1
    have right := (inside (1 / 2) (-(1 / 2)) posHalf negHalf).2.1
    have bottom := (inside (-(1 / 2)) (-(1 / 2)) negHalf negHalf).2.2.1
    have top := (inside (1 / 2) (1 / 2) posHalf posHalf).2.2.2
    exact ⟨by linarith only [left], by linarith only [right],
      by linarith only [bottom], by linarith only [top]⟩
  · rintro ⟨hxMin, hxMax, hyMin, hyMax⟩ u v hu hv
    obtain ⟨huMin, huMax⟩ := abs_le.mp hu
    obtain ⟨hvMin, hvMax⟩ := abs_le.mp hv
    exact ⟨by linarith only [hxMin, huMin, hvMax],
      by linarith only [hxMax, huMax, hvMin],
      by linarith only [hyMin, huMin, hvMin],
      by linarith only [hyMax, huMax, hvMax]⟩
