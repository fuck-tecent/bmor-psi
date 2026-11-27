import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_16_11 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(135*u-352*v)/377 ∧ x+(135*u-352*v)/377≤L ∧ 0≤y+(352*u+135*v)/377 ∧ y+(352*u+135*v)/377≤L) ↔ (487:ℝ)/(2*377)≤x ∧ x≤L-(487:ℝ)/(2*377) ∧ (487:ℝ)/(2*377)≤y ∧ y≤L-(487:ℝ)/(2*377) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (135 * (1/2:ℝ) - 352 * (-1/2:ℝ)) / 377 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (135 * (-1/2:ℝ) - 352 * (1/2:ℝ)) / 377 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (352 * (1/2:ℝ) + 135 * (1/2:ℝ)) / 377 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (352 * (-1/2:ℝ) + 135 * (-1/2:ℝ)) / 377 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (135+352)/(2*377).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
