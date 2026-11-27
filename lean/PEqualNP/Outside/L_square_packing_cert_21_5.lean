import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_21_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(416*u-210*v)/466 ∧ x+(416*u-210*v)/466≤L ∧ 0≤y+(210*u+416*v)/466 ∧ y+(210*u+416*v)/466≤L) ↔ (626:ℝ)/(2*466)≤x ∧ x≤L-(626:ℝ)/(2*466) ∧ (626:ℝ)/(2*466)≤y ∧ y≤L-(626:ℝ)/(2*466) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (416 * (1/2:ℝ) - 210 * (-1/2:ℝ)) / 466 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (416 * (-1/2:ℝ) - 210 * (1/2:ℝ)) / 466 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (210 * (1/2:ℝ) + 416 * (1/2:ℝ)) / 466 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (210 * (-1/2:ℝ) + 416 * (-1/2:ℝ)) / 466 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (416+210)/(2*466).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
