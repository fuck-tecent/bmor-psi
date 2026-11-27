import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_23_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(528*u-46*v)/530 ∧ x+(528*u-46*v)/530≤L ∧ 0≤y+(46*u+528*v)/530 ∧ y+(46*u+528*v)/530≤L) ↔ (574:ℝ)/(2*530)≤x ∧ x≤L-(574:ℝ)/(2*530) ∧ (574:ℝ)/(2*530)≤y ∧ y≤L-(574:ℝ)/(2*530) := by
  intro x y L
  have hnorm : (574:ℝ) / (2 * 530) = 287 / 530 := by norm_num
  constructor
  · intro h
    -- The four corners of the unit square give both one-sided bounds.
    have hxL : x + (528 * (1/2:ℝ) - 46 * (-1/2:ℝ)) / 530 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (528 * (-1/2:ℝ) - 46 * (1/2:ℝ)) / 530 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (46 * (1/2:ℝ) + 528 * (1/2:ℝ)) / 530 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (46 * (-1/2:ℝ) + 528 * (-1/2:ℝ)) / 530 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- The rotation is orthogonal, so every corner displacement has modulus at most 287/530.
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
