import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_22_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(475*u-132*v)/493 ∧ x+(475*u-132*v)/493≤L ∧ 0≤y+(132*u+475*v)/493 ∧ y+(132*u+475*v)/493≤L) ↔ (607:ℝ)/(2*493)≤x ∧ x≤L-(607:ℝ)/(2*493) ∧ (607:ℝ)/(2*493)≤y ∧ y≤L-(607:ℝ)/(2*493) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (475 * (1/2:ℝ) - 132 * (-1/2:ℝ)) / 493 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (475 * (-1/2:ℝ) - 132 * (1/2:ℝ)) / 493 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (132 * (1/2:ℝ) + 475 * (1/2:ℝ)) / 493 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (132 * (-1/2:ℝ) + 475 * (-1/2:ℝ)) / 493 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (475+132)/(2*493).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
