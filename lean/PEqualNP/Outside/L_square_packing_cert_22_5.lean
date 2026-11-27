import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_22_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(459*u-220*v)/509 ∧ x+(459*u-220*v)/509≤L ∧ 0≤y+(220*u+459*v)/509 ∧ y+(220*u+459*v)/509≤L) ↔ (679:ℝ)/(2*509)≤x ∧ x≤L-(679:ℝ)/(2*509) ∧ (679:ℝ)/(2*509)≤y ∧ y≤L-(679:ℝ)/(2*509) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (459 * (1/2:ℝ) - 220 * (-1/2:ℝ)) / 509 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (459 * (-1/2:ℝ) - 220 * (1/2:ℝ)) / 509 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (220 * (1/2:ℝ) + 459 * (1/2:ℝ)) / 509 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (220 * (-1/2:ℝ) + 459 * (-1/2:ℝ)) / 509 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (459+220)/(2*509).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
