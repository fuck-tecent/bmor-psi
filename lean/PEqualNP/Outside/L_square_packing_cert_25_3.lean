import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_25_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(616*u-150*v)/634 ∧ x+(616*u-150*v)/634≤L ∧ 0≤y+(150*u+616*v)/634 ∧ y+(150*u+616*v)/634≤L) ↔ (766:ℝ)/(2*634)≤x ∧ x≤L-(766:ℝ)/(2*634) ∧ (766:ℝ)/(2*634)≤y ∧ y≤L-(766:ℝ)/(2*634) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (616 * (1/2:ℝ) - 150 * (-1/2:ℝ)) / 634 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (616 * (-1/2:ℝ) - 150 * (1/2:ℝ)) / 634 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (150 * (1/2:ℝ) + 616 * (1/2:ℝ)) / 634 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (150 * (-1/2:ℝ) + 616 * (-1/2:ℝ)) / 634 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (616+150)/(2*634).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
