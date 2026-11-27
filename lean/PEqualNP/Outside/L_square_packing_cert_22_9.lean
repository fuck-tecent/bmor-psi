import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_22_9 :
  ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(403*u-396*v)/565 ∧ x+(403*u-396*v)/565≤L ∧ 0≤y+(396*u+403*v)/565 ∧ y+(396*u+403*v)/565≤L) ↔ (799:ℝ)/(2*565)≤x ∧ x≤L-(799:ℝ)/(2*565) ∧ (799:ℝ)/(2*565)≤y ∧ y≤L-(799:ℝ)/(2*565) := by
  intro x y L
  constructor
  · intro h
    have h1 := h (-1 / 2) (1 / 2) (by norm_num) (by norm_num)
    have h2 := h (1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h3 := h (-1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h4 := h (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    have ⟨hu1, hu2⟩ := abs_le.mp hu
    have ⟨hv1, hv2⟩ := abs_le.mp hv
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
