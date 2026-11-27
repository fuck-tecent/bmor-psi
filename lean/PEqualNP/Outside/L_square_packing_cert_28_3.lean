import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_28_3 :
  ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(775*u-168*v)/793 ∧ x+(775*u-168*v)/793≤L ∧ 0≤y+(168*u+775*v)/793 ∧ y+(168*u+775*v)/793≤L) ↔ (943:ℝ)/(2*793)≤x ∧ x≤L-(943:ℝ)/(2*793) ∧ (943:ℝ)/(2*793)≤y ∧ y≤L-(943:ℝ)/(2*793) := by
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
