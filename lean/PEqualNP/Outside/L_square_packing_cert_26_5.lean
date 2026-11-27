import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_26_5 :
  ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(651*u-260*v)/701 ∧ x+(651*u-260*v)/701≤L ∧ 0≤y+(260*u+651*v)/701 ∧ y+(260*u+651*v)/701≤L) ↔ (911:ℝ)/(2*701)≤x ∧ x≤L-(911:ℝ)/(2*701) ∧ (911:ℝ)/(2*701)≤y ∧ y≤L-(911:ℝ)/(2*701) := by
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
