import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_23_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(504*u-230*v)/554 ∧ x+(504*u-230*v)/554≤L ∧ 0≤y+(230*u+504*v)/554 ∧ y+(230*u+504*v)/554≤L) ↔ (734:ℝ)/(2*554)≤x ∧ x≤L-(734:ℝ)/(2*554) ∧ (734:ℝ)/(2*554)≤y ∧ y≤L-(734:ℝ)/(2*554) := by
  intro x y L
  constructor
  · intro h
    have h1 := h (-1 / 2) (1 / 2) (by norm_num) (by norm_num)
    have h2 := h (1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h3 := h (-1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h4 := h (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro h u v hu hv
    obtain ⟨hx1, hx2, hy1, hy2⟩ := h
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    obtain ⟨hv1, hv2⟩ := abs_le.mp hv
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
