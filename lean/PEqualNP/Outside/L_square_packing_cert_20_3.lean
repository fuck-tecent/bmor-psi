import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(391*u-120*v)/409 ∧ x+(391*u-120*v)/409≤L ∧ 0≤y+(120*u+391*v)/409 ∧ y+(120*u+391*v)/409≤L) ↔ (511:ℝ)/(2*409)≤x ∧ x≤L-(511:ℝ)/(2*409) ∧ (511:ℝ)/(2*409)≤y ∧ y≤L-(511:ℝ)/(2*409) := by
  intro x y L
  constructor
  · intro h
    have h1 := (h (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)).1
    have h2 := (h (1 / 2) (-(1 / 2)) (by norm_num) (by norm_num)).2.1
    have h3 := (h (-(1 / 2)) (-(1 / 2)) (by norm_num) (by norm_num)).2.2.1
    have h4 := (h (1 / 2) (1 / 2) (by norm_num) (by norm_num)).2.2.2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    obtain ⟨hv1, hv2⟩ := abs_le.mp hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
