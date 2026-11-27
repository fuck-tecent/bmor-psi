import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_13 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(231*u-520*v)/569 ∧ x+(231*u-520*v)/569≤L ∧ 0≤y+(520*u+231*v)/569 ∧ y+(520*u+231*v)/569≤L) ↔ (751:ℝ)/(2*569)≤x ∧ x≤L-(751:ℝ)/(2*569) ∧ (751:ℝ)/(2*569)≤y ∧ y≤L-(751:ℝ)/(2*569) := by
  intro x y L
  constructor
  · intro fits
    have left := (fits (-(1/2)) (1/2) (by norm_num) (by norm_num)).1
    have right := (fits (1/2) (-(1/2)) (by norm_num) (by norm_num)).2.1
    have bottom := (fits (-(1/2)) (-(1/2)) (by norm_num) (by norm_num)).2.2.1
    have top := (fits (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    exact ⟨by linarith only [left], by linarith only [right],
      by linarith only [bottom], by linarith only [top]⟩
  · rintro ⟨hx₀, hx₁, hy₀, hy₁⟩ u v hu hv
    obtain ⟨hu₀, hu₁⟩ := abs_le.mp hu
    obtain ⟨hv₀, hv₁⟩ := abs_le.mp hv
    exact ⟨by linarith only [hx₀, hu₀, hv₁], by linarith only [hx₁, hu₁, hv₀],
      by linarith only [hy₀, hu₀, hv₀], by linarith only [hy₁, hu₁, hv₁]⟩
