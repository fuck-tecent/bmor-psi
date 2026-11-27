import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_21_11 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(320*u-462*v)/562 ∧ x+(320*u-462*v)/562≤L ∧ 0≤y+(462*u+320*v)/562 ∧ y+(462*u+320*v)/562≤L) ↔ (782:ℝ)/(2*562)≤x ∧ x≤L-(782:ℝ)/(2*562) ∧ (782:ℝ)/(2*562)≤y ∧ y≤L-(782:ℝ)/(2*562) := by
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
