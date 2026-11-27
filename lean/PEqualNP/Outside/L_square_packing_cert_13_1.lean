import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_square_packing_cert_13_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(168*u-26*v)/170 ∧ x+(168*u-26*v)/170≤L ∧ 0≤y+(26*u+168*v)/170 ∧ y+(26*u+168*v)/170≤L) ↔ (194:ℝ)/(2*170)≤x ∧ x≤L-(194:ℝ)/(2*170) ∧ (194:ℝ)/(2*170)≤y ∧ y≤L-(194:ℝ)/(2*170) := by
  intro x y L
  constructor
  · intro H
    have hx1 := (H (-1 / 2) (1 / 2) (by norm_num) (by norm_num)).1
    have hx2 := (H (1 / 2) (-1 / 2) (by norm_num) (by norm_num)).2.1
    have hy1 := (H (-1 / 2) (-1 / 2) (by norm_num) (by norm_num)).2.2.1
    have hy2 := (H (1 / 2) (1 / 2) (by norm_num) (by norm_num)).2.2.2
    norm_num at hx1 hx2 hy1 hy2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    have hu' := abs_le.mp hu
    have hv' := abs_le.mp hv
    have hxlo : -((194 : ℝ) / (2 * 170 * 1)) ≤ (168 * u - 26 * v) / 170 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hxhi : (168 * u - 26 * v) / 170 ≤ ((194 : ℝ) / (2 * 170)) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hylo : -((194 : ℝ) / (2 * 170 * 1)) ≤ (26 * u + 168 * v) / 170 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hyhi : (26 * u + 168 * v) / 170 ≤ ((194 : ℝ) / (2 * 170)) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
