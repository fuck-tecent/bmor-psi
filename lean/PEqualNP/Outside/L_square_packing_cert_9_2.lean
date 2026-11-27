import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_9_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(77*u-36*v)/85 ∧ x+(77*u-36*v)/85≤L ∧ 0≤y+(36*u+77*v)/85 ∧ y+(36*u+77*v)/85≤L) ↔ (113:ℝ)/(2*85)≤x ∧ x≤L-(113:ℝ)/(2*85) ∧ (113:ℝ)/(2*85)≤y ∧ y≤L-(113:ℝ)/(2*85) := by
  intro x y L
  constructor
  · intro inside
    have pos : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have neg : |(-(1 / 2 : ℝ))| ≤ 1 / 2 := by norm_num
    have left := (inside (-(1 / 2)) (1 / 2) neg pos).1
    have right := (inside (1 / 2) (-(1 / 2)) pos neg).2.1
    have bottom := (inside (-(1 / 2)) (-(1 / 2)) neg neg).2.2.1
    have top := (inside (1 / 2) (1 / 2) pos pos).2.2.2
    exact ⟨by linarith only [left], by linarith only [right],
      by linarith only [bottom], by linarith only [top]⟩
  · rintro ⟨xlo, xhi, ylo, yhi⟩ u v hu hv
    rcases abs_le.mp hu with ⟨ulo, uhi⟩
    rcases abs_le.mp hv with ⟨vlo, vhi⟩
    exact ⟨by linarith only [xlo, ulo, vhi], by linarith only [xhi, uhi, vlo],
      by linarith only [ylo, ulo, vlo], by linarith only [yhi, uhi, vhi]⟩
