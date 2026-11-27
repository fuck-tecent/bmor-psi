import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_23_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(525*u-92*v)/533 ∧ x+(525*u-92*v)/533≤L ∧ 0≤y+(92*u+525*v)/533 ∧ y+(92*u+525*v)/533≤L) ↔ (617:ℝ)/(2*533)≤x ∧ x≤L-(617:ℝ)/(2*533) ∧ (617:ℝ)/(2*533)≤y ∧ y≤L-(617:ℝ)/(2*533) := by
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
