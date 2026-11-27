import Mathlib

/-!
# Rotation certificate for slope 50/624

A rotated unit square with rational rotation matrix `(624, 50; -50, 624)/626` fits inside the
axis-aligned square `[0, L] × [0, L]` with centre `(x, y)` exactly when both coordinates stay
`(a + b)/(2n) = 674` away from the boundary. The four corner instances give the lower bound in
both coordinates, and the bounds `|u|, |v| ≤ 1/2` give the converse.
-/

theorem PEqualNP.Outside.L_square_packing_cert_25_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(624*u-50*v)/626 ∧ x+(624*u-50*v)/626≤L ∧ 0≤y+(50*u+624*v)/626 ∧ y+(50*u+624*v)/626≤L) ↔ (674:ℝ)/(2*626)≤x ∧ x≤L-(674:ℝ)/(2*626) ∧ (674:ℝ)/(2*626)≤y ∧ y≤L-(674:ℝ)/(2*626) := by
  intro x y L
  constructor
  · intro h
    have e1 := h (1/2) (1/2) (by norm_num) (by norm_num)
    have e2 := h (1/2) (-(1/2)) (by norm_num) (by norm_num)
    have e3 := h (-(1/2)) (1/2) (by norm_num) (by norm_num)
    have e4 := h (-(1/2)) (-(1/2)) (by norm_num) (by norm_num)
    norm_num at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    rw [abs_le] at hu hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hu.1, hu.2, hv.1, hv.2]
