import Mathlib

/-!
# Rotation certificate for slope 180/299

A rotated unit square with rational rotation matrix `(299, 180; -180, 299)/349` fits inside the
axis-aligned square `[0, L] × [0, L]` with centre `(x, y)` exactly when both coordinates stay
`(a + b)/(2n) = 479` away from the boundary. The four corner instances give the lower bound in
both coordinates, and the bounds `|u|, |v| ≤ 1/2` give the converse.
-/

theorem PEqualNP.Outside.L_square_packing_cert_18_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(299*u-180*v)/349 ∧ x+(299*u-180*v)/349≤L ∧ 0≤y+(180*u+299*v)/349 ∧ y+(180*u+299*v)/349≤L) ↔ (479:ℝ)/(2*349)≤x ∧ x≤L-(479:ℝ)/(2*349) ∧ (479:ℝ)/(2*349)≤y ∧ y≤L-(479:ℝ)/(2*349) := by
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
