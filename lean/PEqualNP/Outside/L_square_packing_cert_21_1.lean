import Mathlib

/-!
# Rotation certificate for slope 42/440

A rotated unit square with rational rotation matrix `(440, 42; -42, 440)/442` fits inside the
axis-aligned square `[0, L] × [0, L]` with centre `(x, y)` exactly when both coordinates stay
`(a + b)/(2n) = 482` away from the boundary. The four corner instances give the lower bound in
both coordinates, and the bounds `|u|, |v| ≤ 1/2` give the converse.
-/

theorem PEqualNP.Outside.L_square_packing_cert_21_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(440*u-42*v)/442 ∧ x+(440*u-42*v)/442≤L ∧ 0≤y+(42*u+440*v)/442 ∧ y+(42*u+440*v)/442≤L) ↔ (482:ℝ)/(2*442)≤x ∧ x≤L-(482:ℝ)/(2*442) ∧ (482:ℝ)/(2*442)≤y ∧ y≤L-(482:ℝ)/(2*442) := by
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
