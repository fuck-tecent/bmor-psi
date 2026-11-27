import Mathlib

/-!
# Exact corner bound for a rotated box with arbitrary positive scale

For arbitrary `A, B ≥ 0` and `D > 0`, the linear form `(A * u - B * v) / D` over the closed
square `|u|, |v| ≤ 1/2` is contained in `[0, L]` after translation by `x` exactly when both
coordinates of the centre stay `(A + B) / (2 * D)` away from the boundary.

The two opposite corner instances `(-1/2, 1/2)` and `(1/2, -1/2)` give the lower and the upper
bound; the estimate `|A * u - B * v| ≤ (A + B) / 2` gives the converse.
-/

theorem PEqualNP.Outside.L_square_packing_scaled_box_extrema :
    ∀ A B D x L : ℝ, 0≤A → 0≤B → 0<D → ((∀ u v : ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(A*u-B*v)/D ∧ x+(A*u-B*v)/D≤L) ↔ (A+B)/(2*D)≤x ∧ x≤L-(A+B)/(2*D)) := by
  intro A B D x L hA hB hD
  have hD0 : (0:ℝ) < D := hD
  have h2D : (0:ℝ) < 2 * D := by linarith
  constructor
  · intro h
    have e1 := h (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)
    have e2 := h (1 / 2) (-(1 / 2)) (by norm_num) (by norm_num)
    have h1 : (-x) * D ≤ A * (-(1 / 2)) - B * (1 / 2) :=
      (le_div_iff₀ hD0).1 (by linarith [e1.1])
    have h2 : A * (1 / 2) - B * (-(1 / 2)) ≤ (L - x) * D :=
      (div_le_iff₀ hD0).1 (by linarith [e2.2])
    constructor
    · rw [div_le_iff₀ h2D]
      nlinarith
    · have g : (A + B) / (2 * D) ≤ L - x := by
        rw [div_le_iff₀ h2D]
        nlinarith
      linarith
  · rintro ⟨hx1, hx2⟩ u v hu hv
    rw [abs_le] at hu hv
    have Au1 : A * (-(1 / 2)) ≤ A * u := mul_le_mul_of_nonneg_left hu.1 hA
    have Au2 : A * u ≤ A * (1 / 2) := mul_le_mul_of_nonneg_left hu.2 hA
    have Bv1 : B * (-(1 / 2)) ≤ B * v := mul_le_mul_of_nonneg_left hv.1 hB
    have Bv2 : B * v ≤ B * (1 / 2) := mul_le_mul_of_nonneg_left hv.2 hB
    have hx1' : A + B ≤ x * (2 * D) := (div_le_iff₀ h2D).1 hx1
    have hx2' : A + B ≤ (L - x) * (2 * D) := (div_le_iff₀ h2D).1 (by linarith [hx2])
    constructor
    · have hlow := (le_div_iff₀ hD0).2 (show (-x) * D ≤ A * u - B * v by nlinarith)
      linarith
    · have hupp := (div_le_iff₀ hD0).2 (show A * u - B * v ≤ (L - x) * D by nlinarith)
      linarith
