import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_17_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(285*u-68*v)/293 ∧ x+(285*u-68*v)/293≤L ∧ 0≤y+(68*u+285*v)/293 ∧ y+(68*u+285*v)/293≤L) ↔ (353:ℝ)/(2*293)≤x ∧ x≤L-(353:ℝ)/(2*293) ∧ (353:ℝ)/(2*293)≤y ∧ y≤L-(353:ℝ)/(2*293) := by
  intro x y L
  constructor
  · intro h
    obtain ⟨hx1, -, -, -⟩ := h (-(1/2)) (1/2) (by norm_num) (by norm_num)
    obtain ⟨-, hx2, -, -⟩ := h (1/2) (-(1/2)) (by norm_num) (by norm_num)
    obtain ⟨-, -, hy1, -⟩ := h (-(1/2)) (-(1/2)) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, hy2⟩ := h (1/2) (1/2) (by norm_num) (by norm_num)
    norm_num at hx1 hx2 hy1 hy2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro h u v hu hv
    obtain ⟨hx1, hx2, hy1, hy2⟩ := h
    have hu1 : -((1:ℝ)/2) ≤ u := by linarith [neg_abs_le u]
    have hu2 : u ≤ (1:ℝ)/2 := by linarith [le_abs_self u]
    have hv1 : -((1:ℝ)/2) ≤ v := by linarith [neg_abs_le v]
    have hv2 : v ≤ (1:ℝ)/2 := by linarith [le_abs_self v]
    have hxabs : |(285:ℝ)*u - (68:ℝ)*v| ≤ (353:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(68:ℝ)*u + (285:ℝ)*v| ≤ (353:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((285:ℝ)*u - (68:ℝ)*v)/293| ≤ (353:ℝ)/(2*293) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (293:ℝ))]
      linarith
    have hydiv : |((68:ℝ)*u + (285:ℝ)*v)/293| ≤ (353:ℝ)/(2*293) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (293:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
