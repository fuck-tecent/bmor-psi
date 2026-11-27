import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_9_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(80*u-18*v)/82 ∧ x+(80*u-18*v)/82≤L ∧ 0≤y+(18*u+80*v)/82 ∧ y+(18*u+80*v)/82≤L) ↔ (98:ℝ)/(2*82)≤x ∧ x≤L-(98:ℝ)/(2*82) ∧ (98:ℝ)/(2*82)≤y ∧ y≤L-(98:ℝ)/(2*82) := by
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
    have hxabs : |(80:ℝ)*u - (18:ℝ)*v| ≤ (98:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(18:ℝ)*u + (80:ℝ)*v| ≤ (98:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((80:ℝ)*u - (18:ℝ)*v)/82| ≤ (98:ℝ)/(2*82) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (82:ℝ))]
      linarith
    have hydiv : |((18:ℝ)*u + (80:ℝ)*v)/82| ≤ (98:ℝ)/(2*82) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (82:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
