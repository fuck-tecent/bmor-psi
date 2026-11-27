import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_13_4 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(153*u-104*v)/185 ∧ x+(153*u-104*v)/185≤L ∧ 0≤y+(104*u+153*v)/185 ∧ y+(104*u+153*v)/185≤L) ↔ (257:ℝ)/(2*185)≤x ∧ x≤L-(257:ℝ)/(2*185) ∧ (257:ℝ)/(2*185)≤y ∧ y≤L-(257:ℝ)/(2*185) := by
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
    have hxabs : |(153:ℝ)*u - (104:ℝ)*v| ≤ (257:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(104:ℝ)*u + (153:ℝ)*v| ≤ (257:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((153:ℝ)*u - (104:ℝ)*v)/185| ≤ (257:ℝ)/(2*185) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (185:ℝ))]
      linarith
    have hydiv : |((104:ℝ)*u + (153:ℝ)*v)/185| ≤ (257:ℝ)/(2*185) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (185:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
