import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_13_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(165*u-52*v)/173 ∧ x+(165*u-52*v)/173≤L ∧ 0≤y+(52*u+165*v)/173 ∧ y+(52*u+165*v)/173≤L) ↔ (217:ℝ)/(2*173)≤x ∧ x≤L-(217:ℝ)/(2*173) ∧ (217:ℝ)/(2*173)≤y ∧ y≤L-(217:ℝ)/(2*173) := by
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
    have hxabs : |(165:ℝ)*u - (52:ℝ)*v| ≤ (217:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(52:ℝ)*u + (165:ℝ)*v| ≤ (217:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((165:ℝ)*u - (52:ℝ)*v)/173| ≤ (217:ℝ)/(2*173) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (173:ℝ))]
      linarith
    have hydiv : |((52:ℝ)*u + (165:ℝ)*v)/173| ≤ (217:ℝ)/(2*173) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (173:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
