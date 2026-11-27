import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_12_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(143*u-24*v)/145 ∧ x+(143*u-24*v)/145≤L ∧ 0≤y+(24*u+143*v)/145 ∧ y+(24*u+143*v)/145≤L) ↔ (167:ℝ)/(2*145)≤x ∧ x≤L-(167:ℝ)/(2*145) ∧ (167:ℝ)/(2*145)≤y ∧ y≤L-(167:ℝ)/(2*145) := by
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
    have hxabs : |(143:ℝ)*u - (24:ℝ)*v| ≤ (167:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(24:ℝ)*u + (143:ℝ)*v| ≤ (167:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((143:ℝ)*u - (24:ℝ)*v)/145| ≤ (167:ℝ)/(2*145) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (145:ℝ))]
      linarith
    have hydiv : |((24:ℝ)*u + (143:ℝ)*v)/145| ≤ (167:ℝ)/(2*145) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (145:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
