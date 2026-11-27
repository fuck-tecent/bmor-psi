import Mathlib

namespace PEqualNP.Outside

theorem L_square_packing_scaled_box_two_axes :
    (∀ A B D x y L : ℝ, 0≤A → 0≤B → 0<D → (let R := (A+B)/(2*D); (∀ u v : ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(A*u-B*v)/D ∧ x+(A*u-B*v)/D≤L ∧ 0≤y+(B*u+A*v)/D ∧ y+(B*u+A*v)/D≤L) ↔ R≤x ∧ x≤L-R ∧ R≤y ∧ y≤L-R)) := by
  intro A B D x y L hA hB hD R
  have hD_ne : D ≠ 0 := hD.ne'
  constructor
  · intro h
    have hp : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have hn : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have h1 := (h (-1 / 2) (1 / 2) hn hp).1
    have h2 := (h (1 / 2) (-1 / 2) hp hn).2.1
    have h3 := (h (-1 / 2) (-1 / 2) hn hn).2.2.1
    have h4 := (h (1 / 2) (1 / 2) hp hp).2.2.2
    have eq1 : x + (A * (-1 / 2) - B * (1 / 2)) / D = x - R := by
      change x + (A * (-1 / 2) - B * (1 / 2)) / D = x - (A + B) / (2 * D)
      field_simp [hD_ne]
      ring
    have eq2 : x + (A * (1 / 2) - B * (-1 / 2)) / D = x + R := by
      change x + (A * (1 / 2) - B * (-1 / 2)) / D = x + (A + B) / (2 * D)
      field_simp [hD_ne]
      ring
    have eq3 : y + (B * (-1 / 2) + A * (-1 / 2)) / D = y - R := by
      change y + (B * (-1 / 2) + A * (-1 / 2)) / D = y - (A + B) / (2 * D)
      field_simp [hD_ne]
      ring
    have eq4 : y + (B * (1 / 2) + A * (1 / 2)) / D = y + R := by
      change y + (B * (1 / 2) + A * (1 / 2)) / D = y + (A + B) / (2 * D)
      field_simp [hD_ne]
      ring
    rw [eq1] at h1
    rw [eq2] at h2
    rw [eq3] at h3
    rw [eq4] at h4
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    rcases abs_le.mp hu with ⟨hu1, hu2⟩
    rcases abs_le.mp hv with ⟨hv1, hv2⟩
    have hau1 : A * (-(1 / 2)) ≤ A * u := mul_le_mul_of_nonneg_left hu1 hA
    have hau2 : A * u ≤ A * (1 / 2) := mul_le_mul_of_nonneg_left hu2 hA
    have hbv1 : B * (-(1 / 2)) ≤ B * v := mul_le_mul_of_nonneg_left hv1 hB
    have hbv2 : B * v ≤ B * (1 / 2) := mul_le_mul_of_nonneg_left hv2 hB
    have hbu1 : B * (-(1 / 2)) ≤ B * u := mul_le_mul_of_nonneg_left hu1 hB
    have hbu2 : B * u ≤ B * (1 / 2) := mul_le_mul_of_nonneg_left hu2 hB
    have hav1 : A * (-(1 / 2)) ≤ A * v := mul_le_mul_of_nonneg_left hv1 hA
    have hav2 : A * v ≤ A * (1 / 2) := mul_le_mul_of_nonneg_left hv2 hA
    have hR_pos : ((A + B) / 2) / D = R := by
      change ((A + B) / 2) / D = (A + B) / (2 * D)
      field_simp [hD_ne]
    have hR_neg : (-(A + B) / 2) / D = -R := by
      change (-(A + B) / 2) / D = -((A + B) / (2 * D))
      field_simp [hD_ne]
    have hd1_lo : -R ≤ (A * u - B * v) / D := by
      rw [← hR_neg]
      exact div_le_div_of_nonneg_right (by linarith) hD.le
    have hd1_hi : (A * u - B * v) / D ≤ R := by
      rw [← hR_pos]
      exact div_le_div_of_nonneg_right (by linarith) hD.le
    have hd2_lo : -R ≤ (B * u + A * v) / D := by
      rw [← hR_neg]
      exact div_le_div_of_nonneg_right (by linarith) hD.le
    have hd2_hi : (B * u + A * v) / D ≤ R := by
      rw [← hR_pos]
      exact div_le_div_of_nonneg_right (by linarith) hD.le
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end PEqualNP.Outside
