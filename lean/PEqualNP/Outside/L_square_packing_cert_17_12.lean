import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_17_12 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(145*u-408*v)/433 ∧ x+(145*u-408*v)/433≤L ∧ 0≤y+(408*u+145*v)/433 ∧ y+(408*u+145*v)/433≤L) ↔ (553:ℝ)/(2*433)≤x ∧ x≤L-(553:ℝ)/(2*433) ∧ (553:ℝ)/(2*433)≤y ∧ y≤L-(553:ℝ)/(2*433) := by
  intro x y L
  constructor
  · intro h
    have hxmin := h (-(1/2):ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
    have hxmax := h (1/2:ℝ) (-(1/2):ℝ) (by norm_num) (by norm_num)
    have hymin := h (-(1/2):ℝ) (-(1/2):ℝ) (by norm_num) (by norm_num)
    have hymax := h (1/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := hxmin.1
      norm_num at h ⊢
      linarith
    · have h := hxmax.2.1
      norm_num at h ⊢
      linarith
    · have h := hymin.2.2.1
      norm_num at h ⊢
      linarith
    · have h := hymax.2.2.2
      norm_num at h ⊢
      linarith
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    have hu1 : -(1/2:ℝ) ≤ u := (abs_le.mp hu).1
    have hu2 : u ≤ (1/2:ℝ) := (abs_le.mp hu).2
    have hv1 : -(1/2:ℝ) ≤ v := (abs_le.mp hv).1
    have hv2 : v ≤ (1/2:ℝ) := (abs_le.mp hv).2
    have hA1 : -((553:ℝ)/2) ≤ (145:ℝ)*u - (408:ℝ)*v := by nlinarith [hu1, hu2, hv1, hv2]
    have hA2 : (145:ℝ)*u - (408:ℝ)*v ≤ (553:ℝ)/2 := by nlinarith [hu1, hu2, hv1, hv2]
    have hB1 : -((553:ℝ)/2) ≤ (408:ℝ)*u + (145:ℝ)*v := by nlinarith [hu1, hu2, hv1, hv2]
    have hB2 : (408:ℝ)*u + (145:ℝ)*v ≤ (553:ℝ)/2 := by nlinarith [hu1, hu2, hv1, hv2]
    have hd : (0:ℝ) < (433:ℝ) := by norm_num
    have hx1' : ((553:ℝ)/2)/(433:ℝ) ≤ x := by
      norm_num at hx1 ⊢
      exact hx1
    have hx2' : x ≤ L - ((553:ℝ)/2)/(433:ℝ) := by
      norm_num at hx2 ⊢
      exact hx2
    have hy1' : ((553:ℝ)/2)/(433:ℝ) ≤ y := by
      norm_num at hy1 ⊢
      exact hy1
    have hy2' : y ≤ L - ((553:ℝ)/2)/(433:ℝ) := by
      norm_num at hy2 ⊢
      exact hy2
    have hdiv1 : -(((553:ℝ)/2)/(433:ℝ)) ≤ ((145:ℝ)*u - (408:ℝ)*v)/(433:ℝ) := by
      have h := div_le_div_of_nonneg_right hA1 (le_of_lt hd)
      simpa [neg_div] using h
    have hdiv2 : ((145:ℝ)*u - (408:ℝ)*v)/(433:ℝ) ≤ ((553:ℝ)/2)/(433:ℝ) :=
      div_le_div_of_nonneg_right hA2 (le_of_lt hd)
    have hdiv3 : -(((553:ℝ)/2)/(433:ℝ)) ≤ ((408:ℝ)*u + (145:ℝ)*v)/(433:ℝ) := by
      have h := div_le_div_of_nonneg_right hB1 (le_of_lt hd)
      simpa [neg_div] using h
    have hdiv4 : ((408:ℝ)*u + (145:ℝ)*v)/(433:ℝ) ≤ ((553:ℝ)/2)/(433:ℝ) :=
      div_le_div_of_nonneg_right hB2 (le_of_lt hd)
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [hx1', hdiv1]
    · linarith [hx2', hdiv2]
    · linarith [hy1', hdiv3]
    · linarith [hy2', hdiv4]
