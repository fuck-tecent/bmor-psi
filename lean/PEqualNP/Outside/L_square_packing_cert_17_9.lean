import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_17_9 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(208*u-306*v)/370 ∧ x+(208*u-306*v)/370≤L ∧ 0≤y+(306*u+208*v)/370 ∧ y+(306*u+208*v)/370≤L) ↔ (514:ℝ)/(2*370)≤x ∧ x≤L-(514:ℝ)/(2*370) ∧ (514:ℝ)/(2*370)≤y ∧ y≤L-(514:ℝ)/(2*370) := by
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
    have hA1 : -((514:ℝ)/2) ≤ (208:ℝ)*u - (306:ℝ)*v := by nlinarith [hu1, hu2, hv1, hv2]
    have hA2 : (208:ℝ)*u - (306:ℝ)*v ≤ (514:ℝ)/2 := by nlinarith [hu1, hu2, hv1, hv2]
    have hB1 : -((514:ℝ)/2) ≤ (306:ℝ)*u + (208:ℝ)*v := by nlinarith [hu1, hu2, hv1, hv2]
    have hB2 : (306:ℝ)*u + (208:ℝ)*v ≤ (514:ℝ)/2 := by nlinarith [hu1, hu2, hv1, hv2]
    have hd : (0:ℝ) < (370:ℝ) := by norm_num
    have hx1' : ((514:ℝ)/2)/(370:ℝ) ≤ x := by
      norm_num at hx1 ⊢
      exact hx1
    have hx2' : x ≤ L - ((514:ℝ)/2)/(370:ℝ) := by
      norm_num at hx2 ⊢
      exact hx2
    have hy1' : ((514:ℝ)/2)/(370:ℝ) ≤ y := by
      norm_num at hy1 ⊢
      exact hy1
    have hy2' : y ≤ L - ((514:ℝ)/2)/(370:ℝ) := by
      norm_num at hy2 ⊢
      exact hy2
    have hdiv1 : -(((514:ℝ)/2)/(370:ℝ)) ≤ ((208:ℝ)*u - (306:ℝ)*v)/(370:ℝ) := by
      have h := div_le_div_of_nonneg_right hA1 (le_of_lt hd)
      simpa [neg_div] using h
    have hdiv2 : ((208:ℝ)*u - (306:ℝ)*v)/(370:ℝ) ≤ ((514:ℝ)/2)/(370:ℝ) :=
      div_le_div_of_nonneg_right hA2 (le_of_lt hd)
    have hdiv3 : -(((514:ℝ)/2)/(370:ℝ)) ≤ ((306:ℝ)*u + (208:ℝ)*v)/(370:ℝ) := by
      have h := div_le_div_of_nonneg_right hB1 (le_of_lt hd)
      simpa [neg_div] using h
    have hdiv4 : ((306:ℝ)*u + (208:ℝ)*v)/(370:ℝ) ≤ ((514:ℝ)/2)/(370:ℝ) :=
      div_le_div_of_nonneg_right hB2 (le_of_lt hd)
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [hx1', hdiv1]
    · linarith [hx2', hdiv2]
    · linarith [hy1', hdiv3]
    · linarith [hy2', hdiv4]
