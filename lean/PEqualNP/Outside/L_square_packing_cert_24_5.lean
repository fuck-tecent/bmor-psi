import Mathlib

private theorem squarePackingCert (a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) :
    ∀ x y L : ℝ,
      (∀ u v : ℝ, |u| ≤ 1 / 2 → |v| ≤ 1 / 2 →
        0 ≤ x + (a * u - b * v) / d ∧ x + (a * u - b * v) / d ≤ L ∧
        0 ≤ y + (b * u + a * v) / d ∧ y + (b * u + a * v) / d ≤ L) ↔
      (a + b) / (2 * d) ≤ x ∧ x ≤ L - (a + b) / (2 * d) ∧
      (a + b) / (2 * d) ≤ y ∧ y ≤ L - (a + b) / (2 * d) := by
  intro x y L
  rw [← div_div]
  constructor
  · intro h
    have hn : |(-(1 / 2) : ℝ)| ≤ 1 / 2 := by norm_num
    have hp : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    refine ⟨sub_nonneg.mp ?_, le_sub_iff_add_le.mpr ?_,
      sub_nonneg.mp ?_, le_sub_iff_add_le.mpr ?_⟩
    · convert (h (-(1 / 2)) (1 / 2) hn hp).1 using 1; ring
    · convert (h (1 / 2) (-(1 / 2)) hp hn).2.1 using 1; ring
    · convert (h (-(1 / 2)) (-(1 / 2)) hn hn).2.2.1 using 1; ring
    · convert (h (1 / 2) (1 / 2) hp hp).2.2.2 using 1; ring
  · rintro ⟨hxlo, hxhi, hylo, hyhi⟩ u v hu hv
    obtain ⟨hul, huu⟩ := abs_le.mp hu
    obtain ⟨hvl, hvu⟩ := abs_le.mp hv
    have bounds (z : ℝ) (hl : -((a + b) / 2) ≤ z) (hh : z ≤ (a + b) / 2) :
        -((a + b) / 2 / d) ≤ z / d ∧ z / d ≤ (a + b) / 2 / d := by
      rw [← neg_div]
      exact ⟨(div_le_div_iff_of_pos_right hd).2 hl, (div_le_div_iff_of_pos_right hd).2 hh⟩
    obtain ⟨hxl, hxu⟩ := bounds (a * u - b * v)
      (by linarith only [mul_le_mul_of_nonneg_left hul ha, mul_le_mul_of_nonneg_left hvu hb])
      (by linarith only [mul_le_mul_of_nonneg_left huu ha, mul_le_mul_of_nonneg_left hvl hb])
    obtain ⟨hyl, hyu⟩ := bounds (b * u + a * v)
      (by linarith only [mul_le_mul_of_nonneg_left hul hb, mul_le_mul_of_nonneg_left hvl ha])
      (by linarith only [mul_le_mul_of_nonneg_left huu hb, mul_le_mul_of_nonneg_left hvu ha])
    exact ⟨by linarith only [hxlo, hxl], by linarith only [hxhi, hxu],
      by linarith only [hylo, hyl], by linarith only [hyhi, hyu]⟩

theorem PEqualNP.Outside.L_square_packing_cert_24_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(551*u-240*v)/601 ∧ x+(551*u-240*v)/601≤L ∧ 0≤y+(240*u+551*v)/601 ∧ y+(240*u+551*v)/601≤L) ↔ (791:ℝ)/(2*601)≤x ∧ x≤L-(791:ℝ)/(2*601) ∧ (791:ℝ)/(2*601)≤y ∧ y≤L-(791:ℝ)/(2*601) := by
  have hsum : (551 : ℝ) + 240 = 791 := by norm_num
  simpa only [hsum] using
    squarePackingCert 551 240 601 (by norm_num) (by norm_num) (by norm_num)
