import Mathlib

namespace PEqualNP.Outside

theorem L_square_packing_rotated_square_containment :
    ∀ (s x y a b : ℝ), a ^ 2 + b ^ 2 = 1 → ((∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ∀ v ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), 0 ≤ x + a * u - b * v ∧ x + a * u - b * v ≤ s ∧ 0 ≤ y + b * u + a * v ∧ y + b * u + a * v ≤ s) ↔ (|a| + |b| ≤ 2 * x ∧ |a| + |b| ≤ 2 * (s - x) ∧ |a| + |b| ≤ 2 * y ∧ |a| + |b| ≤ 2 * (s - y))) := by
  intro s x y a b _
  have hlo : (-(1 / 2) : ℝ) ∈ Set.Icc (-(1 / 2)) (1 / 2) := by norm_num [Set.mem_Icc]
  have hhi : (1 / 2 : ℝ) ∈ Set.Icc (-(1 / 2)) (1 / 2) := by norm_num [Set.mem_Icc]
  constructor
  · intro H
    rcases H (-(1 / 2)) hlo (-(1 / 2)) hlo with ⟨ha1, ha2, ha3, ha4⟩
    rcases H (-(1 / 2)) hlo (1 / 2) hhi with ⟨hb1, hb2, hb3, hb4⟩
    rcases H (1 / 2) hhi (-(1 / 2)) hlo with ⟨hc1, hc2, hc3, hc4⟩
    rcases H (1 / 2) hhi (1 / 2) hhi with ⟨hd1, hd2, hd3, hd4⟩
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg ha, abs_of_nonneg hb]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [abs_of_nonneg ha, abs_of_nonpos hb]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [abs_of_nonpos ha, abs_of_nonneg hb]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [abs_of_nonpos ha, abs_of_nonpos hb]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · intro H u hu v hv
    have hbnd : ∀ (c w : ℝ), w ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → -(|c| / 2) ≤ c * w ∧ c * w ≤ |c| / 2 := by
      intro c w hw
      have hw1 : -(1 / 2 : ℝ) ≤ w := (Set.mem_Icc.1 hw).1
      have hw2 : w ≤ (1 / 2 : ℝ) := (Set.mem_Icc.1 hw).2
      have hw' : |w| ≤ 1 / 2 := by
        rw [abs_le]
        exact ⟨hw1, hw2⟩
      have hmul : |c| * |w| ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left hw' (abs_nonneg c)
      have habs : |c * w| ≤ |c| / 2 := by
        rw [abs_mul]
        linarith
      exact abs_le.1 habs
    have h1 : -(|a| / 2) ≤ a * u ∧ a * u ≤ |a| / 2 := hbnd a u hu
    have h2 : -(|b| / 2) ≤ b * v ∧ b * v ≤ |b| / 2 := hbnd b v hv
    have h3 : -(|b| / 2) ≤ b * u ∧ b * u ≤ |b| / 2 := hbnd b u hu
    have h4 : -(|a| / 2) ≤ a * v ∧ a * v ≤ |a| / 2 := hbnd a v hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, H.1, H.2.1, H.2.2.1, H.2.2.2]

end PEqualNP.Outside
