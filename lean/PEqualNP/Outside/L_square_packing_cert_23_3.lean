import Mathlib

/-- The four corners give the coordinate extrema of the rotated square. -/
theorem PEqualNP.Outside.L_square_packing_cert_23_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(520*u-138*v)/538 ∧ x+(520*u-138*v)/538≤L ∧ 0≤y+(138*u+520*v)/538 ∧ y+(138*u+520*v)/538≤L) ↔ (658:ℝ)/(2*538)≤x ∧ x≤L-(658:ℝ)/(2*538) ∧ (658:ℝ)/(2*538)≤y ∧ y≤L-(658:ℝ)/(2*538) := by
  intro x y L
  constructor
  · intro h
    have hm : |(-(1 / 2) : ℝ)| ≤ 1 / 2 := by norm_num
    have hp : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have hx₁ := (h _ _ hm hp).1
    have hx₂ := (h _ _ hp hm).2.1
    have hy₁ := (h _ _ hm hm).2.2.1
    have hy₂ := (h _ _ hp hp).2.2.2
    norm_num at hx₁ hx₂ hy₁ hy₂
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith only [hx₁, hx₂, hy₁, hy₂]
  · rintro ⟨hx₁, hx₂, hy₁, hy₂⟩ u v hu hv
    obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
    obtain ⟨hv₁, hv₂⟩ := abs_le.mp hv
    norm_num at hx₁ hx₂ hy₁ hy₂
    exact ⟨by linarith only [hx₁, hu₁, hv₂],
      by linarith only [hx₂, hu₂, hv₁],
      by linarith only [hy₁, hu₁, hv₁],
      by linarith only [hy₂, hu₂, hv₂]⟩
