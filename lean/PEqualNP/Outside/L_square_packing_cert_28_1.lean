import Mathlib

namespace PEqualNP.Outside

theorem L_square_packing_cert_28_1 :
(
∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(783*u-56*v)/785 ∧ x+(783*u-56*v)/785≤L ∧ 0≤y+(56*u+783*v)/785 ∧ y+(56*u+783*v)/785≤L) ↔ (839:ℝ)/(2*785)≤x ∧ x≤L-(839:ℝ)/(2*785) ∧ (839:ℝ)/(2*785)≤y ∧ y≤L-(839:ℝ)/(2*785)
) := by
  intro x y L
  constructor
  · intro h
    have hp : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have hn : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
    have h1 := (h (-1 / 2) (1 / 2) hn hp).1
    have h2 := (h (1 / 2) (-1 / 2) hp hn).2.1
    have h3 := (h (-1 / 2) (-1 / 2) hn hn).2.2.1
    have h4 := (h (1 / 2) (1 / 2) hp hp).2.2.2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    rcases abs_le.mp hu with ⟨hu1, hu2⟩
    rcases abs_le.mp hv with ⟨hv1, hv2⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end PEqualNP.Outside
