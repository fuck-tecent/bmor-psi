import Mathlib

namespace PEqualNP.Outside

theorem L_square_packing_cert_29_1 :
(
∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(840*u-58*v)/842 ∧ x+(840*u-58*v)/842≤L ∧ 0≤y+(58*u+840*v)/842 ∧ y+(58*u+840*v)/842≤L) ↔ (898:ℝ)/(2*842)≤x ∧ x≤L-(898:ℝ)/(2*842) ∧ (898:ℝ)/(2*842)≤y ∧ y≤L-(898:ℝ)/(2*842)
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
