import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_14_9 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(115*u-252*v)/277 ∧ x+(115*u-252*v)/277≤L ∧ 0≤y+(252*u+115*v)/277 ∧ y+(252*u+115*v)/277≤L) ↔ (367:ℝ)/(2*277)≤x ∧ x≤L-(367:ℝ)/(2*277) ∧ (367:ℝ)/(2*277)≤y ∧ y≤L-(367:ℝ)/(2*277) := by
  intro x y L
  constructor
  · intro h
    have e1 : |(-1/2:ℝ)| ≤ 1/2 := by rw [abs_le]; constructor <;> norm_num
    have e2 : |(1/2:ℝ)| ≤ 1/2 := by rw [abs_le]; constructor <;> norm_num
    have h1 := (h (-1/2) (1/2) e1 e2).1
    have h2 := (h (1/2) (-1/2) e2 e1).2.1
    have h3 := (h (-1/2) (-1/2) e1 e1).2.2.1
    have h4 := (h (1/2) (1/2) e2 e2).2.2.2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    obtain ⟨hv1, hv2⟩ := abs_le.mp hv
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
