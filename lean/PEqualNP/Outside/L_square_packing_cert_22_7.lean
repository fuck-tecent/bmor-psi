import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_22_7 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(435*u-308*v)/533 ∧ x+(435*u-308*v)/533≤L ∧ 0≤y+(308*u+435*v)/533 ∧ y+(308*u+435*v)/533≤L) ↔ (743:ℝ)/(2*533)≤x ∧ x≤L-(743:ℝ)/(2*533) ∧ (743:ℝ)/(2*533)≤y ∧ y≤L-(743:ℝ)/(2*533) := by
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
