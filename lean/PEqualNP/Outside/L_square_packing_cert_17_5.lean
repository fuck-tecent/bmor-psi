import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_17_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(264*u-170*v)/314 ∧ x+(264*u-170*v)/314≤L ∧ 0≤y+(170*u+264*v)/314 ∧ y+(170*u+264*v)/314≤L) ↔ (434:ℝ)/(2*314)≤x ∧ x≤L-(434:ℝ)/(2*314) ∧ (434:ℝ)/(2*314)≤y ∧ y≤L-(434:ℝ)/(2*314) := by
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
