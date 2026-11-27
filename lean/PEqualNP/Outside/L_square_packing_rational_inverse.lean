import Mathlib

theorem PEqualNP.Outside.L_square_packing_rational_inverse :
    ∀ c s:ℝ,c^2+s^2=1 → c≠ -1 → let t:=s/(1+c); (1-t^2)/(1+t^2)=c ∧ 2*t/(1+t^2)=s := by
  intro c s h hc
  have h1 : (1 + c) ≠ 0 := by intro h'; apply hc; linarith
  dsimp only
  have hden : 1 + (s / (1 + c)) ^ 2 = 2 / (1 + c) := by
    field_simp
    nlinarith [h]
  have hnum : 1 - (s / (1 + c)) ^ 2 = 2 * c / (1 + c) := by
    field_simp
    nlinarith [h]
  constructor
  · rw [hnum, hden]
    field_simp
  · rw [hden]
    field_simp
