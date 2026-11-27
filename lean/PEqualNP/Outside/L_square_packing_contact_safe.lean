import Mathlib

theorem PEqualNP.Outside.L_square_packing_contact_safe :
    ∀ a b r s x:ℝ,r+s≤b-a → |x-a|<r → ¬ |x-b|<s := by
  intro a b r s x hrs h1 h2
  have hx1 : x - a < r := (abs_lt.mp h1).2
  have hy2 : b - x < s := by
    have h3 := (abs_lt.mp h2).1
    linarith
  linarith
