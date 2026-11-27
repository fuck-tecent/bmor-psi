import Mathlib

theorem PEqualNP.Outside.L_square_packing_axis_margin :
    ∀ a b u v e:ℝ,0≤e → |u-a|≤e → |v-b|≤e → a+2*e<b → u<v := by
  intro a b u v e he hua hvb hab
  have h1 : u ≤ a + e := by
    have h := (abs_le.mp hua).2
    linarith
  have h2 : b - e ≤ v := by
    have h := (abs_le.mp hvb).1
    linarith
  linarith
