import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_cross_margin_transfer :
    ∀ G K C T pp κ e : ℝ, |G-(K-C)| ≤ e → |C-T| ≤ κ → T ≤ K-2*κ → pp+e < κ → pp < G := by
  intro G K C T pp κ e hG hC hT hpp
  have hG_lower : - e ≤ G - (K - C) := (abs_le.mp hG).1
  have hC_upper : C - T ≤ κ := (abs_le.mp hC).2
  linarith only [hG_lower, hC_upper, hT, hpp]
