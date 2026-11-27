import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_gap_tail_cover : ∀ a b H : ℝ, 0 ≤ H → 2*H < |a-b| → H < |a| ∨ H < |b| := by
  intro a b H hH h
  have htri : |a - b| ≤ |a| + |b| := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  by_contra hc
  rw [not_or] at hc
  have h1 : |a| ≤ H := not_lt.1 hc.1
  have h2 : |b| ≤ H := not_lt.1 hc.2
  linarith