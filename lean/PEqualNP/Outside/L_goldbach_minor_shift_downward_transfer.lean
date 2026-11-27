import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_downward_transfer :
  ∀ (r : ℕ → ℝ) (n j : ℕ), r (n + 2 * j) - r n ≤ ∑ i ∈ Finset.range j, max 0 (r (n + 2 * (i + 1)) - r (n + 2 * i)) := by
  intro r n j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hstep : r (n + 2 * (j + 1)) - r (n + 2 * j) ≤ max 0 (r (n + 2 * (j + 1)) - r (n + 2 * j)) :=
      le_max_right _ _
    linarith
