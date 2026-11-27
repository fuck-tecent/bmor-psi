import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_prefix_invert :
    ∀ (a : ℕ → ℂ) (k : ℕ),
      (∑ j ∈ Finset.range (k + 1), a j) - (∑ j ∈ Finset.range k, a j) = a k := by
  intro a k
  rw [Finset.sum_range_succ]
  ring
