import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_monotone_var :
    ∀ (w : ℕ → ℝ) (n : ℕ), Antitone w → (∑ k ∈ Finset.range n, |w (k+1)-w k|)=w 0-w n := by
  intro w n hw
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ n)))]
    ring
