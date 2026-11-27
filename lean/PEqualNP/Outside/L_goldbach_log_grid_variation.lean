import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_log_grid_variation :
    ∀ n : ℕ, 1≤n → (∑ k ∈ Finset.range n, |Real.log ((k+1:ℕ):ℝ)-Real.log (k:ℝ)|) = Real.log (n:ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_range_succ, ih]
    have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : Real.log (n:ℝ) ≤ Real.log ((n+1:ℕ):ℝ) :=
      Real.log_le_log hpos (by push_cast; linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    ring
