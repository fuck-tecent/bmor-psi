import Mathlib

theorem PEqualNP.Outside.L_goldbach_phase_geometric :
    ∀ (z : ℂ) (m : ℕ), (1-z)*Finset.sum (Finset.range m) (fun j => z^j) = 1-z^m := by
  intro z m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
