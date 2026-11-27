import Mathlib

theorem PEqualNP.Outside.L_goldbach_abel_endpoints :
    ∀ (N : ℕ) (A g : ℕ → ℂ), Finset.sum (Finset.range N) (fun k => (A (k+1)-A k)*g k) = A N*g N-A 0*g 0-Finset.sum (Finset.range N) (fun k => A (k+1)*(g (k+1)-g k)) := by
  intro N A g
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring
