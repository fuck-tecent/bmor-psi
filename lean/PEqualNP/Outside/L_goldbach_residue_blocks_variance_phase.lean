import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_variance_phase :
    ∀ (q : ℕ) (w u : Fin q → ℝ), (∑ a,w a*u a)^2≤(∑ a,(w a)^2)*(∑ a,(u a)^2) := by
  intro q w u
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q)) w u
