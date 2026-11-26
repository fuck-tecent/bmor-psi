import Mathlib

theorem PEqualNP.Outside.L_twin_primes_time_weights :
    ∀ (l : ℝ → ℝ) (t : ℝ), let g := fun (σ : ℝ) => (l t)^2 * (1+σ*Real.cos (4*Real.pi*t)); 0 ≤ g 1 ∧ 0 ≤ g (-1) ∧ g 1 - g (-1) = 2*(l t)^2*Real.cos (4*Real.pi*t) := by
  intro l t
  simp only []
  have hlo : -1 ≤ Real.cos (4*Real.pi*t) := Real.neg_one_le_cos _
  have hhi : Real.cos (4*Real.pi*t) ≤ 1 := Real.cos_le_one _
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (sq_nonneg _) (by linarith)
  · exact mul_nonneg (sq_nonneg _) (by linarith)
  · ring
