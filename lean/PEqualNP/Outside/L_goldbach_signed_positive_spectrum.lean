import Mathlib

theorem PEqualNP.Outside.L_goldbach_signed_positive_spectrum :
    ∀ (m : ℕ) (μ c : Fin m → ℝ), (∑ j, μ j*(c j)^2) ≤ ∑ j, max (μ j) 0*(c j)^2 := by
  intro m μ c
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (le_max_left (μ j) 0) (sq_nonneg (c j))
