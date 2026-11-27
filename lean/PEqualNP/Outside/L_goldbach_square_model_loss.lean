import Mathlib

/-- A bound for the error in squaring an approximation, in terms of the model and its error. -/
theorem PEqualNP.Outside.L_goldbach_square_model_loss :
    ∀ z w : ℂ, ‖z ^ 2 - w ^ 2‖ ≤ ‖z - w‖ * (2 * ‖w‖ + ‖z - w‖) := by
  intro z w
  have hsum : ‖z + w‖ ≤ 2 * ‖w‖ + ‖z - w‖ := by
    calc
      ‖z + w‖ = ‖(w + w) + (z - w)‖ := by congr 1; ring
      _ ≤ ‖w + w‖ + ‖z - w‖ := norm_add_le _ _
      _ ≤ (‖w‖ + ‖w‖) + ‖z - w‖ := by linarith [norm_add_le w w]
      _ = 2 * ‖w‖ + ‖z - w‖ := by ring
  rw [show z ^ 2 - w ^ 2 = (z - w) * (z + w) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
