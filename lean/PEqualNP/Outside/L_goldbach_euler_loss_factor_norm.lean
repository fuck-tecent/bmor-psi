import Mathlib

/-!
# Lower bound for one Euler factor

The reverse triangle inequality for a single local Euler factor `1 - z`: the distance from `z`
to `1` is at least `1 - ‖z‖`.
-/

theorem PEqualNP.Outside.L_goldbach_euler_loss_factor_norm : ∀ z : ℂ, 1-‖z‖≤‖1-z‖ := by
  intro z
  have h : ‖(1:ℂ) - z + z‖ ≤ ‖(1:ℂ) - z‖ + ‖z‖ := norm_add_le (1 - z) z
  rw [sub_add_cancel, norm_one] at h
  linarith
