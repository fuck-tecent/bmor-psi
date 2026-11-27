import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_product_var :
    ∀ (u v : ℕ → ℂ) (k : ℕ),
      ‖u (k + 1) * v (k + 1) - u k * v k‖ ≤
        ‖u (k + 1)‖ * ‖v (k + 1) - v k‖ +
          ‖v k‖ * ‖u (k + 1) - u k‖ := by
  intro u v k
  have hdiff : u (k + 1) * v (k + 1) - u k * v k =
      u (k + 1) * (v (k + 1) - v k) + v k * (u (k + 1) - u k) := by
    ring
  rw [hdiff]
  simpa only [norm_mul] using
    (norm_add_le (u (k + 1) * (v (k + 1) - v k)) (v k * (u (k + 1) - u k)))
