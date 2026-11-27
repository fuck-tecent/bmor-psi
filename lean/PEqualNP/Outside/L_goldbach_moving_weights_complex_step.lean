import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_complex_step :
    ∀ (n : ℕ) (a u v : Fin n → ℂ), ‖∑ i,a i*(u i-v i)‖^2≤(∑ i,‖a i‖^2)*(∑ i,‖u i-v i‖^2) := by
  intro n a u v
  have hnorm : ‖∑ i, a i * (u i - v i)‖ ≤ ∑ i, ‖a i‖ * ‖u i - v i‖ := by
    simpa only [Complex.norm_mul] using
      (norm_sum_le Finset.univ (fun i : Fin n => a i * (u i - v i)))
  calc
    ‖∑ i, a i * (u i - v i)‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖u i - v i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖u i - v i‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖u i - v i‖)
