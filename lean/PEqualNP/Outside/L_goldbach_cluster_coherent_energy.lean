import Mathlib

theorem PEqualNP.Outside.L_goldbach_cluster_coherent_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), ‖∑ i, u i‖^2 ≤ (m : ℝ)*∑ i, ‖u i‖^2 := by
  intro m u
  calc
    ‖∑ i, u i‖ ^ 2 ≤ (∑ i, ‖u i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ u) 2
    _ ≤ (m : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin m => (1 : ℝ)) (fun i => ‖u i‖)
