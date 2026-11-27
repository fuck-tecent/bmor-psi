import Mathlib

theorem PEqualNP.Outside.L_goldbach_signed_cutoff_projector :
    ∀ (m : ℕ) (μ c : Fin m → ℝ) (t : ℝ), (∑ j, μ j*(c j)^2) ≤ t*(∑ j, (c j)^2) + ∑ j ∈ Finset.univ.filter (fun j => t<μ j), (μ j-t)*(c j)^2 := by
  intro m μ c t
  have hsplit : (∑ j, μ j*(c j)^2)
      = (∑ j ∈ Finset.univ.filter (fun j => t < μ j), μ j*(c j)^2)
        + (∑ j ∈ Finset.univ.filter (fun j => ¬ t < μ j), μ j*(c j)^2) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => t < μ j)
      (fun j => μ j*(c j)^2)).symm
  have hkey : (∑ j ∈ Finset.univ.filter (fun j => t < μ j), μ j*(c j)^2)
      = t * (∑ j ∈ Finset.univ.filter (fun j => t < μ j), (c j)^2)
        + ∑ j ∈ Finset.univ.filter (fun j => t < μ j), (μ j-t)*(c j)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrest : (∑ j ∈ Finset.univ.filter (fun j => ¬ t < μ j), μ j*(c j)^2)
      ≤ t * (∑ j ∈ Finset.univ.filter (fun j => ¬ t < μ j), (c j)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : ¬ t < μ j := (Finset.mem_filter.mp hj).2
    exact mul_le_mul_of_nonneg_right (le_of_not_gt hj') (sq_nonneg (c j))
  have hcd : (∑ j, (c j)^2)
      = (∑ j ∈ Finset.univ.filter (fun j => t < μ j), (c j)^2)
        + (∑ j ∈ Finset.univ.filter (fun j => ¬ t < μ j), (c j)^2) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => t < μ j)
      (fun j => (c j)^2)).symm
  have hD : t * (∑ j, (c j)^2)
      = t * (∑ j ∈ Finset.univ.filter (fun j => t < μ j), (c j)^2)
        + t * (∑ j ∈ Finset.univ.filter (fun j => ¬ t < μ j), (c j)^2) := by
    rw [hcd]
    ring
  linarith
