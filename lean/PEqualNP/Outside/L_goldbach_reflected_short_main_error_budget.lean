import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_short_main_error_budget :
    ∀ {ι : Type} (s : Finset ι) (a f g : ι → ℝ) (E : ℝ), 0 ≤ E → (∀ j ∈ s, |f j-g j| ≤ E) → |∑ j ∈ s, a j*(f j-g j)| ≤ E*(∑ j ∈ s, |a j|) := by
  intro ι s a f g E _ herror
  calc
    |∑ j ∈ s, a j * (f j - g j)| ≤ ∑ j ∈ s, |a j * (f j - g j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, E * |a j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (herror j hj) (abs_nonneg _)
    _ = E * ∑ j ∈ s, |a j| := (Finset.mul_sum _ _ _).symm
