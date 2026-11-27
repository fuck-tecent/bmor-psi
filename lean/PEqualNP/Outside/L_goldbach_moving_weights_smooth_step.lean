import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_smooth_step :
    ∀ (n : ℕ) (w v a : Fin n → ℝ) (e : ℝ), (∀ i,|w i-v i|≤e) → |∑ i,a i*(w i-v i)|≤e*∑ i,|a i| := by
  intro n w v a e he
  calc
    |∑ i, a i * (w i - v i)| ≤ ∑ i, |a i * (w i - v i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, e * |a i| := by
      refine Finset.sum_le_sum ?_
      intro i _
      rw [abs_mul, mul_comm e]
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
    _ = e * ∑ i, |a i| := (Finset.mul_sum _ _ _).symm
