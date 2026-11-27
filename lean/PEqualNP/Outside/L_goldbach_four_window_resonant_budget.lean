import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_four_window_resonant_budget :
    ∀ {ι : Type} (s : Finset ι) (w z : ι → ℂ) (δ L : ℝ), 0 ≤ δ → 0 ≤ L → (∑ i ∈ s, ‖w i‖) ≤ L → (∀ i ∈ s, ‖1-z i‖ ≤ δ) → ‖∑ i ∈ s, w i * (1-z i)^3‖ ≤ L*δ^3 := by
  intro ι s w z δ L hδ _hL hsum hnear
  calc
    ‖∑ i ∈ s, w i * (1 - z i) ^ 3‖ ≤
        ∑ i ∈ s, ‖w i * (1 - z i) ^ 3‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖w i‖ * ‖1 - z i‖ ^ 3 := by
      simp only [Complex.norm_mul, Complex.norm_pow]
    _ ≤ ∑ i ∈ s, ‖w i‖ * δ ^ 3 :=
      Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hnear i hi) 3) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖w i‖) * δ ^ 3 := by rw [Finset.sum_mul]
    _ ≤ L * δ ^ 3 := mul_le_mul_of_nonneg_right hsum (pow_nonneg hδ 3)
