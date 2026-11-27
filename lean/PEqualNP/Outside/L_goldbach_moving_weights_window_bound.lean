import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_window_bound :
    ∀ (a : ℕ → ℂ) (u v : ℕ) (B : ℝ), u ≤ v →
      ‖∑ k ∈ Finset.range u, a k‖ ≤ B →
      ‖∑ k ∈ Finset.range v, a k‖ ≤ B →
      ‖∑ k ∈ Finset.Ico u v, a k‖ ≤ 2 * B := by
  intro a u v B huv hu hv
  rw [Finset.sum_Ico_eq_sub _ huv]
  calc
    ‖(∑ k ∈ Finset.range v, a k) - (∑ k ∈ Finset.range u, a k)‖
        ≤ ‖∑ k ∈ Finset.range v, a k‖ + ‖∑ k ∈ Finset.range u, a k‖ :=
      norm_sub_le _ _
    _ ≤ 2 * B := by linarith
