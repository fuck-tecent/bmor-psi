import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

def low (U : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ≤ U then f n else 0

lemma low_eq_of_le {U n : ℕ} {f : ℕ → ℝ} (h : n ≤ U) : low U f n = f n := by
  simp [low, h]

lemma low_eq_zero_of_gt {U n : ℕ} {f : ℕ → ℝ} (h : U < n) : low U f n = 0 := by
  simp [low, not_le_of_gt h]

lemma norm_low_exponential_sum_le (N U : ℕ) (f : ℕ → ℝ) (C t : ℝ)
    (hC : 0 ≤ C) (hf : ∀ k ≤ U, |f k| ≤ C) :
    ‖∑ k ∈ Finset.range (N + 1), (low U f k : ℂ) *
        Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ ≤
      (U + 1 : ℝ) * C := by
  classical
  let F : ℕ → ℂ := fun k =>
    (f k : ℂ) * Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)
  have hsum : ∑ k ∈ Finset.range (N + 1), (low U f k : ℂ) *
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≤ U), F k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k ≤ U
    · simp [low, h, F]
    · simp [low, h, F]
  rw [hsum]
  have hsubset : (Finset.range (N + 1)).filter (fun k => k ≤ U) ⊆ Finset.range (U + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  calc
    ‖∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≤ U), F k‖
        ≤ ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k ≤ U), ‖F k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ (Finset.range (N + 1)).filter (fun k => k ≤ U), C := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.mem_filter] at hk
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hEk : ‖Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (k : ℝ) * t)
      rw [hEk, mul_one]
      exact hf k hk.2
    _ ≤ ∑ _k ∈ Finset.range (U + 1), C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hk hnot
      exact hC
    _ = (U + 1 : ℝ) * C := by simp

end

end PEqualNP.Outside
