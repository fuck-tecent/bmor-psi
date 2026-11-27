import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_mesh_var :
    ∀ (w : ℝ → ℝ) (n : ℕ) (L : ℝ), 0 < n →
      (∀ x y, |w x - w y| ≤ L * |x - y|) →
      (∑ k ∈ Finset.range n, |w (((k : ℝ) + 1) / n) - w ((k : ℝ) / n)|) ≤ L := by
  intro w n L hn hL
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hInv : 0 ≤ (1 : ℝ) / n := div_nonneg zero_le_one hnR.le
  have hstep (k : ℕ) : ((k : ℝ) + 1) / n - (k : ℝ) / n = (1 : ℝ) / n := by
    rw [← sub_div]
    ring
  calc
    (∑ k ∈ Finset.range n, |w (((k : ℝ) + 1) / n) - w ((k : ℝ) / n)|)
        ≤ ∑ _ ∈ Finset.range n, L * ((1 : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [hstep k, abs_of_nonneg hInv] using hL (((k : ℝ) + 1) / n) ((k : ℝ) / n)
    _ = L := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hnR] <;> ring
