import Mathlib

theorem PEqualNP.Outside.L_goldbach_bulk_exception_budget :
    ∀ (s : Finset ℕ) (r m : ℕ → ℝ) (L : ℝ), 0<L → (∀ n ∈ s, L ≤ m n) → (((s.filter (fun n => r n=0)).card : ℝ)*L^2) ≤ ∑ n ∈ s, (r n-m n)^2 := by
  classical
  intro s r m L hL hm
  calc
    _ = ∑ _n ∈ s.filter (fun n => r n = 0), L ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ s.filter (fun n => r n = 0), (r n - m n)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hns, hr⟩ := Finset.mem_filter.mp hn
      have h := hm n hns
      rw [hr, zero_sub, neg_sq]
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (hL.le.trans h) hL.le)]
    _ ≤ ∑ n ∈ s, (r n - m n)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n _ _
      exact sq_nonneg _
