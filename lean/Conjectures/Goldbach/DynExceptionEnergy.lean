import Mathlib

theorem Conjectures.Goldbach.DynExceptionEnergy :
    ∀ (E : Finset ℕ) (r b : ℕ → ℝ) (L : ℝ), 0 < L → (∀ n ∈ E, L ≤ b n) → ((E.filter (fun n => r n=0)).card:ℝ)*L^2 ≤ ∑ n ∈ E, (r n-b n)^2 := by
  intro E r b L hL hb
  calc ((E.filter (fun n => r n=0)).card:ℝ)*L^2
      = ∑ n ∈ E.filter (fun n => r n=0), L^2 := by simp
    _ ≤ ∑ n ∈ E.filter (fun n => r n=0), (r n-b n)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [hn.2, zero_sub, neg_sq]
        exact pow_le_pow_left₀ hL.le (hb n hn.1) 2
    _ ≤ ∑ n ∈ E, (r n-b n)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
