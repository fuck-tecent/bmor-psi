import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_reflect_orthogonal :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k + b (n-k))*(b k - b (n-k)))=0 := by
  intro n b
  have reflected : (∑ k ∈ Finset.range (n + 1), (b (n - k)) ^ 2) =
      ∑ k ∈ Finset.range (n + 1), (b k) ^ 2 := by
    simpa only [Nat.add_sub_cancel] using
      (Finset.sum_range_reflect (fun k => (b k) ^ 2) (n + 1))
  calc
    (∑ k ∈ Finset.range (n + 1), (b k + b (n - k)) * (b k - b (n - k))) =
        ∑ k ∈ Finset.range (n + 1), ((b k) ^ 2 - (b (n - k)) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    _ = 0 := by simp only [Finset.sum_sub_distrib, reflected, sub_self]
