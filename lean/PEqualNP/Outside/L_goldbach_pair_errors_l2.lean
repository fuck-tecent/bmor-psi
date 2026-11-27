import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_l2 :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)
    ∀ a b n, (C a b n) ^ 2 ≤
      (∑ k ∈ Finset.range (n + 1), (a k) ^ 2) *
        (∑ k ∈ Finset.range (n + 1), (b k) ^ 2) := by
  dsimp only
  intro a b n
  have hreflect : (∑ k ∈ Finset.range (n + 1), (b (n - k)) ^ 2) =
      ∑ k ∈ Finset.range (n + 1), (b k) ^ 2 := by
    simpa using (Finset.sum_range_reflect (fun k => (b k) ^ 2) (n + 1))
  rw [← hreflect]
  exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) a (fun k => b (n - k))
