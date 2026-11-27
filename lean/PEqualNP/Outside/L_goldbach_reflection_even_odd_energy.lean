import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflection_even_odd_energy :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k+b (n-k))^2) + (∑ k ∈ Finset.range (n+1), (b k-b (n-k))^2) = 4*∑ k ∈ Finset.range (n+1), (b k)^2 := by
  intro n b
  have hreflect : (∑ k ∈ Finset.range (n + 1), b (n - k) ^ 2) =
      ∑ k ∈ Finset.range (n + 1), b k ^ 2 :=
    Finset.sum_range_reflect (fun k => b k ^ 2) (n + 1)
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (2 * b k ^ 2 + 2 * b (n - k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect]
      ring
