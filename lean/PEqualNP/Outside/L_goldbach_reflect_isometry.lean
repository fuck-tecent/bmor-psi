import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflect_isometry :
    ∀ (n : ℕ) (b : ℕ → ℂ),
      (∑ k ∈ Finset.range (n + 1), ‖b (n - k)‖ ^ 2) =
        ∑ k ∈ Finset.range (n + 1), ‖b k‖ ^ 2 := by
  intro n b
  rw [← Finset.sum_range_reflect (fun k : ℕ => ‖b k‖ ^ 2) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub]
