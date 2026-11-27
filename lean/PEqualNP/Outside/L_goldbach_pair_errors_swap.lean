import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_swap :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a b n,C a b n=C b a n := by
  dsimp only
  intro a b n
  have h := Finset.sum_range_reflect (fun k => a k * b (n - k)) (n + 1)
  calc
    (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) =
        ∑ k ∈ Finset.range (n + 1), a (n - k) * b (n - (n - k)) := by
      simpa only [Nat.add_sub_cancel] using h.symm
    _ = ∑ k ∈ Finset.range (n + 1), a (n - k) * b k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.sub_sub_self (by omega : k ≤ n)]
    _ = ∑ k ∈ Finset.range (n + 1), b k * a (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
