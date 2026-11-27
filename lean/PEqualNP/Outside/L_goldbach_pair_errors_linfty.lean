import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_linfty :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a b n (E : ℝ), (∀ k≤n, |a k|≤E) → |C a b n|≤E*(∑ k ∈ Finset.range (n+1),|b k|) := by
  dsimp only
  intro a b n E hE
  have hn : n + 1 - 1 = n := by omega
  have hreflect : (∑ k ∈ Finset.range (n + 1), |b (n - k)|) =
      ∑ k ∈ Finset.range (n + 1), |b k| := by
    simpa only [hn] using Finset.sum_range_reflect (fun k => |b k|) (n + 1)
  calc
    |∑ k ∈ Finset.range (n + 1), a k * b (n - k)| ≤
        ∑ k ∈ Finset.range (n + 1), |a k * b (n - k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), E * |b (n - k)| := by
      refine Finset.sum_le_sum ?_
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hE k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) (abs_nonneg _)
    _ = E * (∑ k ∈ Finset.range (n + 1), |b k|) := by
      rw [← Finset.mul_sum, hreflect]
