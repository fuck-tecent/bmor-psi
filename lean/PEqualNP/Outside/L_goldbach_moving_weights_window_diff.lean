import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_window_diff :
    ∀ (a : ℕ → ℂ) (u v : ℕ), u≤v → (∑ k ∈ Finset.Ico u v,a k)=(∑ k ∈ Finset.range v,a k)-(∑ k ∈ Finset.range u,a k) := by
  intro a u v huv
  have hunion : Finset.range v = Finset.range u ∪ Finset.Ico u v := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range u) (Finset.Ico u v) := by
    rw [Finset.disjoint_left]
    intro k hk hkv
    simp only [Finset.mem_range, Finset.mem_Ico] at hk hkv
    omega
  rw [hunion, Finset.sum_union hdisj]
  ring
