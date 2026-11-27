import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_box_to_tent :
  ∀ (n : ℕ) (a : ℕ → ℝ), (∑ j ∈ Finset.range n,∑ k ∈ Finset.range (j+1),a k)=∑ k ∈ Finset.range n,((n-k:ℕ):ℝ)*a k := by
  intro n a
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f:=fun k => a k),
      Finset.sum_range_succ (f:=fun k => ((n+1-k:ℕ):ℝ)*a k)]
    have hcoeff (k : ℕ) (hk : k ∈ Finset.range n) :
        ((n+1-k:ℕ):ℝ) = ((n-k:ℕ):ℝ) + 1 := by
      have hlt := Finset.mem_range.mp hk
      have ht : n+1-k = n-k+1 := by omega
      rw [ht, Nat.cast_add, Nat.cast_one]
    rw [show n+1-n=1 by omega]
    simp only [Nat.cast_one, one_mul]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcoeff k hk]
    ring
