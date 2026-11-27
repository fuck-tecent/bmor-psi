import Mathlib

/-!
# L-goldbach-reflection-mask

The mask contamination identity: the prime-support mask `b` keeps exactly the
prime-prime pairs of the reflected window. The total convolution minus the
masked one is precisely the contribution of pairs where `k` or `n - k` is
composite.
-/

theorem PEqualNP.Outside.L_goldbach_reflection_mask :
    ∀ (n : ℕ) (a : ℕ → ℝ), (let b := fun k => if Nat.Prime k then a k else 0; (∑ k ∈ Finset.range (n+1), a k*a (n-k)) - (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = ∑ k ∈ Finset.range (n+1), if Nat.Prime k ∧ Nat.Prime (n-k) then 0 else a k*a (n-k)) := by
  intro n a
  simp only []
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ k ∈ Finset.range (n+1), a k * a (n-k) - (if Nat.Prime k then a k else 0) * (if Nat.Prime (n-k) then a (n-k) else 0) = if Nat.Prime k ∧ Nat.Prime (n-k) then 0 else a k * a (n-k) := by
    intro k _
    by_cases h2 : Nat.Prime k <;> by_cases h3 : Nat.Prime (n-k) <;> simp [h2, h3]
  rw [Finset.sum_congr rfl h1]
