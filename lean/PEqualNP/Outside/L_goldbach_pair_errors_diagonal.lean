import Mathlib

theorem PEqualNP.Outside.L_goldbach_pair_errors_diagonal :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a m,C a a (2*m)=2*(∑ k ∈ Finset.range m,a k*a (2*m-k))+(a m)^2 := by
  dsimp only
  intro a m
  let f := fun k => a k * a (2*m-k)
  change (∑ k ∈ Finset.range (2*m+1), f k) = 2 * (∑ k ∈ Finset.range m, f k) + (a m)^2
  rw [show 2*m+1=(m+1)+m by omega, Finset.sum_range_add, Finset.sum_range_succ]
  have hr : (∑ k ∈ Finset.range m, f (m+1+k)) = ∑ k ∈ Finset.range m, f k := by
    calc
      _ = ∑ k ∈ Finset.range m, f (m-1-k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp only [f]
        rw [show 2*m-(m+1+k)=m-1-k by omega,
            show 2*m-(m-1-k)=m+1+k by omega, mul_comm]
      _ = _ := Finset.sum_range_reflect f _
  rw [hr, show f m=(a m)^2 by simp only [f, show 2*m-m=m by omega, pow_two]]
  ring
