import Mathlib

theorem PEqualNP.Outside.L_goldbach_pair_errors_odd :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a m,C a a (2*m+1)=2*(∑ k ∈ Finset.range (m+1),a k*a (2*m+1-k)) := by
  dsimp only
  intro a m
  let f := fun k => a k * a (2*m+1-k)
  change (∑ k ∈ Finset.range (2*m+1+1), f k) = 2 * ∑ k ∈ Finset.range (m+1), f k
  rw [show 2*m+1+1=(m+1)+(m+1) by omega, Finset.sum_range_add]
  have hr : (∑ k ∈ Finset.range (m+1), f (m+1+k)) = ∑ k ∈ Finset.range (m+1), f k := by
    calc
      _ = ∑ k ∈ Finset.range (m+1), f ((m+1)-1-k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp only [f]
        rw [show 2*m+1-(m+1+k)=(m+1)-1-k by omega,
            show 2*m+1-((m+1)-1-k)=m+1+k by omega, mul_comm]
      _ = _ := Finset.sum_range_reflect f _
  rw [hr, two_mul]
