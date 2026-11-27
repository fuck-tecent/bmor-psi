import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_cross :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a b e f n,C (fun k => a k+e k) (fun k => b k+f k) n=C a b n+C a f n+C e b n+C e f n := by
  dsimp only
  intro a b e f n
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  all_goals ring
