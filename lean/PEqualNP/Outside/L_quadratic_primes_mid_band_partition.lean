import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_band_partition :
    let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ);
    let middle := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2*x)) (fun n =>
      Finset.sum ((n^2+1).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301)) (w n));
    let band := fun (x:ℕ) (first:Bool) => Finset.sum (Finset.Ioc x (2*x)) (fun n =>
      Finset.sum ((n^2+1).primeFactors.filter (fun p => x<p ∧ p^100000≤n^132301 ∧
        (if first then p^20≤n^23 else n^23<p^20))) (w n));
    ∀ x:ℕ,middle x=band x true+band x false := by
  classical
  dsimp only
  intro x
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rcases le_or_gt (p ^ 20) (n ^ 23) with h | h
  · simp [h, not_lt_of_ge h]
  · simp [h, not_le_of_gt h]
