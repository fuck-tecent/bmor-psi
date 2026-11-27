import Mathlib
theorem PEqualNP.Outside.L_twin_primes_divisor_split : let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let primes := fun X => (w X).filter Nat.Prime; let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let short := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum c))/(X:ℝ); let long := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum c))/(X:ℝ); ∀ X D : ℕ, short X D + long X D = (primes X).sum (fun p => Real.log p*ArithmeticFunction.vonMangoldt (p+2))/(X:ℝ) := by
  dsimp only
  intro X D
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [← mul_add]
  congr 1
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := p+2)
  change (∑ d ∈ (p+2).divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d) = -ArithmeticFunction.vonMangoldt (p+2) at h
  have hm : (∑ d ∈ (p+2).divisors, -(ArithmeticFunction.moebius d : ℝ) * Real.log d) = ArithmeticFunction.vonMangoldt (p+2) := by
    simpa [Finset.sum_neg_distrib] using congrArg Neg.neg h
  rw [← hm]
  simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not (p+2).divisors (fun d => d ≤ D) (fun d => -(ArithmeticFunction.moebius d : ℝ) * Real.log d))

