import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_log_factorization :
    let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ); ∀ x : ℕ, Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum (n^2+1).primeFactors (w n)) = Finset.sum (Finset.Ioc x (2*x)) (fun n => Real.log ((n:ℝ)^2+1)) := by
  dsimp only
  intro x
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have h := (Real.log_nat_eq_sum_factorization (n ^ 2 + 1)).symm
  simp only [Finsupp.sum, Nat.support_factorization] at h
  push_cast at h
  exact h
