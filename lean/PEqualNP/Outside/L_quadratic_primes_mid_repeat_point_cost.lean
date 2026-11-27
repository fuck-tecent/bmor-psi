import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_repeat_point_cost :
    ∀ (n : ℕ) (S : Finset ℕ), S⊆(n^2+1).primeFactors → (∑ p ∈ S, ((((n^2+1).factorization p-1:ℕ):ℝ))*Real.log (p:ℝ)) ≤ Real.log ((n^2+1:ℕ):ℝ) := by
  intro n S hS
  let m : ℕ := n ^ 2 + 1
  change S ⊆ m.primeFactors at hS
  have hlog (p : ℕ) (hp : p ∈ m.primeFactors) : 0 ≤ Real.log (p : ℝ) := by
    have hp1 : 1 ≤ p := Nat.pos_of_mem_primeFactors hp
    exact Real.log_nonneg (by exact_mod_cast hp1)
  calc
    (∑ p ∈ S, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ≤
        ∑ p ∈ S, (m.factorization p : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le (m.factorization p) 1) (hlog p (hS hp))
    _ ≤ ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _) (hlog p hp)
    _ = Real.log (m : ℝ) := by
      simpa only [Finsupp.sum, Nat.support_factorization] using
        (Real.log_nat_eq_sum_factorization m).symm
