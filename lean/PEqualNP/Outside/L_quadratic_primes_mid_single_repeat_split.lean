import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_single_repeat_split :
    ∀ (n : ℕ) (S : Finset ℕ), S⊆(n^2+1).primeFactors → (∑ p ∈ S, (((n^2+1).factorization p:ℕ):ℝ)*Real.log (p:ℝ)) = (∑ p ∈ S, Real.log (p:ℝ)) + ∑ p ∈ S, ((((n^2+1).factorization p-1:ℕ):ℝ))*Real.log (p:ℝ) := by
  intro n S hS
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hs : p ∈ (n ^ 2 + 1).factorization.support := by
    rw [Nat.support_factorization]
    exact hS hp
  have hle : 1 ≤ (n ^ 2 + 1).factorization p :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
  simp only [Nat.cast_sub hle, Nat.cast_one]
  ring
