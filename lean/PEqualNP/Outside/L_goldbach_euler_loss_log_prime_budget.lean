import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_euler_loss_log_prime_budget :
    ∀ (q : ℕ), 0 < q →
      (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
  intro q hq
  have hpos (p : ℕ) (hp : p ∈ q.primeFactors) : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hle := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Real.log_le_log (Finset.prod_pos hpos)
  rw [← Nat.cast_prod]
  exact_mod_cast hle
