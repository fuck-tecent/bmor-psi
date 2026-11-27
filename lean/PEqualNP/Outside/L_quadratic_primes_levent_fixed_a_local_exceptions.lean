import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_local_exceptions :
    ∀ a : ℕ, 0<a → (∑ p ∈ (2*a).primeFactors, Real.log (p : ℝ)) ≤ Real.log ((2*a : ℕ) : ℝ) := by
  intro a ha
  have hn : 0 < 2*a := by omega
  have hdvd : (∏ p ∈ (2*a).primeFactors, p) ∣ 2*a := Nat.prod_primeFactors_dvd (2*a)
  have hle_nat : (∏ p ∈ (2*a).primeFactors, p) ≤ 2*a := Nat.le_of_dvd hn hdvd
  have hcast : ((∏ p ∈ (2*a).primeFactors, p : ℕ) : ℝ)
      = ∏ p ∈ (2*a).primeFactors, (p:ℝ) := by push_cast; rfl
  have hle : (∏ p ∈ (2*a).primeFactors, (p:ℝ)) ≤ ((2*a : ℕ) : ℝ) := by
    rw [← hcast]
    exact_mod_cast hle_nat
  have hposprod : 0 < ∏ p ∈ (2*a).primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact_mod_cast hp'.pos
  have hlog : Real.log (∏ p ∈ (2*a).primeFactors, (p:ℝ)) ≤ Real.log ((2*a : ℕ) : ℝ) :=
    Real.log_le_log hposprod hle
  have hlogprod : Real.log (∏ p ∈ (2*a).primeFactors, (p:ℝ))
      = ∑ p ∈ (2*a).primeFactors, Real.log (p:ℝ) := by
    apply Real.log_prod
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp'.pos
    exact ne_of_gt hpos
  rwa [hlogprod] at hlog
