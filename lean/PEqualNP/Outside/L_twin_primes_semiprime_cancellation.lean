import Mathlib
theorem PEqualNP.Outside.L_twin_primes_semiprime_cancellation : ∀ r q : ℕ, r.Prime → q.Prime → r ≠ q → (r*q).divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d) = 0 := by
  intro r q hr hq hne
  have hnot : ¬ IsPrimePow (r*q) := by
    intro h
    obtain ⟨p, hp, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    have hpr : r = p := huniq r ⟨hr, dvd_mul_right r q⟩
    have hpq : q = p := huniq q ⟨hq, dvd_mul_left q r⟩
    exact hne (hpr.trans hpq.symm)
  have hz : ArithmeticFunction.vonMangoldt (r*q) = 0 := by simp [ArithmeticFunction.vonMangoldt_apply, hnot]
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := r*q)
  change (∑ d ∈ (r*q).divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d) = -ArithmeticFunction.vonMangoldt (r*q) at h
  rw [hz] at h
  simp only [neg_zero] at h
  simpa [Finset.sum_neg_distrib] using congrArg Neg.neg h


