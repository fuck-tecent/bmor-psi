import Mathlib
theorem PEqualNP.Outside.L_twin_primes_mangoldt_divisors : ∀ n : ℕ, 0 < n → ArithmeticFunction.vonMangoldt n = n.divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d) := by
  intro n hn
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  change (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d) = -ArithmeticFunction.vonMangoldt n at h
  calc
    ArithmeticFunction.vonMangoldt n = -(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d) := by linarith
    _ = ∑ d ∈ n.divisors, -(ArithmeticFunction.moebius d : ℝ)*Real.log d := by simp [Finset.sum_neg_distrib]

