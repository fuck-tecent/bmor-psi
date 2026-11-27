import Mathlib

theorem Conjectures.Goldbach.Type2CornerMoebiusTruncation :
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); ∀ (a U : ℕ), 1 < a → (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) = - ∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d := by
  intro μ a U ha
  have hz : (∑ d ∈ a.divisors, ArithmeticFunction.moebius d) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply_ne (by omega)]
  have hr : (∑ d ∈ a.divisors, μ d) = (0:ℝ) := by dsimp only [μ]; exact_mod_cast hz
  have h := Finset.sum_filter_add_sum_filter_not a.divisors (fun d => U<d) μ
  simp only [not_lt] at h
  linarith
