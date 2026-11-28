import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 只取 Lambda(n)·log n 这一支的加权和在每个截点都是 O(X)。
-- child 1 en: The weighted sum of the Lambda(n)*log n branch alone is O(X) at every cutoff.
-- child 2 zh: 只取除数和那一支的加权和在每个截点也是 O(X)。
-- child 2 en: The weighted sum of the divisor-sum branch alone is O(X) at every cutoff.

theorem Conjectures.Cuts.Cutbf901f24a78d99f33739f1c2
    (h₁ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ X : ℕ, (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ C1 * ↑X)
    (h₂ : ∃ C2 : ℝ, 0 < C2 ∧ ∀ X : ℕ, (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * (∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4))) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ C2 * ↑X) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x2) := by
  obtain ⟨C1, hC1, hS1⟩ := h₁
  obtain ⟨C2, hC2, hS2⟩ := h₂
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro X
  have hsplit : ∀ n : ℕ,
      ↑(ArithmeticFunction.moebius n) * ((ArithmeticFunction.vonMangoldt n * Real.log ↑n) + (∑ x4 ∈ n.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (n / x4))) * (if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ))
        = (↑(ArithmeticFunction.moebius n) * (ArithmeticFunction.vonMangoldt n * Real.log ↑n)) * (if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ)) + (↑(ArithmeticFunction.moebius n) * (∑ x4 ∈ n.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (n / x4))) * (if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ)) := by
    intro n
    ring
  rw [Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_add_distrib]
  linarith [hS1 X, hS2 X]
