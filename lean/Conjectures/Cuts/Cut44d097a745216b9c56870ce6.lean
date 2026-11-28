import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 半素数项独自给出 Selberg 加权质量的正比例下界（陈景润型步骤）。
-- child 1 en: The semiprime terms alone carry a positive proportion of the Selberg-weighted mass.
-- child 2 zh: 每个被加项非负，故整和不少于其半素部分。
-- child 2 en: Every summand is nonnegative, so the whole sum dominates its semiprime part.

theorem Conjectures.Cuts.Cut44d097a745216b9c56870ce6
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      c * ↑X * Real.log ↑X ≤
        ∑ n ∈ (Finset.range (X + 1)).filter (fun n => ∃ d ∈ n.divisors, d.Prime ∧ (n / d).Prime ∧ d ≠ n / d),
          (ArithmeticFunction.moebius n : ℝ) ^ 2 *
          (ArithmeticFunction.vonMangoldt n * Real.log ↑n +
            ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
          (if Nat.Prime (n + 2) then Real.log (↑n + 2) else 0))
    (h₂ : ∀ n : ℕ, 0 ≤
      (ArithmeticFunction.moebius n : ℝ) ^ 2 *
      (ArithmeticFunction.vonMangoldt n * Real.log ↑n +
        ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
      (if Nat.Prime (n + 2) then Real.log (↑n + 2) else 0)) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 →
      x1 * ↑x3 * Real.log ↑x3 ≤
        ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)),
          ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) *
          (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 +
            ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) *
          if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) := by
  obtain ⟨c, hc, N, hN⟩ := h₁
  refine ⟨c, hc, N, ?_⟩
  intro X hX
  have hQ := hN X hX
  refine hQ.trans ?_
  have hsub : (Finset.range (X + 1)).filter
      (fun n => ∃ d ∈ n.divisors, d.Prime ∧ (n / d).Prime ∧ d ≠ n / d) ⊆ Finset.range (X + 1) :=
    Finset.filter_subset _ _
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun n =>
      (ArithmeticFunction.moebius n : ℝ) ^ 2 *
      (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
        ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
      (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0))
    hsub (fun n _ _ => h₂ n)
