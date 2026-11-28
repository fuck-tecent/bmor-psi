import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 en: the absolute value of the weighted Mertens sum is O(X).
-- child 1 zh: 加权 Mertens 和的绝对值被某个 C·X 控制。
-- child 2 en: every natural number is nonnegative as a real.
-- child 2 zh: 每个自然数作为实数非负。

theorem Conjectures.Cuts.Cut9587b9558744ab0bb7976db5
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      |(∑ x3 ∈ Finset.range (X + (1 : ℕ)),
        ↑(ArithmeticFunction.moebius x3) *
          (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 +
            ∑ x4 ∈ x3.divisors,
              ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) *
          if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))|
        ≤ C * (X : ℝ))
    (h₂ : ∀ n : ℕ, 0 ≤ (n : ℝ)) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x2) := by
  obtain ⟨C, hC, hbound⟩ := h₁
  refine ⟨C, hC, ?_⟩
  intro X
  exact (le_abs_self _).trans (hbound X)
