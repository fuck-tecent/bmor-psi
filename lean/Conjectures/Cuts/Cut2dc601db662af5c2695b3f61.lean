import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 en: a positive constant bounds the absolute value of the weighted divisor-sum at every cutoff.
-- child 1 zh: 存在正数 C，使加权除数和的绝对值在每个截点都被 C·X 控制。
-- child 2 en: every natural number is nonnegative as an integer.
-- child 2 zh: 每个自然数作为整数非负。

theorem Conjectures.Cuts.Cut2dc601db662af5c2695b3f61
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      |(∑ x3 ∈ Finset.range (X + (1 : ℕ)),
        (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors,
          ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) *
          if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))|
        ≤ C * (X : ℝ))
    (h₂ : ∀ n : ℕ, (0 : ℤ) ≤ (n : ℤ)) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (↑(ArithmeticFunction.moebius x3) * ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x2) := by
  obtain ⟨C, hC, hbound⟩ := h₁
  refine ⟨C, hC, ?_⟩
  intro X
  exact (le_abs_self _).trans (hbound X)
