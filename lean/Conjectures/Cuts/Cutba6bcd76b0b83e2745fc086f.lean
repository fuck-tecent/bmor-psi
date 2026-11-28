import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 存在正实数 C，使带符号 Möbius–von Mangoldt 加权和在每个截点的绝对值不超过 C·X，且每个自然数作为整数都大于 -1。
-- child 1 en: There is a positive constant C bounding the absolute weighted Mertens sum by C·X at every cutoff, together with a trivial integer inequality.
-- child 2 zh: 每个自然数作为整数都非负。
-- child 2 en: Every natural number is nonnegative as an integer.

theorem Conjectures.Cuts.Cutba6bcd76b0b83e2745fc086f
  (h₁ : ∃ (C : ℝ), (0 : ℝ) < C ∧
      (∀ n : ℕ, (-1 : ℤ) < (n : ℤ)) ∧
      ∀ (X : ℕ), |∑ x3 ∈ Finset.range (X + (1 : ℕ)),
        ↑(ArithmeticFunction.moebius x3) *
          (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 +
            ∑ x4 ∈ x3.divisors,
              ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) *
          if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)| ≤
        C * (X : ℝ))
  (h₂ : ∀ n : ℕ, (0 : ℤ) ≤ (n : ℤ)) :
  (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), |∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)| ≤ x1 * ↑x2) := by
  obtain ⟨C, hC, _, hbound⟩ := h₁
  exact ⟨C, hC, hbound⟩
