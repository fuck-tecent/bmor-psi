import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 en: absolute-value parity cancellation along unbounded scales: for every positive epsilon
-- and every starting bound there is a larger scale where |weighted sum| is at most epsilon times X log X.
-- child 1 zh: 绝对值版奇偶抵消：对每个正 epsilon 和每个起点，存在更大尺度使 |加权和| ≤ epsilon·X·log X。
-- child 2 en: every natural number is nonnegative as an integer.
-- child 2 zh: 每个自然数作为整数非负。

theorem Conjectures.Cuts.Cut53eac3acbc67d4fa6b82a522
    (h₁ : ∀ (ε : ℝ), (0 : ℝ) < ε → ∀ (N : ℕ), ∃ (X : ℕ), N < X ∧
      |(∑ n ∈ Finset.range (X + (1 : ℕ)),
          ↑(ArithmeticFunction.moebius n) *
            (ArithmeticFunction.vonMangoldt n * Real.log ↑n +
              ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ))|
        ≤ ε * ↑X * Real.log ↑X)
    (h₂ : ∀ n : ℕ, (0 : ℤ) ≤ (n : ℤ)) :
    (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℕ), x3 < x4 ∧ (∑ x5 ∈ Finset.range (x4 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x4 * Real.log ↑x4) := by
  intro ε hε N
  obtain ⟨X, hNX, hbound⟩ := h₁ ε hε N
  refine ⟨X, hNX, ?_⟩
  exact le_trans (le_abs_self _) hbound
