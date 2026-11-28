import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 加权奇偶和在每个截点都被常数倍的 X 控制，即 Hardy–Littlewood 启发预测的 O(X) 界。
-- child 1 en: The weighted parity sum is bounded by a constant multiple of X at every cutoff, the O(X) Hardy-Littlewood heuristic.
-- child 2 zh: 线性尺度最终被 ε 倍的 X log X 吸收，因为对数因子压倒任意固定常数。
-- child 2 en: A linear scale is eventually absorbed by eps times X log X, since the logarithmic factor beats every fixed constant.

theorem Conjectures.Cuts.Cut7f5165f3e8500a195ea0b244
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, (∑ x5 ∈ Finset.range (X + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) ≤ C * ↑X)
    (h₂ : ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X → C * ↑X ≤ ε * ↑X * Real.log ↑X) :
    (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℕ), x3 < x4 ∧ (∑ x5 ∈ Finset.range (x4 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x4 * Real.log ↑x4) := by
  obtain ⟨C, hC, hS⟩ := h₁
  intro ε hε B
  obtain ⟨N, hN⟩ := h₂ C hC ε hε
  have hB : B < max B N + 1 := by omega
  have hNle : N ≤ max B N + 1 := by omega
  refine ⟨max B N + 1, hB, ?_⟩
  have h1 := hS (max B N + 1)
  have h2 := hN (max B N + 1) hNle
  linarith
