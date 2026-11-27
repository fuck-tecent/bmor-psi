import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 存在正常数 C，使加权 Mertens 和在每个 X 上都被 C·X 控制。
-- child 1 en: There is a positive constant C bounding the weighted Mertens sum by C·X at every X.
-- child 2 zh: 对任意正常数 C 与 ε，充分大的 X 满足 C·X ≤ ε·X·log X。
-- child 2 en: For any positive C and ε, all sufficiently large X satisfy C·X ≤ ε·X·log X.

theorem Conjectures.Cuts.Cut33246c487eb7c57024bca565
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ x5 ∈ Finset.range (X + 1),
        ↑(ArithmeticFunction.moebius x5) *
        (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 +
          ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) *
        if Nat.Prime (x5 + 2) then Real.log (↑x5 + 2) else 0) ≤ C * ↑X)
    (h₂ : ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ X : ℕ, N ≤ X → C * ↑X ≤ ε * ↑X * Real.log ↑X) :
    (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℕ), x3 < x4 ∧
      (∑ x5 ∈ Finset.range (x4 + 1),
        ↑(ArithmeticFunction.moebius x5) *
        (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 +
          ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) *
        if Nat.Prime (x5 + 2) then Real.log (↑x5 + 2) else 0)
      ≤ x1 * ↑x4 * Real.log ↑x4) := by
  obtain ⟨C, hC, hS⟩ := h₁
  intro ε hε B
  obtain ⟨N, hN⟩ := h₂ C hC ε hε
  have hB : B < max B N + 1 := by omega
  have hNle : N ≤ max B N + 1 := by omega
  refine ⟨max B N + 1, hB, ?_⟩
  have h1 := hS (max B N + 1)
  have h2 := hN (max B N + 1) hNle
  linarith
