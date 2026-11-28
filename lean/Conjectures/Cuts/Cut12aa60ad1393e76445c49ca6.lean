import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 二倍区间 (X, 2X] 内的孪生素数对计数最终至少为 X 除以 log X 的平方。
-- child 1 en: The twin-pair count in the dyadic interval (X, 2X] is eventually at least X divided by log X squared.
-- child 2 zh: 对任意常数 c，c 倍的 √(2X)·log(2+2X) 最终远小于 X/(log X)^2，故同一截点即可满足。
-- child 2 en: Any fixed multiple of sqrt(2X)*log(2+2X) is eventually far below X/(log X)^2, so one cutoff serves both.

theorem Conjectures.Cuts.Cut12aa60ad1393e76445c49ca6
    (h₁ : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ↑X / (Real.log ↑X) ^ 2 ≤ ↑{x4 ∈ Finset.Ioc X ((2 : ℕ) * X) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card)
    (h₂ : ∀ c : ℝ, ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * (√((2 : ℝ) * ↑X) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑X)) < ↑X / (Real.log ↑X) ^ 2) :
    (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * (√((2 : ℝ) * ↑x3) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x3)) < ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨X₀, hS⟩ := h₁
  intro c B
  obtain ⟨X, hB, hlt⟩ := h₂ c (max B X₀)
  refine ⟨X, by omega, ?_⟩
  exact lt_of_lt_of_le hlt (hS X (by omega))
