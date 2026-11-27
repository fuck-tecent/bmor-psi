import Mathlib

-- child 1 en: On every natural number, multiplying the second Mangoldt weight by the square of Möbius gives the distinct-semiprime mass plus the prime mass.
-- child 1 zh: 在每个自然数上，二阶 Mangoldt 权乘 Möbius 函数平方，恰等于不同素因子半素数的质量加上素数质量。
-- child 2 en: The sum of the separately counted shifted semiprime and shifted prime masses is at least a fixed positive multiple of x log x for all sufficiently large x.
-- child 2 zh: 分别计入移位半素数质量和移位素数质量后，两项之和最终至少为 x log x 的一个固定正倍数。

theorem Conjectures.Cuts.Cut4e9624e018c89e4663e3e47b
    (h₁ : ∀ n : ℕ,
      (ArithmeticFunction.moebius n : ℝ) ^ 2 *
        (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
          ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (n / d)) =
      (∑ d ∈ n.divisors with d.Prime ∧ (n / d).Prime ∧ d ≠ n / d,
        Real.log (d : ℝ) * Real.log ((n / d : ℕ) : ℝ)) +
      (if n.Prime then (Real.log (n : ℝ)) ^ 2 else 0))
    (h₂ :
      let W := fun n : ℕ => if (n + 2).Prime then Real.log ((n : ℝ) + 2) else 0
      let semi := fun X : ℕ => ∑ n ∈ Finset.range (X + 1),
        (∑ d ∈ n.divisors with d.Prime ∧ (n / d).Prime ∧ d ≠ n / d,
          Real.log (d : ℝ) * Real.log ((n / d : ℕ) : ℝ)) * W n
      let prime := fun X : ℕ => ∑ n ∈ Finset.range (X + 1),
        (if n.Prime then (Real.log (n : ℝ)) ^ 2 else 0) * W n
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        c * (X : ℝ) * Real.log (X : ℝ) ≤ semi X + prime X) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) := by
  dsimp only at h₂
  obtain ⟨c, hc, N, hMass⟩ := h₂
  refine ⟨c, hc, N, fun X hX => ?_⟩
  simp only [h₁, add_mul, Finset.sum_add_distrib]
  exact hMass X hX
