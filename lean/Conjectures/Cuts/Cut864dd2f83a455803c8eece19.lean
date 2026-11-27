import Mathlib

open ArithmeticFunction Finset

-- child 1 zh: 第二塞尔伯格权乘以莫比乌斯函数后，恰为有序异素因子对的对数质量减去素数的平方对数权。
-- child 1 en: The second Selberg weight times the Möbius function is the ordered distinct-prime-factor log mass minus the squared-log prime weight.
-- child 2 zh: 对每个正 ε，在任意晚的截点，右移二位为素数时的异素因子对质量至多为对应素数质量加 ε X log X。
-- child 2 en: For every positive ε and arbitrarily late X, the ordered distinct-prime-factor mass with a prime at offset two is at most the corresponding prime mass plus ε X log X.
theorem Conjectures.Cuts.Cut864dd2f83a455803c8eece19
    (hIdentity : ∀ n : ℕ, (moebius n : ℝ) * (vonMangoldt n * Real.log (n : ℝ) +
      ∑ p ∈ n.divisors, vonMangoldt p * vonMangoldt (n / p)) =
      (∑ p ∈ n.divisors with p.Prime ∧ (n / p).Prime ∧ p ≠ n / p,
        Real.log (p : ℝ) * Real.log ((n / p : ℕ) : ℝ)) -
      (if n.Prime then (Real.log (n : ℝ))^2 else 0))
    (hCounts : let w := fun n : ℕ => if (n+2).Prime then Real.log ((n : ℝ)+2) else 0
      let S := fun X : ℕ => ∑ n ∈ range (X+1),
        (∑ p ∈ n.divisors with p.Prime ∧ (n / p).Prime ∧ p ≠ n / p,
          Real.log (p : ℝ) * Real.log ((n / p : ℕ) : ℝ)) * w n
      let P := fun X : ℕ => ∑ n ∈ range (X+1),
        (if n.Prime then (Real.log (n : ℝ))^2 else 0) * w n
      ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, ∃ X : ℕ, B < X ∧
        S X ≤ P X + ε * (X : ℝ) * Real.log (X : ℝ)) :
    (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℕ), x3 < x4 ∧ (∑ x5 ∈ Finset.range (x4 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x4 * Real.log ↑x4) := by
  intro ε hε B
  dsimp only at hCounts
  obtain ⟨X, hX, hBound⟩ := hCounts ε hε B
  refine ⟨X, hX, ?_⟩
  simp_rw [hIdentity, sub_mul, Finset.sum_sub_distrib]
  linarith only [hBound]
