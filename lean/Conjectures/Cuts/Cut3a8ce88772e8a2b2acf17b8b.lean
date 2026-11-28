import Mathlib

-- child 1 zh: 右移二位为素数的异素因子半素数项提供最终的正加权下界。
-- child 1 en: The shifted distinct-semiprime terms supply an eventual positive weighted lower bound.
-- child 2 zh: 每个自然数的二阶 Mangoldt 权乘 Möbius 平方后恰为半素数权与素数权之和。
-- child 2 en: The squarefree second Mangoldt weight equals the sum of distinct-semiprime and prime weights.
theorem Conjectures.Cuts.Cut3a8ce88772e8a2b2acf17b8b
    (hSemiprime : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)) with ∃ x6 ∈ x5.divisors, Nat.Prime x6 ∧ Nat.Prime (x5 / x6) ∧ x6 ≠ x5 / x6, ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ)))
    (hSplit : (∀ (x1 : ℕ), ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) = ∑ x2 ∈ x1.divisors with Nat.Prime x2 ∧ Nat.Prime (x1 / x2) ∧ x2 ≠ x1 / x2, Real.log ↑x2 * Real.log ↑(x1 / x2) + if Nat.Prime x1 then Real.log ↑x1 ^ (2 : ℕ) else (0 : ℝ))) :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∃ (x4 : ℝ), (0 : ℝ) < x4 ∧ ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → x4 * ↑x6 * Real.log ↑x6 ≤ x2 x6 + x3 x6) := by
  obtain ⟨c, hc, N, hMass⟩ := hSemiprime
  refine ⟨c, hc, N, ?_⟩
  intro X hX
  let shiftedLog (n : ℕ) : ℝ :=
    if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0
  let semiWeight (n : ℕ) : ℝ :=
    ∑ d ∈ n.divisors with d.Prime ∧ (n / d).Prime ∧ d ≠ n / d,
      Real.log (d : ℝ) * Real.log ((n / d : ℕ) : ℝ)
  let primeWeight (n : ℕ) : ℝ :=
    if n.Prime then (Real.log (n : ℝ)) ^ 2 else 0
  let semiprimes := (Finset.range (X + 1)).filter fun n =>
    ∃ d ∈ n.divisors, d.Prime ∧ (n / d).Prime ∧ d ≠ n / d
  change c * (X : ℝ) * Real.log (X : ℝ) ≤
    (∑ n ∈ Finset.range (X + 1), semiWeight n * shiftedLog n) +
    ∑ n ∈ Finset.range (X + 1), primeWeight n * shiftedLog n
  have hSplitSum :
      c * (X : ℝ) * Real.log (X : ℝ) ≤
        ∑ n ∈ semiprimes, (semiWeight n + primeWeight n) * shiftedLog n := by
    have hLower := hMass X hX
    simp only [hSplit] at hLower
    exact hLower
  have hLogNonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
    rcases n with _ | n
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)
  have hWeight (n : ℕ) : 0 ≤ (semiWeight n + primeWeight n) * shiftedLog n := by
    have hSemi : 0 ≤ semiWeight n :=
      Finset.sum_nonneg fun d _ => mul_nonneg (hLogNonneg d) (hLogNonneg (n / d))
    have hPrime : 0 ≤ primeWeight n := by
      dsimp [primeWeight]
      split
      · exact sq_nonneg _
      · exact le_rfl
    have hShift : 0 ≤ shiftedLog n := by
      dsimp [shiftedLog]
      split
      · have hn := Nat.cast_nonneg (α := ℝ) n
        exact Real.log_nonneg (by linarith)
      · exact le_rfl
    exact mul_nonneg (add_nonneg hSemi hPrime) hShift
  calc
    _ ≤ ∑ n ∈ semiprimes, (semiWeight n + primeWeight n) * shiftedLog n := hSplitSum
    _ ≤ ∑ n ∈ Finset.range (X + 1), (semiWeight n + primeWeight n) * shiftedLog n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => hWeight n
    _ = _ := by simp only [add_mul, Finset.sum_add_distrib]
