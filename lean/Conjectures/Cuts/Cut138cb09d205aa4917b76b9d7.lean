import Mathlib

-- child 1 zh: 粗糙集合内素数或异素因子半素数的计数最终至少为正常数乘以 X/log(X)^2。
-- child 1 en: Primes and products of two distinct primes in the rough set eventually number at least a positive multiple of X / log(X)^2.
-- child 2 zh: 同一粗糙集合的总数最终至多为正常数乘以 X/log(X)^2。
-- child 2 en: The same rough set eventually has cardinality at most a positive multiple of X / log(X)^2.
theorem Conjectures.Cuts.Cut138cb09d205aa4917b76b9d7
    (hLower :
      let rough : ℕ → Finset ℕ := fun (X : ℕ) => {n ∈ Finset.range (X + 1) |
        1 < n ∧ (n + 2).Prime ∧ ∀ q ∈ n.divisors, q.Prime → X ≤ q ^ 10}
      let good : ℕ → Prop := fun n : ℕ =>
      n.Prime ∨ ∃ d ∈ n.divisors, d.Prime ∧ (n / d).Prime ∧ d ≠ n / d
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        c * (X : ℝ) ≤ (((rough X).filter good).card : ℝ) * Real.log (X : ℝ) ^ 2)
    (hUpper :
      let rough : ℕ → Finset ℕ := fun (X : ℕ) => {n ∈ Finset.range (X + 1) |
        1 < n ∧ (n + 2).Prime ∧ ∀ q ∈ n.divisors, q.Prime → X ≤ q ^ 10}
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        ((rough X).card : ℝ) * Real.log (X : ℝ) ^ 2 ≤ C * (X : ℝ)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}; let x2 : ℕ → Prop := fun (x2 : ℕ) => Nat.Prime x2 ∨ ∃ x3 ∈ x2.divisors, Nat.Prime x3 ∧ Nat.Prime (x2 / x3) ∧ x3 ≠ x2 / x3; ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → ↑{x7 ∈ x1 x5 | ¬x2 x7}.card ≤ ((1 : ℝ) - x3) * ↑(x1 x5).card) := by
  classical
  obtain ⟨c, hc, M, hGood⟩ := hLower
  obtain ⟨C, hC, N, hRough⟩ := hUpper
  refine ⟨c / C, div_pos hc hC, max (max M N) 2, ?_⟩
  intro X hX
  let rough : Finset ℕ := {n ∈ Finset.range (X + 1) |
    1 < n ∧ (n + 2).Prime ∧ ∀ q ∈ n.divisors, q.Prime → X ≤ q ^ 10}
  let good : ℕ → Prop := fun n : ℕ =>
      n.Prime ∨ ∃ d ∈ n.divisors, d.Prime ∧ (n / d).Prime ∧ d ≠ n / d
  change (((rough.filter (fun n => ¬ good n)).card : ℝ)) ≤
    (1 - c / C) * (rough.card : ℝ)
  have hM : M ≤ X := by omega
  have hN : N ≤ X := by omega
  have hLog : 0 < Real.log (X : ℝ) ^ 2 :=
    sq_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
  have hScaled : (c / C) * (rough.card : ℝ) * Real.log (X : ℝ) ^ 2 ≤
      ((rough.filter good).card : ℝ) * Real.log (X : ℝ) ^ 2 := calc
    _ = (c / C) * ((rough.card : ℝ) * Real.log (X : ℝ) ^ 2) := mul_assoc _ _ _
    _ ≤ (c / C) * (C * (X : ℝ)) := mul_le_mul_of_nonneg_left (hRough X hN) (by positivity)
    _ = c * (X : ℝ) := by rw [← mul_assoc, div_mul_cancel₀ c hC.ne']
    _ ≤ _ := hGood X hM
  have hProportion := le_of_mul_le_mul_right hScaled hLog
  have hPartition : ((rough.filter good).card : ℝ) +
      ((rough.filter (fun n => ¬ good n)).card : ℝ) = rough.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := rough) good
  linarith only [hProportion, hPartition]
