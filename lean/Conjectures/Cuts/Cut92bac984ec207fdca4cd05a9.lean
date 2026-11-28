import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 窗口 (X, 51X/50) 内孪生素数对的（不加权）计数沿无界尺度线性增长。
-- child 1 en: The unweighted count of twin prime pairs in the window (X, 51X/50) grows linearly along unbounded scales.
-- child 2 zh: 每个孪生素数对的权重 log n · log(n+2) 至少为 1，故加权和支配不加权计数。
-- child 2 en: Each twin pair carries weight log n · log(n+2) at least one, so the weighted sum dominates the plain count.

theorem Conjectures.Cuts.Cut92bac984ec207fdca4cd05a9
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * ↑X ≤ ↑((Finset.range ((2 : ℕ) * X + (1 : ℕ))).filter (fun n => X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X ∧ Nat.Prime n ∧ Nat.Prime (n + (2 : ℕ)))).card)
    (h₂ : ∀ X : ℕ, (↑((Finset.range ((2 : ℕ) * X + (1 : ℕ))).filter (fun n => X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X ∧ Nat.Prime n ∧ Nat.Prime (n + (2 : ℕ)))).card : ℝ) ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * X + (1 : ℕ)), (if X < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * X ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ))) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)), if x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ)) := by
  obtain ⟨c, hc, hX⟩ := h₁
  refine ⟨c, hc, ?_⟩
  intro B
  obtain ⟨X, hB, hle⟩ := hX B
  exact ⟨X, hB, by linarith [h₂ X]⟩
