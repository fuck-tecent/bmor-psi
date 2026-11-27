import Mathlib

-- child 1 en: The number of twin pairs is at least a positive multiple of X divided by squared log X on arbitrarily large strict windows.
-- child 1 zh: 在无界的严格短窗上，孪生素数对的个数至少为某个正常数乘以 X，再除以 log X 的平方。
-- child 2 en: For X at least 3, the squared log of X times the twin-pair count is at most the log-weighted mass in the same window.
-- child 2 zh: 当 X 至少为 3 时，短窗的孪生素数对个数乘以 log X 的平方，不超过同一短窗的对数权质量。

theorem Conjectures.Cuts.Cutb4a61d6d8562c8fdfa3301e6
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      c * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 ≤
        ↑{n ∈ Finset.range (2 * X + 1) |
          X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime}.card)
    (h₂ : ∀ X : ℕ, 3 ≤ X →
      (Real.log (X : ℝ)) ^ 2 *
        ↑{n ∈ Finset.range (2 * X + 1) |
          X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime}.card ≤
      ∑ n ∈ Finset.range (2 * X + 1),
        if X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime then
          Real.log (n : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)
        else 0) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)), if x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ)) := by
  obtain ⟨c, hc, hCount⟩ := h₁
  refine ⟨c, hc, fun B => ?_⟩
  obtain ⟨X, hBX, hX⟩ := hCount (max B 3)
  have hLarge : 3 ≤ X := (le_max_right B 3).trans hBX.le
  have hLog : 0 < Real.log (X : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < X by omega))
  refine ⟨X, (le_max_left B 3).trans_lt hBX, ?_⟩
  exact ((div_le_iff₀ (pow_pos hLog 2)).mp hX).trans
    (by simpa only [mul_comm] using h₂ X hLarge)
