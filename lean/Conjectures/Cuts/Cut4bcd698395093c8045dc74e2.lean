import Mathlib

-- child 1 zh: 正计数下界（沿无界的严格窗）：存在常数 c 大于 0，使得对每个起点 B 都存在 X 大于 B，窗口 X 小于 n 小于 51X 之 50 内孪生素数对 n 与 n+2 的个数至少为 c 倍 X。
-- child 1 en: Positive count on unbounded strict windows: some constant c above 0 with, for every bound B, an X above B whose number of twin prime pairs n and n+2 inside the window X below n below 51X over 50 is at least c times X.
-- child 2 zh: 计数不超过质量：对每个 X，窗口内孪生素数对的个数不超过它们的对数权质量，因为窗口内 n 至少为 3，从而 log n 与 log (n+2) 都至少为 1。
-- child 2 en: Count at most mass: for every X, the number of twin prime pairs inside the strict window is at most their log-weighted mass, since n is at least 3 inside the window, so log n and log (n+2) are both at least 1.
-- Refinement of the positive-mass child of the first cut: the mass lower bound splits into a count lower bound (open) and the termwise comparison of the count with the log-weighted mass.

theorem Conjectures.Cuts.Cut4bcd698395093c8045dc74e2
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * (X:ℝ) ≤
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2))).card)
    (h₂ : ∀ X : ℕ,
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2))).card ≤
      ∑ n ∈ Finset.range (2*X+1),
        if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)), if x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ)) := by
  obtain ⟨c, hc0, hc⟩ := h₁
  refine ⟨c, hc0, fun B => ?_⟩
  obtain ⟨X, hBX, hXc⟩ := hc B
  exact ⟨X, hBX, le_trans hXc (h₂ X)⟩
