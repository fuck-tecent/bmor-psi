import Mathlib

-- child 1 en: Reuse the existing strict-window lower bound at a fixed positive constant on the scale X divided by squared log X.
-- child 1 zh: 复用已登记的严格短窗计数下界，尺度为 X 除以 log X 的平方乘一个固定正常数。
-- child 2 en: For every fixed multiplier K and positive coefficient c, the square-root logarithmic scale is eventually strictly below c times X divided by squared log X.
-- child 2 zh: 对任意固定倍数 K 与正常数 c，平方根乘对数的尺度最终严格小于 cX 除以 log X 的平方。

theorem Conjectures.Cuts.Cutca89c0ea19ac09288e3859eb
    (h₁ : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 / Real.log ↑x3 ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)) | x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card))
    (h₂ : (∀ c : ℝ, 0 < c → ∀ K : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      K * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) <
        c * (X : ℝ) / (Real.log (X : ℝ)) ^ 2)) :
    (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * (√((2 : ℝ) * ↑x3) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x3)) < ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨c, hc, hCount⟩ := h₁
  intro K B
  obtain ⟨N, hScale⟩ := h₂ c hc K
  obtain ⟨X, hX, hCountX⟩ := hCount (max B N)
  have hXN : N ≤ X := (le_max_right B N).trans hX.le
  let short := (Finset.range (2 * X + 1)).filter
    (fun n => X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime)
  let dyadic := (Finset.Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)
  have hSub : short ⊆ dyadic := by
    intro n hn
    obtain ⟨hRange, hx, _, hp, hp2⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hx, Nat.lt_succ_iff.mp (Finset.mem_range.mp hRange)⟩, hp, hp2⟩
  have hCard : (short.card : ℝ) ≤ (dyadic.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  exact ⟨X, (le_max_left B N).trans_lt hX, (hScale X hXN).trans_le (hCountX.trans hCard)⟩
