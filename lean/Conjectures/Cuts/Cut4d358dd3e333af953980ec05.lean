import Mathlib

open Finset

-- child 1 zh: 在无界的二倍区间里，真孪生素数对计数至少为某个正常数乘以 X/log(X)^2。
-- child 1 en: On arbitrarily late dyadic intervals the true twin-pair count is at least a positive constant times X divided by squared log X.
-- child 2 zh: 用 201 个起点的严格短窗覆盖二倍区间内的所有整数。
-- child 2 en: The strict short windows based at 201 starting points cover every integer in the dyadic interval.
set_option maxRecDepth 6000 in
theorem Conjectures.Cuts.Cut4d358dd3e333af953980ec05
    (hDensity : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      c * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 ≤
        (((Finset.Ioc X (2 * X)).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+2))).card : ℝ))
    (hCover : ∀ (x1 : ℕ),   (200 : ℕ) ≤ x1 →     ∀ (x3 : ℕ),       x1 < x3 →         x3 ≤ (2 : ℕ) * x1 →           ∃ x6 < (201 : ℕ),             have x7 : ℕ := Min.min ((2 : ℕ) * x1) (x1 + x1 / (100 : ℕ) * x6);             x7 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x7) : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 / Real.log ↑x3 ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)) | x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨c, hc, hDyadic⟩ := hDensity
  refine ⟨c/402, by positivity, ?_⟩
  intro B
  obtain ⟨X, hLate, hMass⟩ := hDyadic (max B 199)
  have hBX : B < X := (le_max_left _ _).trans_lt hLate
  have hX : 200 ≤ X := (show 199 < X from (le_max_right _ _).trans_lt hLate)
  let shell := (Ioc X (2*X)).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+2))
  let start := fun i : ℕ => min (2*X) (X+X/100*i)
  let win := fun Y : ℕ => (range (2*Y+1)).filter (fun n =>
    Y < n ∧ 50*n < 51*Y ∧ Nat.Prime n ∧ Nat.Prime (n+2))
  have covered : shell ⊆ (range 201).biUnion (fun i => win (start i)) := by
    intro n hn
    change n ∈ (Ioc X (2*X)).filter (fun m => Nat.Prime m ∧ Nat.Prime (m+2)) at hn
    have hpairs : n ∈ Ioc X (2*X) ∧ (Nat.Prime n ∧ Nat.Prime (n+2)) := mem_filter.mp hn
    obtain ⟨hInterval,hp,hp2⟩ := hpairs
    obtain ⟨hLo, hHi⟩ := mem_Ioc.mp hInterval
    obtain ⟨i, hi, hWindow⟩ := hCover X hX n hLo hHi
    change start i < n ∧ 50*n < 51*start i at hWindow
    have hRange : n < 2*start i+1 := by omega
    exact mem_biUnion.mpr ⟨i, mem_range.mpr hi,
      mem_filter.mpr ⟨mem_range.mpr hRange,hWindow.1,hWindow.2,hp,hp2⟩⟩
  obtain ⟨i, _, hMax⟩ := (range 201).exists_max_image
    (fun j => (win (start j)).card) (by exact ⟨0, mem_range.mpr (by decide)⟩)
  have hCard : shell.card ≤ 201*(win (start i)).card := calc
    shell.card ≤ ((range 201).biUnion (fun j => win (start j))).card := card_le_card covered
    _ ≤ ∑ j ∈ range 201, (win (start j)).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range 201, (win (start i)).card := sum_le_sum hMax
    _ = _ := by simp
  have hCardR : (shell.card : ℝ) ≤ 201*((win (start i)).card : ℝ) := by exact_mod_cast hCard
  have hLower : X ≤ start i := le_min (by omega) (Nat.le_add_right _ _)
  have hUpper : start i ≤ 2*X := min_le_left _ _
  have hXR : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hYR : (X : ℝ) ≤ (start i : ℝ) := by exact_mod_cast hLower
  have hUR : (start i : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast hUpper
  have hLog := Real.log_pos hXR
  have hLogs := Real.log_le_log (by linarith : (0 : ℝ) < X) hYR
  have hSq : (Real.log (X : ℝ))^2 ≤ (Real.log (start i : ℝ))^2 := by
    exact pow_le_pow_left₀ hLog.le hLogs 2
  have hBound : c * (X : ℝ) ≤ (201*((win (start i)).card : ℝ)) * (Real.log (start i : ℝ))^2 := calc
    _ ≤ (shell.card : ℝ) * (Real.log (X : ℝ))^2 := (div_le_iff₀ (sq_pos_of_pos hLog)).mp hMass
    _ ≤ _ := mul_le_mul hCardR hSq (sq_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  refine ⟨start i, hBX.trans_le hLower, ?_⟩
  change c/402*(start i : ℝ)/(Real.log (start i : ℝ))^2 ≤ ((win (start i)).card : ℝ)
  apply (div_le_iff₀ (sq_pos_of_pos (hLog.trans_le hLogs))).2
  nlinarith only [hBound, mul_le_mul_of_nonneg_left hUR hc.le]
