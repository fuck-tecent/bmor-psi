import Mathlib

open Finset

-- child 1 zh: 在任意晚的二倍区间内，真孪生素数对计数超过任意常数倍的平方根乘对数尺度。
-- child 1 en: The true twin-prime count in arbitrarily late dyadic intervals exceeds each constant times the square-root logarithmic scale.
-- child 2 zh: 用 201 个起点的严格短窗覆盖二倍区间内的所有整数。
-- child 2 en: The strict short windows based at 201 starting points cover every integer in the dyadic interval.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
theorem Conjectures.Cuts.Cuta642fcdcf212d2f61e157f3a
    (hDyadic : ∀ C : ℝ, ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      C * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) <
        (((Finset.Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ))
    (hCover : ∀ X : ℕ, 200 ≤ X → ∀ n : ℕ, X < n → n ≤ 2 * X →
      ∃ i < 201, let Y := min (2*X) (X+(X/100)*i); Y < n ∧ 50*n < 51*Y) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  intro window weight mass error K B
  let pairs := fun X : ℕ => (window X).filter (fun n => n.Prime ∧ (n + 2).Prime)
  let logScale := fun X : ℕ => Real.log (2 + (X : ℝ))
  let start := fun X i : ℕ => min (2 * X) (X + (X / 100) * i)
  let dyadic := fun X : ℕ => (Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)
  have logPos (X : ℕ) : 0 < logScale X := Real.log_pos (by
    change (1 : ℝ) < 2 + (X : ℝ)
    have h := Nat.cast_nonneg (α := ℝ) X
    linarith)
  have countLarge : ∀ C : ℝ, ∀ A : ℕ, ∃ Y : ℕ, A < Y ∧
      C * (Real.sqrt (Y : ℝ) * logScale Y) < ((pairs Y).card : ℝ) := by
    intro C A
    let D := max C 0
    have hD : 0 ≤ D := le_max_right _ _
    obtain ⟨X, hXlate, hLarge⟩ := hDyadic (201*D) (max A 199)
    have hAX : A < X := (le_max_left _ _).trans_lt hXlate
    have hX : 200 ≤ X := by omega
    by_contra! hNo
    have hSubset : dyadic X ⊆ (range 201).biUnion (fun i => pairs (start X i)) := by
      intro n hn
      obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
      obtain ⟨hnLo, hnHi⟩ := mem_Ioc.mp hnI
      obtain ⟨i, hi, hY⟩ := hCover X hX n hnLo hnHi
      change start X i < n ∧ 50*n < 51*start X i at hY
      have hnRange : n < 2 * start X i + 1 := by omega
      exact mem_biUnion.mpr ⟨i, mem_range.mpr hi,
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hnRange, hY⟩, hnP⟩⟩
    have hCompare (i : ℕ) (_hi : i ∈ range 201) :
        ((pairs (start X i)).card : ℝ) ≤
          D * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) := by
      have hBounds : X ≤ start X i ∧ start X i ≤ 2 * X :=
        ⟨le_min (by omega) (Nat.le_add_right _ _), min_le_left _ _⟩
      have hYr : (start X i : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hBounds.2
      have hLog : logScale (start X i) ≤ Real.log (2 + 2 * (X : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith only [hYr])
      have hScale := mul_le_mul (Real.sqrt_le_sqrt hYr) hLog
        (logPos (start X i)).le (Real.sqrt_nonneg _)
      have hNonneg := mul_nonneg (Real.sqrt_nonneg (start X i : ℝ)) (logPos (start X i)).le
      exact (hNo (start X i) (hAX.trans_le hBounds.1)).trans
        ((mul_le_mul_of_nonneg_right (le_max_left C 0) hNonneg).trans
          (mul_le_mul_of_nonneg_left hScale hD))
    have hCard : (dyadic X).card ≤ ∑ i ∈ range 201, (pairs (start X i)).card :=
      (card_le_card hSubset).trans card_biUnion_le
    have hCardR : ((dyadic X).card : ℝ) ≤ ∑ i ∈ range 201, ((pairs (start X i)).card : ℝ) := by
      exact_mod_cast hCard
    have hTotal : (∑ i ∈ range 201, D * (Real.sqrt (2 * (X : ℝ)) *
          Real.log (2 + 2 * (X : ℝ)))) =
        (201*D) * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    exact hLarge.not_ge (hCardR.trans ((sum_le_sum hCompare).trans_eq hTotal))
  obtain ⟨X, hXLate, hCount⟩ := countLarge (4*K) (max B 1)
  have hX : 2 ≤ X := by omega
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hRootPos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.2 hXp
  have hLogLower : logScale X / 2 ≤ Real.log (X : ℝ) := by
    have hTwice : logScale X ≤ 2 * Real.log (X : ℝ) := by
      calc
        logScale X ≤ Real.log ((X : ℝ)^2) :=
          Real.log_le_log (by positivity)
            (by nlinarith only [hXR, mul_nonneg (sub_nonneg.mpr hXR) (sub_nonneg.mpr hXR)])
        _ = _ := by rw [Real.log_pow]; norm_num
    linarith only [hTwice]
  have hTerm (n : ℕ) (hn : n ∈ pairs X) : logScale X ^ 2 / 4 ≤ weight n := by
    obtain ⟨hnW, hnPrime, hnNextPrime⟩ := mem_filter.mp hn
    obtain ⟨_, hnAbove, _⟩ := mem_filter.mp hnW
    have hnR : (X : ℝ) ≤ n := by exact_mod_cast hnAbove.le
    have hnNextR : (X : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by
      push_cast
      linarith only [hnR]
    have hl₁ := hLogLower.trans (Real.log_le_log hXp hnR)
    have hl₂ := hLogLower.trans (Real.log_le_log hXp hnNextR)
    have hBase : 0 ≤ logScale X / 2 := div_nonneg (logPos X).le (by norm_num)
    have hWeight := mul_le_mul hl₁ hl₂ hBase (hBase.trans hl₁)
    change _ ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
    rw [ArithmeticFunction.vonMangoldt_apply_prime hnPrime,
      ArithmeticFunction.vonMangoldt_apply_prime hnNextPrime]
    nlinarith only [hWeight]
  have hMassLower : ((pairs X).card : ℝ) * (logScale X ^ 2 / 4) ≤ (window X).sum weight := by
    calc
      _ = ∑ n ∈ pairs X, logScale X ^ 2 / 4 := by simp
      _ ≤ (pairs X).sum weight := sum_le_sum hTerm
      _ ≤ (window X).sum weight := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun n _ _ => show 0 ≤ ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt (n+2) from
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
  have hScaleEq : (logScale X ^ 3 / Real.sqrt (X : ℝ)) * (X : ℝ) =
      Real.sqrt (X : ℝ) * logScale X ^ 3 := by
    calc
      _ = logScale X ^ 3 / Real.sqrt (X : ℝ) * (Real.sqrt (X : ℝ))^2 := by rw [Real.sq_sqrt hXp.le]
      _ = _ := by field_simp [hRootPos.ne']
  refine ⟨X, (le_max_left _ _).trans_lt hXLate, ?_⟩
  change K * (logScale X ^ 3 / Real.sqrt (X : ℝ)) < (window X).sum weight / (X : ℝ)
  apply (lt_div_iff₀ hXp).2
  calc
    K * (logScale X ^ 3 / Real.sqrt (X : ℝ)) * (X : ℝ) =
        (4*K * (Real.sqrt (X : ℝ) * logScale X)) * (logScale X ^ 2 / 4) := by
      rw [mul_assoc, hScaleEq]
      ring
    _ < ((pairs X).card : ℝ) * (logScale X ^ 2 / 4) :=
      mul_lt_mul_of_pos_right hCount (div_pos (pow_pos (logPos X) _) (by norm_num))
    _ ≤ (window X).sum weight := hMassLower
