import Mathlib

/-!
Cut of `L-log-rank-improved-general-rectangle-exponent` (log-rank) into two rank regimes with an explicit threshold.

child 1 zh: 秩不超过 1000 的布尔矩阵存在密度至少 2^(−C·r^0.49999) 的单色矩形，常数在整档内有界秩上统一。
child 1 en: Boolean matrices of rank at most 1000 carry a monochromatic rectangle of density at least
  2^(−C·r^0.49999), with one constant uniform over the whole bounded-rank regime.
child 2 zh: 秩不小于 1000 的布尔矩阵在同一形式下存在单色矩形，常数与有界秩档独立。
child 2 en: Boolean matrices of rank at least 1000 obey the same density lower bound with an
  independent constant; the two regimes overlap only at rank 1000.
-/

theorem Conjectures.Cuts.Cut3b8ff484100ea7f27c661e88
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ), 0 < m → 0 < n → (∀ i j, M i j = 0 ∨ M i j = 1) → 1 ≤ M.rank → M.rank ≤ 1000 → ∃ (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ), (∀ i ∈ A, ∀ j ∈ B, M i j = v) ∧ (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2 (C * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ)))
    (h₂ : ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ), 0 < m → 0 < n → (∀ i j, M i j = 0 ∨ M i j = 1) → 1 ≤ M.rank → 1000 ≤ M.rank → ∃ (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ), (∀ i ∈ A, ∀ j ∈ B, M i j = v) ∧ (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2 (C * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ))) :
    (∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ), 0 < m → 0 < n → (∀ i j, M i j = 0 ∨ M i j = 1) → 1 ≤ M.rank → ∃ (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ), (∀ i ∈ A, ∀ j ∈ B, M i j = v) ∧ (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2 (C * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ))) := by
  obtain ⟨C₁, hC₁, hsmall⟩ := h₁
  obtain ⟨C₂, hC₂, hlarge⟩ := h₂
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left C₁ C₂), ?_⟩
  intro m n M hm hn hbool hrank
  by_cases hle : M.rank ≤ 1000
  · obtain ⟨A, B, v, hv, hbound⟩ := hsmall m n M hm hn hbool hrank hle
    refine ⟨A, B, v, hv, le_trans hbound ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (Real.rpow_nonneg (Nat.cast_nonneg M.rank) _)
  · obtain ⟨A, B, v, hv, hbound⟩ := hlarge m n M hm hn hbool hrank (by omega)
    refine ⟨A, B, v, hv, le_trans hbound ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.rpow_nonneg (Nat.cast_nonneg M.rank) _)
