import Mathlib

-- child 1 zh: 所有正秩布尔矩阵均存在目标指数尺度的近单色矩形，高误差项的比例至多为 1/(4(r+1))。
-- child 1 en: Every positive-rank Boolean matrix admits a rectangle at the target exponent scale, with at most a 1/(4(r+1)) fraction of entries differing from a single Boolean value.
-- child 2 zh: 在这个误差阈值内，矩形含有同值的单色子矩形，面积至少保留四分之一。
-- child 2 en: Below this error threshold, the rectangle contains a monochromatic subrectangle of the specified value occupying at least one quarter of its area.

theorem Conjectures.Cuts.Cut59db49de9084573dce7a9f25
    (hBias : ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ),
      0 < m → 0 < n → (∀ i j, M i j = 0 ∨ M i j = 1) → 1 ≤ M.rank →
      ∃ (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ),
        (v = 0 ∨ v = 1) ∧
        4 * (M.rank + 1) * ((A.product B).filter (fun ij => M ij.1 ij.2 ≠ v)).card ≤
          A.card * B.card ∧
        (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2
          (C * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ)))
    (hClean : ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ)
      (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ),
      (∀ i j, M i j = 0 ∨ M i j = 1) → (v = 0 ∨ v = 1) →
      4 * (M.rank + 1) * ((A.product B).filter (fun ij => M ij.1 ij.2 ≠ v)).card ≤
        A.card * B.card →
      ∃ (A' : Finset (Fin m)) (B' : Finset (Fin n)),
        A' ⊆ A ∧ B' ⊆ B ∧ (∀ i ∈ A', ∀ j ∈ B', M i j = v) ∧
        A.card * B.card ≤ 4 * (A'.card * B'.card)) :
    (∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ), 0 < m → 0 < n → (∀ i j, M i j = 0 ∨ M i j = 1) → 1 ≤ M.rank → ∃ (A : Finset (Fin m)) (B : Finset (Fin n)) (v : ℝ), (∀ i ∈ A, ∀ j ∈ B, M i j = v) ∧ (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2 (C * Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ))) := by
  obtain ⟨C, hC, hNear⟩ := hBias
  refine ⟨C + 2, by linarith, ?_⟩
  intro m n M hm hn hBoolean hRank
  obtain ⟨A, B, v, hv, hErr, hArea⟩ := hNear m n M hm hn hBoolean hRank
  obtain ⟨A', B', _, _, hMono, hKeep⟩ := hClean m n M A B v hBoolean hv hErr
  refine ⟨A', B', v, hMono, ?_⟩
  let t : ℝ := Real.rpow (M.rank : ℝ) (49999 / 100000 : ℝ)
  have ht : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast hRank) (by norm_num)
  have hKeepR : (A.card : ℝ) * B.card ≤ 4 * ((A'.card : ℝ) * B'.card) := by
    exact_mod_cast hKeep
  have hGrow : (4 : ℝ) * Real.rpow 2 (C * t) ≤ Real.rpow 2 ((C + 2) * t) := by
    calc
      (4 : ℝ) * Real.rpow 2 (C * t) = Real.rpow 2 (2 + C * t) := by
        change 4 * (2 : ℝ) ^ (C * t) = (2 : ℝ) ^ ((2 : ℝ) + C * t)
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ Real.rpow 2 ((C + 2) * t) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  calc
    (m : ℝ) * n ≤ (A.card : ℝ) * B.card * Real.rpow 2 (C * t) := hArea
    _ ≤ (4 * ((A'.card : ℝ) * B'.card)) * Real.rpow 2 (C * t) :=
      mul_le_mul_of_nonneg_right hKeepR (Real.rpow_nonneg (by norm_num) _)
    _ = ((A'.card : ℝ) * B'.card) * (4 * Real.rpow 2 (C * t)) := by ring
    _ ≤ ((A'.card : ℝ) * B'.card) * Real.rpow 2 ((C + 2) * t) :=
      mul_le_mul_of_nonneg_left hGrow (by positivity)
