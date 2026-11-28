import Mathlib

-- child 1 zh: 短窗（H² ≤ X，即 H ≤ √X）上的对数余量例外集界：
--   对任意 A>0，存在 B、C 与阈值 X₀，使所有 X₀≤X、H≤X、H²≤X 且
--   X^(7/120)(log X)^B ≤ H 的窗口，其无表示偶数个数 ≤ C·H/(log X)^A。
-- child 1 en: Polylogarithmic exception bound on short windows (H² ≤ X): for every A>0
--   there are B, C and a threshold so that every window with H² ≤ X and
--   X^(7/120)(log X)^B ≤ H has at most C·H/(log X)^A missed even targets.
--
-- child 2 zh: 长窗（X ≤ H²，即 H ≥ √X）上的同一界；阈值、B、C 允许与短窗不同。
-- child 2 en: The same bound on long windows (X ≤ H²), with possibly different B, C, X₀.
--
-- 组合方式：H² ≤ X 与 X ≤ H² 覆盖全部情形；取 B = max B₁ B₂、C = max C₁ C₂、
-- X₀ = max X₁ X₂ 3。由 X ≥ 3 得 log X ≥ 1，故 (log X)^Bᵢ ≤ (log X)^B，
-- 两条前提都可套用；再比较常数。两个前提各自独立：短窗与长窗是不同尺度，
-- 分别需要不同的零点/筛法输入，且都不能单独推出父题。
-- Combination: H² ≤ X and X ≤ H² cover all cases. Take B = max B₁ B₂,
-- C = max C₁ C₂, X₀ = max X₁ X₂ 3. Since log X ≥ 1 for X ≥ 3, we have
-- (log X)^Bᵢ ≤ (log X)^B, so either premise applies; then compare constants.

theorem Conjectures.Cuts.Cut6f202a37e8c759800f65f111
    (hShort : ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ,
      X₀ ≤ X → H ≤ X → H^2 ≤ X →
      (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B ≤ (H:ℝ) →
      ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^A)
    (hLong : ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ,
      X₀ ≤ X → H ≤ X → X ≤ H^2 →
      (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B ≤ (H:ℝ) →
      ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^A) :
    (∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ, X₀ ≤ X → H ≤ X → (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B ≤ (H:ℝ) → ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^A) := by
  intro A hA
  obtain ⟨B₁, C₁, hB₁, hC₁, X₁, h₁⟩ := hShort A hA
  obtain ⟨B₂, C₂, hB₂, hC₂, X₂, h₂⟩ := hLong A hA
  refine ⟨max B₁ B₂, max C₁ C₂, ?_⟩
  refine ⟨lt_of_lt_of_le hB₁ (le_max_left _ _), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  refine ⟨max (max X₁ X₂) 3, ?_⟩
  intro X H hX hH hmain
  have hX3 : 3 ≤ X := le_trans (le_max_right (max X₁ X₂) 3) hX
  have hX1 : X₁ ≤ X := le_trans (le_max_left X₁ X₂) (le_trans (le_max_left (max X₁ X₂) 3) hX)
  have hX2 : X₂ ≤ X := le_trans (le_max_right X₁ X₂) (le_trans (le_max_left (max X₁ X₂) 3) hX)
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    have h := Real.log_three_gt_d9
    linarith
  have hX3R : (3:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX3
  have hlogX3 : Real.log 3 ≤ Real.log X :=
    (Real.log_le_log_iff (by norm_num) (by linarith : (0:ℝ) < (X:ℝ))).mpr hX3R
  have hlog1 : (1:ℝ) ≤ Real.log X := le_trans hlog3 hlogX3
  have hlogpos : (0:ℝ) < Real.log X := by linarith
  have hlogB₁ : (Real.log (X:ℝ))^B₁ ≤ (Real.log (X:ℝ))^(max B₁ B₂) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
  have hlogB₂ : (Real.log (X:ℝ))^B₂ ≤ (Real.log (X:ℝ))^(max B₁ B₂) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_right _ _)
  have hA₁ : (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B₁ ≤ (H:ℝ) := by
    have hmul : (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B₁ ≤
        (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^(max B₁ B₂) :=
      mul_le_mul_of_nonneg_left hlogB₁ (Real.rpow_nonneg (by positivity) _)
    exact le_trans hmul hmain
  have hA₂ : (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B₂ ≤ (H:ℝ) := by
    have hmul : (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B₂ ≤
        (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^(max B₁ B₂) :=
      mul_le_mul_of_nonneg_left hlogB₂ (Real.rpow_nonneg (by positivity) _)
    exact le_trans hmul hmain
  have hden : (0:ℝ) < (Real.log (X:ℝ))^A := Real.rpow_pos_of_pos hlogpos A
  by_cases hcase : H^2 ≤ X
  · have hres := h₁ X H hX1 hH hcase hA₁
    calc ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ)
        ≤ C₁*(H:ℝ)/(Real.log (X:ℝ))^A := hres
      _ ≤ (max C₁ C₂)*(H:ℝ)/(Real.log (X:ℝ))^A := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hcase2 : X ≤ H^2 := le_of_not_ge hcase
    have hres := h₂ X H hX2 hH hcase2 hA₂
    calc ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ)
        ≤ C₂*(H:ℝ)/(Real.log (X:ℝ))^A := hres
      _ ≤ (max C₁ C₂)*(H:ℝ)/(Real.log (X:ℝ))^A := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
