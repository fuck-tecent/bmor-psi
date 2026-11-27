import Mathlib

-- child 1 zh: 对数平方损失下的计数下界：在任意晚的二倍区间内，孪生素数对的个数超过任意常数倍的 X 除以 log(2+X) 的平方。
-- child 1 en: Count lower bound with a squared logarithm loss: in arbitrarily late dyadic intervals the number of twin prime pairs exceeds any constant multiple of X divided by the square of log(2+X).
-- child 2 zh: 对数损失的多项式补偿：对 X 至少为 16，平方根乘以对数的尺度不超过 20000 倍的 X 除以 log(2+X) 的平方。
-- child 2 en: Polynomial compensation of logarithmic losses: for X at least 16, the square-root times logarithm scale is at most 20000 times X divided by the square of log(2+X).
-- Refinement: the square-root times logarithm lower bound follows from a count lower bound at the scale X / log^2 (2+X) through this elementary inequality.

theorem Conjectures.Cuts.Cut48a026b68007758fc3569f47
    (h₁ : ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, 16 ≤ X ∧ B < X ∧
      K * (X:ℝ) / (Real.log (2 + (X:ℝ)))^2 <
        (((Finset.Ioc X (2*X)).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+2))).card : ℝ))
    (h₂ : ∀ X : ℕ, 16 ≤ X →
      Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ)) ≤
        20000 * (X:ℝ) / (Real.log (2 + (X:ℝ)))^2) :
    (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * (√((2 : ℝ) * ↑x3) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x3)) < ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  intro K B
  obtain ⟨X, hX16, hBX, hcard⟩ := h₁ (20000 * K) B
  refine ⟨X, hBX, ?_⟩
  have hW := h₂ X hX16
  have hxR : (0 : ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have hxpos : (0 : ℝ) < (X:ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < X)
  have hlogpos : (0 : ℝ) < Real.log (2 + (X:ℝ)) := Real.log_pos (by linarith)
  have hL2 : (0 : ℝ) < (Real.log (2 + (X:ℝ)))^2 := sq_pos_of_pos hlogpos
  have hcard0 : (0 : ℝ) ≤ (((Finset.Ioc X (2*X)).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+2))).card : ℝ) :=
    Nat.cast_nonneg _
  have hcard' := (div_lt_iff₀ hL2).mp hcard
  by_cases hK : 0 ≤ K
  · have h1 : K * (Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ))) * (Real.log (2 + (X:ℝ)))^2 ≤
        20000 * K * (X:ℝ) := by
      calc K * (Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ))) * (Real.log (2 + (X:ℝ)))^2
          = K * (Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ)) * (Real.log (2 + (X:ℝ)))^2) := by ring
        _ ≤ K * (20000 * (X:ℝ)) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL2).mp hW) hK
        _ = 20000 * K * (X:ℝ) := by ring
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 hcard') hL2.le
  · have hA : (0 : ℝ) < Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ)) :=
      mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))
    have hneg : K * (Real.sqrt (2 * (X:ℝ)) * Real.log (2 + 2 * (X:ℝ))) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hK) hA
    linarith
