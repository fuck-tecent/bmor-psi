import Mathlib

/- Polynomial compensation of logarithmic losses. The logarithm of 2 + X is at least 1 and at most
8 times its eighth root, so its fourth power is at most a constant times the square root of 2 + X.
Together with log (2 + 2X) at most 2 log (2 + X) this bounds the square-root times logarithm scale
by a constant multiple of X divided by the square of log (2 + X). -/

theorem Conjectures.Cuts.Task9e65cd588a8f8edd3f2253e1 :
    ∀ (x1 : ℕ), (16 : ℕ) ≤ x1 → √((2 : ℝ) * ↑x1) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x1) ≤ (20000 : ℝ) * ↑x1 / Real.log ((2 : ℝ) + ↑x1) ^ (2 : ℕ) := by
  intro X hX
  have hx : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < (X : ℝ) := by linarith
  have ht18 : (18 : ℝ) ≤ 2 + (X : ℝ) := by linarith
  -- the logarithm of 2 + X is at least 1
  have hL : (1 : ℝ) ≤ Real.log (2 + (X : ℝ)) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (2 + (X : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three.le])
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) ≤ Real.log (2 + (X : ℝ)) := by linarith
  -- log (2 + X) = 8 * log ((2 + X) ^ (1/8)) is at most 8 * (2 + X) ^ (1/8)
  have hroot : Real.log (2 + (X : ℝ)) ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) := by
    have e1 : Real.log (Real.sqrt (2 + (X : ℝ))) = Real.log (2 + (X : ℝ)) / 2 := Real.log_sqrt (by linarith : (0 : ℝ) ≤ 2 + (X : ℝ))
    have e2 : Real.log (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) = Real.log (Real.sqrt (2 + (X : ℝ))) / 2 :=
      Real.log_sqrt (Real.sqrt_nonneg _)
    have e3 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ))))) =
        Real.log (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) / 2 := Real.log_sqrt (Real.sqrt_nonneg _)
    have step : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ))))) ≤
        Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) - 1 :=
      Real.log_le_sub_one_of_pos
        (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))))
    rw [e3, e2, e1] at step
    linarith
  have hs3 : Real.sqrt (Real.sqrt (Real.sqrt (2 + (X : ℝ)))) ^ 4 = Real.sqrt (2 + (X : ℝ)) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (Real.sqrt_nonneg _)]
  -- so the fourth power of the logarithm is at most a constant times the square root
  have hL4 : Real.log (2 + (X : ℝ)) ^ 4 ≤ 4096 * Real.sqrt (2 + (X : ℝ)) := by
    have h := pow_le_pow_left₀ hL0 hroot 4
    rw [mul_pow, show (8 : ℝ) ^ 4 = 4096 by norm_num, hs3] at h
    exact h
  have hL3 : Real.log (2 + (X : ℝ)) ^ 3 ≤ 4096 * Real.sqrt (2 + (X : ℝ)) := by
    exact le_trans (pow_le_pow_right₀ hL (by norm_num : (3 : ℕ) ≤ 4)) hL4
  have hsqt : Real.sqrt (2 + (X : ℝ)) ≤ Real.sqrt (2 * (X : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hlog2 : Real.log (2 + 2 * (X : ℝ)) ≤ 2 * Real.log (2 + (X : ℝ)) := by
    have h : Real.log (2 + 2 * (X : ℝ)) ≤ Real.log ((2 + (X : ℝ)) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rwa [Real.log_pow] at h
  have hs2X : Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 * (X : ℝ)) = 2 * (X : ℝ) := by
    calc Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 * (X : ℝ)) = Real.sqrt (2 * (X : ℝ)) ^ 2 := by ring
      _ = 2 * (X : ℝ) := Real.sq_sqrt (by positivity)
  apply (le_div_iff₀ (pow_pos (by linarith) 2)).mpr
  have hstep1 : Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ)) * Real.log (2 + (X : ℝ)) ^ 2 ≤
      Real.sqrt (2 * (X : ℝ)) * (2 * Real.log (2 + (X : ℝ))) * Real.log (2 + (X : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2 (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hL3' : Real.sqrt (2 * (X : ℝ)) * Real.log (2 + (X : ℝ)) ^ 3 ≤ 4096 * (2 * (X : ℝ)) := by
    calc Real.sqrt (2 * (X : ℝ)) * Real.log (2 + (X : ℝ)) ^ 3
        ≤ Real.sqrt (2 * (X : ℝ)) * (4096 * Real.sqrt (2 + (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hL3 (Real.sqrt_nonneg _)
      _ = 4096 * (Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 + (X : ℝ))) := by ring
      _ ≤ 4096 * (Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 * (X : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqt (Real.sqrt_nonneg _)) (by norm_num)
      _ = 4096 * (2 * (X : ℝ)) := by rw [hs2X]
  have hfinal : Real.sqrt (2 * (X : ℝ)) * (2 * Real.log (2 + (X : ℝ))) * Real.log (2 + (X : ℝ)) ^ 2 ≤
      20000 * (X : ℝ) := by
    have hr : Real.sqrt (2 * (X : ℝ)) * (2 * Real.log (2 + (X : ℝ))) * Real.log (2 + (X : ℝ)) ^ 2 =
        2 * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + (X : ℝ)) ^ 3) := by ring
    rw [hr]
    have hmul := mul_le_mul_of_nonneg_left hL3' (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  exact le_trans hstep1 hfinal
