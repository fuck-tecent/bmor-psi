import Mathlib

theorem Conjectures.Goldbach.FiniteRoughPrototypeConstants19 :
    Real.exp 5 < 51 * Real.log 19 := by
  have h_exp5 : Real.exp 5 < (2.7182818286 : ℝ) ^ 5 := by
    rw [show (5 : ℝ) = (5 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
  have h_num : (2.7182818286 : ℝ) ^ 5 < 148.42 := by norm_num
  have h_log2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h_log5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  have h_log19 : (2.9431 : ℝ) < Real.log 19 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hsplit : Real.log 19 = 2 * Real.log 2 + Real.log 5 + Real.log (19 / 20) := by
      calc Real.log 19 = Real.log (4 * 5 * (19 / 20)) := by
            congr 1
            norm_num
        _ = Real.log (4 * 5) + Real.log (19 / 20) := by
            rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = Real.log 4 + Real.log 5 + Real.log (19 / 20) := by
            rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log 2 + Real.log 5 + Real.log (19 / 20) := by
            rw [h4]
    have hneg : -(1 / 19 : ℝ) ≤ Real.log (19 / 20) := by
      have hinv : Real.log (19 / 20) = -Real.log (20 / 19) := by
        rw [show (19 / 20 : ℝ) = (20 / 19)⁻¹ by norm_num, Real.log_inv]
      rw [hinv]
      have hle : Real.log (20 / 19) ≤ (20 / 19) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have hval : (20 / 19 : ℝ) - 1 = 1 / 19 := by norm_num
      linarith
    rw [hsplit]
    linarith
  nlinarith [h_exp5, h_num, h_log19]
