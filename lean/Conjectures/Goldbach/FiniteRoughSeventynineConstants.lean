import Mathlib

theorem Conjectures.Goldbach.FiniteRoughSeventynineConstants :
    Real.exp (19/5) < 11*Real.log 79 ∧ Real.exp 5 < 34*Real.log 79 ∧ (19495926505 : ℕ) < 11^11 := by
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog5 : (1.6094379123:ℝ) < Real.log 5 := Real.log_five_gt_d9
  have hlog80 : Real.log (80:ℝ) = Real.log 5 + 4*Real.log 2 := by
    rw [show (80:ℝ) = 5 * 2^4 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hlog79 : (4.36936:ℝ) < Real.log 79 := by
    have hsplit : Real.log (80:ℝ) = Real.log 79 + Real.log (80/79:ℝ) := by
      have h : Real.log ((79:ℝ) * (80/79)) = Real.log 79 + Real.log (80/79) :=
        Real.log_mul (by norm_num) (by norm_num)
      have h80 : (79:ℝ) * (80/79) = 80 := by norm_num
      rwa [h80] at h
    have hupper : Real.log (80/79:ℝ) ≤ 1/79 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 80/79)
      have hval : (80:ℝ)/79 - 1 = 1/79 := by norm_num
      linarith
    have hlow : (4.36936:ℝ) < Real.log 5 + 4*Real.log 2 - Real.log (80/79:ℝ) := by
      have h1 : (1.6094379123:ℝ) + 4*(0.6931471803:ℝ) - 1/79 > 4.36936 := by norm_num
      linarith
    linarith
  have hexp4 : Real.exp 4 < (2.7182818286:ℝ)^4 := by
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by
      simpa using Real.exp_nat_mul 1 4
    rw [h]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
  have hexp19 : Real.exp (19/5) < (2.7182818286:ℝ)^4 * (5/6) := by
    have h1 : Real.exp (19/5) = Real.exp 4 / Real.exp (1/5) := by
      rw [show (19:ℝ)/5 = 4 - 1/5 by norm_num, Real.exp_sub]
    have hden : (6/5:ℝ) ≤ Real.exp (1/5) := by
      have h := Real.add_one_le_exp (1/5 : ℝ)
      have hval : (1:ℝ) + 1/5 = 6/5 := by norm_num
      linarith
    rw [h1]
    calc Real.exp 4 / Real.exp (1/5) ≤ Real.exp 4 / (6/5) := by
          exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos 4)) (by norm_num) hden
      _ < (2.7182818286:ℝ)^4 / (6/5) := by
          exact div_lt_div_of_pos_right hexp4 (by norm_num)
      _ = (2.7182818286:ℝ)^4 * (5/6) := by norm_num
  have hexp5 : Real.exp 5 < (2.7182818286:ℝ)^5 := by
    have h : Real.exp 5 = Real.exp 1 ^ 5 := by
      simpa using Real.exp_nat_mul 1 5
    rw [h]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
  have hb1 : (2.7182818286:ℝ)^4 * (5/6) < 11 * (4.36936:ℝ) := by norm_num
  have hb2 : (2.7182818286:ℝ)^5 < 34 * (4.36936:ℝ) := by norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · linarith
  · linarith

theorem PEqualNP.Outside.L_goldbach_finite_rough_seventynine_constants :
    Real.exp (19/5) < 11*Real.log 79 ∧ Real.exp 5 < 34*Real.log 79 ∧ (19495926505 : ℕ) < 11^11 :=
  Conjectures.Goldbach.FiniteRoughSeventynineConstants
