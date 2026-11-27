import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

private theorem expLowerFraction : Real.exp (79 / 200) ≤ (1.485 : ℝ) := by
  apply (Real.exp_bound' (x := 79 / 200) (by norm_num) (by norm_num) (n := 8) (by decide)).trans
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem expUpperFraction : Real.exp (4 / 5) ≤ (2.226 : ℝ) := by
  apply (Real.exp_bound' (x := 4 / 5) (by norm_num) (by norm_num) (n := 8) (by decide)).trans
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_constants :
    Real.exp (19/5) < 19*Real.log 11 ∧ Real.exp 5 < 62*Real.log 11 := by
  have he : Real.exp 1 ≤ (2.71829 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp (k : ℕ) : Real.exp (k : ℝ) ≤ (2.71829 : ℝ)^k := by
    simpa only [mul_one] using (Real.exp_nat_mul 1 k).le.trans
      (pow_le_pow_left₀ (Real.exp_pos _).le he k)
  have hlog : (2.395 : ℝ) < Real.log 11 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).2
    rw [show (2.395 : ℝ) = (2 : ℕ) + 79 / 200 by norm_num, Real.exp_add]
    apply lt_of_le_of_lt (mul_le_mul (hp 2) expLowerFraction (Real.exp_pos _).le (by positivity))
    norm_num
  constructor
  · rw [show (19/5 : ℝ) = (3 : ℕ) + 4 / 5 by norm_num, Real.exp_add]
    have h := mul_le_mul (hp 3) expUpperFraction (Real.exp_pos _).le (by positivity)
    norm_num at h
    linarith
  · have h := hp 5
    norm_num at h
    linarith
