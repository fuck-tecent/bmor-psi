import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_band_fixed_loss_bridge :
    ∀ A B P n a b : ℝ, 0 < n → a-b > 1/10^5 → a*n ≤ A → B ≤ b*n → P ≤ n/10^5 → 0 < A-B-P := by
  intro A B P n a b hn hmargin ha hb hP
  have hmul : (1 / 10^5 : ℝ) * n < (a - b) * n := by
    exact mul_lt_mul_of_pos_right hmargin hn
  nlinarith
