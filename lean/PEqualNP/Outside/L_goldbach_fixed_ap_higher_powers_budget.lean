import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

open Finset

namespace FR7022.HigherPowers

theorem two_sqrt_log_le_millionth {x : ℝ} (hx : 10^16 ≤ x) :
    2 * x.sqrt * x.log ≤ x / 10^6 := by
  have xp : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hs : (10:ℝ)^8 ≤ x.sqrt := by
    calc
      (10:ℝ)^8 = Real.sqrt ((10:ℝ)^16) := by
        rw [show (10:ℝ)^16 = ((10:ℝ)^8)^2 by ring, Real.sqrt_sq (by positivity)]
      _ ≤ x.sqrt := Real.sqrt_le_sqrt hx
  have hl : Real.log 10 ≤ 3 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have tangent := Real.log_le_sub_one_of_pos
    (div_pos (Real.sqrt_pos.2 xp) (by norm_num : (0:ℝ) < 10^8))
  rw [Real.log_div (Real.sqrt_pos.2 xp).ne' (by norm_num), Real.log_sqrt xp.le, Real.log_pow] at tangent
  have bound : Real.log x ≤ x.sqrt / 2000000 := by linarith
  have prod := mul_le_mul_of_nonneg_left bound (show 0 ≤ 2*x.sqrt by positivity)
  nlinarith [Real.sq_sqrt xp.le]

theorem total (n : ℕ) (hn : 10^16 ≤ n) :
    (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) ≤ (n:ℝ)/10^6 := by
  have hx : (10:ℝ)^16 ≤ n := by exact_mod_cast hn
  have eq : (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
      Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n), sum_filter]
    simp
  rw [eq]
  exact (le_abs_self _).trans ((Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ (n:ℝ))).trans
    (two_sqrt_log_le_millionth hx))

end FR7022.HigherPowers

theorem PEqualNP.Outside.L_goldbach_fixed_ap_higher_powers_budget :
    ∀ n : ℕ, 10^16 ≤ n → (∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)) ≤ (n:ℝ)/200 := by
  intro n hn
  have h := FR7022.HigherPowers.total n hn
  linarith [Nat.cast_nonneg (α := ℝ) n]
