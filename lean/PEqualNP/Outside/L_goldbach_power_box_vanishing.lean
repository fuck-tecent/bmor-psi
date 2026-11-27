import Mathlib
open Finset Filter Real
open scoped Topology
private lemma natLog2_le (n : ℕ) (hn : 1≤n) :
    (Nat.log 2 n : ℝ) ≤ 2*Real.log n := by
  have hL := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
  have h2 := Real.log_two_gt_d9
  have h := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat,Real.logb] at h
  exact h.trans ((div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]))


private lemma integer_sqrt_le (n : ℕ) : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast (show Nat.sqrt n ^ 2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)

theorem PEqualNP.Outside.L_goldbach_power_box_vanishing : ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ((Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ))*Real.log ((n+1:ℕ):ℝ)^2/(n:ℝ)<ε := by
  intro ε hε
  apply eventually_atTop.mp
  have hsmall : Tendsto (fun n : ℕ => (Real.log n)^3/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop ((3:ℕ):ℝ) (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [(tendsto_order.mp hsmall).2 (ε/8) (by positivity), eventually_ge_atTop (2:ℕ)] with n hratio hn
  have hnR : 2≤(n:ℝ) := by exact_mod_cast hn
  have hnpos : 0<(n:ℝ) := by linarith
  have hs := Real.sqrt_pos.mpr hnpos
  have hL := Real.log_nonneg (show (1:ℝ)≤n by linarith)
  have hL' := Real.log_nonneg (show (1:ℝ)≤(n+1:ℕ) by exact_mod_cast (show 1≤n+1 by omega))
  have hlog : Real.log ((n+1:ℕ):ℝ) ≤ 2*Real.log n := by
    rw [← Nat.cast_ofNat (R:=ℝ) (n:=2),← Real.log_pow]
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n))*(2*Real.log n)^2/(n:ℝ) := by
      gcongr
      · exact integer_sqrt_le n
      · exact natLog2_le n (by omega)
    _ = 8*((Real.log n)^3/Real.sqrt n) := by
      field_simp
      ring_nf
      rw [Real.sq_sqrt hnpos.le]
      ring
    _ < ε := by linarith
