import Mathlib
open Filter
theorem PEqualNP.Outside.L_twin_primes_vanishing_error : let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; Filter.Tendsto e Filter.atTop (nhds 0) := by
  dsimp only
  have hmain : Tendsto (fun y : ℝ => Real.log y ^ 3 / Real.sqrt y) atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_atTop (r := (1/6:ℝ)) (by norm_num)).pow (n := 3) (by norm_num)).tendsto_div_nhds_zero
    apply h.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  have hx : Tendsto (fun x : ℕ => (2:ℝ)+(x:ℝ)) atTop atTop := tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun x : ℕ => Real.log (2+(x:ℝ))^3 / Real.sqrt (2+(x:ℝ))) atTop (nhds 0) := hmain.comp hx
  have h2 : Tendsto (fun x : ℕ => 2*(Real.log (2+(x:ℝ))^3 / Real.sqrt (2+(x:ℝ)))) atTop (nhds 0) := by simpa using hcomp.const_mul 2
  apply squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with x hx
    have : 0 ≤ Real.log (2+(x:ℝ)) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) x; linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with x hx
    have hxpos : 0 < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hx2 : (2:ℝ) ≤ x := by exact_mod_cast hx
    have hsx := Real.sq_sqrt hxpos.le
    have hsy := Real.sq_sqrt (show 0 ≤ 2+(x:ℝ) by positivity)
    have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hsle : Real.sqrt (2+(x:ℝ)) ≤ 2*Real.sqrt x := by nlinarith [Real.sqrt_nonneg (2+(x:ℝ))]
    have hn : 0 ≤ Real.log (2+(x:ℝ))^3 := pow_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) x; linarith)) _
    have hden : 0 < Real.sqrt (2+(x:ℝ)) := Real.sqrt_pos.2 (by positivity)
    apply (div_le_iff₀ hsxpos).2
    have hmul := mul_le_mul_of_nonneg_left hsle hn
    have haux : Real.log (2+(x:ℝ))^3 ≤ (2*Real.log (2+(x:ℝ))^3*Real.sqrt x)/Real.sqrt (2+(x:ℝ)) := (le_div_iff₀ hden).2 (by nlinarith [hmul])
    convert haux using 1 <;> ring




