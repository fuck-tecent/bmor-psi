import Mathlib

namespace Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e_aux

lemma log_two_add_le (x : ℝ) (hx : (2 : ℝ) ≤ x) :
    Real.log (2 + x) ≤ 2 * Real.log x := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hle : (2 : ℝ) + x ≤ x ^ (2 : ℕ) := by nlinarith
  calc Real.log (2 + x) ≤ Real.log (x ^ (2 : ℕ)) := Real.log_le_log (by linarith) hle
    _ = 2 * Real.log x := Real.log_pow x 2

lemma tendsto_log_cube_div_sqrt :
    Filter.Tendsto (fun x : ℝ => Real.log (2 + x) ^ (3 : ℕ) / Real.sqrt x) Filter.atTop (nhds 0) := by
  have h := isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hdiv : Filter.Tendsto (fun x : ℝ => Real.log x ^ ((3 : ℕ) : ℝ) / x ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) :=
    h.tendsto_div_nhds_zero
  have h8 : Filter.Tendsto (fun x : ℝ => 8 * (Real.log x ^ ((3 : ℕ) : ℝ) / x ^ (1 / 2 : ℝ))) Filter.atTop
      (nhds 0) := by
    simpa using hdiv.const_mul 8
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    have hnn : 0 ≤ Real.log (2 + x) ^ (3 : ℕ) / Real.sqrt x :=
      div_nonneg (pow_nonneg hlog 3) (Real.sqrt_nonneg x)
    linarith
  · intro b hb
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), (tendsto_order.1 h8).2 b hb] with x hx hlt
    have hL : Real.log (2 + x) ≤ 2 * Real.log x := log_two_add_le x hx
    have hlog : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    have hcube : Real.log (2 + x) ^ (3 : ℕ) ≤ 8 * Real.log x ^ (3 : ℕ) := by
      have hstep : Real.log (2 + x) ^ (3 : ℕ) ≤ (2 * Real.log x) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hlog hL 3
      have hexp : (2 * Real.log x) ^ (3 : ℕ) = 8 * Real.log x ^ (3 : ℕ) := by ring
      linarith
    have hbound : Real.log (2 + x) ^ (3 : ℕ) / Real.sqrt x ≤
        8 * (Real.log x ^ ((3 : ℕ) : ℝ) / x ^ (1 / 2 : ℝ)) := by
      calc Real.log (2 + x) ^ (3 : ℕ) / Real.sqrt x
          ≤ 8 * Real.log x ^ (3 : ℕ) / Real.sqrt x :=
            div_le_div_of_nonneg_right hcube (Real.sqrt_nonneg x)
        _ = 8 * (Real.log x ^ ((3 : ℕ) : ℝ) / x ^ (1 / 2 : ℝ)) := by
            rw [Real.rpow_natCast (Real.log x) 3, Real.sqrt_eq_rpow x]
            ring
    linarith

end Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e_aux

theorem Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℕ), ∀ (x4 : ℕ), x3 ≤ x4 →
      Real.log ((2 : ℝ) + ↑x4) ^ (3 : ℕ) / √↑x4 < x1 := by
  intro x1 hx1
  have h := Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e_aux.tendsto_log_cube_div_sqrt.comp
    tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log ((2 : ℝ) + ↑n) ^ (3 : ℕ) / √↑n < x1 := (tendsto_order.1 h).2 x1 hx1
  exact Filter.eventually_atTop.1 hev
