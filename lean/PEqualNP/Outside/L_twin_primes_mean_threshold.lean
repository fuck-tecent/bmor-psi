import Mathlib

theorem PEqualNP.Outside.L_twin_primes_mean_threshold :
    ∀ θ : ℝ, θ < 7/8 → ∃ ε : ℝ, 0 < ε ∧ Filter.Tendsto (fun x : ℝ => x ^ (θ+1/8+ε) / x) Filter.atTop (nhds 0) := by
  intro θ hθ
  refine ⟨(7/8 - θ)/2, by linarith, ?_⟩
  have h := tendsto_rpow_neg_atTop (y := (7/8 - θ)/2) (by linarith)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with x hx
  rw [show θ + 1/8 + (7/8 - θ)/2 = -((7/8 - θ)/2) + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  field_simp
