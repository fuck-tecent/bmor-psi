import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_euler_allowed_local_series :
    ∀ p u : ℝ, 1 < p → |u| < p → HasSum (fun k : ℕ => (u/p)^k/(p-1)) (p/((p-1)*(p-u))) := by
  intro p u hp hu
  have hp0 : 0 < p := by linarith
  have hp1 : p-1 ≠ 0 := by linarith
  have hpu : p-u ≠ 0 := by have := (abs_lt.mp hu).2; linarith
  have hratio : ‖u/p‖ < 1 := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hp0,div_lt_one hp0]
    exact hu
  have h := (hasSum_geometric_of_norm_lt_one hratio).div_const (p-1)
  convert h using 1
  field_simp
