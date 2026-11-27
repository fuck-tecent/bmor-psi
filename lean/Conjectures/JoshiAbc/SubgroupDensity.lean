import Mathlib

theorem Conjectures.JoshiAbc.SubgroupDensity :
    ∀ (w v : ℝ) (d i : ℕ), 0 < w → 0 < d → 0 < i → w/i ≤ v → Real.log w/d-Real.log i/d ≤ Real.log v/d := by
  intro w v d i hw _hd hi h
  have hi' : (0 : ℝ) < i := Nat.cast_pos.2 hi
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [← sub_div, ← Real.log_div hw.ne' hi'.ne']
  exact div_le_div_of_nonneg_right (Real.log_le_log (div_pos hw hi') h) hd'
