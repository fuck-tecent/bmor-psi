import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_log_transport :
    ∀ d H k : ℕ, 1≤d → H≤k → Real.log ((d*(k+2):ℕ):ℝ) ≤ 2*(((k+1:ℕ):ℝ)/((H+1:ℕ):ℝ))*Real.log ((d*(H+2):ℕ):ℝ) := by
  intro d H k hd hk
  push_cast
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (H : ℝ) ≤ k := by exact_mod_cast hk
  let r := ((k : ℝ) + 1) / ((H : ℝ) + 1)
  have hr : 1 ≤ r := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < H + 1)).mpr
    linarith
  have hrpos : 0 < r := by linarith
  have hscale : (k : ℝ) + 2 ≤ (H + 2 : ℝ) * r := by
    dsimp [r]
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  have hb : (2 : ℝ) ≤ d * ((H : ℝ) + 2) := by
    calc
      _ ≤ (H : ℝ) + 2 := by exact_mod_cast (show 2 ≤ H + 2 by omega)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hd'
  have hlog : 1 / 2 ≤ Real.log (d * ((H : ℝ) + 2)) := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [Real.log_le_log (by norm_num) hb]
  calc
    _ ≤ Real.log ((d * ((H : ℝ) + 2)) * r) := by
      apply Real.log_le_log (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ d)
    _ = _ + Real.log r := Real.log_mul (by positivity) hrpos.ne'
    _ ≤ _ := by
      nlinarith [Real.log_le_sub_one_of_pos hrpos,
        mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hlog)]
