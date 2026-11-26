import Mathlib

namespace PEqualNP.Outside

noncomputable section

/-- The real budget identity behind the GRH-to-BV summation: if the individual
error is `C * sqrt X * (log X)^2`, then summing over
`sqrt X / (log X)^(A+2)` moduli gives `C * X / (log X)^A`. -/
lemma grh_bv_budget {X C A : ℝ} (hX : 1 < X) :
    (Real.sqrt X / (Real.log X) ^ (A + 2)) *
        (C * Real.sqrt X * (Real.log X) ^ 2) =
      C * X / (Real.log X) ^ A := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hLne : Real.log X ≠ 0 := hL.ne'
  have hsqrt : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0.le
  rw [div_mul_eq_mul_div]
  -- numerator: C * (sqrt X * sqrt X) * (log X)^2
  have hnum : (Real.sqrt X * (C * Real.sqrt X * (Real.log X) ^ 2)) =
      C * X * (Real.log X) ^ 2 := by
    calc
      _ = C * (Real.sqrt X) ^ 2 * (Real.log X) ^ 2 := by ring
      _ = C * X * (Real.log X) ^ 2 := by rw [hsqrt]
  rw [hnum]
  -- exponent bookkeeping
  have hpow : (Real.log X) ^ (A + 2) = (Real.log X) ^ A * (Real.log X) ^ 2 := by
    rw [Real.rpow_add hL]
    norm_num
  rw [hpow]
  field_simp [hLne]

end

end PEqualNP.Outside
