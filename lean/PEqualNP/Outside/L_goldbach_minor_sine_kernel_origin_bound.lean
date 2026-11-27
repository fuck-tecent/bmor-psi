import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_minor_sine_kernel_origin_bound :
    ∀ x : ℝ, |Real.sin x| ≤ min 1 |x| := by
  intro x
  exact le_min (Real.abs_sin_le_one x) (Real.abs_sin_le_abs (x := x))

end PEqualNP.Outside
