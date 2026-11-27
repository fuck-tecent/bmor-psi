import Mathlib

theorem Conjectures.JoshiAbc.FixedPlaceStress : ∀ N : ℕ, let x := (N:ℝ); let lo := -(3*x+3)*Real.log 337; let hi := (-4*(3*x+15/7)+3*(6/7)+1)*Real.log 337; lo-hi=(9*x+2)*Real.log 337 ∧ hi<lo := by
  intro N
  have hL : (0:ℝ) < Real.log 337 := Real.log_pos (by norm_num)
  have hx : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hpos : (0:ℝ) < (9*(N:ℝ)+2) * Real.log 337 := mul_pos (by nlinarith) hL
  constructor
  · show -(3*(N:ℝ)+3)*Real.log 337 - ((-4*(3*(N:ℝ)+15/7)+3*(6/7)+1)*Real.log 337) = (9*(N:ℝ)+2)*Real.log 337
    ring
  · show ((-4*(3*(N:ℝ)+15/7)+3*(6/7)+1)*Real.log 337) < -(3*(N:ℝ)+3)*Real.log 337
    nlinarith [hpos]
