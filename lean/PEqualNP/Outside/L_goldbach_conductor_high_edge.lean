import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_high_edge :
    ∀ n d : ℕ, (n^3 < d^4 ↔ (n : ℝ)^((3:ℝ)/4) < (d : ℝ)) := by
  intro n d
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ ((3:ℝ)/4)) ^ 4 = (n : ℝ)^3 := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((3:ℝ)/4)) 4, ← Real.rpow_mul hnn]
    norm_num
  have key : ((n : ℝ) ^ ((3:ℝ)/4)) ^ 4 < (d : ℝ)^4 ↔
      (n : ℝ)^((3:ℝ)/4) < (d : ℝ) :=
    pow_lt_pow_iff_left₀ (Real.rpow_nonneg hnn _) (Nat.cast_nonneg d) (by norm_num : (4:ℕ) ≠ 0)
  rw [← key, hpow, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_lt]