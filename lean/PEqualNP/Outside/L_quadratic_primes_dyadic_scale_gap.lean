import Mathlib

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.L_quadratic_primes_dyadic_scale_gap :
    ∀ (x n : ℝ), (2 : ℝ) ^ (13230 : ℕ) < x → 0 ≤ n → n ≤ 2 * x → n ^ ((1323 : ℝ) / 1000) < x ^ ((13231 : ℝ) / 10000) := by
  intro x n hx hn hnx
  have hxpos : 0 < x := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (13230 : ℕ) := pow_pos (by norm_num) 13230
    exact h2pos.trans hx
  have hpow : (2 : ℝ) ^ (13230 : ℝ) < x := by
    calc
      (2 : ℝ) ^ (13230 : ℝ) = (2 : ℝ) ^ (13230 : ℕ) :=
        Real.rpow_natCast (2 : ℝ) 13230
      _ < x := hx
  have hroot := Real.rpow_lt_rpow
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (13230 : ℝ))
    hpow (by norm_num : (0 : ℝ) < 1 / 10000)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hroot
  have he1 : (13230 : ℝ) * (1 / 10000) = (1323 : ℝ) / 1000 := by norm_num
  have he2 : (1 / 10000 : ℝ) = ((13231 : ℝ) / 10000) - ((1323 : ℝ) / 1000) := by norm_num
  rw [he1, he2] at hroot
  have hmono : n ^ ((1323 : ℝ) / 1000) ≤ (2 * x) ^ ((1323 : ℝ) / 1000) :=
    Real.rpow_le_rpow hn hnx (by norm_num)
  calc
    n ^ ((1323 : ℝ) / 1000) ≤ (2 * x) ^ ((1323 : ℝ) / 1000) := hmono
    _ = (2 : ℝ) ^ ((1323 : ℝ) / 1000) * x ^ ((1323 : ℝ) / 1000) := by
      rw [Real.mul_rpow (by norm_num) hxpos.le]
    _ < x ^ (((13231 : ℝ) / 10000) - ((1323 : ℝ) / 1000)) * x ^ ((1323 : ℝ) / 1000) :=
      mul_lt_mul_of_pos_right hroot (Real.rpow_pos_of_pos hxpos _)
    _ = x ^ ((13231 : ℝ) / 10000) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
