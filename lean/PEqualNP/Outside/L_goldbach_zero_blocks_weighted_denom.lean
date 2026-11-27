import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_weighted_denom :
    ∀ (n : ℕ) (ρ a : Fin n → ℂ) (x : ℝ), 0<x → (∀ i,(ρ i).re=1/2) → ‖∑ i, a i*(x:ℂ)^(ρ i)/ρ i‖ ≤ 2*Real.sqrt x*∑ i,‖a i‖ := by
  intro n ρ a x hx hρ
  have hterm : ∀ i : Fin n, ‖a i * (x:ℂ)^(ρ i) / ρ i‖ ≤ 2 * Real.sqrt x * ‖a i‖ := by
    intro i
    have hgt : (1/2 : ℝ) ≤ ‖ρ i‖ := by
      have h := Complex.abs_re_le_norm (ρ i)
      rw [hρ i] at h
      simpa using h
    have hpos : (0:ℝ) < ‖ρ i‖ := lt_of_lt_of_le (by norm_num) hgt
    have h2 : (1:ℝ)/‖ρ i‖ ≤ 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hgt
      have h3 : (1:ℝ)/(1/2) = 2 := by norm_num
      linarith
    have hn : (0:ℝ) ≤ ‖a i‖ * Real.sqrt x := by positivity
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ i, ← Real.sqrt_eq_rpow]
    calc ‖a i‖ * Real.sqrt x / ‖ρ i‖ = (‖a i‖ * Real.sqrt x) * (1/‖ρ i‖) := by ring
      _ ≤ (‖a i‖ * Real.sqrt x) * 2 := mul_le_mul_of_nonneg_left h2 hn
      _ = 2 * Real.sqrt x * ‖a i‖ := by ring
  calc ‖∑ i, a i * (x:ℂ)^(ρ i) / ρ i‖ ≤ ∑ i, ‖a i * (x:ℂ)^(ρ i) / ρ i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * Real.sqrt x * ‖a i‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * Real.sqrt x * ∑ i, ‖a i‖ := by rw [Finset.mul_sum]
