import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_normalized_phase :
    ∀ (n : ℕ) (ρ : Fin n → ℂ) (x : ℝ), 0<x → (∀ i,(ρ i).re=1/2) → ∀ i, ‖(x:ℂ)^(ρ i)/(Real.sqrt x:ℂ)‖=1 := by
  intro n ρ x hx hρ i
  have hpos : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ i, ← Real.sqrt_eq_rpow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact div_self hpos.ne'
