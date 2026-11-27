import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_cpow_norm :
    ∀ (n : ℕ) (ρ : Fin n → ℂ) (x : ℝ), 0<x → (∀ i,(ρ i).re=1/2) → ∀ i, ‖(x:ℂ)^(ρ i)‖=Real.sqrt x := by
  intro n ρ x hx hρ i
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ i, ← Real.sqrt_eq_rpow]
