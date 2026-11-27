import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_weight_perturb :
    ∀ (n : ℕ) (ρ a : Fin n → ℂ) (b : Fin n → ℂ) (x : ℝ), 0<x → (∀ i,(ρ i).re=1/2) → ‖∑ i,(a i-b i)*(x:ℂ)^(ρ i)‖≤Real.sqrt x*∑ i,‖a i-b i‖ := by
  intro n ρ a b x hx hρ
  calc ‖∑ i, (a i - b i) * (x:ℂ)^(ρ i)‖ ≤ ∑ i, ‖(a i - b i) * (x:ℂ)^(ρ i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i - b i‖ * Real.sqrt x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ i, ← Real.sqrt_eq_rpow]
    _ = Real.sqrt x * ∑ i, ‖a i - b i‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
