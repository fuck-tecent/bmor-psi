import Mathlib

/-
Finite high-zero-block estimate.  The critical-line location is an explicit
hypothesis; no zero-location theorem from the upstream RH project is imported.
The proof uses the norm of a complex power of a positive real number, the
imaginary-part lower bound for the norm, and the finite triangle inequality.
-/
theorem PEqualNP.Outside.L_goldbach_zero_blocks_high_gain :
    ∀ (n : ℕ) (ρ a : Fin n → ℂ) (x T : ℝ), 0<x → 0<T → (∀ i,(ρ i).re=1/2 ∧ T≤|(ρ i).im|) → ‖∑ i,a i*(x:ℂ)^(ρ i)/ρ i‖≤Real.sqrt x/T*∑ i,‖a i‖ := by
  intro n ρ a x T hx hT hρ
  have hterm (i : Fin n) :
      ‖a i * (x : ℂ) ^ (ρ i) / ρ i‖ ≤ Real.sqrt x / T * ‖a i‖ := by
    have hpow : ‖(x : ℂ) ^ (ρ i)‖ = Real.sqrt x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, (hρ i).1, Real.sqrt_eq_rpow]
    have hden : T ≤ ‖ρ i‖ := (hρ i).2.trans (Complex.abs_im_le_norm _)
    rw [norm_div, norm_mul, hpow]
    calc
      ‖a i‖ * Real.sqrt x / ‖ρ i‖ ≤ ‖a i‖ * Real.sqrt x / T :=
        div_le_div_of_nonneg_left
          (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hT hden
      _ = Real.sqrt x / T * ‖a i‖ := by ring
  calc
    ‖∑ i, a i * (x : ℂ) ^ (ρ i) / ρ i‖ ≤
        ∑ i, ‖a i * (x : ℂ) ^ (ρ i) / ρ i‖ := norm_sum_le _ _
    _ ≤ ∑ i, Real.sqrt x / T * ‖a i‖ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = Real.sqrt x / T * ∑ i, ‖a i‖ := (Finset.mul_sum ..).symm
