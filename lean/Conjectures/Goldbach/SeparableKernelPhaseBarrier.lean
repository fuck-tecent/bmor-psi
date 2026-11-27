import Mathlib

/-- Complete both off-diagonal phase sums to squares by restoring their diagonals. -/
theorem Conjectures.Goldbach.SeparableKernelPhaseBarrier :
    ∀ (m : ℕ) (L : ℝ) (γ : ℕ → ℝ) (W₁ W₂ : ℕ → ℂ), let E : ℕ → ℂ := fun j => Complex.exp (((γ j * L : ℝ) : ℂ) * Complex.I); let cross : (ℕ → ℂ) → ℝ := fun W => ∑ j ∈ Finset.range m, ∑ l ∈ (Finset.range m).erase j, (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re; cross W₁ + cross W₂ = ‖∑ j ∈ Finset.range m, W₁ j * E j‖ ^ 2 + ‖∑ j ∈ Finset.range m, W₂ j * E j‖ ^ 2 - ∑ j ∈ Finset.range m, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2) ∧ -(∑ j ∈ Finset.range m, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2)) ≤ cross W₁ + cross W₂ := by
  intro m L γ W₁ W₂
  let s := Finset.range m
  let E (j : ℕ) := Complex.exp (((γ j * L : ℝ) : ℂ) * Complex.I)
  let cross (W : ℕ → ℂ) := ∑ j ∈ s, ∑ l ∈ s.erase j,
    (W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l)).re
  change cross W₁ + cross W₂ = ‖∑ j ∈ s, W₁ j * E j‖ ^ 2 +
      ‖∑ j ∈ s, W₂ j * E j‖ ^ 2 - ∑ j ∈ s, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2) ∧
    -(∑ j ∈ s, (‖W₁ j‖ ^ 2 + ‖W₂ j‖ ^ 2)) ≤ cross W₁ + cross W₂
  have hre (z : ℂ) : (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  have energy (W : ℕ → ℂ) :
      cross W + ∑ j ∈ s, ‖W j‖ ^ 2 = ‖∑ j ∈ s, W j * E j‖ ^ 2 := by
    let z (j : ℕ) := W j * E j
    have pair (j l : ℕ) :
        W j * starRingEnd ℂ (W l) * E j * starRingEnd ℂ (E l) =
        z j * starRingEnd ℂ (z l) := by
      simp only [z, map_mul]
      ring
    have diag (j : ℕ) : (z j * starRingEnd ℂ (z j)).re = ‖W j‖ ^ 2 := by
      rw [hre, show ‖z j‖ = ‖W j‖ from by simp only [z, E, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]]
    calc
      cross W + ∑ j ∈ s, ‖W j‖ ^ 2 =
          ∑ j ∈ s, ((∑ l ∈ s.erase j, (z j * starRingEnd ℂ (z l)).re) +
                    (z j * starRingEnd ℂ (z j)).re) := by
              simp only [cross, pair, diag, Finset.sum_add_distrib]
      _ = ∑ j ∈ s, ∑ l ∈ s, (z j * starRingEnd ℂ (z l)).re := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            exact Finset.sum_erase_add s (fun l => (z j * starRingEnd ℂ (z l)).re) hj
      _ = ((∑ j ∈ s, z j) * starRingEnd ℂ (∑ j ∈ s, z j)).re := by
            simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
            exact Finset.sum_comm
      _ = ‖∑ j ∈ s, W j * E j‖ ^ 2 := hre _
  rw [Finset.sum_add_distrib]
  constructor
  · linarith [energy W₁, energy W₂]
  · linarith [energy W₁, energy W₂, sq_nonneg ‖∑ j ∈ s, W₁ j * E j‖,
              sq_nonneg ‖∑ j ∈ s, W₂ j * E j‖]
