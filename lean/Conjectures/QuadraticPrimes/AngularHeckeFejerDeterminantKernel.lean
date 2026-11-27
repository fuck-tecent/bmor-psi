import Mathlib

open scoped BigOperators

/-!
Angular Fejér phase bound: the squared modulus of the length-(M+1) geometric sum with ratio
`exp(4iθ)`, divided by `M+1`, is at most `min (M+1) (1/((M+1) sin²(2θ)))`.

Method (adapted from `PEqualNP.Outside.L_goldbach_even_shift_phase_filter`): the phase sum is a
geometric sum `G = Σ_{j<M+1} z^j` with `z = exp(4iθ)`, `‖z‖ = 1`; the triangle inequality gives
`‖G‖ ≤ M+1`, and `G(z-1) = z^(M+1)-1` with `‖z-1‖ = 2|sin 2θ|` and `‖z^(M+1)-1‖ ≤ 2` gives
`‖G‖ ≤ 1/|sin 2θ|`. Squaring and dividing by `M+1 > 0` yields both branches of the minimum.
-/

namespace Conjectures.QuadraticPrimes

theorem AngularHeckeFejerDeterminantKernel :
    ∀ (M : ℕ) (θ : ℝ), Real.sin (2*θ) ≠ 0 →
      ‖(∑ j ∈ Finset.range (M+1), Complex.exp (Complex.I * (4*(j:ℝ)*θ : ℝ)))‖^2 / (M+1 : ℝ)
        ≤ min (M+1 : ℝ) (1/((M+1 : ℝ)*(Real.sin (2*θ))^2)) := by
  intro M θ hsin
  let z : ℂ := Complex.exp (Complex.I * ((4*θ : ℝ) : ℂ))
  have hz : ‖z‖ = 1 := by
    simpa [z, mul_comm] using Complex.norm_exp_ofReal_mul_I (4*θ)
  have hphase (j : ℕ) :
      Complex.exp (Complex.I * (4*(j:ℝ)*θ : ℝ)) = z ^ j := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  let G : ℂ := ∑ j ∈ Finset.range (M+1), z ^ j
  have hG1 : ‖G‖ ≤ (M:ℝ) + 1 := by
    calc
      ‖G‖ ≤ ∑ j ∈ Finset.range (M+1), ‖z ^ j‖ := norm_sum_le _ _
      _ = ((M+1 : ℕ) : ℝ) := by simp [norm_pow, hz]
      _ = (M:ℝ) + 1 := by push_cast; ring
  have chord : ‖z - 1‖ = 2 * |Real.sin (2*θ)| := by
    have h : ‖z - 1‖ = ‖2 * Real.sin ((4*θ) / 2)‖ := by
      simpa [z] using Complex.norm_exp_I_mul_ofReal_sub_one (4*θ)
    rw [h]
    have harg : (4*θ : ℝ) / 2 = 2*θ := by ring
    rw [harg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have geom : ‖G‖ * (2 * |Real.sin (2*θ)|) ≤ 2 := by
    rw [← chord, ← norm_mul, show G * (z - 1) = z ^ (M+1) - 1 from geom_sum_mul z (M+1)]
    calc
      ‖z ^ (M+1) - 1‖ ≤ ‖z ^ (M+1)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hz]; norm_num
  have hsinpos : 0 < |Real.sin (2*θ)| := abs_pos.mpr hsin
  have hG2 : ‖G‖ ≤ 1 / |Real.sin (2*θ)| := by
    rw [le_div_iff₀ hsinpos]
    have h2 : ‖G‖ * |Real.sin (2*θ)| * 2 ≤ 2 := by
      calc ‖G‖ * |Real.sin (2*θ)| * 2 = ‖G‖ * (2 * |Real.sin (2*θ)|) := by ring
        _ ≤ 2 := geom
    linarith
  have hsq : ‖G‖ ^ 2 ≤ 1 / (Real.sin (2*θ)) ^ 2 := by
    have hnn : 0 ≤ ‖G‖ := norm_nonneg _
    have hrhs : 0 ≤ 1 / |Real.sin (2*θ)| := by positivity
    have h1 : ‖G‖ ^ 2 ≤ (1 / |Real.sin (2*θ)|) ^ 2 := by nlinarith
    have h2 : (1 / |Real.sin (2*θ)|) ^ 2 = 1 / (Real.sin (2*θ)) ^ 2 := by
      rw [div_pow, one_pow, sq_abs]
    linarith
  have hN : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hNs : (0:ℝ) < ((M:ℝ) + 1) * (Real.sin (2*θ)) ^ 2 :=
    mul_pos hN (sq_pos_of_ne_zero hsin)
  simp_rw [hphase]
  change ‖G‖ ^ 2 / ((M:ℝ) + 1) ≤ min ((M:ℝ) + 1) (1 / (((M:ℝ) + 1) * (Real.sin (2*θ)) ^ 2))
  apply le_min
  · rw [div_le_iff₀ hN]
    have hsq1 : ‖G‖ ^ 2 ≤ ((M:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg G) hG1 2
    nlinarith
  · rw [div_le_div_iff₀ hN hNs]
    have hmul := mul_le_mul_of_nonneg_right hsq (le_of_lt hNs)
    have hs2 : (Real.sin (2*θ)) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
    have hid : (1 / (Real.sin (2*θ)) ^ 2) * (((M:ℝ) + 1) * (Real.sin (2*θ)) ^ 2) = (M:ℝ) + 1 := by
      field_simp
    linarith

end Conjectures.QuadraticPrimes
