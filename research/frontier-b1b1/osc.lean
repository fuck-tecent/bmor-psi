import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [show ((2*Real.pi*x:ℝ):ℂ)*Complex.I = ((2*Real.pi*x:ℝ):ℂ) * Complex.I from rfl]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Length bound for the Fourier integral over an interval. -/
lemma norm_integral_E_le_length (h : ℤ) {A B : ℝ} (hAB : A ≤ B) :
    ‖∫ t in A..B, E ((h:ℝ)*t)‖ ≤ B - A := by
  have h1 : ‖∫ t in A..B, E ((h:ℝ)*t)‖ ≤ 1 * |B - A| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [norm_E]
  rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr hAB)] at h1

/-- Oscillation bound: the Fourier integral over any interval is at most
`1/(π |h|)` for nonzero integer `h`. -/
lemma norm_integral_E_le_osc (h : ℤ) (hh : h ≠ 0) {A B : ℝ} :
    ‖∫ t in A..B, E ((h:ℝ)*t)‖ ≤ 1/(Real.pi * |(h:ℝ)|) := by
  have hhR : (h:ℝ) ≠ 0 := by exact_mod_cast hh
  have hc : ((2*Real.pi*Complex.I)*(h:ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
    · exact_mod_cast hh
  have hcongr : ∀ t : ℝ, E ((h:ℝ)*t) = Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (t:ℂ)) := by
    intro t
    unfold E
    congr 1
    push_cast
    ring
  simp_rw [hcongr]
  rw [integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (B:ℂ)) -
      Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (A:ℂ))‖ ≤ 2 := by
    have hnorm : ∀ x : ℝ, ‖Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (x:ℂ))‖ = 1 := by
      intro x
      rw [Complex.norm_exp]
      have : (((2*Real.pi*Complex.I)*(h:ℂ)) * (x:ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [this, Real.exp_zero]
    calc ‖Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (B:ℂ)) -
          Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (A:ℂ))‖
        ≤ ‖Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (B:ℂ))‖ +
          ‖Complex.exp (((2*Real.pi*Complex.I)*(h:ℂ)) * (A:ℂ))‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hnorm B, hnorm A]
      _ = 2 := by norm_num
  have hden : ‖((2*Real.pi*Complex.I)*(h:ℂ))‖ = 2*Real.pi*|(h:ℝ)| := by
    rw [norm_mul, norm_mul]
    have h1 : ‖(2 * (Real.pi:ℂ))‖ = 2*Real.pi := by
      rw [show (2 * (Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖(h:ℂ)‖ = |(h:ℝ)| := by
      rw [show (h:ℂ) = ((h:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2, Complex.norm_I, mul_one]
  rw [hden]
  have hdenpos : (0:ℝ) < 2*Real.pi*|(h:ℝ)| := by positivity
  rw [div_le_iff₀ hdenpos]
  have hval : (1/(Real.pi * |(h:ℝ)|)) * (2*Real.pi*|(h:ℝ)|) = 2 := by
    field_simp
  rw [hval]
  exact hnum

end B1B1
