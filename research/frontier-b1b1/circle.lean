import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma E_zero : E 0 = 1 := by simp [E]

lemma E_int (h : ℤ) : E ((h:ℝ)) = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (h:ℝ) : ℝ) : ℂ) * Complex.I)
      = (h:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I h

/-- The full-circle Fourier integral: `∫_0^1 e(h t) dt` is `1` at `h = 0`
and `0` otherwise. -/
lemma integral_E_circle (h : ℤ) :
    (∫ t in (0:ℝ)..1, E ((h:ℝ)*t)) = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst hh
    simp [E]
  · have hc : ((2*Real.pi*Complex.I) * (h:ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · exact_mod_cast hh
    rw [if_neg hh]
    have hcongr : ∀ t : ℝ,
        E ((h:ℝ)*t) = Complex.exp (((2*Real.pi*Complex.I) * (h:ℂ)) * (t:ℂ)) := by
      intro t
      unfold E
      congr 1
      push_cast
      ring
    simp_rw [hcongr]
    rw [integral_exp_mul_complex hc]
    have htop : Complex.exp (((2*Real.pi*Complex.I) * (h:ℂ)) * ((1:ℝ):ℂ)) = 1 := by
      rw [show ((2*Real.pi*Complex.I) * (h:ℂ)) * ((1:ℝ):ℂ)
          = (h:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I h
    have hbot : Complex.exp (((2*Real.pi*Complex.I) * (h:ℂ)) * ((0:ℝ):ℂ)) = 1 := by simp
    rw [htop, hbot, sub_self, zero_div]

end B1B1
