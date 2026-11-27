import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma E_int (h : ℤ) : E ((h:ℝ)) = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (h:ℝ) : ℝ) : ℂ) * Complex.I)
      = (h:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I h

lemma E_nat_mul (x : ℝ) (a : ℕ) : E ((a:ℝ)*x) = E x ^ a := by
  unfold E
  rw [show (((2*Real.pi*((a:ℝ)*x):ℝ):ℂ)*Complex.I)
      = (a:ℂ) * (((2*Real.pi*x:ℝ):ℂ)*Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul _ a

/-- The geometric sum over a full denominator period. -/
lemma geom_sum_E (h : ℤ) (q : ℕ) (hq : 0 < q) :
    ∑ a ∈ Finset.range q, E ((h:ℝ)*(a:ℝ)/(q:ℝ)) =
      if E ((h:ℝ)/(q:ℝ)) = 1 then (q:ℂ) else 0 := by
  set ω : ℂ := E ((h:ℝ)/(q:ℝ)) with hω
  have hpow : ∀ a : ℕ, E ((h:ℝ)*(a:ℝ)/(q:ℝ)) = ω ^ a := by
    intro a
    rw [hω]
    rw [show (h:ℝ)*(a:ℝ)/(q:ℝ) = (a:ℝ)*((h:ℝ)/(q:ℝ)) by ring]
    exact E_nat_mul _ a
  simp_rw [hpow]
  have hωq : ω ^ q = 1 := by
    rw [hω]
    rw [← E_nat_mul]
    have hqR : (q:ℝ) ≠ 0 := by positivity
    rw [show (q:ℝ) * ((h:ℝ)/(q:ℝ)) = (h:ℝ) by field_simp]
    exact E_int h
  by_cases hω1 : ω = 1
  · rw [if_pos hω1]
    simp [hω1]
  · rw [if_neg hω1, geom_sum_eq hω1 q, hωq, sub_self, zero_div]

end B1B1
