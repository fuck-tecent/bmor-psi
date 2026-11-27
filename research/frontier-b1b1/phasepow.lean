import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma E_nat_mul (x : ℝ) (a : ℕ) : E ((a:ℝ)*x) = E x ^ a := by
  unfold E
  rw [show (((2*Real.pi*((a:ℝ)*x):ℝ):ℂ)*Complex.I)
      = (a:ℂ) * (((2*Real.pi*x:ℝ):ℂ)*Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul _ a

/-- The arc phase is a power of the primitive phase `E(h/q)`. -/
lemma E_phase_pow (h : ℤ) (q a : ℕ) :
    E ((h:ℝ)*(a:ℝ)/(q:ℝ)) = E ((h:ℝ)/(q:ℝ)) ^ a := by
  rw [show (h:ℝ)*(a:ℝ)/(q:ℝ) = (a:ℝ)*((h:ℝ)/(q:ℝ)) by ring]
  exact E_nat_mul _ a

end B1B1
