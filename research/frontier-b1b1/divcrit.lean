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

/-- The phase is one exactly at integer multiples of `1/q`. -/
lemma E_div_eq_one_iff (h : ℤ) (q : ℕ) (hq : 0 < q) :
    E ((h:ℝ)/(q:ℝ)) = 1 ↔ (q:ℤ) ∣ h := by
  constructor
  · intro hE
    unfold E at hE
    rw [Complex.exp_eq_one_iff] at hE
    obtain ⟨n, hn⟩ := hE
    have hn2 : ((2*Real.pi*((h:ℝ)/(q:ℝ)) : ℝ) : ℂ) =
        ((n:ℝ)*(2*Real.pi) : ℝ) := by
      have h2 : ((2*Real.pi*((h:ℝ)/(q:ℝ)) : ℝ) : ℂ) * Complex.I =
          ((n:ℝ) * (2*Real.pi) : ℝ) * Complex.I := by
        calc ((2*Real.pi*((h:ℝ)/(q:ℝ)) : ℝ) : ℂ) * Complex.I
            = ((n:ℝ) : ℂ) * (2*Real.pi*Complex.I) := hn
          _ = ((n:ℝ) * (2*Real.pi) : ℝ) * Complex.I := by push_cast; ring
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have hreal : (2*Real.pi)*((h:ℝ)/(q:ℝ)) = (n:ℝ)*(2*Real.pi) := by
      have := Complex.ofReal_injective hn2
      push_cast at this
      linarith
    have hpi : (2*Real.pi) ≠ 0 := by positivity
    have hratio : (h:ℝ)/(q:ℝ) = (n:ℝ) := by
      field_simp at hreal ⊢
      linarith
    have hcast : (h:ℤ) = (q:ℤ) * n := by
      have : (h:ℝ) = (q:ℝ) * (n:ℝ) := by
        field_simp at hratio ⊢
        linarith
      exact_mod_cast this
    exact ⟨n, hcast⟩
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    have hqR : (q:ℝ) ≠ 0 := by positivity
    rw [show (((q:ℤ)*(k:ℤ) : ℤ) : ℝ)/(q:ℝ) = (k:ℝ) by push_cast; field_simp]
    exact E_int k

end B1B1
