import Mathlib

theorem Conjectures.JoshiAbc.FiveFactorization :
    (Polynomial.X^3-2 : Polynomial (ZMod 5)) = (Polynomial.X-3)*(Polynomial.X^2+3*Polynomial.X+4) ∧
      ∀ x : ZMod 5, x^2+3*x+4 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have h5 : (5 : Polynomial (ZMod 5)) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (Polynomial (ZMod 5)) 5
    linear_combination (Polynomial.X + 2) * h5
  · decide
