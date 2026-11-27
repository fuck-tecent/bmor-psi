import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4
import Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion

open Finset
open scoped BigOperators
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition DyadicMixedB4LowBand
open DyadicMixedB4Scale DyadicMixedB4PairIntegral

noncomputable section

namespace B1B1Port

/-- The `Λ`-weighted progression sum attached to one atom. -/
def atomWave (a U R : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.Icc (U+1) R, (ArithmeticFunction.vonMangoldt r : ℂ) * phase ((a*r : ℕ) * t)

/-- The balanced-frontier coefficient `τ₁` as `lowBandCoefficient`, expanded into
atoms indexed by the small divisor `a ∈ (U, B₁]`. -/
theorem plainPolynomial_tau1 (n : ℕ) (t : ℝ) :
    plainPolynomial n (fun m => (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)) t
      = ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
          (lowMoebiusWeight (cutoffU n) a : ℂ) * atomWave a (cutoffU n) (n / a) t := by
  have h := Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion
  simp only [plainPolynomial, atomWave, lowBandCoefficient, lowMoebiusWeight,
    cutoffU, lowCut, phase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Finset.mul_sum] at h ⊢
  exact h n t

end B1B1Port
