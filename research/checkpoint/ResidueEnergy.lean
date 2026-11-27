import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators Interval

namespace GoldbachSupport

/-- A lower bound on the unweighted sum of the residue amplitudes gives a
lower bound on their second moment. The cardinality bound may be strict. -/
theorem residueEnergy {ι : Type*} (s : Finset ι) (z : ι → ℂ) {n : ℝ} {q : ℕ}
    (hn : 0 ≤ n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hamp : n / 8 ≤ ‖∑ a ∈ s, z a‖) :
    n ^ 2 / (64 * (q : ℝ)) ≤ ∑ a ∈ s, ‖z a‖ ^ 2 := by
  have hsum := hamp.trans (norm_sum_le s z)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ n / 8) hsum 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => ‖z a‖)
  have hc : (s.card : ℝ) ≤ q := by exact_mod_cast hcard
  have henergy : 0 ≤ ∑ a ∈ s, ‖z a‖ ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  apply (div_le_iff₀ (by positivity : 0 < 64 * (q : ℝ))).2
  nlinarith only [hsq, hcs, mul_le_mul_of_nonneg_right hc henergy]

/-- Integrating the pointwise estimate along each residue window of width
`1 / (6*n)` gives the contribution `n / (384*q)` for one denominator. -/
theorem residueWindowEnergy {ι : Type*} (s : Finset ι) (z : ι → ℝ → ℂ) {n : ℝ} {q : ℕ}
    (hn : 0 < n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hz : ∀ a ∈ s, Continuous (z a))
    (hamp : ∀ h ∈ Set.Icc 0 (1 / (6 * n)), n / 8 ≤ ‖∑ a ∈ s, z a h‖) :
    n / (384 * (q : ℝ)) ≤ ∑ a ∈ s, ∫ h in (0 : ℝ)..1 / (6 * n), ‖z a h‖ ^ 2 := by
  have hcont : Continuous (fun h => ∑ a ∈ s, ‖z a h‖ ^ 2) :=
    continuous_finsetSum _ fun a ha => (hz a ha).norm.pow 2
  calc
    n / (384 * (q : ℝ)) = ∫ _ in (0 : ℝ)..1 / (6 * n), n ^ 2 / (64 * (q : ℝ)) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
      ring
    _ ≤ ∫ h in (0 : ℝ)..1 / (6 * n), ∑ a ∈ s, ‖z a h‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
        (hcont.intervalIntegrable ..)
      exact fun h hh => residueEnergy s (fun a => z a h) hn.le hq hcard (hamp h hh)
    _ = _ := intervalIntegral.integral_finsetSum fun a ha =>
      ((hz a ha).norm.pow 2).intervalIntegrable ..

end GoldbachSupport

#print axioms GoldbachSupport.residueEnergy
#print axioms GoldbachSupport.residueWindowEnergy
