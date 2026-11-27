import arcs
import type1_bound

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace PEqualNP.Outside.Vaughan

noncomputable section

/-- Pointwise Type-I bound on a Type-I major arc: for every `t` in the
major-arc union there is a representative denominator `q ≤ Q` for which the
combined Type-I estimate holds. -/
theorem norm_expSum_vaughan_typeI_le_on_majorArc (n U Q : ℕ) (t : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hU1 : 1 ≤ U)
    (ht : t ∈ typeIMajorArcs U Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧
      ‖expSum n Λ t - expSum n (high U (μ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) t‖ ≤
        6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
          6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
  obtain ⟨q, a, β, hq1, hqQ, _ha, hcop, hteq, hβ⟩ :=
    exists_majorArc_representation U Q ht
  refine ⟨q, hq1, hqQ, ?_⟩
  rw [hteq]
  exact norm_expSum_vaughan_typeI_le_majorArc_small_q n q U a β
    hn hUn (by omega) hcop hU1 hβ

/-- Uniform Type-I major-arc bound: on the whole major-arc union the
denominator `q` can be bounded by `Q`, giving a single estimate. -/
theorem norm_expSum_vaughan_typeI_le_on_majorArc_uniform (n U Q : ℕ) (t : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hU1 : 1 ≤ U)
    (ht : t ∈ typeIMajorArcs U Q) :
    ‖expSum n Λ t - expSum n (high U (μ : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) t‖ ≤
      6 * ((U:ℝ) * (U:ℝ)) * (Q:ℝ) * Real.log (n:ℝ) +
        6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
  obtain ⟨q, hq1, hqQ, hbound⟩ :=
    norm_expSum_vaughan_typeI_le_on_majorArc n U Q t hn hUn hU1 ht
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqQ' : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hnum : 0 ≤ (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
    positivity
  have h1 : 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) ≤
      6 * ((U:ℝ) * (U:ℝ)) * (Q:ℝ) * Real.log (n:ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    apply mul_le_mul_of_nonneg_left hqQ'
    positivity
  have h2 : 6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) ≤
      6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ))]
    nlinarith [hnum, hqR]
  linarith

end

end PEqualNP.Outside.Vaughan
