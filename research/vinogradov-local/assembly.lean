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

/-- Type-I second term in the classical distance-to-integer form. -/
lemma norm_expSum_low_mu_mul_log_le_dist (n U : ℕ) (t : ℝ)
    (hdist : ∀ d ∈ Finset.Icc 1 U, typeIDist ((d:ℝ) * t) ≠ 0) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U, Real.log (n:ℝ) / typeIDist ((d:ℝ) * t) := by
  have hsin : ∀ d ∈ Finset.Icc 1 U, Real.sin (Real.pi * ((d:ℝ) * t)) ≠ 0 := by
    intro d hd h0
    have hpos : 0 < typeIDist ((d:ℝ) * t) :=
      lt_of_le_of_ne (typeIDist_nonneg _) (Ne.symm (hdist d hd))
    have hlower := abs_sin_pi_mul_ge_two_mul_typeIDist ((d:ℝ) * t)
    rw [h0, abs_zero] at hlower
    nlinarith
  refine (norm_expSum_low_mu_mul_log_le n U t hsin).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  have hpos : 0 < typeIDist ((d:ℝ) * t) :=
    lt_of_le_of_ne (typeIDist_nonneg _) (Ne.symm (hdist d hd))
  have hlower := abs_sin_pi_mul_ge_two_mul_typeIDist ((d:ℝ) * t)
  have hone : (1:ℝ) / |Real.sin (Real.pi * ((d:ℝ) * t))| ≤
      1 / (2 * typeIDist ((d:ℝ) * t)) :=
    one_div_le_one_div_of_le (by positivity) hlower
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  calc
    2 * Real.log (n:ℝ) / |Real.sin (Real.pi * ((d:ℝ) * t))| =
        2 * Real.log (n:ℝ) *
          (1 / |Real.sin (Real.pi * ((d:ℝ) * t))|) := by ring
    _ ≤ 2 * Real.log (n:ℝ) *
          (1 / (2 * typeIDist ((d:ℝ) * t))) := by
        apply mul_le_mul_of_nonneg_left hone
        nlinarith
    _ = Real.log (n:ℝ) / typeIDist ((d:ℝ) * t) := by
        field_simp

/-- Type-I second term in the classical reciprocal-distance form. -/
lemma norm_expSum_low_mu_mul_log_le_recip (n U : ℕ) (t : ℝ) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U,
        Real.log (n:ℝ) * typeIDistRecip (n / d) ((d:ℝ) * t) := by
  rw [expSum_low_mu_mul_log_eq n U t]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
    have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
      ArithmeticFunction.abs_moebius_le_one
    have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast h
    simpa using h'
  have hphase : (∑ l ∈ Finset.Icc 1 (n / d),
        (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)) =
      ∑ l ∈ Finset.Icc 1 (n / d),
        (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t)) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [show (((d * l : ℕ) : ℝ) * t) = (l : ℝ) * ((d : ℝ) * t) by
      push_cast
      ring]
  calc
    |(μ : ArithmeticFunction ℝ) d| *
        ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖
        ≤ 1 * ‖∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖ :=
          mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ = ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t))‖ := by
        rw [hphase, one_mul]
    _ ≤ Real.log (n:ℝ) * typeIDistRecip (n / d) ((d:ℝ) * t) :=
        norm_log_weighted_geometric_sum_Icc_le_recip n (n / d) ((d:ℝ) * t)
          (Nat.div_le_self n d)

/-- Type-I second term for every `α ∈ [0,1]` when `Q ≥ 16U`: the Farey
approximation is already inside the major-arc radius, so the small-`q`
second-term bound applies (in particular on the minor arcs). -/
lemma norm_expSum_low_mu_mul_log_le_of_large_Q (n U Q : ℕ) (α : ℝ)
    (hUn : U ≤ n) (hU1 : 1 ≤ U) (hQ : 16 * U ≤ Q)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧
      ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) α‖ ≤
        2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) +
          2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
  have hQpos : 0 < Q := by omega
  obtain ⟨a, q, hq1, hqQ, _ha, hcop, hdist⟩ :=
    exists_farey_approx α hα0 hα1 Q hQpos
  let β : ℝ := α - (a:ℝ)/(q:ℝ)
  have hβ : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
    have h1 : |β| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
      simpa [β] using hdist
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hQle : (16:ℝ) * (U:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    have hden : (q:ℝ) * ((16:ℝ) * (U:ℝ)) ≤ (q:ℝ) * (Q:ℝ) :=
      mul_le_mul_of_nonneg_left hQle hqR.le
    have hstep : 1 / ((q:ℝ) * (Q:ℝ)) ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      calc
        (16:ℝ) * (q:ℝ) * (U:ℝ) = (q:ℝ) * ((16:ℝ) * (U:ℝ)) := by ring
        _ ≤ (q:ℝ) * (Q:ℝ) := hden
    exact h1.trans hstep
  refine ⟨q, hq1, hqQ, ?_⟩
  have hαeq : α = (a:ℝ)/(q:ℝ) + β := by simp [β]
  rw [hαeq]
  exact norm_expSum_low_mu_mul_log_le_majorArc_small_q n q U a β
    (by omega) hcop hU1 hUn hβ

/-- Uniform Type-I second-term bound for `Q ≥ 16U`. -/
lemma norm_expSum_low_mu_mul_log_le_uniform_of_large_Q (n U Q : ℕ) (α : ℝ)
    (hUn : U ≤ n) (hU1 : 1 ≤ U) (hQ : 16 * U ≤ Q)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) α‖ ≤
      2 * (U:ℝ) * (Q:ℝ) * Real.log (n:ℝ) +
        2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
  obtain ⟨q, hq1, hqQ, hbound⟩ :=
    norm_expSum_low_mu_mul_log_le_of_large_Q n U Q α hUn hU1 hQ hα0 hα1
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqQ' : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hnum : 0 ≤ 2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
    positivity
  have h1 : 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) ≤
      2 * (U:ℝ) * (Q:ℝ) * Real.log (n:ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    apply mul_le_mul_of_nonneg_left hqQ'
    positivity
  have h2 : 2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) ≤
      2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ))]
    nlinarith [hnum, hqR]
  linarith

/-- When `Q ≥ 16 U²`, the Type-I major arcs cover `[0,1]`. -/
lemma typeIMajorArcs_Icc_subset_of_large_Q (U Q : ℕ) (hU1 : 1 ≤ U)
    (hQpos : 0 < Q) (hQ : 16 * (U * U) ≤ Q) :
    Set.Icc (0:ℝ) 1 ⊆ typeIMajorArcs U Q := by
  intro α hα
  obtain ⟨a, q, hq1, hqQ, ha, hcop, hdist⟩ :=
    exists_farey_approx α hα.1 hα.2 Q hQpos
  refine ⟨q, a, hq1, hqQ, ha, hcop, ?_⟩
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hQcast : (16:ℝ) * ((U * U : ℕ) : ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hden : (q:ℝ) * ((16:ℝ) * ((U * U : ℕ) : ℝ)) ≤ (q:ℝ) * (Q:ℝ) :=
    mul_le_mul_of_nonneg_left hQcast hqR.le
  have hstep : 1 / ((q:ℝ) * (Q:ℝ)) ≤
      1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (16:ℝ) * (q:ℝ) * ((U * U : ℕ) : ℝ) =
          (q:ℝ) * ((16:ℝ) * ((U * U : ℕ) : ℝ)) := by ring
      _ ≤ (q:ℝ) * (Q:ℝ) := hden
  exact hdist.trans hstep

/-- When `Q ≥ 16 U²`, the Type-I minor arcs are empty inside `[0,1]`. -/
lemma typeIMinorArcs_inter_Icc_eq_empty_of_large_Q (U Q : ℕ) (hU1 : 1 ≤ U)
    (hQpos : 0 < Q) (hQ : 16 * (U * U) ≤ Q) :
    typeIMinorArcs U Q ∩ Set.Icc (0:ℝ) 1 = ∅ := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hmin hIcc
  exact hmin (typeIMajorArcs_Icc_subset_of_large_Q U Q hU1 hQpos hQ hIcc)

/-- Global Type-I bound when `Q ≥ 16 U²`; the minor arcs are empty, so the
uniform major-arc estimate covers every `α ∈ [0,1]`. -/
lemma norm_expSum_vaughan_typeI_le_uniform_of_large_Q (n U Q : ℕ) (α : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hU1 : 1 ≤ U)
    (hQpos : 0 < Q) (hQ : 16 * (U * U) ≤ Q)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖expSum n Λ α - expSum n (high U (μ : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) α‖ ≤
      6 * ((U:ℝ) * (U:ℝ)) * (Q:ℝ) * Real.log (n:ℝ) +
        6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) :=
  norm_expSum_vaughan_typeI_le_on_majorArc_uniform n U Q α hn hUn hU1
    (typeIMajorArcs_Icc_subset_of_large_Q U Q hU1 hQpos hQ ⟨hα0, hα1⟩)

/-- Trivial global Type-I bound, valid for every real `t`. -/
lemma norm_expSum_vaughan_typeI_le_trivial (n U : ℕ) (t : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) :
    ‖expSum n Λ t - expSum n (high U (μ : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) t‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
        + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 := by
  have hdecomp : expSum n Λ t - expSum n (high U (μ : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) t =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) t +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) t := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn t
  have h2 := norm_expSum_low_mu_mul_log_le_trivial n U t hUn
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_trivial n U t hUn
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) t +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) t‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) t +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) t‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) t‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) t‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) +
          (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) +
        (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ = ((U:ℝ) + 1) * Real.log (n:ℝ)
          + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
          + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- Combined Type-I bound with a threshold `M`: the third term is estimated
by the truncated bound, the second term trivially. -/
lemma norm_expSum_vaughan_typeI_le_truncated (n q U M a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
        + (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
  have hdecomp : expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
      expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn ((a:ℝ)/(q:ℝ) + β)
  have h2 := norm_expSum_low_mu_mul_log_le_trivial n U ((a:ℝ)/(q:ℝ) + β) hUn
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_truncated n q U M a β
    hq hcop hU1 hUn hβM
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
              ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
            ((a:ℝ)/(q:ℝ) + β)‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) +
          (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) +
        (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
          + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
          + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
              ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ = ((U:ℝ) + 1) * Real.log (n:ℝ)
          + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
          + (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
              + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
              + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                  ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
      ring

set_option maxHeartbeats 1000000 in
/-- Consequence of the threshold bound at the optimal choice
`M ≈ 1/(16q|β|)`: the `2qM` factor is replaced by `1/(8|β|)`. -/
lemma norm_expSum_vaughan_typeI_le_threshold_recip (n q U M a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U)
    (hβpos : 0 < |β|)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
        + (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) / (8 * |β|)
        + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
        + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
  have hbase := norm_expSum_vaughan_typeI_le_truncated n q U M a β
    hn hUn hq hcop hU1 hβM
  have hM0 : M ≠ 0 := by
    intro hM
    rw [hM] at hβM
    have hzero : (1:ℝ) / (16 * (q:ℝ) * ((0:ℕ):ℝ)) = 0 := by norm_num
    rw [hzero] at hβM
    linarith
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqM : 2 * (q:ℝ) * (M:ℝ) ≤ 1 / (8 * |β|) := by
    have hden : (0:ℝ) < 16 * (q:ℝ) * (M:ℝ) := by positivity
    have h1 : 16 * (q:ℝ) * (M:ℝ) * |β| ≤ 1 := by
      calc
        16 * (q:ℝ) * (M:ℝ) * |β| = |β| * (16 * (q:ℝ) * (M:ℝ)) := by ring
        _ ≤ (1 / (16 * (q:ℝ) * (M:ℝ))) * (16 * (q:ℝ) * (M:ℝ)) :=
          mul_le_mul_of_nonneg_right hβM hden.le
        _ = 1 := by field_simp
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * |β|)]
    nlinarith [h1]
  have hterm : 2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ≤
      (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) / (8 * |β|) := by
    have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    have hprod : 0 ≤ Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by positivity
    calc
      2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
          = (2 * (q:ℝ) * (M:ℝ)) * (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) := by ring
      _ ≤ (1 / (8 * |β|)) * (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) :=
        mul_le_mul_of_nonneg_right hqM hprod
      _ = (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) / (8 * |β|) := by ring
  calc
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ((U:ℝ) + 1) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
            + (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
                + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
                + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                    ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := hbase
    _ ≤ ((U:ℝ) + 1) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
            + (Real.log (n:ℝ) * (1 + Real.log (n:ℝ))) / (8 * |β|)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
      nlinarith [hterm]

set_option maxHeartbeats 1000000 in
/-- Combined Type-I bound on a minor arc with threshold `M`: both the second
and third terms are truncated at `M`, the first term is trivial. -/
lemma norm_expSum_vaughan_typeI_le_truncated_tail (n q U M a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U) (hM1 : 1 ≤ M) (hMU : M ≤ U)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (Real.log (U:ℝ) - Real.log (M:ℝ)))
        + (2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
  have hdecomp : expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
      expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn ((a:ℝ)/(q:ℝ) + β)
  have h2 := norm_expSum_low_mu_mul_log_le_truncated n q U M a β
    hq hcop hU1 hUn hM1 hMU hβM
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_truncated_tail n q U M a β
    hq hcop hU1 hUn hM1 (le_trans hMU (Nat.le_mul_of_pos_left U (by omega))) hβM
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
              ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
            ((a:ℝ)/(q:ℝ) + β)‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) +
          (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (Real.log (U:ℝ) - Real.log (M:ℝ)))) +
        (2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ = ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (Real.log (U:ℝ) - Real.log (M:ℝ)))
        + (2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
      ring

set_option maxHeartbeats 1000000 in
/-- Type-I bound from a Farey approximation when `Q ≥ 16 U`: the natural
threshold is `M = U`, so the truncation tails vanish. -/
lemma norm_expSum_vaughan_typeI_le_farey_large (n q U Q a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U) (hlarge : 16 * U ≤ Q)
    (hβ : |β| ≤ 1 / ((q:ℝ) * (Q:ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ))
        + (2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (U:ℝ)))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hQR : (16:ℝ) * (U:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hlarge
  have hβU : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
    refine hβ.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [hQR, hqR, hUpos]
  have hbase := norm_expSum_vaughan_typeI_le_truncated_tail n q U U a β
    hn hUn hq hcop hU1 hU1 le_rfl hβU
  have hUR : (U:ℝ) ≠ 0 := ne_of_gt hUpos
  have hlogU : ((U:ℝ) * (U:ℝ)) / (U:ℝ) = (U:ℝ) := by field_simp
  rw [hlogU] at hbase
  calc
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ((U:ℝ) + 1) * Real.log (n:ℝ)
            + (2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ)
                + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)
                + (n:ℝ) * Real.log (n:ℝ) * (Real.log (U:ℝ) - Real.log (U:ℝ)))
            + (2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ))))
                + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) * (1 + Real.log (U:ℝ)))
                + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                    ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := hbase
    _ = ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ))
        + (2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (U:ℝ)))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
      ring

set_option maxHeartbeats 1000000 in
/-- Type-I bound from a Farey approximation when `Q < 16 U` (and `Q ≥ 16`):
the natural threshold is `M = Q/16`. -/
lemma norm_expSum_vaughan_typeI_le_farey_small (n q U Q a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U) (hQ16 : 16 ≤ Q) (hsmallQ : Q < 16 * U)
    (hβ : |β| ≤ 1 / ((q:ℝ) * (Q:ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (q:ℝ) * ((Q / 16 : ℕ) : ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) *
                (Real.log (U:ℝ) - Real.log ((Q / 16 : ℕ) : ℝ)))
        + (2 * (q:ℝ) * (Real.log (n:ℝ) *
              (((Q / 16 : ℕ) : ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (((U:ℝ) * (U:ℝ)) / ((Q / 16 : ℕ) : ℝ))))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hM1 : 1 ≤ Q / 16 := Nat.one_le_div_iff (by norm_num : 0 < 16) |>.mpr hQ16
  have hMU : Q / 16 ≤ U := by
    have hcast : ((Q / 16 : ℕ) : ℝ) ≤ (Q:ℝ) / 16 := Nat.cast_div_le
    have hlt : (Q:ℝ) / 16 < (U:ℝ) := by
      have : (Q:ℝ) < 16 * (U:ℝ) := by exact_mod_cast hsmallQ
      linarith
    have : ((Q / 16 : ℕ) : ℝ) < (U:ℝ) := lt_of_le_of_lt hcast hlt
    exact_mod_cast le_of_lt this
  have hβM : |β| ≤ 1 / (16 * (q:ℝ) * ((Q / 16 : ℕ) : ℝ)) := by
    refine hβ.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have hcast : ((Q / 16 : ℕ) : ℝ) ≤ (Q:ℝ) / 16 := Nat.cast_div_le
    have h16 : 16 * ((Q / 16 : ℕ) : ℝ) ≤ (Q:ℝ) := by linarith
    nlinarith [h16, hqR]
  exact norm_expSum_vaughan_typeI_le_truncated_tail n q U (Q / 16) a β
    hn hUn hq hcop hU1 hM1 hMU hβM

set_option maxHeartbeats 1000000 in
/-- Uniform global Type-I bound for `Q ≥ 16 U`: for every `α ∈ [0,1]` the
Farey approximation `q ≤ Q` produces the threshold-`U` estimate, and all
`q`-dependences are relaxed to `q ≤ Q`. -/
lemma norm_expSum_vaughan_typeI_le_uniform_threshold (n U Q : ℕ) (α : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hU1 : 1 ≤ U) (hlarge : 16 * U ≤ Q)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖expSum n Λ α - expSum n (high U (μ : ArithmeticFunction ℝ) *
      (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) α‖ ≤
      ((U:ℝ) + 1) * Real.log (n:ℝ)
        + (2 * (Q:ℝ) * (U:ℝ) * Real.log (n:ℝ)
            + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)))
        + (2 * (Q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ))))
            + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                (1 + Real.log (U:ℝ)))
            + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                (1 + Real.log (((U * U : ℕ)) : ℝ)))) := by
  have hQpos : 0 < Q := by omega
  obtain ⟨a, q, hq1, hqQ, _ha, hcop, hdist⟩ :=
    exists_farey_approx α hα0 hα1 Q hQpos
  have hq : 0 < q := by omega
  let β : ℝ := α - (a:ℝ)/(q:ℝ)
  have hβ : |β| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
    simpa [β] using hdist
  have hαeq : α = (a:ℝ)/(q:ℝ) + β := by simp [β]
  rw [hαeq]
  have hbase := norm_expSum_vaughan_typeI_le_farey_large n q U Q a β
    hn hUn hq hcop hU1 hlarge hβ
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hlogU : 0 ≤ Real.log (U:ℝ) := Real.log_natCast_nonneg U
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqQ' : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQpos
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hU0 : (0:ℝ) ≤ (U:ℝ) := by positivity
  have hlogU2 : 0 ≤ Real.log (((U * U : ℕ)) : ℝ) := Real.log_natCast_nonneg (U * U)
  have hm1 : 2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ) ≤
      2 * (Q:ℝ) * (U:ℝ) * Real.log (n:ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    nlinarith [hqQ', hqR, hU0]
  have hm2 : (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) ≤
      (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
    rw [div_le_iff₀ hqR]
    nlinarith [hq1R, hlog,
      show (0:ℝ) ≤ (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) by positivity]
  have hm3 : 2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) ≤
      2 * (Q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [hqQ', hqR]
  have hfac : (1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)) ≤
      1 * (1 + Real.log (((U * U : ℕ)) : ℝ)) := by
    apply mul_le_mul
    · rw [div_le_one hqR]
      exact hq1R
    · have hdivle : ((U * U) / q : ℕ) ≤ U * U := Nat.div_le_self _ _
      have hmono : Real.log ((((U * U) / q : ℕ)) : ℝ) ≤
          Real.log (((U * U : ℕ)) : ℝ) := by
        rcases Nat.eq_zero_or_pos ((U * U) / q) with h0 | hpos
        · rw [h0]
          simpa using hlogU2
        · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hdivle)
      linarith
    · positivity
    · positivity
  have hm5 : (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
        ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))
      ≤ (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
        (1 + Real.log (((U * U : ℕ)) : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc Real.log (((U * U : ℕ)) : ℝ) *
          ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))
        ≤ Real.log (((U * U : ℕ)) : ℝ) *
            (1 * (1 + Real.log (((U * U : ℕ)) : ℝ))) :=
          mul_le_mul_of_nonneg_left hfac hlogU2
      _ = Real.log (((U * U : ℕ)) : ℝ) *
            (1 + Real.log (((U * U : ℕ)) : ℝ)) := by ring
  refine hbase.trans ?_
  linarith [hm1, hm2, hm3, hm5]

/-- Wide Type-I major arcs: rational centres `a/q` with `q ≤ Q0` and the
radius `1/(qQ)` used by the disjoint-arc circle method. -/
def typeIMajorArcsWide (Q0 Q : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q0 ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ 1 / ((q:ℝ) * (Q:ℝ))}

/-- The wide Type-I minor arcs are the complement of the wide major arcs. -/
def typeIMinorArcsWide (Q0 Q : ℕ) : Set ℝ := (typeIMajorArcsWide Q0 Q)ᶜ

/-- Every wide major-arc point has the `a/q + β` form with `q ≤ Q0`. -/
lemma exists_wideMajorArc_representation (Q0 Q : ℕ) {t : ℝ}
    (ht : t ∈ typeIMajorArcsWide Q0 Q) :
    ∃ q a : ℕ, ∃ β : ℝ, 1 ≤ q ∧ q ≤ Q0 ∧ a ≤ q ∧ Nat.Coprime a q ∧
      t = (a:ℝ)/(q:ℝ) + β ∧ |β| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
  obtain ⟨q, a, hq1, hqQ, ha, hcop, hβ⟩ := ht
  exact ⟨q, a, t - (a:ℝ)/(q:ℝ), hq1, hqQ, ha, hcop, by ring, by simpa using hβ⟩

/-- On the wide minor arcs every Farey approximation with radius `1/(qQ)`
has denominator strictly bigger than `Q0`. -/
lemma lt_of_not_mem_typeIMajorArcsWide {Q0 Q : ℕ} {t : ℝ} {q a : ℕ}
    (ht : t ∉ typeIMajorArcsWide Q0 Q) (hq1 : 1 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q)
    (hβ : |t - (a:ℝ)/(q:ℝ)| ≤ 1 / ((q:ℝ) * (Q:ℝ))) :
    Q0 < q := by
  by_contra h
  exact ht ⟨q, a, hq1, by omega, ha, hcop, hβ⟩

/-- Farey approximation on the wide minor arcs: the denominator satisfies
`Q0 < q ≤ Q`. -/
lemma exists_farey_approx_minorWide (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (Q0 Q : ℕ) (hQ : 0 < Q) (hminor : α ∉ typeIMajorArcsWide Q0 Q) :
    ∃ a q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ Q0 < q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - (a:ℝ)/(q:ℝ)| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
  obtain ⟨a, q, hq1, hqQ, ha, hcop, hβ⟩ := exists_farey_approx α hα0 hα1 Q hQ
  exact ⟨a, q, hq1, hqQ,
    lt_of_not_mem_typeIMajorArcsWide hminor hq1 ha hcop hβ, ha, hcop, hβ⟩

set_option maxHeartbeats 1000000 in
/-- Type-I estimate on the wide minor arcs in the regime `Q ≥ 16 U`, with the
denominator `q` controlled from below by `Q0`: all `1/q` factors are relaxed
to `1/Q0`. -/
theorem norm_expSum_vaughan_typeI_le_wideMinorArc (n U Q0 Q : ℕ) (α : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hU1 : 1 ≤ U) (hlarge : 16 * U ≤ Q)
    (hQ0 : 1 ≤ Q0) (hQpos : 0 < Q) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hminor : α ∉ typeIMajorArcsWide Q0 Q) :
    ∃ q : ℕ, Q0 < q ∧ q ≤ Q ∧
      ‖expSum n Λ α - expSum n (high U (μ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ) * high U (Λ : ArithmeticFunction ℝ)) α‖ ≤
        ((U:ℝ) + 1) * Real.log (n:ℝ)
          + (2 * (Q:ℝ) * (U:ℝ) * Real.log (n:ℝ)
              + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (Q0:ℝ))
          + (2 * (Q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ))))
              + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
                  (1 + Real.log (U:ℝ)))
              + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
                  (1 + Real.log (((U * U : ℕ)) : ℝ))) / (Q0:ℝ)) := by
  obtain ⟨a, q, hq1, hqQ, hQ0q, ha, hcop, hβ⟩ :=
    exists_farey_approx_minorWide α hα0 hα1 Q0 Q hQpos hminor
  have hq : 0 < q := by omega
  let β : ℝ := α - (a:ℝ)/(q:ℝ)
  have hβ' : |β| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by simpa [β] using hβ
  have hαeq : α = (a:ℝ)/(q:ℝ) + β := by simp [β]
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hlogU : 0 ≤ Real.log (U:ℝ) := Real.log_natCast_nonneg U
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hQ0R : (0:ℝ) < (Q0:ℝ) := by exact_mod_cast hQ0
  have hqQ' : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
  have hQ0q' : (Q0:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_of_lt hQ0q
  have hlogU2 : 0 ≤ Real.log (((U * U : ℕ)) : ℝ) := Real.log_natCast_nonneg (U * U)
  refine ⟨q, hQ0q, hqQ, ?_⟩
  rw [hαeq]
  have hbase := norm_expSum_vaughan_typeI_le_farey_large n q U Q a β
    hn hUn hq hcop hU1 hlarge hβ'
  -- Replace the `1/q` factors by `1/Q0`.
  have hm2 : (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) ≤
      (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (Q0:ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity) hQ0R hQ0q'
  have hm5 : (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
        ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))
      ≤ (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
          (1 + Real.log (((U * U : ℕ)) : ℝ))) / (Q0:ℝ) := by
    have hfac : (1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)) ≤
        (1 / (Q0:ℝ)) * (1 + Real.log (((U * U : ℕ)) : ℝ)) := by
      apply mul_le_mul
      · exact one_div_le_one_div_of_le hQ0R hQ0q'
      · have hdivle : ((U * U) / q : ℕ) ≤ U * U := Nat.div_le_self _ _
        have hmono : Real.log ((((U * U) / q : ℕ)) : ℝ) ≤
            Real.log (((U * U : ℕ)) : ℝ) := by
          rcases Nat.eq_zero_or_pos ((U * U) / q) with h0 | hpos
          · rw [h0]
            simpa using hlogU2
          · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hdivle)
        linarith
      · positivity
      · positivity
    calc (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
          ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))))
        ≤ (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            ((1 / (Q0:ℝ)) * (1 + Real.log (((U * U : ℕ)) : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac hlogU2
      _ = (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            (1 + Real.log (((U * U : ℕ)) : ℝ))) / (Q0:ℝ) := by ring
  have hm1 : 2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ) ≤
      2 * (Q:ℝ) * (U:ℝ) * Real.log (n:ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    nlinarith [hqQ', hqR, show (0:ℝ) ≤ (U:ℝ) by positivity]
  have hm3 : 2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) ≤
      2 * (Q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [hqQ', hqR]
  have hstep1 : ((U:ℝ) + 1) * Real.log (n:ℝ) +
        (2 * (q:ℝ) * (U:ℝ) * Real.log (n:ℝ) +
          (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)) +
        (2 * (q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) +
          (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
            (1 + Real.log (U:ℝ))) +
          (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))))
      ≤ ((U:ℝ) + 1) * Real.log (n:ℝ) +
        (2 * (Q:ℝ) * (U:ℝ) * Real.log (n:ℝ) +
          (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (Q0:ℝ)) +
        (2 * (Q:ℝ) * (Real.log (n:ℝ) * ((U:ℝ) * (1 + Real.log (U:ℝ)))) +
          (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
            (1 + Real.log (U:ℝ))) +
          (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            (1 + Real.log (((U * U : ℕ)) : ℝ))) / (Q0:ℝ)) := by
    linarith [hm1, hm2, hm3, hm5]
  exact hbase.trans hstep1

set_option maxHeartbeats 1000000 in
/-- The Type-I second term at a minor arc with `q ≥ 2U`: the classical
`q`-saving `2q log n (1 + log q)` replacing `2qU log n + n log n (1+log n)/q`. -/
theorem norm_expSum_low_mu_mul_log_le_residues (n U q a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hUn : U ≤ n) (hUq : 2 * U ≤ q)
    (hβ : (U:ℝ) * |β| ≤ 1 / (2 * (q:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
        ((a:ℝ)/(q:ℝ) + β)‖ ≤
      4 * (q:ℝ) * Real.log (n:ℝ) * (1 + Real.log (q:ℝ)) := by
  refine (norm_expSum_low_mu_mul_log_le_recip n U ((a:ℝ)/(q:ℝ) + β)).trans ?_
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  -- Pointwise: the capped reciprocal distance is at most `2q / r_d`.
  have hpoint : ∀ d ∈ Finset.Icc 1 U,
      Real.log (n:ℝ) * typeIDistRecip (n / d) ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))
        ≤ Real.log (n:ℝ) * (2 * (q:ℝ) /
            (((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ)) := by
    intro d hd
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    have hUq' : U < q := by omega
    have hdq : d < q := lt_of_le_of_lt hdU hUq'
    have hβd : (d:ℝ) * |β| ≤ 1 / (2 * (q:ℝ)) := by
      have hdU' : (d:ℝ) ≤ (U:ℝ) := by exact_mod_cast hdU
      exact (mul_le_mul_of_nonneg_right hdU' (abs_nonneg β)).trans hβ
    have hxne : (d * a) % q ≠ 0 := by
      intro h0
      have hdvd : q ∣ d * a := Nat.dvd_of_mod_eq_zero h0
      have hqd : q ∣ d := hcop.symm.dvd_of_dvd_mul_right hdvd
      have := Nat.le_of_dvd (by omega) hqd
      omega
    have hx1 : 1 ≤ (d * a) % q := Nat.one_le_iff_ne_zero.mpr hxne
    have hxq : (d * a) % q < q := Nat.mod_lt _ hq
    have hr1 : 1 ≤ min ((d * a) % q) (q - (d * a) % q) :=
      le_min hx1 (by omega)
    have hrpos : (0:ℝ) < (((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) := by
      exact_mod_cast (by omega : 0 < min ((d * a) % q) (q - (d * a) % q))
    have hsep := typeIDist_mul_farey_shift_ge_residue q a d β hq hcop hd1 hdq hβd
    have hdistpos : 0 < typeIDist ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) :=
      lt_of_lt_of_le (div_pos (by positivity) (by positivity)) hsep
    have hrecip : typeIDistRecip (n / d) ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))
        ≤ 1 / typeIDist ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
      rw [typeIDistRecip, if_neg (ne_of_gt hdistpos)]
      exact min_le_right _ _
    have hone : 1 / typeIDist ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))
        ≤ 1 / ((((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) / (2 * (q:ℝ))) :=
      one_div_le_one_div_of_le (div_pos hrpos (by positivity)) hsep
    have hval : 1 / ((((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) / (2 * (q:ℝ)))
        = 2 * (q:ℝ) / (((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) := by
      field_simp
    calc Real.log (n:ℝ) * typeIDistRecip (n / d) ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))
        ≤ Real.log (n:ℝ) * (1 / typeIDist ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))) :=
          mul_le_mul_of_nonneg_left hrecip hlog
      _ ≤ Real.log (n:ℝ) * (1 / ((((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) / (2 * (q:ℝ)))) :=
          mul_le_mul_of_nonneg_left hone hlog
      _ = Real.log (n:ℝ) * (2 * (q:ℝ) /
            (((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ)) := by rw [hval]
  calc (∑ d ∈ Finset.Icc 1 U,
        Real.log (n:ℝ) * typeIDistRecip (n / d) ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))
      ≤ ∑ d ∈ Finset.Icc 1 U,
          Real.log (n:ℝ) * (2 * (q:ℝ) /
            (((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ)) :=
        Finset.sum_le_sum hpoint
    _ = Real.log (n:ℝ) * (2 * (q:ℝ)) *
          ∑ d ∈ Finset.Icc 1 U,
            (1:ℝ)/(((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ ≤ Real.log (n:ℝ) * (2 * (q:ℝ)) * (2 * (1 + Real.log (q:ℝ))) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_residue_le q a U hq hcop hUq)
        positivity
    _ = 4 * (q:ℝ) * Real.log (n:ℝ) * (1 + Real.log (q:ℝ)) := by ring

end

end PEqualNP.Outside.Vaughan
