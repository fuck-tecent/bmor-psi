import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.Vaughan

/-- The Type-I major arcs: rational centres `a/q` with `q ≤ Q` and radius
`1/(16 q U²)`, the width used by the Type-I estimates. -/
def typeIMajorArcs (U Q : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))}

/-- The Type-I minor arcs are the complement of the major arcs. -/
def typeIMinorArcs (U Q : ℕ) : Set ℝ := (typeIMajorArcs U Q)ᶜ

lemma mem_typeIMajorArcs_iff (U Q : ℕ) (t : ℝ) :
    t ∈ typeIMajorArcs U Q ↔
      ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)) :=
  Iff.rfl

lemma measurableSet_typeIMajorArcs (U Q : ℕ) :
    MeasurableSet (typeIMajorArcs U Q) := by
  classical
  have hset : typeIMajorArcs U Q =
      ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))} := by
    ext t
    simp only [typeIMajorArcs, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  by_cases hq : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · have hset2 : {t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))} =
        Set.Icc ((a:ℝ)/(q:ℝ) - 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)))
          ((a:ℝ)/(q:ℝ) + 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_Icc]
      have hiff : (1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) ↔
          |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)) := by
        constructor
        · rintro ⟨_, _, _, _, h⟩
          exact h
        · intro h
          exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, h⟩
      rw [hiff, abs_le]
      constructor <;> intro h <;> constructor <;> linarith
    rw [hset2]
    exact measurableSet_Icc
  · have hempty : {t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hq ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [hempty]
    exact MeasurableSet.empty

lemma measurableSet_typeIMinorArcs (U Q : ℕ) :
    MeasurableSet (typeIMinorArcs U Q) :=
  (measurableSet_typeIMajorArcs U Q).compl

/-- Every major-arc point has the `a/q + β` form used by the Type-I estimates. -/
lemma exists_majorArc_representation (U Q : ℕ) {t : ℝ}
    (ht : t ∈ typeIMajorArcs U Q) :
    ∃ q a : ℕ, ∃ β : ℝ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      t = (a:ℝ)/(q:ℝ) + β ∧
      |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)) := by
  obtain ⟨q, a, hq1, hqQ, ha, hcop, hβ⟩ := ht
  refine ⟨q, a, t - (a:ℝ)/(q:ℝ), hq1, hqQ, ha, hcop, by ring, ?_⟩
  exact hβ

end PEqualNP.Outside.Vaughan
