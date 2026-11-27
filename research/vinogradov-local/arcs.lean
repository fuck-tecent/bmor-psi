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

lemma exists_farey_approx (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ a q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - (a:ℝ)/(q:ℝ)| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
  classical
  obtain ⟨j, k, hkpos, hkQ, hdist⟩ := Real.exists_int_int_abs_mul_sub_le α hQ
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have hhalf : 1 / ((Q:ℝ) + 1) ≤ 1 / 2 := by
    have h2 : (2:ℝ) ≤ (Q:ℝ) + 1 := by
      have : (2:ℕ) ≤ Q + 1 := by omega
      exact_mod_cast this
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
  have hdist_half : |(k:ℝ) * α - (j:ℝ)| ≤ 1 / 2 := hdist.trans hhalf
  have hkα0 : 0 ≤ (k:ℝ) * α := mul_nonneg hkR.le hα0
  have hkα1 : (k:ℝ) * α ≤ (k:ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hα1 hkR.le
  have hj0 : 0 ≤ j := by
    by_contra h
    have hjle : j ≤ -1 := by omega
    have hjR : (j:ℝ) ≤ -1 := by exact_mod_cast hjle
    have hle : (k:ℝ) * α - (j:ℝ) ≤ |(k:ℝ) * α - (j:ℝ)| := le_abs_self _
    linarith
  have hjk : j ≤ k := by
    by_contra h
    have hkle : k + 1 ≤ j := by omega
    have hkRle : (k:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast hkle
    have hneg : -((k:ℝ) * α - (j:ℝ)) ≤ |(k:ℝ) * α - (j:ℝ)| := neg_le_abs _
    linarith
  let a0 : ℕ := j.toNat
  let q0 : ℕ := k.toNat
  have hjcast : (a0 : ℤ) = j := by
    dsimp only [a0]
    exact Int.toNat_of_nonneg hj0
  have hkcast : (q0 : ℤ) = k := by
    dsimp only [q0]
    exact Int.toNat_of_nonneg hkpos.le
  have hq0pos : 0 < q0 := by
    have h : (0:ℤ) < (q0 : ℤ) := by rw [hkcast]; exact hkpos
    exact_mod_cast h
  have hq0Q : q0 ≤ Q := by
    have h : (q0 : ℤ) ≤ (Q : ℤ) := by rw [hkcast]; exact hkQ
    exact_mod_cast h
  have ha0q0 : a0 ≤ q0 := by
    have h : (a0 : ℤ) ≤ (q0 : ℤ) := by rw [hjcast, hkcast]; exact hjk
    exact_mod_cast h
  have hmul : |(k:ℝ) * α - (j:ℝ)| = (k:ℝ) * |α - (j:ℝ)/(k:ℝ)| := by
    have harg : (k:ℝ) * α - (j:ℝ) = (k:ℝ) * (α - (j:ℝ)/(k:ℝ)) := by
      field_simp [hkR.ne']
    rw [harg, abs_mul, abs_of_pos hkR]
  have hdist0 : |α - (j:ℝ)/(k:ℝ)| ≤ 1 / ((k:ℝ) * ((Q:ℝ) + 1)) := by
    rw [hmul] at hdist
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ) * ((Q:ℝ) + 1))]
    calc
      |α - (j:ℝ)/(k:ℝ)| * ((k:ℝ) * ((Q:ℝ) + 1))
          = ((k:ℝ) * |α - (j:ℝ)/(k:ℝ)|) * ((Q:ℝ) + 1) := by ring
      _ ≤ (1 / ((Q:ℝ) + 1)) * ((Q:ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_right hdist (by positivity)
      _ = 1 := by field_simp
  let g : ℕ := Nat.gcd a0 q0
  have hgpos : 0 < g := by
    dsimp only [g]
    exact Nat.gcd_pos_of_pos_right a0 hq0pos
  let a : ℕ := a0 / g
  let q : ℕ := q0 / g
  have hqpos : 0 < q := by
    dsimp only [q]
    exact Nat.div_pos (Nat.gcd_le_right a0 hq0pos) hgpos
  have hqQ : q ≤ Q := by
    dsimp only [q]
    exact le_trans (Nat.div_le_self q0 g) hq0Q
  have haq : a ≤ q := by
    dsimp only [a, q]
    exact Nat.div_le_div_right ha0q0
  have hcop : Nat.Coprime a q := by
    dsimp only [a, q, g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have ha_eq : a * g = a0 := by
    dsimp only [a]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left a0 q0)
  have hq_eq : q * g = q0 := by
    dsimp only [q]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right a0 q0)
  have heq : (a0:ℝ)/(q0:ℝ) = (a:ℝ)/(q:ℝ) := by
    have haR : (a0:ℝ) = (a:ℝ) * (g:ℝ) := by
      rw [← ha_eq]; push_cast; ring
    have hqR : (q0:ℝ) = (q:ℝ) * (g:ℝ) := by
      rw [← hq_eq]; push_cast; ring
    rw [haR, hqR]
    field_simp [show (g:ℝ) ≠ 0 by exact_mod_cast hgpos.ne']
  have hjR : (a0:ℝ) = (j:ℝ) := by exact_mod_cast hjcast
  have hkR' : (q0:ℝ) = (k:ℝ) := by exact_mod_cast hkcast
  have hqle : (q:ℝ) ≤ (q0:ℝ) := by
    have : q ≤ q0 := by dsimp only [q]; exact Nat.div_le_self q0 g
    exact_mod_cast this
  refine ⟨a, q, hqpos, hqQ, haq, hcop, ?_⟩
  calc
    |α - (a:ℝ)/(q:ℝ)| = |α - (a0:ℝ)/(q0:ℝ)| := by rw [heq]
    _ = |α - (j:ℝ)/(k:ℝ)| := by rw [hjR, hkR']
    _ ≤ 1 / ((k:ℝ) * ((Q:ℝ) + 1)) := hdist0
    _ ≤ 1 / ((k:ℝ) * (Q:ℝ)) := by
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < (k:ℝ) * (Q:ℝ))
          nlinarith [hkR.le, hQpos.le]
    _ = 1 / ((q0:ℝ) * (Q:ℝ)) := by rw [← hkR']
    _ ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < (q:ℝ) * (Q:ℝ))
          exact mul_le_mul_of_nonneg_right hqle hQpos.le


/-- Minor-arc entry: every `α ∈ [0,1]` outside the major arcs has a Farey
approximation `a/q` with `q ≤ Q` that lies outside the major-arc radius but
inside the Dirichlet radius. -/
lemma exists_farey_approx_minor (U Q : ℕ) (hQ : 0 < Q) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmin : α ∈ typeIMinorArcs U Q) :
    ∃ a q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ)) < |α - (a:ℝ)/(q:ℝ)| ∧
      |α - (a:ℝ)/(q:ℝ)| ≤ 1 / ((q:ℝ) * (Q:ℝ)) := by
  obtain ⟨a, q, hq1, hqQ, ha, hcop, hdist⟩ :=
    exists_farey_approx α hα0 hα1 Q hQ
  refine ⟨a, q, hq1, hqQ, ha, hcop, ?_, hdist⟩
  by_contra hnot
  apply hmin
  exact ⟨q, a, hq1, hqQ, ha, hcop, le_of_not_gt hnot⟩

end PEqualNP.Outside.Vaughan
