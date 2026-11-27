import Mathlib

theorem PEqualNP.Outside.L_goldbach_hardy_central_positive_tail_margin :
    ∀ {ι : Type} (s : Finset ι) (eigen w : ι → ℝ) (A B Q : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ Q → (∀ i ∈ s, 0 ≤ w i ∧ eigen i ≤ B) → (∑ i ∈ s, w i) ≤ Q → (∑ i ∈ s.filter (fun i => A < eigen i), w i) ≤ A*Q/(2*(B+1)) → (∑ i ∈ s, eigen i*w i) ≤ (3/2)*A*Q := by
  intro ι s eigen w A B Q hA hB hQ hpoint htotal htail
  classical
  have hbound : (∑ i ∈ s, eigen i * w i) ≤
      A * (∑ i ∈ s, w i) + B * (∑ i ∈ s.filter (fun i => A < eigen i), w i) := by
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hw := (hpoint i hi).1
    have hb := (hpoint i hi).2
    by_cases he : A < eigen i
    · simp only [he, ite_true]
      nlinarith
    · simp only [he, ite_false, mul_zero, add_zero]
      have : eigen i ≤ A := le_of_not_gt he
      nlinarith
  have htail_nonneg : 0 ≤ ∑ i ∈ s.filter (fun i => A < eigen i), w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hpoint i (Finset.mem_filter.mp hi).1).1
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have htail' := (le_div_iff₀ hdenom).mp htail
  have hprod : B * (∑ i ∈ s.filter (fun i => A < eigen i), w i) ≤ A * Q / 2 := by
    nlinarith [mul_nonneg hA hQ]
  nlinarith [mul_nonneg hA (sub_nonneg.mpr htotal)]
