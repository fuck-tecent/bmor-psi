import Mathlib

theorem Conjectures.Goldbach.AntispikeOptimalWeight :
∀ (s : Finset ℕ) (c : ℕ → ℝ) (B : ℝ), 0 ≤ B → (∃ w : ℕ → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i ∈ s, (w i)^2) ≤ B^2 ∧ (∑ i ∈ s, w i*c i) = -(B*Real.sqrt (∑ i ∈ s, (max 0 (-c i))^2))) ∧ (∀ v : ℕ → ℝ, (∀ i, 0 ≤ v i) → (∑ i ∈ s, (v i)^2) ≤ B^2 → -(B*Real.sqrt (∑ i ∈ s, (max 0 (-c i))^2)) ≤ ∑ i ∈ s, v i*c i) := by
  intro s c B hB
  let d (i : ℕ) := max 0 (-c i)
  let R := Real.sqrt (∑ i ∈ s,(d i)^2)
  have hd (i) : 0 ≤ d i := le_max_left .. 
  have hr : 0 ≤ R := Real.sqrt_nonneg _
  have hr2 : R^2 = ∑ i ∈ s,(d i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hp (i) : d i*c i = -(d i)^2 := by
    by_cases h : 0 ≤ -c i
    · simp only [d,max_eq_right h]; ring
    · simp [d,max_eq_left (le_of_not_ge h)]
  constructor
  · by_cases h : R = 0
    · refine ⟨fun _ => 0,fun _ => le_rfl,?_,?_⟩
      · simpa using sq_nonneg B
      · change _ = -(B*R); simp [h]
    refine ⟨fun i => (B/R)*d i,fun i => mul_nonneg (div_nonneg hB hr) (hd i),?_,?_⟩
    · simp_rw [mul_pow,← Finset.mul_sum,← hr2]
      apply le_of_eq; field_simp
    · change _ = -(B*R)
      simp_rw [mul_assoc,hp,← Finset.mul_sum,Finset.sum_neg_distrib,← hr2]
      field_simp
  · intro v hv hnorm
    have hpair : (∑ i ∈ s,v i*d i)^2 ≤ (B*R)^2 := calc
      _ ≤ (∑ i ∈ s,(v i)^2)*(∑ i ∈ s,(d i)^2) := Finset.sum_mul_sq_le_sq_mul_sq s v d
      _ ≤ B^2*R^2 := by rw [← hr2]; gcongr
      _ = _ := by ring
    have hle : (∑ i ∈ s,v i*d i) ≤ B*R :=
      (sq_le_sq₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (hd i)) (mul_nonneg hB hr)).mp hpair
    have hsum := Finset.sum_le_sum (s:=s) fun i _ => mul_le_mul_of_nonneg_left (le_max_right 0 (-c i)) (hv i)
    change -(B*R) ≤ _
    simp only [mul_neg,Finset.sum_neg_distrib] at hsum
    change -(∑ i ∈ s, v i*c i) ≤ ∑ i ∈ s,v i*d i at hsum
    linarith only [hle,hsum]
