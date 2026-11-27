import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_two_tail_budget :
    ∀ {ι : Type} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ), t ⊆ s → (∀ i, 0 ≤ w i) → (∑ ij ∈ (s.product s).filter (fun ij => ij.1 ∈ t ∨ ij.2 ∈ t), w ij.1*w ij.2) ≤ 2*(∑ i ∈ s, w i)*(∑ i ∈ t, w i) := by
  intro ι _ s t w hsub hw
  let f (ij : ι × ι) := w ij.1 * w ij.2
  have rect₁ : (∑ ij ∈ s.product s, if ij.1 ∈ t then f ij else 0) =
      (∑ i ∈ t, w i)*(∑ j ∈ s, w j) := by
    have aset : (s.product s).filter (fun ij => ij.1 ∈ t) = t.product s := by
      ext ⟨i,j⟩
      simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
      constructor
      · rintro ⟨⟨_,hs⟩,ht⟩
        exact ⟨ht,hs⟩
      · rintro ⟨ht,hs⟩
        exact ⟨⟨hsub ht,hs⟩,ht⟩
    rw [← Finset.sum_filter,aset,Finset.product_eq_sprod,Finset.sum_product,Finset.sum_mul]
    simp only [f,Finset.mul_sum]
  have rect₂ : (∑ ij ∈ s.product s, if ij.2 ∈ t then f ij else 0) =
      (∑ i ∈ s, w i)*(∑ j ∈ t, w j) := by
    have bset : (s.product s).filter (fun ij => ij.2 ∈ t) = s.product t := by
      ext ⟨i,j⟩
      simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
      constructor
      · rintro ⟨⟨hs,_⟩,ht⟩
        exact ⟨hs,ht⟩
      · rintro ⟨hs,ht⟩
        exact ⟨⟨hs,hsub ht⟩,ht⟩
    rw [← Finset.sum_filter,bset,Finset.product_eq_sprod,Finset.sum_product,Finset.sum_mul]
    simp only [f,Finset.mul_sum]
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ ij ∈ s.product s, ((if ij.1 ∈ t then f ij else 0)+(if ij.2 ∈ t then f ij else 0)) := by
      apply Finset.sum_le_sum
      intro ij _
      have hf : 0 ≤ f ij := mul_nonneg (hw _) (hw _)
      by_cases h₁ : ij.1 ∈ t <;> by_cases h₂ : ij.2 ∈ t <;> simp [h₁,h₂,hf,f]
    _ = _ := by rw [Finset.sum_add_distrib,rect₁,rect₂]; ring
