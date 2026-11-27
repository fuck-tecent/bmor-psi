import Mathlib

theorem PEqualNP.Outside.L_goldbach_sparse_weight_duality :
    ∀ (s t : Finset ℕ) (f v : ℕ → ℝ) (B : ℝ), 0≤B → (∀ k ∈ s, f k≠0 → k∈t) → (∀ k ∈ s, |f k|≤B) → (∀ k ∈ s, |v k|≤1) → |∑ k ∈ s, f k*v k| ≤ (t.card:ℝ)*B := by
  intro s t f v B hB hsupp hf hv
  have hsum : ∑ k ∈ s, f k * v k = ∑ k ∈ s ∩ t, f k * v k := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left : s ∩ t ⊆ s)
    intro k hks hknt
    have hfk : f k = 0 := by
      by_contra hne
      exact hknt (Finset.mem_inter.mpr ⟨hks, hsupp k hks hne⟩)
    rw [hfk, zero_mul]
  rw [hsum]
  calc
    |∑ k ∈ s ∩ t, f k * v k| ≤ ∑ k ∈ s ∩ t, |f k * v k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s ∩ t, B := by
      apply Finset.sum_le_sum
      intro k hk
      have hks : k ∈ s := (Finset.mem_inter.mp hk).1
      rw [abs_mul]
      calc
        |f k| * |v k| ≤ |f k| * 1 := mul_le_mul_of_nonneg_left (hv k hks) (abs_nonneg (f k))
        _ = |f k| := mul_one |f k|
        _ ≤ B := hf k hks
    _ = ((s ∩ t).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (t.card : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : s ∩ t ⊆ t)
