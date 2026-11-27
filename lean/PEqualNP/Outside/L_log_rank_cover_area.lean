import Mathlib

theorem PEqualNP.Outside.L_log_rank_cover_area :
    ∀ (m n k:ℕ) (I:Fin k→Finset (Fin m)) (J:Fin k→Finset (Fin n)), (∀ i j,∃ h,i∈I h ∧ j∈J h) → m*n≤∑ h,(I h).card*(J h).card := by
  intro m n k I J hcov
  have hcover : (Finset.univ : Finset (Fin m × Fin n)) ⊆
      (Finset.univ : Finset (Fin k)).biUnion (fun h => (I h) ×ˢ (J h)) := by
    intro p hp
    obtain ⟨i, j⟩ := p
    obtain ⟨h, hi, hj⟩ := hcov i j
    exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, Finset.mem_product.mpr ⟨hi, hj⟩⟩
  have hbound : ∀ s : Finset (Fin k),
      (s.biUnion (fun h => (I h) ×ˢ (J h))).card ≤ ∑ h ∈ s, (I h).card * (J h).card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc ((I a) ×ˢ (J a) ∪ s.biUnion (fun h => (I h) ×ˢ (J h))).card
          ≤ ((I a) ×ˢ (J a)).card + (s.biUnion (fun h => (I h) ×ˢ (J h))).card :=
            Finset.card_union_le _ _
        _ ≤ (I a).card * (J a).card + ∑ h ∈ s, (I h).card * (J h).card := by
            rw [Finset.card_product]
            exact Nat.add_le_add_left ih _
  calc m * n = (Finset.univ : Finset (Fin m × Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    _ ≤ ((Finset.univ : Finset (Fin k)).biUnion (fun h => (I h) ×ˢ (J h))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ h : Fin k, (I h).card * (J h).card := by
        have h := hbound Finset.univ
        simpa [Finset.card_product] using h
