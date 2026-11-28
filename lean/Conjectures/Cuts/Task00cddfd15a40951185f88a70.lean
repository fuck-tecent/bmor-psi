import Mathlib

theorem Conjectures.Cuts.Task00cddfd15a40951185f88a70 : (∀ (x1 : Finset (ℕ × ℕ)), ∃ x2 ⊆ x1, {x3 ∈ (x2 ×ˢ x2) ×ˢ x2 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} = ∅ ∧ x1.card ≤ x2.card + {x3 ∈ (x1 ×ˢ x1) ×ˢ x1 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card) := by
  intro x1
  induction x1 using Finset.strongInduction with
  | _ T ih =>
  by_cases hne : {x3 ∈ (T ×ˢ T) ×ˢ T | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have haT : a ∈ (T ×ˢ T) ×ˢ T := (Finset.mem_filter.mp ha).1
    have hp1 : a.1.1 ∈ T := (Finset.mem_product.mp (Finset.mem_product.mp haT).1).1
    obtain ⟨S, hST', hSfree, hbound⟩ := ih (T.erase a.1.1) (Finset.erase_ssubset hp1)
    refine ⟨S, hST'.trans (Finset.erase_subset _ _), hSfree, ?_⟩
    have hsub : {x3 ∈ ((T.erase a.1.1) ×ˢ (T.erase a.1.1)) ×ˢ (T.erase a.1.1) | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} ⊆ {x3 ∈ (T ×ˢ T) ×ˢ T | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} := by
      intro y hy
      obtain ⟨hyP, hyC⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨?_, hyC⟩
      obtain ⟨hy12, hy3⟩ := Finset.mem_product.mp hyP
      obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy12
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.erase_subset _ _ hy1, Finset.erase_subset _ _ hy2⟩,
        Finset.erase_subset _ _ hy3⟩
    have hnot : a ∉ {x3 ∈ ((T.erase a.1.1) ×ˢ (T.erase a.1.1)) ×ˢ (T.erase a.1.1) | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} := by
      intro h
      have hmem : a.1.1 ∈ T.erase a.1.1 :=
        (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1).1
      exact Finset.notMem_erase _ _ hmem
    have hclt : {x3 ∈ ((T.erase a.1.1) ×ˢ (T.erase a.1.1)) ×ˢ (T.erase a.1.1) | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card <
        {x3 ∈ (T ×ˢ T) ×ˢ T | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card :=
      Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨a, ha, hnot⟩)
    have herase : (T.erase a.1.1).card = T.card - 1 := Finset.card_erase_of_mem hp1
    have hpos : 0 < T.card := Finset.card_pos.mpr ⟨a.1.1, hp1⟩
    have hT1 : T.card ≤ (T.erase a.1.1).card + 1 := by omega
    calc T.card ≤ (T.erase a.1.1).card + 1 := hT1
      _ ≤ S.card + {x3 ∈ ((T.erase a.1.1) ×ˢ (T.erase a.1.1)) ×ˢ (T.erase a.1.1) | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card + 1 := by omega
      _ ≤ S.card + {x3 ∈ (T ×ˢ T) ×ˢ T | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card := by omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨T, Finset.Subset.refl T, hne, Nat.le_add_right _ _⟩
