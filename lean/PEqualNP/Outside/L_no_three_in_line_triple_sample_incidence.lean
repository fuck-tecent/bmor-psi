import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_triple_sample_incidence :
  ∀ (n k : ℕ) (E : Finset (Finset (Fin n))), 3 ≤ k → k ≤ n → (∀ e ∈ E, e.card = 3) → (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card) = E.card * Nat.choose (n - 3) (k - 3) := by
  intro n k E hk hkn hE
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hterm : ∀ e ∈ E,
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, if e ⊆ T then 1 else 0) =
        Nat.choose (n - 3) (k - 3) := by
    intro e he
    have hecard : e.card = 3 := hE e he
    rw [← Finset.card_filter]
    have hbij : ((Finset.univ \ e).powersetCard (k - 3)).card =
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => e ⊆ T)).card := by
      refine Finset.card_bij (fun S _ => e ∪ S) ?_ ?_ ?_
      · intro S hS
        rw [Finset.mem_powersetCard] at hS
        have hdisj : Disjoint e S := by
          rw [Finset.disjoint_left]
          intro x hxe hxS
          exact (Finset.mem_sdiff.mp (hS.1 hxS)).2 hxe
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_left⟩
        rw [Finset.card_union_of_disjoint hdisj, hecard, hS.2]
        omega
      · intro S₁ hS₁ S₂ hS₂ heq
        rw [Finset.mem_powersetCard] at hS₁ hS₂
        ext x
        constructor
        · intro hx
          have hxn : x ∉ e := (Finset.mem_sdiff.mp (hS₁.1 hx)).2
          have hmem : x ∈ e ∪ S₂ := heq ▸ Finset.mem_union_right e hx
          exact (Finset.mem_union.mp hmem).resolve_left hxn
        · intro hx
          have hxn : x ∉ e := (Finset.mem_sdiff.mp (hS₂.1 hx)).2
          have hmem : x ∈ e ∪ S₁ := heq.symm ▸ Finset.mem_union_right e hx
          exact (Finset.mem_union.mp hmem).resolve_left hxn
      · intro T hT
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
        refine ⟨T \ e, ?_, Finset.union_sdiff_of_subset hT.2⟩
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
        · have hsplit := Finset.card_sdiff_add_card_eq_card hT.2
          omega
    rw [← hbij, Finset.card_powersetCard]
    have hdiff : (Finset.univ \ e : Finset (Fin n)).card = n - 3 := by
      have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ e)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
      omega
    rw [hdiff]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
