import Mathlib

private lemma incidence_count (n k : ℕ) (E : Finset (Finset (Fin n)))
    (hk : 3 ≤ k) (hkn : k ≤ n) (hE : ∀ e ∈ E, e.card = 3) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card) =
      E.card * Nat.choose (n - 3) (k - 3) := by
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

private lemma hit_set {n : ℕ} (T : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ e ∈ F, e.Nonempty ∧ e ⊆ T) :
    ∃ H ⊆ T, H.card ≤ F.card ∧ ∀ e ∈ F, ∃ x ∈ H, x ∈ e := by
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, Finset.empty_subset T, by simp, by simp⟩
  | @insert e s hes ih =>
    obtain ⟨H, hHT, hHcard, hHhit⟩ := ih (fun e' he' => hF e' (Finset.mem_insert_of_mem he'))
    obtain ⟨⟨x, hxe⟩, heT⟩ := hF e (Finset.mem_insert_self e s)
    refine ⟨insert x H, Finset.insert_subset (heT hxe) hHT, ?_, ?_⟩
    · calc (insert x H).card ≤ H.card + 1 := Finset.card_insert_le x H
        _ ≤ s.card + 1 := Nat.add_le_add_right hHcard 1
        _ = (insert e s).card := (Finset.card_insert_of_notMem hes).symm
    · intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | he's
      · exact ⟨x, Finset.mem_insert_self x H, hxe⟩
      · obtain ⟨y, hyH, hye'⟩ := hHhit e' he's
        exact ⟨y, Finset.mem_insert_of_mem hyH, hye'⟩

theorem PEqualNP.Outside.L_no_three_in_line_sample_conflict_budget :
  ∀ (n k b : ℕ) (E : Finset (Finset (Fin n))), 3 ≤ k → k ≤ n → (∀ e ∈ E, e.card = 3) → E.card * Nat.choose (n - 3) (k - 3) ≤ b * Nat.choose n k → ∃ U : Finset (Fin n), k ≤ U.card + b ∧ ∀ e ∈ E, ¬ e ⊆ U := by
  intro n k b E hk hkn hE hbud
  let P := (Finset.univ : Finset (Fin n)).powersetCard k
  have hPcard : P.card = Nat.choose n k := by
    simp [P]
  have hPpos : 0 < P.card := by
    rw [hPcard]
    exact Nat.choose_pos hkn
  have hsum : (∑ T ∈ P, (E.filter (fun e => e ⊆ T)).card) ≤ b * P.card := by
    rw [incidence_count n k E hk hkn hE, hPcard]
    exact hbud
  have hex : ∃ T ∈ P, (E.filter (fun e => e ⊆ T)).card ≤ b := by
    by_contra hall
    push_neg at hall
    have hge : ∑ T ∈ P, (b + 1) ≤ ∑ T ∈ P, (E.filter (fun e => e ⊆ T)).card :=
      Finset.sum_le_sum (fun T hT => Nat.succ_le_of_lt (hall T hT))
    rw [Finset.sum_const, smul_eq_mul] at hge
    nlinarith
  obtain ⟨T, hTP, hTb⟩ := hex
  have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTP).2
  let F := E.filter (fun e => e ⊆ T)
  have hF : ∀ e ∈ F, e.Nonempty ∧ e ⊆ T := by
    intro e he
    have ⟨heE, heT⟩ := Finset.mem_filter.mp he
    have hcard := hE e heE
    exact ⟨Finset.card_pos.mp (by omega), heT⟩
  obtain ⟨H, hHT, hHcard, hHhit⟩ := hit_set T F hF
  refine ⟨T \ H, ?_, ?_⟩
  · have hsplit := Finset.card_sdiff_add_card_eq_card hHT
    have hFb : F.card ≤ b := hTb
    omega
  · intro e heE heU
    have heT : e ⊆ T := Finset.Subset.trans heU Finset.sdiff_subset
    have heF : e ∈ F := Finset.mem_filter.mpr ⟨heE, heT⟩
    obtain ⟨x, hxH, hxe⟩ := hHhit e heF
    exact (Finset.mem_sdiff.mp (heU hxe)).2 hxH
