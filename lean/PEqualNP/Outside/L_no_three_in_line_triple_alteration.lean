import Mathlib

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

theorem PEqualNP.Outside.L_no_three_in_line_triple_alteration :
  ∀ (n : ℕ) (T : Finset (Fin n)) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 3) → ∃ U ⊆ T, T.card ≤ U.card + (E.filter (fun e => e ⊆ T)).card ∧ ∀ e ∈ E, ¬ e ⊆ U := by
  intro n T E hE
  let F := E.filter (fun e => e ⊆ T)
  have hF : ∀ e ∈ F, e.Nonempty ∧ e ⊆ T := by
    intro e he
    have ⟨heE, heT⟩ := Finset.mem_filter.mp he
    have hcard := hE e heE
    exact ⟨Finset.card_pos.mp (by omega), heT⟩
  obtain ⟨H, hHT, hHcard, hHhit⟩ := hit_set T F hF
  refine ⟨T \ H, Finset.sdiff_subset, ?_, ?_⟩
  · have hsplit := Finset.card_sdiff_add_card_eq_card hHT
    change T.card ≤ (T \ H).card + F.card
    omega
  · intro e heE heU
    have heT : e ⊆ T := Finset.Subset.trans heU Finset.sdiff_subset
    have heF : e ∈ F := Finset.mem_filter.mpr ⟨heE, heT⟩
    obtain ⟨x, hxH, hxe⟩ := hHhit e heF
    exact (Finset.mem_sdiff.mp (heU hxe)).2 hxH
