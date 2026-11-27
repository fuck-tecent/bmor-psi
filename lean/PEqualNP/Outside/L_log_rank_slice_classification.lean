import Mathlib

theorem PEqualNP.Outside.L_log_rank_slice_classification :
    ∀ (n k : ℕ) (A : Finset (Fin n)) (a : ℤ), 2 ≤ k → k+2 ≤ n → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; (∀ B ∈ layer, adj A B a) → A.card ≤ 1 ∨ n ≤ A.card+1 := by
  intro n k A a hk hkn
  dsimp only
  intro h
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hA1, hAn1⟩ := hcon
  have hA2 : 2 ≤ A.card := by omega
  have hAn2 : A.card + 2 ≤ n := by omega
  have hsum : A.card + (Aᶜ).card = n := by
    simp
  have hkey : ∀ m : ℕ, m ≤ k → m ≤ A.card → k - m ≤ (Aᶜ).card →
      ∃ B : Finset (Fin n), B ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ (A ∩ B).card = m := by
    intro m hmk hmA hmc
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hmA
    obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq hmc
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxnot : x ∉ A := by
        have hx : x ∈ Aᶜ := hTA hxT
        simpa using hx
      exact hxnot (hSA hxS)
    refine ⟨S ∪ T, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hScard, hTcard]
      omega
    · have hinter : A ∩ (S ∪ T) = S := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA, hxS | hxT⟩
          · exact hxS
          · have hxnot : x ∉ A := by
              have hx : x ∈ Aᶜ := hTA hxT
              simpa using hx
            exact absurd hxA hxnot
        · intro hxS
          exact ⟨hSA hxS, Or.inl hxS⟩
      rw [hinter, hScard]
  have hcontra : ∀ (m1 m2 : ℕ), m1 + 2 ≤ m2 →
      (∃ B : Finset (Fin n), B ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ (A ∩ B).card = m1) →
      (∃ B : Finset (Fin n), B ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ (A ∩ B).card = m2) → False := by
    intro m1 m2 hle h1 h2
    obtain ⟨B1, hB1, hc1⟩ := h1
    obtain ⟨B2, hB2, hc2⟩ := h2
    have e1 := h B1 hB1
    have e2 := h B2 hB2
    rw [hc1] at e1
    rw [hc2] at e2
    have hcast : ((m1 : ℕ) : ℤ) + 2 ≤ ((m2 : ℕ) : ℤ) := by
      have hh : ((m1 + 2 : ℕ) : ℤ) ≤ ((m2 : ℕ) : ℤ) := by exact_mod_cast hle
      simpa using hh
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> omega
  by_cases hkc : k ≤ A.card
  · obtain ⟨B1, hB1, hc1⟩ := hkey (k - 2) (by omega) (by omega) (by omega)
    obtain ⟨B2, hB2, hc2⟩ := hkey k le_rfl hkc (by omega)
    exact hcontra (k - 2) k (by omega) ⟨B1, hB1, hc1⟩ ⟨B2, hB2, hc2⟩
  · obtain ⟨B2, hB2, hc2⟩ := hkey A.card (by omega) le_rfl (by omega)
    by_cases hkq : k ≤ (Aᶜ).card
    · obtain ⟨B1, hB1, hc1⟩ := hkey 0 (by omega) (by omega) (by omega)
      exact hcontra 0 A.card (by omega) ⟨B1, hB1, hc1⟩ ⟨B2, hB2, hc2⟩
    · obtain ⟨B1, hB1, hc1⟩ := hkey (k - (Aᶜ).card) (by omega) (by omega) (by omega)
      exact hcontra (k - (Aᶜ).card) A.card (by omega) ⟨B1, hB1, hc1⟩ ⟨B2, hB2, hc2⟩
