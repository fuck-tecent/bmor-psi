import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_4_8 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 4; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 8; R.card*C.card=Nat.choose S.card 4*Nat.choose (n-S.card) 8 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  · intro A hA B hB
    rw [Finset.mem_powersetCard] at hA hB
    exact Disjoint.mono hA.1 hB.1 Finset.disjoint_sdiff
