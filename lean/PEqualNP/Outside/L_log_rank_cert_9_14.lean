import Mathlib

/-! Certificate gap `L-log-rank-cert-9-14` (log-rank desk): rows are the 9-subsets of `S`,
columns the 14-subsets of its complement. The rectangle has the stated area, and every row is
disjoint from every column because a column lies in the complement of `S`. -/

theorem PEqualNP.Outside.L_log_rank_cert_9_14 : ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 9; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 14; R.card*C.card=Nat.choose S.card 9*Nat.choose (n-S.card) 14 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ_sdiff,
      Fintype.card_fin]
  · intro A hA B hB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBS : B ⊆ Finset.univ \ S := (Finset.mem_powersetCard.mp hB).1
    exact Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_sdiff.mp (hBS hb)).2 (hAS ha)
