import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_7_9 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 7; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 9; R.card*C.card=Nat.choose S.card 7*Nat.choose (n-S.card) 9 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · have hcard : (Finset.univ \ S).card = n - S.card := by
      simp [Finset.card_sdiff]
    rw [Finset.card_powersetCard, Finset.card_powersetCard, hcard]
  · intro A hA B hB
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_powersetCard] at hA hB
    exact (Finset.mem_sdiff.1 (hB.1 hxB)).2 (hA.1 hxA)
