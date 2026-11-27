import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_8_9 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 8; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 9; R.card*C.card=Nat.choose S.card 8*Nat.choose (n-S.card) 9 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · simp [Finset.card_powersetCard, Finset.card_sdiff]
  · intro A hA B hB
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hB).1 hxB)).2
      ((Finset.mem_powersetCard.mp hA).1 hxA)
