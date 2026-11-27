import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_1_1 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 1; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 1; R.card*C.card=Nat.choose S.card 1*Nat.choose (n-S.card) 1 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · simp [Finset.card_powersetCard, Finset.card_sdiff]
  · intro A hA B hB
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 : x ∈ S := (Finset.mem_powersetCard.mp hA).1 hxA
    have h2 : x ∈ Finset.univ \ S := (Finset.mem_powersetCard.mp hB).1 hxB
    exact (Finset.mem_sdiff.mp h2).2 h1
