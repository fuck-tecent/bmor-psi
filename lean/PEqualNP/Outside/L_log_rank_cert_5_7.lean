import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_5_7 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 5; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 7; R.card*C.card=Nat.choose S.card 5*Nat.choose (n-S.card) 7 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  have hcard : (Finset.univ \ S : Finset (Fin n)).card = n - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  constructor
  · rw [Finset.card_powersetCard, Finset.card_powersetCard, hcard]
  · intro A hA B hB
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxS : x ∈ S := (Finset.mem_powersetCard.mp hA).1 hxA
    have hxT : x ∈ (Finset.univ \ S : Finset (Fin n)) := (Finset.mem_powersetCard.mp hB).1 hxB
    exact (Finset.mem_sdiff.mp hxT).2 hxS
