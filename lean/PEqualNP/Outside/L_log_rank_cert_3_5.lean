import Mathlib

theorem PEqualNP.Outside.L_log_rank_cert_3_5 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 3; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 5; R.card*C.card=Nat.choose S.card 3*Nat.choose (n-S.card) 5 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  constructor
  · simp only [Finset.card_powersetCard, Finset.card_univ_sdiff, Fintype.card_fin]
  · intro A hA B hB
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    have hiS : i ∈ S := (Finset.mem_powersetCard.mp hA).1 hiA
    have hiC : i ∈ (Finset.univ : Finset (Fin n)) \ S :=
      (Finset.mem_powersetCard.mp hB).1 hiB
    exact (Finset.mem_sdiff.mp hiC).2 hiS
