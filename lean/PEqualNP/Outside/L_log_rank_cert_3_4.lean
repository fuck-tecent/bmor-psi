import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_log_rank_cert_3_4 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 3; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 4; R.card*C.card=Nat.choose S.card 3*Nat.choose (n-S.card) 4 ∧ ∀ A∈R,∀ B∈C,Disjoint A B := by
  intro n S
  dsimp only
  constructor
  · rw [Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  · intro A hA B hB
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBS : B ⊆ (Finset.univ : Finset (Fin n)) \ S := (Finset.mem_powersetCard.mp hB).1
    exact (Finset.mem_sdiff.mp (hBS hxB)).2 (hAS hxA)

end PEqualNP.Outside
