import Mathlib

namespace PEqualNP.Outside

private theorem logRankRectangle (r c : ℕ) :
    ∀ (n : ℕ) (S : Finset (Fin n)),
      let R := S.powersetCard r
      let C := ((Finset.univ : Finset (Fin n)) \ S).powersetCard c
      R.card * C.card = Nat.choose S.card r * Nat.choose (n - S.card) c ∧
        ∀ A ∈ R, ∀ B ∈ C, Disjoint A B := by
  intro n S
  constructor
  · rw [Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_fin]
  · intro A hA B hB
    exact Disjoint.mono (Finset.mem_powersetCard.mp hA).1
      (Finset.mem_powersetCard.mp hB).1 Finset.disjoint_sdiff

theorem L_log_rank_cert_5_3 :
    ∀ (n:ℕ) (S:Finset (Fin n)), let R:=S.powersetCard 5; let C:=((Finset.univ:Finset (Fin n)) \ S).powersetCard 3; R.card*C.card=Nat.choose S.card 5*Nat.choose (n-S.card) 3 ∧ ∀ A∈R,∀ B∈C,Disjoint A B :=
  logRankRectangle 5 3

end PEqualNP.Outside
