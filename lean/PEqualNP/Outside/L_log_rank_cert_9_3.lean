import Mathlib

namespace PEqualNP.Outside

/-- Fix a coordinate block `S` of the ground set `Fin n`. The nine-element rows drawn from `S`
and the three-element columns drawn from its complement form a monochromatic rectangle, and its
area is exactly the product of the two binomial coefficients: `#S` choose nine times
`n - #S` choose three. Distinctness of the two blocks makes every such row disjoint from every
such column, so no row meets a column. -/
theorem L_log_rank_cert_9_3 :
    ∀ (n : ℕ) (S : Finset (Fin n)),
      let R := S.powersetCard 9
      let C := ((Finset.univ : Finset (Fin n)) \ S).powersetCard 3
      R.card * C.card = Nat.choose S.card 9 * Nat.choose (n - S.card) 3 ∧
        ∀ A ∈ R, ∀ B ∈ C, Disjoint A B := by
  intro n S
  show (S.powersetCard 9).card *
        (((Finset.univ : Finset (Fin n)) \ S).powersetCard 3).card =
      Nat.choose S.card 9 * Nat.choose (n - S.card) 3 ∧
    ∀ A ∈ S.powersetCard 9,
      ∀ B ∈ ((Finset.univ : Finset (Fin n)) \ S).powersetCard 3, Disjoint A B
  constructor
  · rw [Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ_sdiff,
      Fintype.card_fin]
  · intro A hA B hB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBS : B ⊆ (Finset.univ : Finset (Fin n)) \ S := (Finset.mem_powersetCard.mp hB).1
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hBS hx')).2 (hAS hx)

end PEqualNP.Outside
