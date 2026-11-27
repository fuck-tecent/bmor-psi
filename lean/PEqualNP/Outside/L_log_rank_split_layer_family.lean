import Mathlib

namespace PEqualNP.Outside

/-- Fix a coordinate block `S` of the ground set `Fin n` and any two layer sizes `r` and `c`.
The `r`-element rows drawn from `S` and the `c`-element columns drawn from its complement form a
monochromatic rectangle whose area is exactly `#S` choose `r` times `n - #S` choose `c`, and
distinctness of the two blocks makes every such row disjoint from every such column. The two
claims are proved separately: the count by the cardinality of a powerset layer on each side, and
disjointness by containment in complementary blocks. Specialising `r` and `c` recovers the
individual layer certificates. -/
theorem L_log_rank_split_layer_family :
    ∀ (n r c : ℕ) (S : Finset (Fin n)),
      let R := S.powersetCard r
      let C := ((Finset.univ : Finset (Fin n)) \ S).powersetCard c
      R.card * C.card = Nat.choose S.card r * Nat.choose (n - S.card) c ∧
        ∀ A ∈ R, ∀ B ∈ C, Disjoint A B := by
  intro n r c S
  show (S.powersetCard r).card *
        (((Finset.univ : Finset (Fin n)) \ S).powersetCard c).card =
      Nat.choose S.card r * Nat.choose (n - S.card) c ∧
    ∀ A ∈ S.powersetCard r,
      ∀ B ∈ ((Finset.univ : Finset (Fin n)) \ S).powersetCard c, Disjoint A B
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
