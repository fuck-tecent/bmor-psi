import Mathlib

namespace PEqualNP.Outside

theorem L_log_rank_cert_8_4 :
    ∀ (n : ℕ) (S : Finset (Fin n)),
      (S.powersetCard 8).card * (((Finset.univ : Finset (Fin n)) \ S).powersetCard 4).card =
          Nat.choose S.card 8 * Nat.choose (n - S.card) 4 ∧
        ∀ A ∈ S.powersetCard 8, ∀ B ∈ ((Finset.univ : Finset (Fin n)) \ S).powersetCard 4,
          Disjoint A B := by
  intro n S
  constructor
  · simp [Finset.card_sdiff_of_subset (show S ⊆ (Finset.univ : Finset (Fin n)) by simp)]
  · intro A hA B hB
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    have hBC : B ⊆ (Finset.univ : Finset (Fin n)) \ S := (Finset.mem_powersetCard.mp hB).1
    rw [Finset.disjoint_left]
    intro a haA haB
    have haS : a ∈ S := hAS haA
    have haB' : a ∈ (Finset.univ : Finset (Fin n)) \ S := hBC haB
    exact (Finset.mem_sdiff.mp haB').2 haS

end PEqualNP.Outside
