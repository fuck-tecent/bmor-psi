import Mathlib

theorem PEqualNP.Outside.L_twin_primes_ordered_indices :
    ∀ m : ℕ, ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2)).card = m*(m-1) := by
  intro m
  have h : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2))
      = (Finset.univ : Finset (Fin m)).offDiag := by
    ext z
    simp [Finset.mem_offDiag]
  rw [h, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  exact (Nat.mul_sub_one m m).symm
