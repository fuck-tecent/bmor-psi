import Mathlib

theorem Conjectures.SquarePacking.SeventeenWeightBudget :
    ∀ (n k q : ℕ) (S : Fin n → Finset (Fin k)) (w : Fin k → ℕ), (∀ i j, i ≠ j → Disjoint (S i) (S j)) → (∀ i, q ≤ ∑ j ∈ S i, w j) → n*q ≤ ∑ j, w j := by
  intro n k q S w hd hq
  have h1 : ∑ i : Fin n, q ≤ ∑ i : Fin n, ∑ j ∈ S i, w j :=
    Finset.sum_le_sum (fun i _ => hq i)
  have h2 : ∑ i : Fin n, ∑ j ∈ S i, w j = ∑ j ∈ (Finset.univ : Finset (Fin n)).biUnion S, w j := by
    rw [Finset.sum_biUnion]
    intro a _ b _ hab
    exact hd a b hab
  have h3 : ∑ j ∈ (Finset.univ : Finset (Fin n)).biUnion S, w j ≤ ∑ j, w j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simp at h1
  omega
