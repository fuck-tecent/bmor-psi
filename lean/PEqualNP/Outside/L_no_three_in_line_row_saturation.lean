import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_row_saturation :
    ∀ (n:ℕ) (r:Fin n→ℕ), (∀ i,r i≤2) → (∑ i,r i)=2*n → ∀ i,r i=2 := by
  intro n r hle hsum i
  by_contra hne
  have hn : 1 ≤ n := by
    have := i.isLt
    omega
  have hlt : r i < 2 := lt_of_le_of_ne (hle i) hne
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hcard : ((Finset.univ : Finset (Fin n)).erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
  have hbound : ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, r j ≤ 2 * (n - 1) := by
    have h1 : ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, r j
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (2:ℕ) :=
      Finset.sum_le_sum (fun j _ => hle j)
    have h2 : ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, (2:ℕ)
        = ((Finset.univ : Finset (Fin n)).erase i).card * 2 := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [h2, hcard] at h1
    omega
  have hsplit : (∑ j, r j)
      = r i + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, r j := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n)) r hmem, Nat.add_comm]
  rw [hsplit] at hsum
  omega
