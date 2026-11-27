import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_sparse_rows :
    ∀ (n:ℕ) (r:Fin n→ℕ), (∀ i,r i≤2) → ((Finset.univ:Finset (Fin n)).filter (fun i => r i<2)).card+(∑ i,r i)≤2*n := by
  intro n r hle
  classical
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => r i < 2)).card
      + ((Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2)).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => r i < 2)
    have hc : (Finset.univ : Finset (Fin n)).card = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hsumsplit : ∑ i, r i
      = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), r i
        + ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), r i := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => r i < 2) (f := r)]
  have hcardA : ((Finset.univ : Finset (Fin n)).filter (fun i => r i < 2)).card
      = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (1:ℕ) :=
    Finset.card_eq_sum_ones _
  have hA : ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (1 + r i)
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (2:ℕ) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : r i < 2 := (Finset.mem_filter.mp hi).2
    omega
  have hB : ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), r i
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), (2:ℕ) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : ¬ r i < 2 := (Finset.mem_filter.mp hi).2
    have := hle i
    omega
  have h2sum : ∑ _i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (2:ℕ)
        + ∑ _i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), (2:ℕ) = 2 * n := by
    rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    omega
  calc ((Finset.univ : Finset (Fin n)).filter (fun i => r i < 2)).card + ∑ i, r i
      = (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (1:ℕ))
        + (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), r i
          + ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), r i) := by
        rw [hcardA, hsumsplit]
    _ = (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (1 + r i))
        + ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), r i := by
        rw [Finset.sum_add_distrib]
        ring
    _ ≤ (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => r i < 2), (2:ℕ))
        + ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ r i < 2), (2:ℕ) := add_le_add hA hB
    _ = 2 * n := h2sum
