import Mathlib

theorem PEqualNP.Outside.L_log_rank_design_second_moment :
    ∀ (n d l : ℕ) (Y : Finset (Finset (Fin n))) (A : Finset (Fin n)),
      (∀ i : Fin n, (Y.filter (fun B => i ∈ B)).card = d) →
      (∀ i j : Fin n, i ≠ j → (Y.filter (fun B => i ∈ B ∧ j ∈ B)).card = l) →
      Finset.sum Y (fun B => (A ∩ B).card ^ 2) = d*A.card + l*A.card*(A.card-1) := by
  intro n d l Y A hd hl
  have hcard : ∀ B : Finset (Fin n),
      (A ∩ B).card = ∑ i ∈ A, (if i ∈ B then 1 else 0) := by
    intro B
    rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsq : ∀ B : Finset (Fin n),
      (A ∩ B).card ^ 2 = ∑ i ∈ A, ∑ j ∈ A, (if i ∈ B ∧ j ∈ B then 1 else 0) := by
    intro B
    rw [hcard B, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : i ∈ B <;> by_cases h2 : j ∈ B <;> simp [h1, h2]
  have hinner : ∀ i j : Fin n,
      (∑ B ∈ Y, (if i ∈ B ∧ j ∈ B then 1 else 0)) = (if i = j then d else l) := by
    intro i j
    rw [← Finset.card_filter]
    by_cases hij : i = j
    · subst hij
      have hf : (Y.filter (fun B => i ∈ B ∧ i ∈ B)) = (Y.filter (fun B => i ∈ B)) := by
        congr 1
        ext B
        simp
      rw [hf, hd i]
      simp
    · have hif : (if i = j then d else l) = l := by simp [hij]
      rw [hif]
      exact hl i j hij
  have hkey : (∑ i ∈ A, ∑ j ∈ A, (if i = j then d else l)) = d * A.card + l * A.card * (A.card - 1) := by
    have hrow : ∀ i ∈ A, (∑ j ∈ A, (if i = j then d else l)) = d + l * (A.card - 1) := by
      intro i hi
      have hsplit : (∑ j ∈ A, (if i = j then d else l))
          = d + ∑ j ∈ A.erase i, (if i = j then d else l) := by
        have h := Finset.sum_erase_add A (fun j => if i = j then d else l) hi
        simp at h
        omega
      rw [hsplit]
      have hoff : (∑ j ∈ A.erase i, (if i = j then d else l)) = ∑ j ∈ A.erase i, l := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_erase] at hj
        have hne' : ¬ (i = j) := fun h => hj.1 h.symm
        have hne : (if i = j then d else l) = l := by simp [hne']
        rw [hne]
      rw [hoff, Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
      simp only [Nat.cast_id]
      rw [Nat.mul_comm (A.card - 1) l]
    rw [Finset.sum_congr rfl hrow]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [Nat.cast_id]
    rw [Nat.mul_comm A.card d, Nat.mul_left_comm A.card l (A.card - 1),
      Nat.mul_assoc l A.card (A.card - 1)]
  calc Finset.sum Y (fun B => (A ∩ B).card ^ 2)
      = ∑ B ∈ Y, ∑ i ∈ A, ∑ j ∈ A, (if i ∈ B ∧ j ∈ B then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro B _
          exact hsq B
    _ = ∑ i ∈ A, ∑ B ∈ Y, ∑ j ∈ A, (if i ∈ B ∧ j ∈ B then 1 else 0) := Finset.sum_comm
    _ = ∑ i ∈ A, ∑ j ∈ A, ∑ B ∈ Y, (if i ∈ B ∧ j ∈ B then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ i ∈ A, ∑ j ∈ A, (if i = j then d else l) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hinner i j
    _ = d * A.card + l * A.card * (A.card - 1) := hkey
