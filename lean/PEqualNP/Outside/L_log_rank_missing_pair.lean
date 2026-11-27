import Mathlib

theorem PEqualNP.Outside.L_log_rank_missing_pair :
    ∀ (n : ℕ) (Y : Finset (Finset (Fin n))) (i j : Fin n), 4 ≤ n → i ≠ j → let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a; (∀ B ∈ Y, ¬ (i ∈ B ∧ j ∈ B)) → ¬ detects Y := by
  intro n Y i j hn hij
  dsimp only
  intro missing detects
  have pairSize : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  obtain ⟨B, hB, outside⟩ := detects {i, j} (by omega) (by omega) 0
  apply outside
  by_cases hi : i ∈ B
  · have hj : j ∉ B := fun hj => missing B hB ⟨hi, hj⟩
    right
    simp [Finset.insert_inter_of_mem hi, Finset.singleton_inter_of_notMem hj]
  · rw [Finset.insert_inter_of_notMem hi]
    by_cases hj : j ∈ B
    · right
      simp [Finset.singleton_inter_of_mem hj]
    · left
      simp [Finset.singleton_inter_of_notMem hj]
