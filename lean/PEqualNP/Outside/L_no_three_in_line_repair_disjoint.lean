import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_repair_disjoint :
    ∀ (T:Finset (Finset (ℕ×ℕ))) (D:Finset (ℕ×ℕ)), (∀ A∈T,(A∩D).Nonempty) → (∀ A∈T,∀ B∈T,A≠B → Disjoint A B) → T.card≤D.card := by
  intro T D h1 h2
  classical
  have hwit : ∀ A ∈ T, ∃ p, p ∈ A ∧ p ∈ D := by
    intro A hA
    obtain ⟨p, hp⟩ := h1 A hA
    exact ⟨p, Finset.mem_inter.mp hp⟩
  choose f hf using hwit
  let g : Finset (ℕ×ℕ) → ℕ×ℕ := fun A => if h : A ∈ T then f A h else (0, 0)
  have hg : ∀ A ∈ T, g A ∈ D := by
    intro A hA
    simp only [g, dif_pos hA]
    exact (hf A hA).2
  have hginj : ∀ A ∈ T, ∀ B ∈ T, g A = g B → A = B := by
    intro A hA B hB heq
    simp only [g, dif_pos hA, dif_pos hB] at heq
    by_contra hne
    have hdisj := h2 A hA B hB hne
    have hA' : f A hA ∈ A := (hf A hA).1
    have hB' : f B hB ∈ B := (hf B hB).1
    rw [heq] at hA'
    exact Finset.disjoint_left.mp hdisj hA' hB'
  exact Finset.card_le_card_of_injOn g hg hginj
