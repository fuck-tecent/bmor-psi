import Mathlib

theorem PEqualNP.Outside.L_log_rank_survive_deletion :
    ∀ (n : ℕ) (A : Finset (Fin n)) (a : ℤ) (Y D : Finset (Finset (Fin n))), let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; (Y.filter (fun B => ¬ adj A B a)).card > D.card → ∃ B ∈ Y \ D, ¬ adj A B a := by
  intro n A a Y D
  dsimp only
  intro h
  by_contra hc
  push Not at hc
  have hsub : Y.filter (fun B => ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1)) ⊆ D := by
    intro B hB
    simp only [Finset.mem_filter] at hB
    obtain ⟨hBY, hBnadj⟩ := hB
    by_contra hBD
    exact hBnadj (hc B (Finset.mem_sdiff.mpr ⟨hBY, hBD⟩))
  have hle : (Y.filter (fun B => ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1))).card ≤ D.card :=
    Finset.card_le_card hsub
  omega
