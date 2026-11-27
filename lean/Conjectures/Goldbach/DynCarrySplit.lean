import Mathlib

theorem Conjectures.Goldbach.DynCarrySplit :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card; ∀ (m n : ℕ) (A B : Finset ℕ), n < m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) → ((A ×ˢ B).filter (fun t => (t.1+t.2)%m=n)).card = W A B n + W A B (n+m) := by
  intro W m n A B hn hA hB
  simp only [W]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    constructor
    · rintro ⟨h, h2⟩
      refine Or.elim (Nat.lt_or_ge (a+b) m) (fun h3 => ?_) (fun h3 => ?_)
      · left
        exact ⟨h, by rw [Nat.mod_eq_of_lt h3] at h2; exact h2⟩
      · right
        have := hA a h.1
        have := hB b h.2
        refine ⟨h, ?_⟩
        have e : a + b = (a+b-m) + m := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h2
        omega
    · rintro (⟨h, h2⟩ | ⟨h, h2⟩)
      · exact ⟨h, by rw [h2]; exact Nat.mod_eq_of_lt hn⟩
      · refine ⟨h, ?_⟩
        rw [h2, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt hn
  · rw [Finset.disjoint_filter]
    intro t _ h1 h2
    omega
