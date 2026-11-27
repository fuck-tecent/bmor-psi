import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_insert :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ), x∉S → (ok (insert x S) ↔ ok S ∧ ∀ a∈S, ∀ b∈S,a≠b → d a b x≠0) := by
  dsimp only
  intro S x hx
  have cyc : ∀ a b c : ℤ × ℤ,
      (c.1-b.1)*(a.2-b.2)-(c.2-b.2)*(a.1-b.1)
        = (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1) := by intro a b c; ring
  have swp : ∀ a b c : ℤ × ℤ,
      (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
        = -((c.1-a.1)*(b.2-a.2)-(c.2-a.2)*(b.1-a.1)) := by intro a b c; ring
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha b hb c hc hab hbc hac
      exact h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) c
        (Finset.mem_insert_of_mem hc) hab hbc hac
    · intro a ha b hb hab
      have hax : a ≠ x := fun h' => hx (h' ▸ ha)
      have hbx : b ≠ x := fun h' => hx (h' ▸ hb)
      exact h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) x
        (Finset.mem_insert_self x S) hab hbx hax
  · rintro ⟨hS, hcross⟩ a ha b hb c hc hab hbc hac
    by_cases hax : a = x
    · rw [hax] at hab hac ⊢
      have hbS : b ∈ S := by
        rcases Finset.mem_insert.mp hb with h | h
        · exact absurd h.symm hab
        · exact h
      have hcS : c ∈ S := by
        rcases Finset.mem_insert.mp hc with h | h
        · exact absurd h.symm hac
        · exact h
      intro h0
      exact hcross b hbS c hcS hbc (by rw [cyc x b c]; exact h0)
    · have haS : a ∈ S := by
        rcases Finset.mem_insert.mp ha with h | h
        · exact absurd h hax
        · exact h
      by_cases hbx : b = x
      · rw [hbx] at hab hbc ⊢
        have hcS : c ∈ S := by
          rcases Finset.mem_insert.mp hc with h | h
          · exact absurd h.symm hbc
          · exact h
        intro h0
        exact hcross a haS c hcS hac (by rw [swp a x c] at h0; linarith)
      · have hbS : b ∈ S := by
          rcases Finset.mem_insert.mp hb with h | h
          · exact absurd h hbx
          · exact h
        by_cases hcx : c = x
        · rw [hcx] at hac hbc ⊢
          exact hcross a haS b hbS hab
        · have hcS : c ∈ S := by
            rcases Finset.mem_insert.mp hc with h | h
            · exact absurd h hcx
            · exact h
          exact hS a haS b hbS c hcS hab hbc hac
