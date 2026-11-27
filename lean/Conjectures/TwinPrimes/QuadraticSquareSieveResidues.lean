import Mathlib

theorem Conjectures.TwinPrimes.QuadraticSquareSieveResidues :
    ∀ ℓ : ℕ, ℓ.Prime → ((Finset.range ℓ).filter fun a => (a = 0 ∨ a ^ 2 % ℓ = 2 % ℓ)).card = if ℓ = 2 then 1 else 1 + ((Finset.range ℓ).filter fun a => a ^ 2 % ℓ = 2 % ℓ).card := by
  intro ℓ hℓ
  split_ifs with h2
  · subst h2
    have hT : ((Finset.range 2).filter fun a => (a = 0 ∨ a ^ 2 % 2 = 2 % 2)) = ({0} : Finset ℕ) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h0 | h1⟩
        · exact h0
        · interval_cases a <;> simp_all
      · rintro rfl
        exact ⟨by norm_num, Or.inl rfl⟩
    rw [hT]
    simp
  · have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    have hT : ((Finset.range ℓ).filter fun a => (a = 0 ∨ a ^ 2 % ℓ = 2 % ℓ)) =
        insert 0 ((Finset.range ℓ).filter fun a => a ^ 2 % ℓ = 2 % ℓ) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨ha, h0 | h1⟩
        · exact Or.inl h0
        · exact Or.inr ⟨ha, h1⟩
      · rintro (rfl | ⟨ha, h1⟩)
        · exact ⟨hℓ.pos, Or.inl rfl⟩
        · exact ⟨ha, Or.inr h1⟩
    rw [hT]
    have h0not : (0 : ℕ) ∉ ((Finset.range ℓ).filter fun a => a ^ 2 % ℓ = 2 % ℓ) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _
      have hz : 0 ^ 2 % ℓ = 0 := by simp
      have hm : 2 % ℓ = 2 := Nat.mod_eq_of_lt (by omega)
      omega
    rw [Finset.card_insert_of_notMem h0not]
    omega
