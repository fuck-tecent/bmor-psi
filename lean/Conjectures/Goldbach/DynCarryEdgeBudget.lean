import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.DynCarryEdgeBudget :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card
    ∀ (m n : ℕ) (A B : Finset ℕ), n < m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) →
      W A B (n+m) ≤ min ((A.filter (fun a => n < a)).card) ((B.filter (fun b => n < b)).card) := by
  intro W m n A B hnm hA hB
  set T := (A ×ˢ B).filter (fun t : ℕ × ℕ => t.1 + t.2 = n+m) with hT
  have hmem : ∀ t ∈ T, t ∈ A ×ˢ B ∧ t.1 + t.2 = n+m := by
    intro t ht
    rw [hT] at ht
    exact Finset.mem_filter.mp ht
  have hsideA : T.card ≤ (A.filter (fun a => n < a)).card := by
    have hmap : ∀ t ∈ T, t.1 ∈ A.filter (fun a => n < a) := by
      intro t ht
      obtain ⟨hp, hs⟩ := hmem t ht
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      exact Finset.mem_filter.mpr ⟨h1, by have := hB t.2 h2; omega⟩
    have hinj : ∀ t ∈ T, ∀ t' ∈ T, t.1 = t'.1 → t = t' := by
      intro t ht t' ht' heq
      have h1 : t.1 + t.2 = n + m := (hmem t ht).2
      have h2 : t'.1 + t'.2 = n + m := (hmem t' ht').2
      exact Prod.ext heq (by omega)
    exact Finset.card_le_card_of_injOn (fun t : ℕ × ℕ => t.1) hmap hinj
  have hsideB : T.card ≤ (B.filter (fun b => n < b)).card := by
    have hmap : ∀ t ∈ T, t.2 ∈ B.filter (fun b => n < b) := by
      intro t ht
      obtain ⟨hp, hs⟩ := hmem t ht
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      exact Finset.mem_filter.mpr ⟨h2, by have := hA t.1 h1; omega⟩
    have hinj : ∀ t ∈ T, ∀ t' ∈ T, t.2 = t'.2 → t = t' := by
      intro t ht t' ht' heq
      have h1 : t.1 + t.2 = n + m := (hmem t ht).2
      have h2 : t'.1 + t'.2 = n + m := (hmem t' ht').2
      exact Prod.ext (by omega) heq
    exact Finset.card_le_card_of_injOn (fun t : ℕ × ℕ => t.2) hmap hinj
  have hWeq : W A B (n+m) = T.card := by rw [hT]
  rw [hWeq]
  exact le_min hsideA hsideB
