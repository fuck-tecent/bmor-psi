import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_reflected_union :
    ∀ (n : ℕ) (s : Finset ℕ), ((Finset.range (n+1)).filter (fun k => k∈s ∨ n-k∈s)).card ≤ 2*s.card := by
  intro n s
  have hsub : (Finset.range (n+1)).filter (fun k => k∈s ∨ n-k∈s) ⊆ s ∪ s.image (fun k => n-k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, h | h⟩ := hk
    · exact Finset.mem_union_left _ h
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n-k, h, ?_⟩)
      omega
  calc ((Finset.range (n+1)).filter (fun k => k∈s ∨ n-k∈s)).card
      ≤ (s ∪ s.image (fun k => n-k)).card := Finset.card_le_card hsub
    _ ≤ s.card + (s.image (fun k => n-k)).card := Finset.card_union_le _ _
    _ ≤ s.card + s.card := by
        have := Finset.card_image_le (s := s) (f := fun k => n-k)
        omega
    _ = 2*s.card := by ring
