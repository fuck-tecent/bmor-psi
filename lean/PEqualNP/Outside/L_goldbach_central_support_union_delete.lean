import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_union_delete :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (A D:Finset ℕ), A⊆S n → ((A∩A.image (fun k => n-k)).card)≤(((A\D)∩(A\D).image (fun k => n-k)).card)+2*D.card := by
  intro S n A D _
  let f := fun k : ℕ => n-k
  let C := (A \ D) ∩ (A \ D).image f
  have hs : A ∩ A.image f ⊆ C ∪ (D ∪ D.image f) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxA, hxIm⟩
    rcases Finset.mem_image.mp hxIm with ⟨y, hyA, rfl⟩
    by_cases hx : f y ∈ D
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    by_cases hy : y ∈ D
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f hy))
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxA, hx⟩,
        Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨hyA, hy⟩)⟩
  have hsub := Finset.card_le_card hs
  have hu := Finset.card_union_le C (D ∪ D.image f)
  have hd := Finset.card_union_le D (D.image f)
  have hi : (D.image f).card ≤ D.card := Finset.card_image_le
  change (A ∩ A.image f).card ≤ C.card + 2 * D.card
  omega
