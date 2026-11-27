import Mathlib.Data.Finset.Prod

namespace Conjectures.Goldbach

theorem DynCarryReflection :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card; ∀ (m n : ℕ) (A B : Finset ℕ), 2 ≤ m → n+2 ≤ m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) → W A B (n+m) = W (A.image (fun a => m-1-a)) (B.image (fun b => m-1-b)) (m-2-n) := by
  dsimp only
  intro m n A B _ hn ha hb
  let r := fun a : ℕ => m-1-a
  let R := fun t : ℕ × ℕ => (r t.1,r t.2)
  have hInv {a : ℕ} (h : a < m) : r (r a) = a := by dsimp [r]; omega
  have hr {a : ℕ} (h : a < m) : r a < m := by dsimp [r]; omega
  have hA {a : ℕ} (h : a ∈ A.image r) : r a ∈ A ∧ a < m := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    exact ⟨by rw [hInv (ha u hu)]; exact hu, hr (ha u hu)⟩
  have hB {b : ℕ} (h : b ∈ B.image r) : r b ∈ B ∧ b < m := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    exact ⟨by rw [hInv (hb u hu)]; exact hu, hr (hb u hu)⟩
  refine Finset.card_nbij' R R ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht ⊢
    obtain ⟨⟨h1,h2⟩,h3⟩ := ht
    exact ⟨⟨Finset.mem_image_of_mem r h1, Finset.mem_image_of_mem r h2⟩, by
      have := ha _ h1
      have := hb _ h2
      dsimp [R,r]
      omega⟩
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht ⊢
    obtain ⟨⟨h1,h2⟩,h3⟩ := ht
    have ⟨h1',h4⟩ := hA h1
    have ⟨h2',h5⟩ := hB h2
    refine ⟨⟨h1',h2'⟩,?_⟩
    dsimp [R,r]
    omega
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht
    exact Prod.ext (hInv (ha t.1 ht.1.1)) (hInv (hb t.2 ht.1.2))
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ht
    exact Prod.ext (hInv (hA ht.1.1).2) (hInv (hB ht.1.2).2)

end Conjectures.Goldbach
