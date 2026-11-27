import Mathlib

theorem Conjectures.Goldbach.DynClosureRigidity :
    ∀ (A B : Set ℤ), (∀ x ∈ A, 0 < x) → (∀ x ∈ B, x < 0) → ∀ (P Q : Set ℤ), P.Nonempty → Q.Nonempty → (∀ F : Finset ℤ, ∃ k : ℤ, ∀ i ∈ F, (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B)) → ∃ k : ℤ, ∀ i : ℤ, (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B) := by
  classical
  intro A B positive negative P Q ⟨left, hleft⟩ ⟨right, hright⟩ localMatch
  let agreesAt (shift coord : ℤ) :=
    (coord ∈ P ↔ coord + shift ∈ A) ∧ (coord ∈ Q ↔ coord + shift ∈ B)
  change ∃ shift, ∀ coord, agreesAt shift coord
  by_contra! noShift
  choose witness fails using noShift
  let candidates := Finset.Ioo (-left) (-right)
  let window := insert left (insert right (candidates.image witness))
  obtain ⟨shift, agrees⟩ := localMatch window
  have left_pos := positive _ ((agrees left (by simp [window])).1.mp hleft)
  have right_neg := negative _ ((agrees right (by simp [window])).2.mp hright)
  have inside : shift ∈ candidates := Finset.mem_Ioo.mpr (by constructor <;> omega)
  exact fails shift (agrees _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem witness inside))))
