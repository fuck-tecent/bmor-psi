import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_many :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (A : Finset ℕ), A⊆S n → (∀ p∈A,Nat.Prime p) → (S n).card+1<2*A.card → ∃ p∈A, ∃ q∈A, p≠q ∧ p+q=n := by
  intro S n A hA _ hsize
  let f := fun k : ℕ => n - k
  have hi : (A.image f).card = A.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy heq
    have hx' := Finset.mem_range.mp (Finset.mem_filter.mp (hA hx)).1
    have hy' := Finset.mem_range.mp (Finset.mem_filter.mp (hA hy)).1
    change n - x = n - y at heq
    omega
  have hu : A ∪ A.image f ⊆ S n := by
    apply Finset.union_subset hA
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hj', hlo, hhi⟩ := Finset.mem_filter.mp (hA hj)
    have hjn := Finset.mem_range.mp hj'
    apply Finset.mem_filter.mpr
    change n - j ∈ Finset.range (n+1) ∧ _
    exact ⟨Finset.mem_range.mpr (by omega), by dsimp [f]; constructor <;> omega⟩
  have h := Finset.card_union_add_card_inter A (A.image f)
  have hh := Finset.card_le_card hu
  have hlarge : 1 < (A ∩ A.image f).card := by omega
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp hlarge
  have witness : ∀ k ∈ A ∩ A.image f, 2*k ≠ n → ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ p+q=n := by
    intro k hk hoff
    obtain ⟨hkA, hkIm⟩ := Finset.mem_inter.mp hk
    obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hkIm
    have hjn := Finset.mem_range.mp (Finset.mem_filter.mp (hA hjA)).1
    refine ⟨f j, hkA, j, hjA, ?_, ?_⟩ <;> dsimp [f] at * <;> omega
  by_cases hpdiag : 2*p=n
  · exact witness r hr (by omega)
  · exact witness p hp hpdiag
