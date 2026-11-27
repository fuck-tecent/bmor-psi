import Mathlib

theorem Conjectures.Goldbach.DynInteriorBox :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ X : ℕ, 64 ≤ X → (P X).card * ((Finset.Icc X (3*X/2)).filter Nat.Prime).card ≤ ∑ n ∈ E X, H X n := by
  intro E P H X hX
  have hs : 8 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]; omega
  have hss : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have key : ∑ n ∈ E X, H X n = ((E X ×ˢ P X).filter (fun x => x.2 ≤ x.1 ∧ Nat.Prime (x.1 - x.2))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [H]
    rw [Finset.card_filter]
  rw [key, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun x => (x.2 + x.1, x.1))
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_product, P, E] at hx ⊢
    obtain ⟨⟨⟨hp1, hp2⟩, hpp⟩, ⟨⟨hq1, hq2⟩, hqp⟩⟩ := hx
    have h4 : 4 * Nat.sqrt X ≤ X := by nlinarith
    have hpo : Odd x.1 := hpp.odd_of_ne_two (by omega)
    have hqo : Odd x.2 := hqp.odd_of_ne_two (by omega)
    have hev : Even (x.2 + x.1) := hqo.add_odd hpo
    refine ⟨⟨⟨⟨by omega, by omega⟩, hev⟩, ⟨⟨hp1, hp2⟩, hpp⟩⟩, by omega, ?_⟩
    simpa using hqp
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
