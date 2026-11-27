import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Conjectures.Goldbach

theorem DynDeletionLoss :
    ∀ (A B D E : Finset ℕ) (t : ℕ), let r := fun (B' : Finset ℕ) (n : ℕ) => (A.filter (fun p => p≤n ∧ n-p ∈ B')).card; t * (E.filter (fun n => t ≤ r B n ∧ r (B \ D) n = 0)).card ≤ A.card * (B ∩ D).card := by
  dsimp only
  intro A B D E t
  let r := fun (B' : Finset ℕ) (n : ℕ) => (A.filter (fun p => p ≤ n ∧ n-p ∈ B')).card
  let T := E.filter (fun n => t ≤ r B n ∧ r (B \ D) n=0)
  let C := (T ×ˢ A).filter (fun u => u.2 ≤ u.1 ∧ u.1-u.2 ∈ B)
  change t*T.card ≤ _
  have hC : C.card = ∑ n ∈ T, r B n := by
    simp only [C, r, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  calc
    t*T.card = ∑ _n ∈ T, t := by simp [Nat.mul_comm]
    _ ≤ ∑ n ∈ T, r B n := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Finset.mem_filter.mp hn).2.1
    _ = C.card := hC.symm
    _ ≤ A.card*(B ∩ D).card := by
      rw [← Finset.card_product]
      apply Finset.card_le_card_of_injOn (fun (u : ℕ × ℕ) => (u.2,u.1-u.2))
      · intro u hu
        simp only [Finset.mem_coe, C, Finset.mem_filter, Finset.mem_product] at hu ⊢
        obtain ⟨⟨hT,hA⟩,hp,hB⟩ := hu
        refine ⟨hA, Finset.mem_inter.mpr ⟨hB,?_⟩⟩
        by_contra hD
        have hm : u.2 ∈ A.filter (fun p => p ≤ u.1 ∧ u.1-p ∈ B \ D) :=
          Finset.mem_filter.mpr ⟨hA,hp,Finset.mem_sdiff.mpr ⟨hB,hD⟩⟩
        have hz := (Finset.mem_filter.mp hT).2.2
        have hpos : 0 < r (B \ D) u.1 := Finset.card_pos.mpr ⟨_,hm⟩
        omega
      · intro u hu v hv he
        simp only [Finset.mem_coe, C, Finset.mem_filter, Finset.mem_product] at hu hv
        have hl := congrArg Prod.fst he
        have hr := congrArg Prod.snd he
        dsimp only at hl hr
        exact Prod.ext (by have := hu.2.1; have := hv.2.1; omega) hl

end Conjectures.Goldbach
