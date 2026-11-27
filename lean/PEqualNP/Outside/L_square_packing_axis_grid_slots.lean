import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_square_packing_axis_grid_slots :
    ∀ (n k : ℕ), n ≤ k ^ 2 → ∃ centers : Fin n → ℕ × ℕ,
      Function.Injective centers ∧ ∀ i, (centers i).1 < k ∧ (centers i).2 < k := by
  intro n k hnk
  let h : n ≤ k * k := by simpa [pow_two] using hnk
  let e : Fin (k * k) ≃ Fin k × Fin k := (finProdFinEquiv (m := k) (n := k)).symm
  let centers : Fin n → ℕ × ℕ := fun i =>
    (((e (Fin.castLE h i)).1 : ℕ), ((e (Fin.castLE h i)).2 : ℕ))
  refine ⟨centers, ?_, ?_⟩
  · intro i j hij
    simp only [centers, Prod.mk.injEq] at hij
    have hpair : e (Fin.castLE h i) = e (Fin.castLE h j) := by
      apply Prod.ext
      · exact Fin.ext hij.1
      · exact Fin.ext hij.2
    have hcast : Fin.castLE h i = Fin.castLE h j := e.injective hpair
    exact Fin.ext (by simpa using congrArg Fin.val hcast)
  · intro i
    exact ⟨(e (Fin.castLE h i)).1.isLt, (e (Fin.castLE h i)).2.isLt⟩
