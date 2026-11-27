import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_mellin_log_support :
    ∀ (φ : ℝ → ℝ) (a b : ℝ), 0<a → a<b → (∀ u, u<a ∨ b<u → φ u=0) → let F := fun x => Real.exp (x/2)*φ (Real.exp x); (∀ x, x<Real.log a ∨ Real.log b<x → F x=0) ∧ HasCompactSupport F := by
  intro φ a b ha hab hφ
  let F : ℝ → ℝ := fun x => Real.exp (x / 2) * φ (Real.exp x)
  change (∀ x, x < Real.log a ∨ Real.log b < x → F x = 0) ∧ HasCompactSupport F
  have hb : 0 < b := lt_trans ha hab
  have hzero : ∀ x, x < Real.log a ∨ Real.log b < x → F x = 0 := by
    intro x hx
    have he : Real.exp x < a ∨ b < Real.exp x := by
      rcases hx with hx | hx
      · exact Or.inl ((Real.lt_log_iff_exp_lt ha).mp hx)
      · exact Or.inr ((Real.log_lt_iff_lt_exp hb).mp hx)
    change Real.exp (x / 2) * φ (Real.exp x) = 0
    rw [hφ (Real.exp x) he, mul_zero]
  refine ⟨hzero, HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (Real.log a) (Real.log b))) ?_⟩
  intro x hx
  apply hzero
  rcases lt_or_ge x (Real.log a) with h | h
  · exact Or.inl h
  · right
    by_contra h'
    exact hx ⟨h, le_of_not_gt h'⟩
