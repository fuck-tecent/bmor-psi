import Mathlib.Data.Finset.Basic

theorem PEqualNP.Outside.L_goldbach_finite_exception_cover_refinement :
    ∀ (D U V : Finset ℕ) (G : ℕ → Prop), (∀ n ∈ D, n ∉ U → G n) →
      (∀ n ∈ U, n ∉ V → G n) → ∀ n ∈ D, n ∉ V → G n := by
  intro D U V G first second n hnD hnV
  by_cases hnU : n ∈ U
  · exact second n hnU hnV
  · exact first n hnD hnU
