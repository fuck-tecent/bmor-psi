import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseExactObstruction :
    ∃ A : Set ℝ, Dense A ∧ (0:ℝ) ∈ closure A ∧ (0:ℝ) ∉ A := by
  refine ⟨({0}ᶜ : Set ℝ), dense_compl_singleton (0 : ℝ), ?_, ?_⟩
  · rw [closure_compl_singleton]
    simp
  · simp
