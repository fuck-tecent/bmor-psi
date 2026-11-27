import Mathlib

theorem Conjectures.JoshiAbc.FiveVolumeObstruction :
    ∀ (V : ℤ → ℝ), ¬ (V 5 = (1 : ℝ) / 5 ∧ V 5 = (1 : ℝ) / 25) := by
  intro V h
  rcases h with ⟨h₁, h₂⟩
  rw [h₁] at h₂
  norm_num at h₂
