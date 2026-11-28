import Mathlib

theorem Conjectures.Cuts.Task6002d18ef9cebc6a57683d5e :
    ∀ (x1 : ℕ), (0 : ℝ) ≤ ↑x1 := by
  intro x1
  exact Nat.cast_nonneg x1
