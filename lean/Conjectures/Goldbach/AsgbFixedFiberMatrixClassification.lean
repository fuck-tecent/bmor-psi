import Mathlib

/-- New route · K01 · Classify the slopes of sum-preserving unimodular matrices on a fixed fiber.
On the fiber `a + c = 1`, `b + d = 1` the determinant of the column pair collapses to the slope
difference: `a * d - b * c = a * (1 - b) - b * (1 - a) = a - b`.  Hence a unimodular matrix
(`a * d - b * c = ±1`) forces the slope to be `±1`. -/
theorem Conjectures.Goldbach.AsgbFixedFiberMatrixClassification :
∀ a b c d : ℤ, a+c=1 → b+d=1 → (a*d-b*c=1 ∨ a*d-b*c = -1) → a-b=1 ∨ a-b = -1 := by
  intro a b c d hac hbd hdet
  have hc : c = 1 - a := by omega
  have hd : d = 1 - b := by omega
  have key : a * d - b * c = a - b := by
    rw [hc, hd]
    ring
  rw [key] at hdet
  exact hdet
