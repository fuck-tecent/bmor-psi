import Mathlib

theorem Conjectures.JoshiAbc.AdelicErrorSum :
    ∀ (n : ℕ) (w q r h : Fin n → ℝ), (∀ i, 0 ≤ w i ∧ -q i-h i ≤ r i) → -(∑ i, w i*q i)-(∑ i, w i*h i) ≤ ∑ i, w i*r i := by
  intro n w q r h hw
  have step : ∀ i, w i * (-q i - h i) ≤ w i * r i := by
    intro i
    exact mul_le_mul_of_nonneg_left (hw i).2 (hw i).1
  have sumstep : ∑ i, w i * (-q i - h i) ≤ ∑ i, w i * r i :=
    Finset.sum_le_sum (fun i _ => step i)
  simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at sumstep
  linarith [sumstep]
