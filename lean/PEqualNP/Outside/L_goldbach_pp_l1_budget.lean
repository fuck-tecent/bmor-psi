import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_l1_budget :
    ∀ (n : ℕ) (s : Finset ℕ) (b : ℕ → ℝ) (L : ℝ), 0<n → (∀ k ∈ s, b k≤L^2) → (∑ k ∈ s, b k)/(n : ℝ) ≤ (s.card : ℝ)*L^2/n := by
  intro n s b L hn hb
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply div_le_div_of_nonneg_right _ hn'
  calc
    (∑ k ∈ s, b k) ≤ ∑ _k ∈ s, L ^ 2 := Finset.sum_le_sum hb
    _ = (s.card : ℝ) * L ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
