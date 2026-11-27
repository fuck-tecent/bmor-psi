import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_mass_product :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)
    ∀ a b X, (∀ k, 0 ≤ a k) → (∀ k, 0 ≤ b k) →
      (∑ n ∈ Finset.range (X + 1), C a b n) ≤
        (∑ k ∈ Finset.range (X + 1), a k) * (∑ k ∈ Finset.range (X + 1), b k) := by
  dsimp only
  intro a b X ha hb
  have htriangle := (Finset.sum_Ico_Ico_comm (M := ℝ) 0 (X + 1)
    (fun k n => a k * b (n - k))).symm
  simp only [Nat.Ico_zero_eq_range] at htriangle
  rw [htriangle, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.sub_le _ _)) (fun j _ _ => hb j))
    (ha k)
