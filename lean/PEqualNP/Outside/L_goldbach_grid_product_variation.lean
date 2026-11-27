import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_grid_product_variation :
    ∀ (a b : ℕ → ℝ) (n : ℕ) (A B : ℝ), (∀ i≤n, |a i|≤A) → (∀ i≤n, |b i|≤B) → (∑ i ∈ Finset.range n, |a (i+1)*b (i+1)-a i*b i|) ≤ A*(∑ i ∈ Finset.range n, |b (i+1)-b i|)+B*(∑ i ∈ Finset.range n, |a (i+1)-a i|) := by
  intro a b n A B ha hb
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hin := Finset.mem_range.mp hi
  calc
    _ = |a (i+1)*(b (i+1)-b i) + b i*(a (i+1)-a i)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (ha _ (by omega)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hb _ (by omega)) (abs_nonneg _)))
