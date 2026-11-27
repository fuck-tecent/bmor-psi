import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_linear_taper :
    ∀ n : ℕ, 0<n → (∑ k ∈ Finset.range n,(1-(k:ℝ)/n))=((n:ℝ)+1)/2 := by
  intro n hn
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (∑ k ∈ Finset.range n, (k : ℝ)) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (Finset.sum_range_id_mul_two n)
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h
    exact h
  have hdiv : (∑ k ∈ Finset.range n, (k : ℝ) / n) =
      (∑ k ∈ Finset.range n, (k : ℝ)) / n := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, hdiv]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp [hnℝ]
  nlinarith only [hs]
