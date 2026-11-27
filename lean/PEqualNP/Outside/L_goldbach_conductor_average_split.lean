import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_conductor_average_split :
    ∀ (n m : ℕ) (d : Fin m → ℕ) (u : Fin m → ℝ), (2/(Nat.totient n : ℝ))*(∑ j, u j) = (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => n^3 < (d j)^4), u j) + (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => (d j)^4 ≤ n^3), u j) := by
  intro n m d u
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin m)) (fun j => n^3 < (d j)^4) u
  simp only [not_lt] at h
  rw [← mul_add, h]
