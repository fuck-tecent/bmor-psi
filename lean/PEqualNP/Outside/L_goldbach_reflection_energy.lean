import Mathlib

/-!
# L-goldbach-reflection-energy

The reflection energy identity: expanding the square of the reflected sum and
its antisymmetric counterpart, the cross terms survive. Termwise
`(x + y)^2 - (x - y)^2 = 4 * x * y` summed over the reflection window
`k ↦ n - k` gives the convolution normalisation.
-/

theorem PEqualNP.Outside.L_goldbach_reflection_energy :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k + b (n-k))^2) - (∑ k ∈ Finset.range (n+1), (b k - b (n-k))^2) = 4 * ∑ k ∈ Finset.range (n+1), b k * b (n-k) := by
  intro n b
  have h4 : ∀ k ∈ Finset.range (n+1), (b k + b (n-k))^2 - (b k - b (n-k))^2 = 4 * (b k * b (n-k)) := by
    intro k _
    ring
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl h4, Finset.mul_sum]
