import Mathlib

theorem Conjectures.Goldbach.CellLpDualCertificate : ∀ (C K : ℕ) (M s t : ℕ → ℝ) (y B : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (U : ℝ), (∀ c ∈ Finset.range C, 0 ≤ M c) → (∀ c ∈ Finset.range C, (∑ k ∈ Finset.range K, y k * A k c) - s c ≤ t c) → (∀ k ∈ Finset.range K, B k ≤ y k * ∑ c ∈ Finset.range C, M c * A k c) → (∑ c ∈ Finset.range C, M c * s c ≤ U) → ∑ k ∈ Finset.range K, B k - U ≤ ∑ c ∈ Finset.range C, M c * t c := by
  intro C K M s t y B A U hM hst hB hU
  have h1 : (∑ k ∈ Finset.range K, B k) ≤ ∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c :=
    Finset.sum_le_sum fun k hk => hB k hk
  have h2 : (∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c)
      = ∑ c ∈ Finset.range C, M c * ∑ k ∈ Finset.range K, y k * A k c := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h3 : (∑ c ∈ Finset.range C, M c * ∑ k ∈ Finset.range K, y k * A k c)
      ≤ ∑ c ∈ Finset.range C, M c * (s c + t c) := by
    refine Finset.sum_le_sum fun c hc => ?_
    have h4 : (∑ k ∈ Finset.range K, y k * A k c) ≤ s c + t c := by
      have := hst c hc
      linarith
    exact mul_le_mul_of_nonneg_left h4 (hM c hc)
  have h5 : (∑ c ∈ Finset.range C, M c * (s c + t c))
      = (∑ c ∈ Finset.range C, M c * s c) + ∑ c ∈ Finset.range C, M c * t c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  linarith
