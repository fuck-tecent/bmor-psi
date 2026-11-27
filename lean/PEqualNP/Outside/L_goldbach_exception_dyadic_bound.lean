import Mathlib

/-- Each exception in the dyadic block contributes at least the square of the
model's lower bound to the total squared error. -/
theorem PEqualNP.Outside.L_goldbach_exception_dyadic_bound :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    let reps := fun n : ℕ => (Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    let D := fun X : ℕ => (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n)
    let bad := fun X : ℕ => (D X).filter (fun n => (reps n).card = 0)
    ∀ (X : ℕ) (m : ℕ → ℝ) (c V : ℝ), 0 ≤ c →
      (∀ n ∈ D X, c * (X : ℝ) ≤ m n) →
      Finset.sum (D X) (fun n => (conv w w n - m n) ^ 2) ≤ V →
      ((bad X).card : ℝ) * (c * (X : ℝ)) ^ 2 ≤ V := by
  intro w conv reps D bad X m c V hc hfloor hvariance
  have hD : bad X ⊆ D X := Finset.filter_subset _ _
  have hzero (n : ℕ) (hn : n ∈ bad X) : conv w w n = 0 := by
    have hcard : (reps n).card = 0 := (Finset.mem_filter.mp hn).2
    have hempty : reps n = ∅ := Finset.card_eq_zero.mp hcard
    change ∑ k ∈ Finset.range (n + 1), w k * w (n - k) = 0
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hp : Nat.Prime k
    · have hq : ¬ Nat.Prime (n - k) := by
        intro hq
        have hmem : k ∈ reps n := Finset.mem_filter.mpr ⟨hk, hp, hq⟩
        simp [hempty] at hmem
      simp [w, hq]
    · simp [w, hp]
  have hnonneg : 0 ≤ c * (X : ℝ) := mul_nonneg hc (Nat.cast_nonneg X)
  calc
    ((bad X).card : ℝ) * (c * (X : ℝ)) ^ 2 =
        ∑ _n ∈ bad X, (c * (X : ℝ)) ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ ∑ n ∈ bad X, (conv w w n - m n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [hzero n hn, zero_sub, neg_sq]
      exact pow_le_pow_left₀ hnonneg (hfloor n (hD hn)) 2
    _ ≤ ∑ n ∈ D X, (conv w w n - m n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hD (fun n _ _ => sq_nonneg _)
    _ ≤ V := hvariance
