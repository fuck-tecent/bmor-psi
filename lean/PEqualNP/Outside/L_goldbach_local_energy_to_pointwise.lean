import Mathlib

theorem PEqualNP.Outside.L_goldbach_local_energy_to_pointwise :
    ∀ (I W : Finset ℕ) (n : ℕ) (e : ℕ → ℝ) (B : ℝ),
      W ⊆ I →
      0 < B →
      (∀ m ∈ W, |e n - e m| ≤ B / 2) →
      Finset.sum I (fun m => (e m) ^ 2) < (W.card : ℝ) * (B / 2) ^ 2 →
      |e n| < B := by
  intro I W n e B hWI hB hclose hsum
  by_contra hnot
  have hge : B ≤ |e n| := le_of_not_gt hnot
  have hhalf_nonneg : 0 ≤ B / 2 := by positivity
  have hmem : ∀ m ∈ W, (B / 2) ^ 2 ≤ (e m) ^ 2 := by
    intro m hm
    have hclose' := hclose m hm
    have htri : |e n| - |e m| ≤ |e n - e m| := abs_sub_abs_le_abs_sub _ _
    have hhalf : B / 2 ≤ |e m| := by nlinarith
    have hs : (B / 2) ^ 2 ≤ |e m| ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hhalf_nonneg] using hhalf)
    simpa [sq_abs] using hs
  have hcard : (W.card : ℝ) * (B / 2) ^ 2 ≤ Finset.sum W (fun m => (e m) ^ 2) := by
    calc
      (W.card : ℝ) * (B / 2) ^ 2 = ∑ _m ∈ W, (B / 2) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ W, (e m) ^ 2 := Finset.sum_le_sum hmem
  have hsub : Finset.sum W (fun m => (e m) ^ 2) ≤
      Finset.sum I (fun m => (e m) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hWI (by
      intro m hm hnot
      exact sq_nonneg (e m))
  linarith
