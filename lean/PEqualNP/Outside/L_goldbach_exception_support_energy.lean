import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_support_energy :
    ∀ (I : Finset ℕ) (r : ℕ → ℝ), (Finset.sum I r)^2 ≤ (((I.filter (fun n => r n ≠ 0)).card:ℕ):ℝ) * Finset.sum I (fun n => (r n)^2) := by
  intro I r
  let S := I.filter (fun n => r n ≠ 0)
  have hzero : ∀ n ∈ I, n ∉ S → r n = 0 := by
    intro n hn hnot
    simpa [S, hn] using hnot
  have hmass : S.sum r = I.sum r :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  have henergy : (∑ n ∈ S, (r n)^2) = ∑ n ∈ I, (r n)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    simp [hzero n hn hnot]
  simpa only [hmass, henergy] using (sq_sum_le_card_mul_sum_sq (s := S) (f := r))
