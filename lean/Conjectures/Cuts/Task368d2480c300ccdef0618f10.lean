import Mathlib

theorem Conjectures.Cuts.Task368d2480c300ccdef0618f10 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => (∑ x2 ∈ Finset.range (x1 + (1 : ℕ)) with Nat.Prime x2 ∧ Odd x2 ∧ Nat.Prime (x1 - x2) ∧ Odd (x1 - x2), Real.log ↑x2 * Real.log ↑(x1 - x2)) / ↑x1; let x2 : ℕ → Prop := fun (x2 : ℕ) => (0 : ℕ) < {x3 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Odd x3 ∧ Nat.Prime (x2 - x3) ∧ Odd (x2 - x3)}.card; ∀ (x3 : Finset ℕ), (∑ x4 ∈ x3, x1 x4) ^ (2 : ℕ) ≤ ↑(Finset.filter x2 x3).card * ∑ x4 ∈ x3, x1 x4 ^ (2 : ℕ)) := by
  classical
  intro R represented W
  let T := W.filter represented
  have zero_off (n : ℕ) (hn : ¬represented n) : R n = 0 := by
    have empty : (Finset.range (n+1)).filter (fun p =>
        Nat.Prime p ∧ Odd p ∧ Nat.Prime (n-p) ∧ Odd (n-p)) = ∅ := by
      apply Finset.card_eq_zero.mp
      exact Nat.eq_zero_of_not_pos hn
    simp [R, empty]
  have restrict : ∑ n ∈ T, R n = ∑ n ∈ W, R n := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro n hn hout
    exact zero_off n (fun hg => hout (Finset.mem_filter.mpr ⟨hn,hg⟩))
  have restrict₂ : (∑ n ∈ T, (R n)^2) = ∑ n ∈ W, (R n)^2 := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro n hn hout
    rw [zero_off n (fun hg => hout (Finset.mem_filter.mpr ⟨hn,hg⟩))]
    norm_num
  change (∑ n ∈ W, R n)^2 ≤ (T.card:ℝ) * ∑ n ∈ W, (R n)^2
  rw [← restrict, ← restrict₂]
  exact sq_sum_le_card_mul_sum_sq
