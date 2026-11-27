import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.MovingCutoffFreezeBudget :
    ∀ (I : Finset ℕ) (K : ℕ) (b : ℕ → ℕ) (f : ℕ → ℂ) (r y : ℕ → ℝ) (G : ℕ → ℝ → ℂ), (∀ m ∈ I, b m < K) → (∀ m ∈ I, ‖f m‖ ≤ 1) → let B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j); ‖∑ m ∈ I, f m * G m (r m)‖ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ j ∈ Finset.range K, ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖ ∧ (∑ j ∈ Finset.range K, Real.sqrt ((B j).card : ℝ)) ≤ Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ) := by
  intro I K b f r y G hb hf
  let B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j)
  change ‖∑ m ∈ I, f m * G m (r m)‖ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ j ∈ Finset.range K, ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖ ∧ (∑ j ∈ Finset.range K, Real.sqrt ((B j).card : ℝ)) ≤ Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ)
  constructor
  · have hmaps : ∀ m ∈ I, b m ∈ Finset.range K := by
      intro m hm
      exact Finset.mem_range.mpr (hb m hm)
    have hsplit : (∑ m ∈ I, f m * G m (r m)) =
        ∑ j ∈ Finset.range K, ∑ m ∈ B j, f m * G m (r m) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    rw [hsplit]
    calc
      _ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (r m)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range K, (‖∑ m ∈ B j, f m * G m (y j)‖ +
          ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have heq : (∑ m ∈ B j, f m * G m (r m)) =
            (∑ m ∈ B j, f m * G m (y j)) +
            (∑ m ∈ B j, f m * (G m (r m) - G m (y j))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro m hm
          ring
        rw [heq]
        calc
          _ ≤ ‖∑ m ∈ B j, f m * G m (y j)‖ + ‖∑ m ∈ B j, f m * (G m (r m) - G m (y j))‖ := norm_add_le _ _
          _ ≤ ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ m ∈ B j, ‖f m * (G m (r m) - G m (y j))‖ := by
            gcongr
            exact norm_sum_le _ _
          _ ≤ _ := by
            gcongr with m hm
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hf m (Finset.mem_filter.mp hm).1)
      _ = _ := Finset.sum_add_distrib
  · have hcount : (∑ j ∈ Finset.range K, ((B j).card : ℝ)) = (I.card : ℝ) := by
      have h := Finset.sum_card_fiberwise_eq_card_filter I (Finset.range K) b
      have heq : I.filter (fun m => b m ∈ Finset.range K) = I := by
        apply Finset.filter_eq_self.mpr
        intro m hm
        exact Finset.mem_range.mpr (hb m hm)
      rw [heq] at h
      exact_mod_cast h
    have hc := Real.sum_sqrt_mul_sqrt_le (Finset.range K)
      (f := fun _ => (1 : ℝ)) (g := fun j => ((B j).card : ℝ))
      (by intro; norm_num) (by intro; positivity)
    simpa [hcount] using hc
