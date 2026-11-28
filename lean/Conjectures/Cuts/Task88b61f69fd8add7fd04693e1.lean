import Mathlib

theorem Conjectures.Cuts.Task88b61f69fd8add7fd04693e1 : (∃ (x1 : ℕ), ∀ x2 ≥ x1, ∑ x4 ∈ Finset.range x2 with ¬Nat.Prime x4, ArithmeticFunction.vonMangoldt x4 ≤ √↑x2 * √√↑x2 / (2 : ℝ)) := by
  have hlog : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (n : ℝ)‖ ≤ (1 / 4 : ℝ) * ‖(n : ℝ) ^ (1 / 4 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound (by norm_num))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max 1 T, ?_⟩
  intro n hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left 1 T).trans hn
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hroot : (n : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt n) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
    norm_num
  have hl := hT n ((le_max_right _ _).trans hn)
  rw [hroot, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hl
  have heq : (∑ k ∈ Finset.range (n + 1),
      if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
      Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n),
      Finset.sum_filter]
    simp
  calc
    _ ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬k.Prime),
          ArithmeticFunction.vonMangoldt k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega),
          (Finset.mem_filter.mp hi).2⟩
      · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi n - Chebyshev.theta n := by simpa [Finset.sum_filter] using heq
    _ ≤ 2 * Real.sqrt n * Real.log n := (le_abs_self _).trans
      (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log h1)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg (n : ℝ))]
