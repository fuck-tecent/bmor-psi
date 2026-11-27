import Mathlib

theorem Conjectures.Goldbach.FrozenMinorBessel :
    ∀ (x : ℕ) (b : ℕ → ℝ) (A : Set ℝ), MeasurableSet A → let H := fun t : ℝ => ∑ k ∈ Finset.range (x+1), (b k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I); let f := A.indicator (fun t => H t ^ 2); let c := fun j : ℤ => fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f j; ∀ (F : Finset ℤ) (T : ℝ), 0 < T → (((F.filter fun j => (c j).re ≤ -T).card : ℝ) * T ^ 2) ≤ intervalIntegral (A.indicator (fun t => ‖H t‖^4)) 0 1 MeasureTheory.volume := by
  intro x b A hA H f c F T hT
  have hHc : Continuous H := by
    show Continuous (fun t : ℝ => ∑ k ∈ Finset.range (x+1), (b k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I))
    fun_prop
  have hc : Continuous (fun t => H t ^ 2) := hHc.pow 2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hmem : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine MeasureTheory.MemLp.of_bound ((hc.measurable.indicator hA).aestronglyMeasurable) C ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    exact (norm_indicator_le_norm_self _ _).trans (hC t (Set.Ioc_subset_Icc_self ht))
  have hP := hasSum_sq_fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) hmem
  have hint : (∫ t in (0:ℝ)..1, ‖f t‖ ^ 2) =
      intervalIntegral (A.indicator (fun t => ‖H t‖^4)) 0 1 MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [f, Set.indicator]
    split_ifs
    · rw [norm_pow]; ring
    · simp
  have hle : ∑ j ∈ F, ‖c j‖ ^ 2 ≤ ∑' j : ℤ, ‖c j‖ ^ 2 :=
    hP.summable.sum_le_tsum F (fun _ _ => by positivity)
  have htsum : ∑' j : ℤ, ‖c j‖ ^ 2 =
      intervalIntegral (A.indicator (fun t => ‖H t‖^4)) 0 1 MeasureTheory.volume := by
    rw [hP.tsum_eq, ← hint]; simp
  have hfil : ((F.filter fun j => (c j).re ≤ -T).card : ℝ) * T ^ 2 ≤
      ∑ j ∈ F.filter (fun j => (c j).re ≤ -T), ‖c j‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have h2 : |(c j).re| ≤ ‖c j‖ := Complex.abs_re_le_norm _
    have h3 : T ≤ ‖c j‖ := by
      have := neg_abs_le (c j).re
      linarith
    nlinarith
  calc _ ≤ ∑ j ∈ F.filter (fun j => (c j).re ≤ -T), ‖c j‖ ^ 2 := hfil
    _ ≤ ∑ j ∈ F, ‖c j‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := hle.trans htsum.le
