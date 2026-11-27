import Mathlib

open MeasureTheory

theorem Conjectures.Goldbach.MaskedBesselVariance :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t);
    ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ), MeasurableSet A →
      (∑ m ∈ Finset.range M, ‖intervalIntegral (A.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤
        intervalIntegral (A.indicator (fun t => ‖S X u t‖^4)) (0 : ℝ) 1 MeasureTheory.volume := by
  intro E S X M u A hA
  let signal : ℝ → ℂ := fun t => (S X u t) ^ 2
  let masked := A.indicator signal
  let hab : (0 : ℝ) < 1 := zero_lt_one
  have hsignal : Continuous signal := by
    dsimp [signal, S, E]
    fun_prop
  have hLp : MemLp masked 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MemLp.indicator hA.nullMeasurableSet ?_
    rw [memLp_two_iff_integrable_sq_norm hsignal.aestronglyMeasurable]
    exact ((hsignal.norm.pow 2).intervalIntegrable 0 1).1
  have hcoeff (m : ℕ) :
      fourierCoeffOn hab masked (m : ℤ) =
        ∫ t in (0 : ℝ)..1, A.indicator (fun x => (S X u x) ^ 2 * E (-(m : ℝ) * x)) t := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ A
    · simp only [masked, signal, Set.indicator_of_mem ht, smul_eq_mul, fourier_coe_apply]
      rw [mul_comm]
      congr 2
      dsimp [E]
      push_cast
      ring
    · simp [masked, ht]
  have henergy (t : ℝ) : ‖masked t‖ ^ 2 = A.indicator (fun x => ‖S X u x‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · rw [Set.indicator_of_mem ht]
      simp only [masked, signal, Set.indicator_of_mem ht, norm_pow, ← pow_mul]
    · simp [masked, ht]
  let frequency : ℕ ↪ ℤ := ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hbound := sum_le_hasSum ((Finset.range M).map frequency)
    (fun i _ => sq_nonneg ‖fourierCoeffOn hab masked i‖)
    (hasSum_sq_fourierCoeffOn hab hLp)
  rw [Finset.sum_map] at hbound
  change (∑ m ∈ Finset.range M, ‖fourierCoeffOn hab masked (m : ℤ)‖ ^ 2) ≤ _ at hbound
  simpa only [hcoeff, henergy, sub_zero, inv_one, one_smul] using hbound
