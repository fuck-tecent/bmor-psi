import Mathlib

theorem PEqualNP.Outside.L_goldbach_integrated_loss :
    ∀ (f g : ℝ → ℝ) (a b D : ℝ), a≤b → Continuous f → Continuous g → (∀ t∈Set.Icc a b, g t-D≤f t) → intervalIntegral g a b MeasureTheory.volume-(b-a)*D ≤ intervalIntegral f a b MeasureTheory.volume := by
  intro f g a b D hab hf hg hbound
  have hD : IntervalIntegrable (fun _ : ℝ => D) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on hab
    ((hg.intervalIntegrable a b).sub hD) (hf.intervalIntegrable a b) hbound
  simpa only [intervalIntegral.integral_sub (hg.intervalIntegrable a b) hD,
    intervalIntegral.integral_const, smul_eq_mul] using hmono
