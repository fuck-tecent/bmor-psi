import Mathlib

theorem PEqualNP.Outside.L_goldbach_offset_cost :
    ∀ X h : ℝ, 0≤h → intervalIntegral (fun t : ℝ => (1+X*t)^2) (0:ℝ) h MeasureTheory.volume=h+X*h^2+X^2*h^3/3 := by
  intro X h _
  let F : ℝ → ℝ := fun t => t + X * t ^ 2 + X ^ 2 * t ^ 3 / 3
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) h, HasDerivAt F ((1 + X * t) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun t : ℝ => X * t ^ 2) (X * (2 * t ^ (2 - 1))) t :=
      (hasDerivAt_pow 2 t).const_mul X
    have h3 : HasDerivAt (fun t : ℝ => X ^ 2 * t ^ 3 / 3) (X ^ 2 * (3 * t ^ (3 - 1)) / 3) t :=
      ((hasDerivAt_pow 3 t).const_mul (X ^ 2)).div_const 3
    convert (h1.add h2).add h3 using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (1 + X * t) ^ 2) MeasureTheory.volume 0 h :=
    ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).intervalIntegrable 0 h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [F]
  ring
