import Mathlib

open MeasureTheory

theorem Conjectures.Goldbach.PacketDoublingTilt :
    ∀ (s : ℝ) (g : ℝ → ℝ), Continuous g → Function.Periodic g 1 → (∀ t, 0 ≤ g t) →
      intervalIntegral (fun t => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) (0:ℝ) 1 MeasureTheory.volume ≤ Real.cosh s * intervalIntegral (g) (0:ℝ) 1 MeasureTheory.volume := by
  intro s g hg hper hnn
  -- the half-frequency integrand
  set h : ℝ → ℝ := fun u => Real.exp (s * Real.cos (Real.pi * u)) * g u with hh
  have hcont : Continuous h := by
    apply Continuous.mul
    · exact Real.continuous_exp.comp (continuous_const.mul (Real.continuous_cos.comp (by fun_prop)))
    · exact hg
  -- substitution t = u / 2
  have hsub : intervalIntegral (fun t => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) (0:ℝ) 1 MeasureTheory.volume
      = (1/2 : ℝ) * ∫ u in (0:ℝ)..2, h u := by
    have hfun : (fun t : ℝ => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) = fun t => h (2*t) := by
      funext t
      have harg : Real.pi * (2*t) = 2*Real.pi*t := by ring
      simp only [hh, harg]
    rw [hfun, intervalIntegral.integral_comp_mul_left h (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  -- split [0,2] and reflect the second half
  have hshift : ∫ x in (1:ℝ)..2, h x = ∫ u in (0:ℝ)..1, h (u+1) := by
    have hc := intervalIntegral.integral_comp_add_right (f := h) (d := 1) (a := (0:ℝ)) (b := 1)
    rw [show (0:ℝ) + 1 = 1 by norm_num, show (1:ℝ) + 1 = 2 by norm_num] at hc
    exact hc.symm
  have hgi : Continuous fun u : ℝ => h (u+1) := hcont.comp (continuous_id.add continuous_const)
  have hkey : ∫ u in (0:ℝ)..2, h u = ∫ u in (0:ℝ)..1, (h u + h (u+1)) := by
    rw [(intervalIntegral.integral_add_adjacent_intervals (f := h) (a := (0:ℝ)) (b := 1) (c := 2)
      (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 2)).symm]
    rw [hshift, ← intervalIntegral.integral_add (hcont.intervalIntegrable 0 1) (hgi.intervalIntegrable 0 1)]
  -- pointwise bound
  have hpoint : ∀ u : ℝ, h u + h (u+1) ≤ 2 * Real.cosh s * g u := by
    intro u
    have hcos : Real.cos (Real.pi * (u+1)) = -Real.cos (Real.pi * u) := by
      rw [show Real.pi * (u+1) = Real.pi * u + Real.pi by ring, Real.cos_add_pi]
    have hperu : g (u+1) = g u := hper u
    have hgu : 0 ≤ g u := hnn u
    have hcosh : Real.cosh (s * Real.cos (Real.pi * u)) ≤ Real.cosh s := by
      rw [Real.cosh_le_cosh]
      calc |s * Real.cos (Real.pi * u)| = |s| * |Real.cos (Real.pi * u)| := abs_mul s _
        _ ≤ |s| * 1 := by gcongr; exact Real.abs_cos_le_one _
        _ = |s| := by ring
    have hsum : Real.exp (s * Real.cos (Real.pi * u)) + Real.exp (-(s * Real.cos (Real.pi * u)))
        = 2 * Real.cosh (s * Real.cos (Real.pi * u)) := by
      rw [Real.cosh_eq]; ring
    simp only [hh, hcos, hperu]
    have hneg : s * -Real.cos (Real.pi * u) = -(s * Real.cos (Real.pi * u)) := by ring
    rw [hneg, ← add_mul, hsum]
    nlinarith [hcosh, hgu, Real.cosh_pos s]
  -- integrate the bound
  have hmono : ∫ u in (0:ℝ)..1, (h u + h (u+1)) ≤ ∫ u in (0:ℝ)..1, (2 * Real.cosh s * g u) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (hcont.add hgi).intervalIntegrable 0 1
    · exact ((continuous_const.mul hg).intervalIntegrable 0 1)
    · intro u _
      exact hpoint u
  have hright : ∫ u in (0:ℝ)..1, (2 * Real.cosh s * g u) = 2 * Real.cosh s * ∫ u in (0:ℝ)..1, g u := by
    rw [intervalIntegral.integral_const_mul]
  rw [hsub, hkey]
  have := hmono
  rw [hright] at this
  linarith [this, Real.cosh_pos s]
