import Mathlib

open MeasureTheory Set

theorem PEqualNP.Outside.L_goldbach_mellin_autocorr_diagonal :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x);
    let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h);
    ∀ φ : ℝ → ℝ, Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) →
      R (F φ) 0 = intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume := by
  dsimp only
  intro φ _ hsupp
  simp only [add_zero]
  let g : ℝ → ℝ := fun x => Real.exp x * (φ (Real.exp x)) ^ 2
  have hfactor (x : ℝ) :
      (Real.exp (x / 2) * φ (Real.exp x)) * (Real.exp (x / 2) * φ (Real.exp x)) = g x := by
    calc
      _ = (Real.exp (x / 2) * Real.exp (x / 2)) * (φ (Real.exp x)) ^ 2 := by ring
      _ = g x := by
        change (Real.exp (x / 2) * Real.exp (x / 2)) * (φ (Real.exp x)) ^ 2 =
          Real.exp x * (φ (Real.exp x)) ^ 2
        rw [← Real.exp_add, show x / 2 + x / 2 = x by ring]
  simp_rw [hfactor]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hg_zero (x : ℝ) (hx : x ∈ univ \ Iic (0 : ℝ)) : g x = 0 := by
    have hx_pos : 0 < x := lt_of_not_ge hx.2
    have hexp : 1 < Real.exp x := by
      simpa only [Real.exp_zero] using Real.exp_strictMono hx_pos
    have hφ : φ (Real.exp x) = 0 :=
      hsupp _ (Or.inr ((by norm_num : (2 : ℝ) / 3 < 1).trans hexp))
    simp [g, hφ]
  calc
    (∫ x : ℝ, g x) = ∫ x in Iic (0 : ℝ), g x := by
      simpa only [setIntegral_univ] using
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
          (subset_univ (Iic (0 : ℝ))) hg_zero
    _ = ∫ u in Ioc (0 : ℝ) 1, (φ u) ^ 2 := by
      simpa only [Real.image_exp_Iic, Real.exp_zero, smul_eq_mul, g] using
        (integral_image_eq_integral_deriv_smul_of_monotoneOn
          (s := Iic (0 : ℝ)) (f := Real.exp) (f' := Real.exp)
          measurableSet_Iic
          (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
          (Real.exp_strictMono.monotone.monotoneOn _)
          (fun u : ℝ => (φ u) ^ 2)).symm

