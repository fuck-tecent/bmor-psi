import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_diagonal_floor :
    let Adm := fun φ : ℝ → ℝ => (∀ j : ℕ, ContDiff ℝ j φ) ∧ (∀ u, 0≤φ u ∧ φ u≤1) ∧ (∀ u, φ (1-u)=φ u) ∧ (∀ u, u < 1/3 ∨ 2/3 < u → φ u=0) ∧ (∀ u, 5/12≤u → u≤7/12 → φ u=1); ∀ φ : ℝ → ℝ, Adm φ → 1/6 ≤ intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume := by
  dsimp only
  intro φ hAdm
  rcases hAdm with ⟨hsmooth, hbound, hsym, hsupp, hplateau⟩
  have hc : Continuous (fun u : ℝ => (φ u)^2) := (hsmooth 0).continuous.pow 2
  have hmiddle : (1:ℝ)/6 ≤
      intervalIntegral (fun u : ℝ => (φ u)^2) (5/12) (7/12) MeasureTheory.volume := by
    calc
      (1:ℝ)/6 = intervalIntegral (fun _ : ℝ => (1:ℝ))
          (5/12) (7/12) MeasureTheory.volume := by norm_num
      _ ≤ intervalIntegral (fun u : ℝ => (φ u)^2)
          (5/12) (7/12) MeasureTheory.volume := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
        intro u hu
        rw [hplateau u hu.1 hu.2]
        norm_num
  apply hmiddle.trans
  apply intervalIntegral.integral_mono_interval (by norm_num : (0:ℝ) ≤ 5/12)
    (by norm_num : (5/12:ℝ) ≤ 7/12) (by norm_num : (7/12:ℝ) ≤ 1)
  · exact Filter.Eventually.of_forall (fun u => sq_nonneg (φ u))
  · exact hc.intervalIntegrable 0 1
