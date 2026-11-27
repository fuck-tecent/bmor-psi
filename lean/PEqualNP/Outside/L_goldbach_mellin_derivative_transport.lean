import Mathlib

open MeasureTheory
open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_mellin_derivative_transport :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ F : ℝ → ℝ, (∀ j : ℕ, ContDiff ℝ j F) → HasCompactSupport F → ∀ t : ℝ, W (deriv F) t = -((t:ℂ)*Complex.I)*W F t := by
  dsimp only
  intro F hF hsupp t
  set c : ℂ := (t : ℂ) * Complex.I with hc
  have hexp_eq : ∀ x : ℝ, Complex.exp (((t*x:ℝ):ℂ)*Complex.I) = Complex.exp (c * (x:ℂ)) := by
    intro x
    congr 1
    rw [hc]
    push_cast
    ring
  have hderivF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (F y : ℂ)) ((deriv F x : ℝ) : ℂ) x := by
    intro x
    have h1 : HasDerivAt F (deriv F x) x :=
      ((hF 1).differentiable_one).differentiableAt.hasDerivAt
    exact h1.ofReal_comp
  have hexp_deriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * (y:ℂ))) (c * Complex.exp (c * (x:ℂ))) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) (1:ℂ) x := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => c * (y:ℂ)) c x := by
      simpa using h0.const_mul c
    have h := hlin.cexp
    simpa [mul_comm] using h
  have hF_cont : Continuous F := (hF 0).continuous
  have hdF_cont : Continuous (deriv F) := (hF 1).continuous_deriv le_rfl
  have hdF_supp : HasCompactSupport (deriv F) := hsupp.deriv
  have key : ∀ (g : ℝ → ℝ), Continuous g → HasCompactSupport g →
      Integrable (fun x : ℝ => (g x : ℂ) * Complex.exp (c * (x:ℂ))) := by
    intro g hg hgs
    have hgC : Continuous (fun x : ℝ => (g x : ℂ)) := Complex.continuous_ofReal.comp hg
    have hgsupC : HasCompactSupport (fun x : ℝ => (g x : ℂ)) := by
      refine hgs.mono' ?_
      intro x hx
      exact subset_tsupport g (by simpa using hx)
    have hgInt : Integrable (fun x : ℝ => (g x : ℂ)) := hgC.integrable_of_hasCompactSupport hgsupC
    refine hgInt.mul_bdd (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => c * (x:ℂ))).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp]
      have hre : (c * (x:ℂ)).re = 0 := by simp [hc]
      rw [hre]
      simp
  have key2 : ∀ (g : ℝ → ℝ), Continuous g → HasCompactSupport g →
      Integrable (fun x : ℝ => (g x : ℂ) * (c * Complex.exp (c * (x:ℂ)))) := by
    intro g hg hgs
    have h := (key g hg hgs).const_mul c
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    ring
  have hIBP := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => (F x : ℂ))
    (v := fun x : ℝ => Complex.exp (c * (x:ℂ)))
    (u' := fun x : ℝ => ((deriv F x : ℝ) : ℂ))
    (v' := fun x : ℝ => c * Complex.exp (c * (x:ℂ)))
    (fun x _ => hderivF x) (fun x _ => hexp_deriv x)
    (key2 F hF_cont hsupp) (key (deriv F) hdF_cont hdF_supp) (key F hF_cont hsupp)
  have hIBP2 : c * (∫ x : ℝ, (F x : ℂ) * Complex.exp (c * (x:ℂ)))
      = - ∫ x : ℝ, ((deriv F x : ℝ) : ℂ) * Complex.exp (c * (x:ℂ)) := by
    rw [← MeasureTheory.integral_const_mul]
    calc ∫ x : ℝ, c * ((F x : ℂ) * Complex.exp (c*(x:ℂ)))
        = ∫ x : ℝ, (F x : ℂ) * (c * Complex.exp (c*(x:ℂ))) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          ring
      _ = - ∫ x : ℝ, ((deriv F x : ℝ) : ℂ) * Complex.exp (c*(x:ℂ)) := hIBP
  have hzero : (∫ x : ℝ, ((deriv F x : ℝ) : ℂ) * Complex.exp (c * (x:ℂ)))
      + c * (∫ x : ℝ, (F x : ℂ) * Complex.exp (c * (x:ℂ))) = 0 := by
    rw [hIBP2]; ring
  have hval : ∫ x : ℝ, ((deriv F x : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))
      = -(c * ∫ x : ℝ, (F x : ℂ) * Complex.exp (c * (x:ℂ))) :=
    eq_neg_of_add_eq_zero_left hzero
  simp only [hexp_eq]
  rw [hval, hc]
  ring
