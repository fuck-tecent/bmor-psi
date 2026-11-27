import Mathlib

private theorem mellin_edge :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x)
    let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h)
    ∀ φ : ℝ → ℝ, Continuous φ →
      (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) →
      ∀ h : ℝ, Real.log 2 ≤ |h| → R (F φ) h=0 := by
  dsimp only
  intro φ hc hφ h hh
  have hl : Set.EqOn φ (fun _ => 0) (Set.Iio (1/3 : ℝ)) := by
    intro u hu
    exact hφ u (Or.inl hu)
  have hr : Set.EqOn φ (fun _ => 0) (Set.Ioi (2/3 : ℝ)) := by
    intro u hu
    exact hφ u (Or.inr hu)
  have hlc : Set.EqOn φ (fun _ => 0) (Set.Iic (1/3 : ℝ)) := by
    simpa only [closure_Iio] using hl.closure hc continuous_const
  have hrc : Set.EqOn φ (fun _ => 0) (Set.Ici (2/3 : ℝ)) := by
    simpa only [closure_Ioi] using hr.closure hc continuous_const
  have hbounds : ∀ y : ℝ, φ (Real.exp y) ≠ 0 →
      Real.log (1/3 : ℝ) < y ∧ y < Real.log (2/3 : ℝ) := by
    intro y hy
    constructor
    · apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<1/3)).mpr
      exact lt_of_not_ge (fun he => hy (hlc he))
    · apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<2/3)).mpr
      exact lt_of_not_ge (fun he => hy (hrc he))
  have hlog : Real.log (2/3 : ℝ) = Real.log (1/3 : ℝ) + Real.log 2 := by
    have he := Real.log_mul (by norm_num : (1/3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)
    norm_num at he
    exact he
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : φ (Real.exp x) = 0
  · simp [hx]
  by_cases hxh : φ (Real.exp (x+h)) = 0
  · simp [hxh]
  have hbx := hbounds x hx
  have hbxh := hbounds (x+h) hxh
  have habs : |h| < Real.log 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact False.elim (not_lt_of_ge hh habs)


theorem PEqualNP.Outside.L_goldbach_mellin_eliminate_prime_side :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h); ∀ (φ : ℝ → ℝ) (b : ℕ → ℂ), Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → (∑' k : ℕ, (ArithmeticFunction.vonMangoldt k : ℂ)*b k*(R (F φ) (Real.log (k:ℝ)):ℂ))=0 := by
  dsimp only
  intro φ b hc hφ
  calc
    _ = ∑' _k : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : k ≤ 1
      · interval_cases k <;> simp
      · have hk₂ : (2:ℝ) ≤ (k:ℝ) := by
          exact_mod_cast (show 2 ≤ k by omega)
        have he : Real.log 2 ≤ |Real.log (k:ℝ)| :=
          (Real.log_le_log (by norm_num) hk₂).trans (le_abs_self _)
        have hz := mellin_edge φ hc hφ (Real.log (k:ℝ)) he
        dsimp only at hz
        rw [hz]
        simp
    _ = 0 := tsum_zero
