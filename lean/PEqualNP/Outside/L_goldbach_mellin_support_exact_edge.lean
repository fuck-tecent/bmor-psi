import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_support_exact_edge :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h); ∀ φ : ℝ → ℝ, Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∀ h : ℝ, Real.log 2 ≤ |h| → R (F φ) h=0 := by
  dsimp only
  intro φ hφ hs h hh
  have lowerOpen : Set.EqOn φ (fun _ => 0) (Set.Iio (1/3 : ℝ)) :=
    fun x hx => hs x (Or.inl hx)
  have upperOpen : Set.EqOn φ (fun _ => 0) (Set.Ioi (2/3 : ℝ)) :=
    fun x hx => hs x (Or.inr hx)
  have lower : Set.EqOn φ (fun _ => 0) (Set.Iic (1/3 : ℝ)) := by
    simpa only [closure_Iio] using lowerOpen.closure hφ continuous_const
  have upper : Set.EqOn φ (fun _ => 0) (Set.Ici (2/3 : ℝ)) := by
    simpa only [closure_Ioi] using upperOpen.closure hφ continuous_const
  have gap {x y : ℝ} (hx : φ (Real.exp x) ≠ 0) (hy : φ (Real.exp y) ≠ 0) :
      y - x < Real.log 2 := by
    have hx' : 1/3 < Real.exp x := lt_of_not_ge (fun hle => hx (lower hle))
    have hy' : Real.exp y < 2/3 := lt_of_not_ge (fun hle => hy (upper hle))
    apply (Real.lt_log_iff_exp_lt (by norm_num)).2
    rw [Real.exp_sub, div_lt_iff₀ (Real.exp_pos x)]
    linarith
  apply (MeasureTheory.integral_congr_ae (g := fun _ : ℝ => (0 : ℝ)) ?_).trans
  · simp
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : φ (Real.exp x) = 0
    · simp [hx]
    by_cases hy : φ (Real.exp (x+h)) = 0
    · simp [hy]
    have hf := gap hx hy
    have hb := gap hy hx
    exact ((not_lt_of_ge hh) (abs_lt.mpr ⟨by linarith, by linarith⟩)).elim
