import Mathlib

open Filter Asymptotics

theorem Conjectures.Cuts.Taske844da16db62043ce30096d6 :
    ∀ c : ℝ, 0 < c → ∀ K : ℝ, ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      K * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) <
        c * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
  intro c hc K
  let δ : ℝ := c / (4 * (|K| + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hSmall : (fun y : ℝ => Real.log y ^ (3 : ℕ)) =o[atTop] (fun y : ℝ => Real.sqrt y) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) ((3 : ℕ) : ℝ) (by norm_num))
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hSmall.bound hδ)
  refine ⟨max 16 ⌈R⌉₊, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := (le_max_left _ _).trans hX
  have hXR : R ≤ (X : ℝ) :=
    (Nat.le_ceil R).trans (by exact_mod_cast ((le_max_right 16 ⌈R⌉₊).trans hX))
  have hReal : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX16
  have hXpos : 0 < (X : ℝ) := by linarith
  have hLogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hLogY : 0 ≤ Real.log (2 + (X : ℝ)) := Real.log_nonneg (by linarith)
  have hLogUp : Real.log (X : ℝ) ≤ Real.log (2 + (X : ℝ)) :=
    Real.log_le_log hXpos (by linarith)
  have hLogTwo : Real.log (2 + 2 * (X : ℝ)) ≤ 2 * Real.log (2 + (X : ℝ)) := by
    have hh := Real.log_le_log (show (0 : ℝ) < 2 + 2 * (X : ℝ) by linarith)
      (show 2 + 2 * (X : ℝ) ≤ (2 + (X : ℝ)) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hLogThree : Real.log (2 + (X : ℝ)) ^ 3 ≤ δ * Real.sqrt (2 + (X : ℝ)) := by
    have hh := hR (2 + (X : ℝ)) (by linarith)
    simpa only [Real.norm_of_nonneg (pow_nonneg hLogY _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hh
  have hRoot :
      Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 + (X : ℝ)) ≤ 2 * (X : ℝ) := calc
    _ ≤ Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 * (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hLeft :
      K * (Real.sqrt (2 * (X : ℝ)) * Real.log (2 + 2 * (X : ℝ))) ≤
        |K| * (Real.sqrt (2 * (X : ℝ)) * (2 * Real.log (2 + (X : ℝ)))) := by
    exact (mul_le_mul_of_nonneg_right (le_abs_self K)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith)))).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLogTwo (Real.sqrt_nonneg _)) (abs_nonneg K))
  have hδSmall : 4 * |K| * δ < c := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (|K| + 1))).mpr
    nlinarith
  apply (lt_div_iff₀ (sq_pos_of_pos hLogX)).mpr
  calc
    _ ≤ (|K| * (Real.sqrt (2 * (X : ℝ)) * (2 * Real.log (2 + (X : ℝ))))) *
        (Real.log (2 + (X : ℝ))) ^ 2 :=
      mul_le_mul hLeft (pow_le_pow_left₀ hLogX.le hLogUp 2) (sq_nonneg _) (by positivity)
    _ = 2 * |K| * (Real.sqrt (2 * (X : ℝ)) * (Real.log (2 + (X : ℝ))) ^ 3) := by ring
    _ ≤ 2 * |K| * (Real.sqrt (2 * (X : ℝ)) * (δ * Real.sqrt (2 + (X : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLogThree (Real.sqrt_nonneg _)) (by positivity)
    _ = (2 * |K| * δ) * (Real.sqrt (2 * (X : ℝ)) * Real.sqrt (2 + (X : ℝ))) := by ring
    _ ≤ (2 * |K| * δ) * (2 * (X : ℝ)) := mul_le_mul_of_nonneg_left hRoot (by positivity)
    _ = (4 * |K| * δ) * (X : ℝ) := by ring
    _ < _ := mul_lt_mul_of_pos_right hδSmall hXpos
