import Mathlib

open Filter Asymptotics

theorem Conjectures.Cuts.Taskfcf490daee82654cc927356b :
    (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * (√((2 : ℝ) * ↑x3) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x3)) < ↑x3 / Real.log ↑x3 ^ (2 : ℕ)) := by
  intro K B
  let ε : ℝ := 1 / (4 * (|K| + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hSmall :
      (fun x : ℝ => Real.log x ^ (3 : ℕ)) =o[atTop] (fun x : ℝ => Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) ((3 : ℕ) : ℝ) (by norm_num))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hSmall.bound hε)
  let X := max (B + 1) (max 3 ⌈R⌉₊)
  let x : ℝ := X
  have hBeyond : B < X := (Nat.lt_succ_self B).trans_le (le_max_left _ _)
  have hX3 : 3 ≤ X := (le_max_left 3 ⌈R⌉₊).trans (le_max_right _ _)
  have hx3 : (3 : ℝ) ≤ x := by
    change (3 : ℝ) ≤ (X : ℝ)
    exact_mod_cast hX3
  have hxpos : 0 < x := by linarith
  have hCeil : ⌈R⌉₊ ≤ X := (le_max_right 3 ⌈R⌉₊).trans (le_max_right _ _)
  have hxR : R ≤ x := by
    change R ≤ (X : ℝ)
    exact (Nat.le_ceil R).trans (by exact_mod_cast hCeil)
  refine ⟨X, hBeyond, ?_⟩
  change K * (Real.sqrt (2 * x) * Real.log (2 + 2 * x)) < x / Real.log x ^ 2
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogShift : 0 ≤ Real.log (2 + 2 * x) := Real.log_nonneg (by linarith)
  have hlogBound : Real.log (2 + 2 * x) ≤ 2 * Real.log x := calc
    _ ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) (by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx3) (by positivity : 0 ≤ x + 1)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hsqrtBound : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := calc
    _ ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hFour : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      rw [hFour]
  have hCube : Real.log x ^ 3 ≤ ε * Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hlog.le 3),
      Real.norm_of_nonneg (Real.sqrt_nonneg x)] using hR x hxR
  have hScale : K * (Real.sqrt (2 * x) * Real.log (2 + 2 * x)) ≤
      4 * |K| * Real.sqrt x * Real.log x := calc
    _ ≤ |K| * (Real.sqrt (2 * x) * Real.log (2 + 2 * x)) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (mul_nonneg (Real.sqrt_nonneg _) hlogShift)
    _ ≤ |K| * ((2 * Real.sqrt x) * (2 * Real.log x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hsqrtBound hlogBound hlogShift (by positivity))
        (abs_nonneg K)
    _ = _ := by ring
  have hCoeff : 4 * |K| * ε < 1 := by
    dsimp [ε]
    rw [← mul_div_assoc, mul_one]
    exact (div_lt_iff₀ (by positivity : 0 < 4 * (|K| + 1))).2 (by linarith)
  apply (lt_div_iff₀ (sq_pos_of_pos hlog)).2
  calc
    _ ≤ (4 * |K| * Real.sqrt x * Real.log x) * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right hScale (sq_nonneg _)
    _ = (4 * |K| * Real.sqrt x) * Real.log x ^ 3 := by ring
    _ ≤ (4 * |K| * Real.sqrt x) * (ε * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hCube (by positivity)
    _ = (4 * |K| * ε) * (Real.sqrt x ^ 2) := by ring
    _ = (4 * |K| * ε) * x := by rw [Real.sq_sqrt hxpos.le]
    _ < x := by simpa only [one_mul] using mul_lt_mul_of_pos_right hCoeff hxpos
