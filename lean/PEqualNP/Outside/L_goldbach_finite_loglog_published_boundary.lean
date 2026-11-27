import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_loglog_published_boundary :
    let C : ℝ := 4*10^18; (75:ℝ)/20 < Real.log (Real.log C) ∧ Real.log (Real.log C) < (76:ℝ)/20 := by
  dsimp only
  set L : ℝ := Real.log (4*10^18) with hL
  have hlog : L = 20 * Real.log 2 + 18 * Real.log 5 := by
    rw [hL]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_four_eq, Real.log_pow, Real.log_ten_eq]
    ring
  have hlow : (42.8328260274 : ℝ) < L := by
    rw [hlog]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hhigh : L < 42.8328260428 := by
    rw [hlog]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hpos : 0 < L := by linarith
  have h43 : L < 43 := by linarith
  have key : ∀ u : ℝ, 0 ≤ u → u / (1 + u) ≤ Real.log (1 + u) := by
    intro u hu
    have h1 : 0 < 1 + u := by linarith
    have h3 : -Real.log (1 + u) ≤ 1 / (1 + u) - 1 := by
      have hp : 0 < 1 / (1 + u) := div_pos one_pos h1
      have h := Real.log_le_sub_one_of_pos hp
      have hdiv : Real.log (1 / (1 + u)) = -Real.log (1 + u) := by
        rw [Real.log_div (by norm_num) (by linarith), Real.log_one]
        ring
      rwa [hdiv] at h
    have h4 : u / (1 + u) = 1 - 1 / (1 + u) := by
      field_simp
      ring
    rw [h4]
    linarith only [h3]
  have h40 : Real.log (40:ℝ) = 3 * Real.log 2 + Real.log 5 := by
    rw [show (40:ℝ) = 4 * 10 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_four_eq, Real.log_ten_eq]
    ring
  constructor
  · set u : ℝ := 70820650685/10^12 with hu
    have hu0 : 0 ≤ u := by rw [hu]; norm_num
    have h42 : (42.8328260274 : ℝ) = 40 * (1 + u) := by rw [hu]; norm_num
    have h2 : (75:ℝ)/20 < Real.log (42.8328260274 : ℝ) := by
      rw [h42, Real.log_mul (by norm_num) (by linarith), h40]
      have hle := key u hu0
      have hlb : (3:ℝ) * Real.log 2 + Real.log 5 > 3.6888794532 := by
        linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
      have hnum : (0.0661:ℝ) < u / (1 + u) := by rw [hu]; norm_num
      have hbase : (75:ℝ)/20 < 3.6888794532 + 0.0661 := by norm_num
      calc (75:ℝ)/20 < 3.6888794532 + 0.0661 := hbase
        _ < (3 * Real.log 2 + Real.log 5) + u / (1 + u) := add_lt_add hlb hnum
        _ ≤ (3 * Real.log 2 + Real.log 5) + Real.log (1 + u) := add_le_add (le_refl _) hle
    have h1 : Real.log (42.8328260274 : ℝ) < Real.log L :=
      Real.log_lt_log (by norm_num) hlow
    exact lt_trans h2 h1
  · have h1 : Real.log L < Real.log (43:ℝ) := Real.log_lt_log hpos h43
    have h2 : Real.log (43:ℝ) < (76:ℝ)/20 := by
      set v : ℝ := 3/40 with hv
      have hv1 : 0 < 1 + v := by rw [hv]; norm_num
      have h43eq : (43:ℝ) = 40 * (1 + v) := by rw [hv]; norm_num
      rw [h43eq, Real.log_mul (by norm_num) (by linarith), h40]
      have hle : Real.log (1 + v) ≤ v := by
        have h := Real.log_le_sub_one_of_pos hv1
        have h2 : (1 + v) - 1 = v := by ring
        linarith only [h, h2]
      have hub : (3:ℝ) * Real.log 2 + Real.log 5 < 3.688879455 := by
        linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
      have hfin : 3.688879455 + v < (76:ℝ)/20 := by rw [hv]; norm_num
      calc (3 * Real.log 2 + Real.log 5) + Real.log (1 + v)
          ≤ (3 * Real.log 2 + Real.log 5) + v := add_le_add (le_refl _) hle
        _ < 3.688879455 + v := add_lt_add_of_lt_of_le hub (le_refl v)
        _ < (76:ℝ)/20 := hfin
    exact lt_trans h1 h2
