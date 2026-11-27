import Mathlib

private noncomputable def E_fn (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def Q_fn (n : ℕ) : ℕ :=
  (Nat.log 2 (n + 2)) ^ 2

private def arcs_fn (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q_fn n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q_fn n : ℝ) / ((q : ℝ) * (n : ℝ))}

private noncomputable def P_fn (d M : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range M, (E_fn ((d : ℝ) * t)) ^ (j + 1)

private noncomputable def m_fn (s : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  intervalIntegral (s.indicator f) (0 : ℝ) 1 MeasureTheory.volume

private lemma one_le_Q (n : ℕ) : 1 ≤ Q_fn n := by
  unfold Q_fn
  have hlog : 1 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega)
  calc
    1 = 1 ^ 2 := by norm_num
    _ ≤ (Nat.log 2 (n + 2)) ^ 2 := Nat.pow_le_pow_left hlog 2

private lemma measurableSet_arcs (n : ℕ) : MeasurableSet (arcs_fn n) := by
  have h_eq : arcs_fn n =
      ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1 ≤ q ∧ q ≤ Q_fn n ∧ a ≤ q ∧ Nat.Coprime a q} ∩
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q_fn n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp [arcs_fn, and_assoc]
  rw [h_eq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ q ≤ Q_fn n ∧ a ≤ q ∧ Nat.Coprime a q
  · have hset : {t : ℝ | 1 ≤ q ∧ q ≤ Q_fn n ∧ a ≤ q ∧ Nat.Coprime a q} = Set.univ := by
      ext t
      exact iff_true_intro h
    rw [hset, Set.univ_inter]
    exact (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  · have hset : {t : ℝ | 1 ≤ q ∧ q ≤ Q_fn n ∧ a ≤ q ∧ Nat.Coprime a q} = ∅ := by
      ext t; simp [h]
    rw [hset, Set.empty_inter]
    exact MeasurableSet.empty

private lemma measurableSet_arcs_compl (n : ℕ) : MeasurableSet (arcs_fn n)ᶜ :=
  (measurableSet_arcs n).compl

private lemma continuous_E : Continuous E_fn := by
  unfold E_fn
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

private lemma continuous_P (d M : ℕ) : Continuous (P_fn d M) := by
  unfold P_fn
  exact continuous_finsetSum _ fun j _ =>
    (continuous_E.comp (continuous_const.mul continuous_id)).pow (j + 1)

private lemma continuous_norm_P_sq (d M : ℕ) : Continuous (fun t => ‖P_fn d M t‖ ^ 2) :=
  ((continuous_P d M).norm).pow 2

private lemma continuous_norm_sum_sq (R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) :
    Continuous (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2) :=
  ((continuous_finsetSum _ fun d _ => continuous_const.mul (continuous_P d (M d))).norm).pow 2

private lemma intervalIntegrable_indicator {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private lemma intervalIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    {a b : ℝ} (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    intervalIntegral (fun t => ∑ i ∈ s, f i t) a b MeasureTheory.volume =
      ∑ i ∈ s, intervalIntegral (f i) a b MeasureTheory.volume := by
  exact intervalIntegral.integral_finsetSum (s := s) (f := f) hf

private lemma sum_integral_adjacent (f : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ)
    (hf : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y) :
    (∑ k ∈ Finset.range N, intervalIntegral f (a k) (a (k + 1)) MeasureTheory.volume) =
      intervalIntegral f (a 0) (a N) MeasureTheory.volume := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact intervalIntegral.integral_add_adjacent_intervals (hf (a 0) (a N)) (hf (a N) (a (N + 1)))

private lemma mem_arcs_of_abs_sub_le {n d k : ℕ} {t : ℝ}
    (hn : 0 < n) (hd1 : 1 ≤ d) (hdQ : d ≤ Q_fn n) (hkd : k ≤ d)
    (ht : |t - (k : ℝ) / (d : ℝ)| ≤ (Q_fn n : ℝ) / ((d : ℝ) * (n : ℝ))) :
    t ∈ arcs_fn n := by
  let g := Nat.gcd k d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right k (by omega)
  have hgd_dvd : g ∣ d := Nat.gcd_dvd_right k d
  have hgk_dvd : g ∣ k := Nat.gcd_dvd_left k d
  have hgd_le : g ≤ d := Nat.le_of_dvd (by omega) hgd_dvd
  let a := k / g
  let q := d / g
  have hq1 : 1 ≤ q := Nat.div_pos hgd_le hg_pos
  have hq_le_d : q ≤ d := Nat.div_le_self d g
  have hqQ : q ≤ Q_fn n := le_trans hq_le_d hdQ
  have haq : a ≤ q := Nat.div_le_div_right hkd
  have hcop : Nat.Coprime a q := Nat.coprime_div_gcd_div_gcd hg_pos
  have hfrac : (a : ℝ) / (q : ℝ) = (k : ℝ) / (d : ℝ) := by
    have hak : a * g = k := Nat.div_mul_cancel hgk_dvd
    have hqd : q * g = d := Nat.div_mul_cancel hgd_dvd
    have hakR : (a : ℝ) * (g : ℝ) = (k : ℝ) := by exact_mod_cast hak
    have hqdR : (q : ℝ) * (g : ℝ) = (d : ℝ) := by exact_mod_cast hqd
    have hg0 : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← hakR, ← hqdR, mul_div_mul_right _ _ hg0]
  have hrad : (Q_fn n : ℝ) / ((d : ℝ) * (n : ℝ)) ≤ (Q_fn n : ℝ) / ((q : ℝ) * (n : ℝ)) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hq_le_dR : (q : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hq_le_d
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hq_pos hn_pos)
      (mul_le_mul_of_nonneg_right hq_le_dR (le_of_lt hn_pos))
  refine ⟨q, a, hq1, hqQ, haq, hcop, ?_⟩
  rw [hfrac]
  exact le_trans ht hrad

private lemma norm_exp_real_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
  have hconj : starRingEnd ℂ (Complex.exp ((x : ℂ) * Complex.I)) =
      Complex.exp (-((x : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    simp
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I)‖ * ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I)‖ * ‖Complex.exp ((x : ℂ) * Complex.I)‖
          = ‖Complex.exp ((x : ℂ) * Complex.I)‖ *
              ‖starRingEnd ℂ (Complex.exp ((x : ℂ) * Complex.I))‖ := by
            simp
      _ = ‖Complex.exp ((x : ℂ) * Complex.I) * Complex.exp (-((x : ℂ) * Complex.I))‖ := by
            rw [hconj, norm_mul]
      _ = ‖Complex.exp (((x : ℂ) * Complex.I) + -((x : ℂ) * Complex.I))‖ := by
            rw [Complex.exp_add]
      _ = 1 := by simp
  have h0 : 0 ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith

private lemma norm_E (x : ℝ) : ‖E_fn x‖ = 1 :=
  norm_exp_real_mul_I (2 * Real.pi * x)

private lemma norm_E_sub_one (u : ℝ) :
    ‖E_fn u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
  unfold E_fn
  set θ : ℂ := ((Real.pi * u : ℝ) : ℂ)
  have h1 : (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) = θ * Complex.I + θ * Complex.I := by
    simp only [θ]
    push_cast
    ring
  have h2 : Complex.exp (θ * Complex.I + θ * Complex.I) - 1 =
      Complex.exp (θ * Complex.I) *
        (Complex.exp (θ * Complex.I) - Complex.exp (-(θ * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    simp
  have h3 : Complex.exp (θ * Complex.I) - Complex.exp (-(θ * Complex.I)) =
      (2 : ℂ) * ((Real.sin (Real.pi * u) : ℝ) : ℂ) * Complex.I := by
    rw [show -(θ * Complex.I) = (-θ) * Complex.I by ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    have hsin : Complex.sin θ = ((Real.sin (Real.pi * u) : ℝ) : ℂ) := by
      simp [θ, Complex.ofReal_sin]
    rw [hsin]
    ring
  rw [h1, h2, h3, norm_mul, norm_mul, norm_mul]
  have hI : ‖Complex.I‖ = 1 := by
    have hsq : ‖Complex.I‖ * ‖Complex.I‖ = 1 := by
      rw [← norm_mul, Complex.I_mul_I, norm_neg, norm_one]
    nlinarith [norm_nonneg Complex.I]
  have h2n : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  rw [norm_exp_real_mul_I (Real.pi * u), h2n, Complex.norm_real, Real.norm_eq_abs, hI]
  ring

private lemma mul_sub_one_P (z : ℂ) (M : ℕ) :
    (z - 1) * (∑ j ∈ Finset.range M, z ^ (j + 1)) = z * (z ^ M - 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private lemma norm_P_sq_le {d M : ℕ} {t c : ℝ}
    (hc : 0 < c) (hsin : c ≤ |Real.sin (Real.pi * ((d : ℝ) * t))|) :
    ‖P_fn d M t‖ ^ 2 ≤ 1 / c ^ 2 := by
  set z : ℂ := E_fn ((d : ℝ) * t)
  have hz_norm : ‖z‖ = 1 := norm_E ((d : ℝ) * t)
  have hgeom : (z - 1) * P_fn d M t = z * (z ^ M - 1) := mul_sub_one_P z M
  have hnorm : ‖z - 1‖ * ‖P_fn d M t‖ ≤ 2 := by
    calc
      ‖z - 1‖ * ‖P_fn d M t‖
          = ‖(z - 1) * P_fn d M t‖ := (norm_mul _ _).symm
      _ = ‖z * (z ^ M - 1)‖ := by rw [hgeom]
      _ = ‖z‖ * ‖z ^ M - 1‖ := norm_mul _ _
      _ = ‖z ^ M - 1‖ := by rw [hz_norm, one_mul]
      _ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz_norm, one_pow, norm_one]; norm_num
  have hsin_eq : ‖z - 1‖ = 2 * |Real.sin (Real.pi * ((d : ℝ) * t))| :=
    norm_E_sub_one ((d : ℝ) * t)
  have h2c : 2 * c ≤ ‖z - 1‖ := by linarith
  have hprod : 2 * c * ‖P_fn d M t‖ ≤ 2 := by
    calc
      2 * c * ‖P_fn d M t‖ ≤ ‖z - 1‖ * ‖P_fn d M t‖ :=
        mul_le_mul_of_nonneg_right h2c (norm_nonneg _)
      _ ≤ 2 := hnorm
  have hcp : c * ‖P_fn d M t‖ ≤ 1 := by linarith
  have hsq : (c * ‖P_fn d M t‖) ^ 2 ≤ 1 ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hc) (norm_nonneg (P_fn d M t))]
  rw [le_div_iff₀ (pow_pos hc 2)]
  nlinarith

private lemma abs_sin_add_nat_mul_pi (x : ℝ) (k : ℕ) :
    |Real.sin (x + (k : ℝ) * Real.pi)| = |Real.sin x| := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [add_mul, one_mul, ← add_assoc, Real.sin_add_pi, abs_neg, ih]

private lemma sin_lower_left {d k : ℕ} {t : ℝ}
    (hd : 0 < d)
    (ht1 : (k : ℝ) / (d : ℝ) ≤ t)
    (ht2 : t ≤ ((k : ℝ) + 1 / 2) / (d : ℝ)) :
    2 * (d : ℝ) * (t - (k : ℝ) / (d : ℝ)) ≤ |Real.sin (Real.pi * ((d : ℝ) * t))| := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  set u : ℝ := (d : ℝ) * t - (k : ℝ)
  have hu0 : 0 ≤ u := by
    have : (k : ℝ) ≤ (d : ℝ) * t := by
      have := mul_le_mul_of_nonneg_left ht1 (le_of_lt hd_pos)
      rwa [mul_div_cancel₀ _ hd_ne] at this
    linarith
  have hu1 : u ≤ 1 / 2 := by
    have : (d : ℝ) * t ≤ (k : ℝ) + 1 / 2 := by
      have := mul_le_mul_of_nonneg_left ht2 (le_of_lt hd_pos)
      rwa [mul_div_cancel₀ _ hd_ne] at this
    linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  have hsin_ge : 2 * u ≤ Real.sin (Real.pi * u) := by
    have h := Real.mul_le_sin (mul_nonneg (le_of_lt hpi_pos) hu0)
      (by nlinarith : Real.pi * u ≤ Real.pi / 2)
    have hsimp : 2 / Real.pi * (Real.pi * u) = 2 * u := by
      rw [← mul_assoc, div_mul_cancel₀ _ hpi_ne]
    linarith
  have heq : Real.pi * ((d : ℝ) * t) = Real.pi * u + (k : ℝ) * Real.pi := by
    simp only [u]; ring
  rw [heq, abs_sin_add_nat_mul_pi]
  have hu_eq : 2 * (d : ℝ) * (t - (k : ℝ) / (d : ℝ)) = 2 * u := by
    simp only [u]
    rw [mul_sub, mul_assoc (2 : ℝ) (d : ℝ) ((k : ℝ) / (d : ℝ)), mul_div_cancel₀ _ hd_ne]
    ring
  rw [hu_eq]
  exact le_trans hsin_ge (le_abs_self _)

private lemma sin_lower_right {d k : ℕ} {t : ℝ}
    (hd : 0 < d)
    (ht1 : ((k : ℝ) + 1 / 2) / (d : ℝ) ≤ t)
    (ht2 : t ≤ ((k + 1 : ℕ) : ℝ) / (d : ℝ)) :
    2 * (d : ℝ) * (((k + 1 : ℕ) : ℝ) / (d : ℝ) - t) ≤ |Real.sin (Real.pi * ((d : ℝ) * t))| := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  set v : ℝ := ((k + 1 : ℕ) : ℝ) - (d : ℝ) * t
  have hv0 : 0 ≤ v := by
    have : (d : ℝ) * t ≤ ((k + 1 : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left ht2 (le_of_lt hd_pos)
      rwa [mul_div_cancel₀ _ hd_ne] at this
    linarith
  have hv1 : v ≤ 1 / 2 := by
    have : (k : ℝ) + 1 / 2 ≤ (d : ℝ) * t := by
      have := mul_le_mul_of_nonneg_left ht1 (le_of_lt hd_pos)
      rwa [mul_div_cancel₀ _ hd_ne] at this
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  have hsin_ge : 2 * v ≤ Real.sin (Real.pi * v) := by
    have h := Real.mul_le_sin (mul_nonneg (le_of_lt hpi_pos) hv0)
      (by nlinarith : Real.pi * v ≤ Real.pi / 2)
    have hsimp : 2 / Real.pi * (Real.pi * v) = 2 * v := by
      rw [← mul_assoc, div_mul_cancel₀ _ hpi_ne]
    linarith
  have heq : Real.pi * ((d : ℝ) * t) = -(Real.pi * v) + ((k + 1 : ℕ) : ℝ) * Real.pi := by
    simp only [v]; ring
  rw [heq, abs_sin_add_nat_mul_pi, Real.sin_neg, abs_neg]
  have hv_eq : 2 * (d : ℝ) * (((k + 1 : ℕ) : ℝ) / (d : ℝ) - t) = 2 * v := by
    simp only [v]
    rw [mul_sub, mul_assoc (2 : ℝ) (d : ℝ) (((k + 1 : ℕ) : ℝ) / (d : ℝ)), mul_div_cancel₀ _ hd_ne]
    ring
  rw [hv_eq]
  exact le_trans hsin_ge (le_abs_self _)

private lemma integral_inv_sq_left_le {d a ε m : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (ham : a + ε ≤ m) :
    intervalIntegral (fun t => 1 / (4 * d ^ 2 * (t - a) ^ 2)) (a + ε) m MeasureTheory.volume ≤
      1 / (4 * d ^ 2 * ε) := by
  let F : ℝ → ℝ := fun t => -(1 / (4 * d ^ 2)) * (t - a)⁻¹
  have hderiv : ∀ t ∈ Set.uIcc (a + ε) m,
      HasDerivAt F (1 / (4 * d ^ 2 * (t - a) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le ham] at ht
    have hta : 0 < t - a := by linarith [ht.1]
    have hta_ne : t - a ≠ 0 := ne_of_gt hta
    have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id t).sub_const a
    have h2 : HasDerivAt (fun x : ℝ => (x - a)⁻¹) (-1 / (t - a) ^ 2) t := h1.inv hta_ne
    have h3 : HasDerivAt F (-(1 / (4 * d ^ 2)) * (-1 / (t - a) ^ 2)) t :=
      h2.const_mul (-(1 / (4 * d ^ 2)))
    convert h3 using 1
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / (4 * d ^ 2 * (t - a) ^ 2)) (Set.uIcc (a + ε) m) := by
    refine continuousOn_const.div ?_ ?_
    · exact (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le ham] at ht
      have hta : 0 < t - a := by linarith [ht.1]
      change (4 * d ^ 2 * (t - a) ^ 2) ≠ (0 : ℝ)
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd.ne')) (pow_ne_zero _ hta.ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hma : 0 < m - a := by linarith
  have hterm : 0 ≤ (1 / (4 * d ^ 2)) * (m - a)⁻¹ := by positivity
  have hsub : F m - F (a + ε) = 1 / (4 * d ^ 2 * ε) - (1 / (4 * d ^ 2)) * (m - a)⁻¹ := by
    simp only [F, add_sub_cancel_left, div_eq_mul_inv, mul_inv]
    ring
  linarith

private lemma integral_inv_sq_right_le {d b ε m : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hmb : m ≤ b - ε) :
    intervalIntegral (fun t => 1 / (4 * d ^ 2 * (b - t) ^ 2)) m (b - ε) MeasureTheory.volume ≤
      1 / (4 * d ^ 2 * ε) := by
  let G : ℝ → ℝ := fun t => (1 / (4 * d ^ 2)) * (b - t)⁻¹
  have hderiv : ∀ t ∈ Set.uIcc m (b - ε),
      HasDerivAt G (1 / (4 * d ^ 2 * (b - t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hmb] at ht
    have hbt : 0 < b - t := by linarith [ht.2]
    have hbt_ne : b - t ≠ 0 := ne_of_gt hbt
    have h1 : HasDerivAt (fun x : ℝ => b - x) (0 - 1) t :=
      (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have h2 : HasDerivAt (fun x : ℝ => (b - x)⁻¹) (-(0 - 1) / (b - t) ^ 2) t := h1.inv hbt_ne
    have h3 : HasDerivAt G ((1 / (4 * d ^ 2)) * (-(0 - 1) / (b - t) ^ 2)) t :=
      h2.const_mul (1 / (4 * d ^ 2))
    convert h3 using 1
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hcont : ContinuousOn (fun t : ℝ => 1 / (4 * d ^ 2 * (b - t) ^ 2)) (Set.uIcc m (b - ε)) := by
    refine continuousOn_const.div ?_ ?_
    · exact (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le hmb] at ht
      have hbt : 0 < b - t := by linarith [ht.2]
      change (4 * d ^ 2 * (b - t) ^ 2) ≠ (0 : ℝ)
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd.ne')) (pow_ne_zero _ hbt.ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hbm : 0 < b - m := by linarith
  have hterm : 0 ≤ (1 / (4 * d ^ 2)) * (b - m)⁻¹ := by positivity
  have hsub : G (b - ε) - G m = 1 / (4 * d ^ 2 * ε) - (1 / (4 * d ^ 2)) * (b - m)⁻¹ := by
    simp only [G, sub_sub_cancel, div_eq_mul_inv, mul_inv]
    ring
  linarith

private lemma integral_indicator_compl_eq_zero {s : Set ℝ} {f : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hsub : ∀ t ∈ Set.Icc u v, t ∈ s) :
    intervalIntegral (sᶜ.indicator f) u v MeasureTheory.volume = 0 := by
  have hcongr : Set.EqOn (sᶜ.indicator f) (fun _ => (0 : ℝ)) (Set.uIcc u v) := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have hnot : t ∉ sᶜ := fun h => h (hsub t ht)
    simp only [Set.indicator, if_neg hnot]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero]

private lemma subinterval_bound {n d k M : ℕ}
    (hn : 0 < n) (hd1 : 1 ≤ d) (hdQ : d ≤ Q_fn n) (hkd : k < d) :
    intervalIntegral ((arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d M t‖ ^ 2))
        ((k : ℝ) / (d : ℝ)) (((k + 1 : ℕ) : ℝ) / (d : ℝ)) MeasureTheory.volume ≤
      (n : ℝ) / (2 * (d : ℝ) * (Q_fn n : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hQ_pos : (0 : ℝ) < (Q_fn n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_Q n))
  set a : ℝ := (k : ℝ) / (d : ℝ)
  set m : ℝ := ((k : ℝ) + 1 / 2) / (d : ℝ)
  set b : ℝ := ((k + 1 : ℕ) : ℝ) / (d : ℝ)
  set ε : ℝ := (Q_fn n : ℝ) / ((d : ℝ) * (n : ℝ))
  set f : ℝ → ℝ := (arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d M t‖ ^ 2)
  have hε_pos : 0 < ε := by positivity
  have ham_diff : m - a = 1 / (2 * (d : ℝ)) := by
    simp only [m, a]
    rw [← sub_div, add_sub_cancel_left, div_div, mul_comm (2 : ℝ) (d : ℝ)]
  have hmb_diff : b - m = 1 / (2 * (d : ℝ)) := by
    simp only [b, m]
    rw [Nat.cast_add, Nat.cast_one, ← sub_div]
    have hnum : (k : ℝ) + 1 - ((k : ℝ) + 1 / 2) = 1 / 2 := by ring
    rw [hnum, div_div, mul_comm (2 : ℝ) (d : ℝ)]
  have hab : a ≤ b := by
    have : 0 < 1 / (2 * (d : ℝ)) := by positivity
    linarith
  have hf_int : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y := fun x y =>
    intervalIntegrable_indicator ((continuous_norm_P_sq d M).intervalIntegrable x y)
      (measurableSet_arcs_compl n)
  by_cases hε : 1 / (2 * (d : ℝ)) ≤ ε
  · have hsub : ∀ t ∈ Set.Icc a b, t ∈ arcs_fn n := by
      intro t ht
      by_cases htm : t ≤ m
      · have habs : |t - a| ≤ ε := by
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith
        exact mem_arcs_of_abs_sub_le hn hd1 hdQ (le_of_lt hkd) habs
      · have habs : |t - b| ≤ ε := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
          linarith
        exact mem_arcs_of_abs_sub_le hn hd1 hdQ hkd habs
    rw [integral_indicator_compl_eq_zero hab hsub]
    positivity
  · push_neg at hε
    have ham_le : a + ε ≤ m := by linarith
    have hmb_le : m ≤ b - ε := by linarith
    have hsplit : intervalIntegral f a b MeasureTheory.volume =
        intervalIntegral f a (a + ε) MeasureTheory.volume +
        intervalIntegral f (a + ε) m MeasureTheory.volume +
        intervalIntegral f m (b - ε) MeasureTheory.volume +
        intervalIntegral f (b - ε) b MeasureTheory.volume := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hf_int a (a + ε)) (hf_int (a + ε) m)]
      rw [intervalIntegral.integral_add_adjacent_intervals (hf_int a m) (hf_int m (b - ε))]
      rw [intervalIntegral.integral_add_adjacent_intervals (hf_int a (b - ε)) (hf_int (b - ε) b)]
    have hpart1 : intervalIntegral f a (a + ε) MeasureTheory.volume = 0 := by
      refine integral_indicator_compl_eq_zero (by linarith) fun t ht => ?_
      have habs : |t - a| ≤ ε := by
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2]
      exact mem_arcs_of_abs_sub_le hn hd1 hdQ (le_of_lt hkd) habs
    have hpart4 : intervalIntegral f (b - ε) b MeasureTheory.volume = 0 := by
      refine integral_indicator_compl_eq_zero (by linarith) fun t ht => ?_
      have habs : |t - b| ≤ ε := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      exact mem_arcs_of_abs_sub_le hn hd1 hdQ hkd habs
    have hcont_left : ContinuousOn (fun t : ℝ => 1 / (4 * (d : ℝ) ^ 2 * (t - a) ^ 2))
        (Set.uIcc (a + ε) m) := by
      refine continuousOn_const.div ?_ ?_
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn
      · intro t ht
        rw [Set.uIcc_of_le ham_le] at ht
        have hta : 0 < t - a := by linarith [ht.1]
        change (4 * (d : ℝ) ^ 2 * (t - a) ^ 2) ≠ (0 : ℝ)
        exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd_pos.ne')) (pow_ne_zero _ hta.ne')
    have hpart2 : intervalIntegral f (a + ε) m MeasureTheory.volume ≤
        1 / (4 * (d : ℝ) ^ 2 * ε) := by
      refine le_trans ?_ (integral_inv_sq_left_le hd_pos hε_pos ham_le)
      refine intervalIntegral.integral_mono_on ham_le (hf_int (a + ε) m)
        hcont_left.intervalIntegrable fun t ht => ?_
      have hta : 0 < t - a := by linarith [ht.1]
      have hle_ind : f t ≤ ‖P_fn d M t‖ ^ 2 := by
        by_cases hmem : t ∈ (arcs_fn n)ᶜ
        · simp only [f, Set.indicator, if_pos hmem, le_refl]
        · simp only [f, Set.indicator, if_neg hmem]
          exact sq_nonneg _
      have hsin := sin_lower_left (by omega : 0 < d) (by linarith [ht.1]) ht.2
      have hbound := norm_P_sq_le (d := d) (M := M) (t := t) (by positivity) hsin
      have hsq_eq : (2 * (d : ℝ) * (t - a)) ^ 2 = 4 * (d : ℝ) ^ 2 * (t - a) ^ 2 := by ring
      rw [hsq_eq] at hbound
      exact le_trans hle_ind hbound
    have hcont_right : ContinuousOn (fun t : ℝ => 1 / (4 * (d : ℝ) ^ 2 * (b - t) ^ 2))
        (Set.uIcc m (b - ε)) := by
      refine continuousOn_const.div ?_ ?_
      · exact (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).continuousOn
      · intro t ht
        rw [Set.uIcc_of_le hmb_le] at ht
        have hbt : 0 < b - t := by linarith [ht.2]
        change (4 * (d : ℝ) ^ 2 * (b - t) ^ 2) ≠ (0 : ℝ)
        exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd_pos.ne')) (pow_ne_zero _ hbt.ne')
    have hpart3 : intervalIntegral f m (b - ε) MeasureTheory.volume ≤
        1 / (4 * (d : ℝ) ^ 2 * ε) := by
      refine le_trans ?_ (integral_inv_sq_right_le hd_pos hε_pos hmb_le)
      refine intervalIntegral.integral_mono_on hmb_le (hf_int m (b - ε))
        hcont_right.intervalIntegrable fun t ht => ?_
      have hbt : 0 < b - t := by linarith [ht.2]
      have hle_ind : f t ≤ ‖P_fn d M t‖ ^ 2 := by
        by_cases hmem : t ∈ (arcs_fn n)ᶜ
        · simp only [f, Set.indicator, if_pos hmem, le_refl]
        · simp only [f, Set.indicator, if_neg hmem]
          exact sq_nonneg _
      have hsin := sin_lower_right (by omega : 0 < d) ht.1 (by linarith [ht.2])
      have hbound := norm_P_sq_le (d := d) (M := M) (t := t) (by positivity) hsin
      have hsq_eq : (2 * (d : ℝ) * (b - t)) ^ 2 = 4 * (d : ℝ) ^ 2 * (b - t) ^ 2 := by ring
      rw [hsq_eq] at hbound
      exact le_trans hle_ind hbound
    have hsum_eq : 1 / (4 * (d : ℝ) ^ 2 * ε) + 1 / (4 * (d : ℝ) ^ 2 * ε) =
        (n : ℝ) / (2 * (d : ℝ) * (Q_fn n : ℝ)) := by
      simp only [ε]
      have h1 : 4 * (d : ℝ) ^ 2 * ((Q_fn n : ℝ) / ((d : ℝ) * (n : ℝ))) =
          (4 * (d : ℝ) * (Q_fn n : ℝ)) / (n : ℝ) := by
        rw [mul_div_assoc',
          show 4 * (d : ℝ) ^ 2 * (Q_fn n : ℝ) = (d : ℝ) * (4 * (d : ℝ) * (Q_fn n : ℝ)) by ring,
          mul_div_mul_left _ _ hd_ne]
      rw [h1, one_div_div]
      ring
    linarith

private lemma single_d_bound {n d M : ℕ}
    (hn : 0 < n) (hd1 : 1 ≤ d) (hdQ : d ≤ Q_fn n) :
    m_fn (arcs_fn n)ᶜ (fun t => ‖P_fn d M t‖ ^ 2) ≤ (2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hQ_pos : (0 : ℝ) < (Q_fn n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (one_le_Q n))
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hf_int : ∀ x y : ℝ,
      IntervalIntegrable ((arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d M t‖ ^ 2))
        MeasureTheory.volume x y := fun x y =>
    intervalIntegrable_indicator ((continuous_norm_P_sq d M).intervalIntegrable x y)
      (measurableSet_arcs_compl n)
  have hsplit := sum_integral_adjacent
    ((arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d M t‖ ^ 2))
    (fun k : ℕ => (k : ℝ) / (d : ℝ)) d hf_int
  have h0 : ((0 : ℕ) : ℝ) / (d : ℝ) = 0 := by simp
  have h1 : ((d : ℕ) : ℝ) / (d : ℝ) = 1 := div_self hd_ne
  rw [h0, h1] at hsplit
  have hsum : m_fn (arcs_fn n)ᶜ (fun t => ‖P_fn d M t‖ ^ 2) ≤
      (n : ℝ) / (2 * (Q_fn n : ℝ)) := by
    unfold m_fn
    rw [← hsplit]
    calc
      (∑ k ∈ Finset.range d,
        intervalIntegral ((arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d M t‖ ^ 2))
          ((k : ℝ) / (d : ℝ)) (((k + 1 : ℕ) : ℝ) / (d : ℝ)) MeasureTheory.volume)
          ≤ ∑ _k ∈ Finset.range d, (n : ℝ) / (2 * (d : ℝ) * (Q_fn n : ℝ)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact subinterval_bound hn hd1 hdQ (Finset.mem_range.mp hk)
      _ = (d : ℝ) * ((n : ℝ) / (2 * (d : ℝ) * (Q_fn n : ℝ))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (n : ℝ) / (2 * (Q_fn n : ℝ)) := by
            rw [mul_div_assoc',
              show 2 * (d : ℝ) * (Q_fn n : ℝ) = (d : ℝ) * (2 * (Q_fn n : ℝ)) by ring,
              mul_div_mul_left _ _ hd_ne]
  have hpi : (1 : ℝ) / 2 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hfinal : (n : ℝ) / (2 * (Q_fn n : ℝ)) ≤ 2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ) := by
    have hmul : (1 / 2 : ℝ) * ((n : ℝ) / (Q_fn n : ℝ)) ≤
        (2 * Real.pi) * ((n : ℝ) / (Q_fn n : ℝ)) :=
      mul_le_mul_of_nonneg_right hpi (by positivity)
    have hl : (1 / 2 : ℝ) * ((n : ℝ) / (Q_fn n : ℝ)) = (n : ℝ) / (2 * (Q_fn n : ℝ)) := by ring
    have hr : (2 * Real.pi) * ((n : ℝ) / (Q_fn n : ℝ)) =
        2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ) := by ring
    linarith
  exact le_trans hsum hfinal

private lemma pointwise_weighted_cs (R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) (t : ℝ) :
    ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2 ≤
      (∑ d ∈ Finset.Icc 1 R, |c d|) *
        (∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) := by
  have htri : ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ≤
      ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ := by
    calc
      ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖
          ≤ ∑ d ∈ Finset.Icc 1 R, ‖(c d : ℂ) * P_fn d (M d) t‖ := norm_sum_le _ _
      _ = ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsq : ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2 ≤
      (∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t)]
  have hcs : (∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖) ^ 2 ≤
      (∑ d ∈ Finset.Icc 1 R, |c d|) *
        (∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 R)
      (fun d => Real.sqrt |c d|) (fun d => Real.sqrt |c d| * ‖P_fn d (M d) t‖)
    have h1 : (∑ d ∈ Finset.Icc 1 R, Real.sqrt |c d| * (Real.sqrt |c d| * ‖P_fn d (M d) t‖)) =
        ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have h2 : (∑ d ∈ Finset.Icc 1 R, Real.sqrt |c d| ^ 2) =
        ∑ d ∈ Finset.Icc 1 R, |c d| := by
      refine Finset.sum_congr rfl fun d _ => Real.sq_sqrt (abs_nonneg _)
    have h3 : (∑ d ∈ Finset.Icc 1 R, (Real.sqrt |c d| * ‖P_fn d (M d) t‖) ^ 2) =
        ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2 := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    rw [h1, h2, h3] at h
    exact h
  exact le_trans hsq hcs

private lemma packetDivisorMixtureLeakage_aux
    (n R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) (hn : 0 < n) (hR : R ≤ Q_fn n) :
    m_fn (arcs_fn n)ᶜ (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2) ≤
      (2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ)) * (∑ d ∈ Finset.Icc 1 R, |c d|) ^ 2 := by
  set S : ℝ := ∑ d ∈ Finset.Icc 1 R, |c d|
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun d _ => abs_nonneg (c d)
  have h_lhs_int : IntervalIntegrable
      ((arcs_fn n)ᶜ.indicator (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2))
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_indicator ((continuous_norm_sum_sq R c M).intervalIntegrable 0 1)
      (measurableSet_arcs_compl n)
  have h_term_int : ∀ d ∈ Finset.Icc 1 R, IntervalIntegrable
      (fun t => |c d| * (arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d (M d) t‖ ^ 2) t)
      MeasureTheory.volume 0 1 := fun d _ =>
    let h := intervalIntegrable_indicator ((continuous_norm_P_sq d (M d)).intervalIntegrable 0 1)
      (measurableSet_arcs_compl n)
    ⟨h.1.const_mul |c d|, h.2.const_mul |c d|⟩
  have h_weighted_cont : Continuous (fun t => ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) := by
    refine continuous_finsetSum (Finset.Icc 1 R) ?_
    intro d _
    exact continuous_const.mul (continuous_norm_P_sq d (M d))
  have h_rhs_cont : Continuous (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) :=
    continuous_const.mul h_weighted_cont
  have h_rhs_int : IntervalIntegrable
      ((arcs_fn n)ᶜ.indicator (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2))
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_indicator (h_rhs_cont.intervalIntegrable 0 1) (measurableSet_arcs_compl n)
  have h_mono : m_fn (arcs_fn n)ᶜ (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2) ≤
      m_fn (arcs_fn n)ᶜ (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) := by
    unfold m_fn
    refine intervalIntegral.integral_mono_on (by norm_num) h_lhs_int h_rhs_int fun t _ => ?_
    by_cases ht : t ∈ (arcs_fn n)ᶜ
    · simp only [Set.indicator, if_pos ht]
      exact pointwise_weighted_cs R c M t
    · simp only [Set.indicator, if_neg ht, le_refl]
  have h_eq : m_fn (arcs_fn n)ᶜ (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) =
      S * ∑ d ∈ Finset.Icc 1 R, |c d| * m_fn (arcs_fn n)ᶜ (fun t => ‖P_fn d (M d) t‖ ^ 2) := by
    unfold m_fn
    have hfun : (arcs_fn n)ᶜ.indicator (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) =
        fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * (arcs_fn n)ᶜ.indicator (fun t => ‖P_fn d (M d) t‖ ^ 2) t := by
      ext t
      by_cases ht : t ∈ (arcs_fn n)ᶜ <;> simp [Set.indicator, ht]
    rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral_finset_sum _ _ h_term_int]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    exact intervalIntegral.integral_const_mul |c d| _
  calc
    m_fn (arcs_fn n)ᶜ (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d : ℂ) * P_fn d (M d) t‖ ^ 2)
        ≤ m_fn (arcs_fn n)ᶜ (fun t => S * ∑ d ∈ Finset.Icc 1 R, |c d| * ‖P_fn d (M d) t‖ ^ 2) := h_mono
    _ = S * ∑ d ∈ Finset.Icc 1 R, |c d| * m_fn (arcs_fn n)ᶜ (fun t => ‖P_fn d (M d) t‖ ^ 2) := h_eq
    _ ≤ S * ∑ d ∈ Finset.Icc 1 R, |c d| * (2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS_nonneg
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdQ : d ≤ Q_fn n := le_trans (Finset.mem_Icc.mp hd).2 hR
          exact mul_le_mul_of_nonneg_left (single_d_bound hn hd1 hdQ) (abs_nonneg _)
    _ = (2 * Real.pi * (n : ℝ) / (Q_fn n : ℝ)) * S ^ 2 := by
          rw [← Finset.sum_mul]
          ring

theorem Conjectures.Goldbach.PacketDivisorMixtureLeakage :
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let P := fun (d M : ℕ) (t : ℝ) => ∑ j ∈ Finset.range M, (E ((d:ℝ)*t))^(j+1); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ (n R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ), 0<n → R ≤ Q n → m (arcs n)ᶜ (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d:ℂ)*P d (M d) t‖^2) ≤ (2*Real.pi*(n:ℝ)/(Q n:ℝ))*(∑ d ∈ Finset.Icc 1 R, |c d|)^2 := by
  intro E Q arcs P m n R c M hn hR
  exact packetDivisorMixtureLeakage_aux n R c M hn hR
