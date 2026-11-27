import Mathlib

private lemma peak_nonneg (n q a : ℕ) (t : ℝ) :
    0 ≤ 4 * (n : ℝ) ^ 2 /
      ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)) := by
  positivity

private lemma peak_continuous (n q a : ℕ) (hq : 1 ≤ q) :
    Continuous (fun t : ℝ =>
      4 * (n : ℝ) ^ 2 /
        ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))) := by
  have hphi : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  refine continuous_const.div ?_ (fun t => ?_)
  · exact continuous_const.mul
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2))
  · exact mul_ne_zero (pow_ne_zero 2 hphi.ne')
      (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)))

private lemma intervalIntegrable_indicator_of_measurable {s : Set ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hs : MeasurableSet s) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private lemma intervalIntegrable_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    {a b : ℝ} (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) MeasureTheory.volume a b := by
  have hsum : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
    funext t
    simp only [Finset.sum_apply]
  rw [← hsum]
  exact IntervalIntegrable.sum s hf

private lemma closed_ball_measurable (c r : ℝ) :
    MeasurableSet {t : ℝ | |t - c| ≤ r} :=
  (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

private lemma measurableSet_arcs (n Q : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  have heq :
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} =
      ⋃ (q : ℕ) (a : ℕ) (_ : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q),
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, hd⟩
      exact ⟨q, a, ⟨hq, hQ, ha, hc⟩, hd⟩
    · rintro ⟨q, a, ⟨hq, hQ, ha, hc⟩, hd⟩
      exact ⟨q, a, hq, hQ, ha, hc, hd⟩
  rw [heq]
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => closed_ball_measurable _ _

private lemma measurableSet_W (n Q : ℕ) (p : ℕ → Prop) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ^ 2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ ((Q : ℝ) ^ 2) / ((q : ℝ) * (n : ℝ))} := by
  have heq :
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ^ 2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ ((Q : ℝ) ^ 2) / ((q : ℝ) * (n : ℝ))} =
      ⋃ (q : ℕ) (a : ℕ) (_ : 1 ≤ q ∧ q ≤ Q ^ 2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q),
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ ((Q : ℝ) ^ 2) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, hp, hd⟩
      exact ⟨q, a, ⟨hq, hQ, ha, hc, hp⟩, hd⟩
    · rintro ⟨q, a, ⟨hq, hQ, ha, hc, hp⟩, hd⟩
      exact ⟨q, a, hq, hQ, ha, hc, hp, hd⟩
  rw [heq]
  exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => closed_ball_measurable _ _

private lemma peak_full_integral_le (n q a : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    intervalIntegral
      (fun t : ℝ => 4 * (n : ℝ) ^ 2 /
        ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))
      (0 : ℝ) 1 MeasureTheory.volume ≤ 16 * (n : ℝ) / (Nat.totient q : ℝ) ^ 2 := by
  set c : ℝ := (a : ℝ) / (q : ℝ)
  set C : ℝ := 4 * (n : ℝ) / (Nat.totient q : ℝ) ^ 2
  set F : ℝ → ℝ := fun t => C * Real.arctan ((n : ℝ) * (t - c))
  have hphi : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F
        (4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2))) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => (n : ℝ) * (x - c)) (n : ℝ) t := by
      simpa [mul_one] using ((hasDerivAt_id t).sub_const c).const_mul (n : ℝ)
    have h2 : HasDerivAt (fun x : ℝ => Real.arctan ((n : ℝ) * (x - c)))
        ((1 + ((n : ℝ) * (t - c)) ^ 2)⁻¹ * (n : ℝ)) t := by
      simpa only [one_div] using h1.arctan
    have h3 : HasDerivAt F (C * ((1 + ((n : ℝ) * (t - c)) ^ 2)⁻¹ * (n : ℝ))) t :=
      by simpa only [mul_assoc] using h2.const_mul C
    convert h3 using 1
    have hden : 0 < 1 + ((n : ℝ) * (t - c)) ^ 2 := by positivity
    dsimp [C]
    field_simp
  have hint : IntervalIntegrable
      (fun t : ℝ => 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2)))
      MeasureTheory.volume 0 1 :=
    (peak_continuous n q a hq).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  rw [← mul_sub]
  have harctan :
      Real.arctan ((n : ℝ) * (1 - c)) - Real.arctan ((n : ℝ) * (0 - c)) ≤ 4 := by
    have h1 := Real.arctan_lt_pi_div_two ((n : ℝ) * (1 - c))
    have h2 := Real.neg_pi_div_two_lt_arctan ((n : ℝ) * (0 - c))
    have h3 := Real.pi_lt_four
    linarith
  have hC_nonneg : 0 ≤ C := by positivity
  calc C * (Real.arctan ((n : ℝ) * (1 - c)) - Real.arctan ((n : ℝ) * (0 - c)))
      ≤ C * 4 := mul_le_mul_of_nonneg_left harctan hC_nonneg
    _ = 16 * (n : ℝ) / (Nat.totient q : ℝ) ^ 2 := by dsimp [C]; ring

private lemma peak_tail_integral_le (n q a : ℕ) (r : ℝ) (E : Set ℝ)
    (hn : 1 ≤ n) (hq : 1 ≤ q) (ha : a ≤ q) (hr : 0 < r)
    (hE_meas : MeasurableSet E)
    (hE_sub : ∀ t ∈ E, r < |t - (a : ℝ) / (q : ℝ)|) :
    intervalIntegral
      (E.indicator (fun t : ℝ => 4 * (n : ℝ) ^ 2 /
        ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))))
      (0 : ℝ) 1 MeasureTheory.volume ≤ 8 / ((Nat.totient q : ℝ) ^ 2 * r) := by
  set c : ℝ := (a : ℝ) / (q : ℝ)
  set g : ℝ → ℝ := fun t =>
    4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2))
  have hc0 : 0 ≤ c := by positivity
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hc1 : c ≤ 1 := (div_le_one hq_pos).mpr (Nat.cast_le.mpr ha)
  have hphi : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  set u : ℝ := max 0 (c - r)
  set v : ℝ := min 1 (c + r)
  have h0u : 0 ≤ u := le_max_left 0 (c - r)
  have huv : u ≤ v :=
    max_le (le_min (by norm_num) (by linarith)) (le_min (by linarith) (by linarith))
  have hv1 : v ≤ 1 := min_le_left 1 (c + r)
  have hg_int : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y :=
    fun x y => (peak_continuous n q a hq).intervalIntegrable x y
  have hEg_int : ∀ x y : ℝ, IntervalIntegrable (E.indicator g) MeasureTheory.volume x y :=
    fun x y => intervalIntegrable_indicator_of_measurable hE_meas (hg_int x y)
  have hsplit1 : (∫ t in (0 : ℝ)..1, E.indicator g t) =
      (∫ t in (0 : ℝ)..u, E.indicator g t) + (∫ t in u..1, E.indicator g t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hEg_int 0 u) (hEg_int u 1)).symm
  have hsplit2 : (∫ t in u..1, E.indicator g t) =
      (∫ t in u..v, E.indicator g t) + (∫ t in v..1, E.indicator g t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hEg_int u v) (hEg_int v 1)).symm
  have hmid : (∫ t in u..v, E.indicator g t) = 0 := by
    have hcongr : (∫ t in u..v, E.indicator g t) = (∫ _ in u..v, (0 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le huv] at ht
      have ht_abs : |t - c| ≤ r := abs_le.mpr ⟨by linarith [le_max_right 0 (c - r), ht.1],
        by linarith [min_le_right 1 (c + r), ht.2]⟩
      have htE : t ∉ E := fun hmem => not_lt_of_ge ht_abs (hE_sub t hmem)
      simp [Set.indicator, htE]
    rw [hcongr, intervalIntegral.integral_zero]
  have hpoint_le : ∀ t : ℝ, t - c ≠ 0 →
      g t ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2) := by
    intro t htc
    have hsq_pos : 0 < (t - c) ^ 2 := sq_pos_of_ne_zero htc
    have h1 : (n : ℝ) ^ 2 * (t - c) ^ 2 ≤ 1 + ((n : ℝ) * (t - c)) ^ 2 := by
      rw [mul_pow]; linarith
    have h2 : (Nat.totient q : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (t - c) ^ 2) ≤
        (Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hrew : 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2) =
        4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (t - c) ^ 2)) := by
      field_simp
    rw [hrew]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  have hF_deriv : ∀ t : ℝ, t - c ≠ 0 →
      HasDerivAt (fun x : ℝ => -(4 / (Nat.totient q : ℝ) ^ 2) * (x - c)⁻¹)
        (4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2)) t := by
    intro t htc
    have h1 : HasDerivAt (fun x : ℝ => (x - c)⁻¹) (-1 / (t - c) ^ 2) t :=
      ((hasDerivAt_id t).sub_const c).inv htc
    have h2 := h1.const_mul (-(4 / (Nat.totient q : ℝ) ^ 2))
    convert h2 using 1
    field_simp [hphi.ne', htc] <;> ring
  have hleft : (∫ t in (0 : ℝ)..u, E.indicator g t) ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * r) := by
    have hle1 : (∫ t in (0 : ℝ)..u, E.indicator g t) ≤ (∫ t in (0 : ℝ)..u, g t) := by
      refine intervalIntegral.integral_mono_on h0u (hEg_int 0 u) (hg_int 0 u) (fun t _ => ?_)
      by_cases ht : t ∈ E
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        exact peak_nonneg n q a t
    refine hle1.trans ?_
    by_cases hu0 : u = 0
    · rw [hu0, intervalIntegral.integral_same]
      positivity
    · have hu_pos : 0 < u := lt_of_le_of_ne h0u (Ne.symm hu0)
      have hu_eq : u = c - r := by
        dsimp [u] at hu_pos ⊢
        exact max_eq_right (le_of_lt ((lt_max_iff.mp hu_pos).resolve_left (lt_irrefl 0)))
      have hne_on : ∀ t ∈ Set.Icc (0 : ℝ) u, t - c ≠ 0 := by
        intro t ht; linarith [ht.2]
      have hh_cont : ContinuousOn (fun t : ℝ => 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2))
          (Set.Icc 0 u) := by
        refine continuousOn_const.div ?_ (fun t ht => ?_)
        · exact continuousOn_const.mul
            ((continuousOn_id.sub continuousOn_const).pow 2)
        · exact mul_ne_zero (pow_ne_zero 2 hphi.ne') (pow_ne_zero 2 (hne_on t ht))
      have hh_int : IntervalIntegrable
          (fun t : ℝ => 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2)) MeasureTheory.volume 0 u :=
        hh_cont.intervalIntegrable_of_Icc h0u
      have hle2 : (∫ t in (0 : ℝ)..u, g t) ≤
          (∫ t in (0 : ℝ)..u, 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2)) :=
        intervalIntegral.integral_mono_on h0u (hg_int 0 u) hh_int
          (fun t ht => hpoint_le t (hne_on t ht))
      refine hle2.trans ?_
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hF_deriv t (hne_on t (by rwa [Set.uIcc_of_le h0u] at ht))) hh_int]
      have hc_pos : 0 < c := by linarith
      have hcalc : -(4 / (Nat.totient q : ℝ) ^ 2) * (u - c)⁻¹ -
          -(4 / (Nat.totient q : ℝ) ^ 2) * (0 - c)⁻¹ =
          4 / ((Nat.totient q : ℝ) ^ 2 * r) - 4 / ((Nat.totient q : ℝ) ^ 2 * c) := by
        have hdiff : c - r - c = -r := by ring
        rw [hu_eq, hdiff, zero_sub]
        field_simp [hphi.ne', hr.ne', hc_pos.ne'] <;> ring
      rw [hcalc]
      have hsub_nonneg : 0 ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * c) := by positivity
      linarith
  have hright : (∫ t in v..1, E.indicator g t) ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * r) := by
    have hle1 : (∫ t in v..1, E.indicator g t) ≤ (∫ t in v..1, g t) := by
      refine intervalIntegral.integral_mono_on hv1 (hEg_int v 1) (hg_int v 1) (fun t _ => ?_)
      by_cases ht : t ∈ E
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        exact peak_nonneg n q a t
    refine hle1.trans ?_
    by_cases hv_eq1 : v = 1
    · rw [hv_eq1, intervalIntegral.integral_same]
      positivity
    · have hv_lt : v < 1 := lt_of_le_of_ne hv1 hv_eq1
      have hv_eq : v = c + r := by
        dsimp [v] at hv_lt ⊢
        exact min_eq_right (le_of_lt ((min_lt_iff.mp hv_lt).resolve_left (lt_irrefl 1)))
      have hne_on : ∀ t ∈ Set.Icc v (1 : ℝ), t - c ≠ 0 := by
        intro t ht; linarith [ht.1]
      have hh_cont : ContinuousOn (fun t : ℝ => 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2))
          (Set.Icc v 1) := by
        refine continuousOn_const.div ?_ (fun t ht => ?_)
        · exact continuousOn_const.mul
            ((continuousOn_id.sub continuousOn_const).pow 2)
        · exact mul_ne_zero (pow_ne_zero 2 hphi.ne') (pow_ne_zero 2 (hne_on t ht))
      have hh_int : IntervalIntegrable
          (fun t : ℝ => 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2)) MeasureTheory.volume v 1 :=
        hh_cont.intervalIntegrable_of_Icc hv1
      have hle2 : (∫ t in v..1, g t) ≤
          (∫ t in v..1, 4 / ((Nat.totient q : ℝ) ^ 2 * (t - c) ^ 2)) :=
        intervalIntegral.integral_mono_on hv1 (hg_int v 1) hh_int
          (fun t ht => hpoint_le t (hne_on t ht))
      refine hle2.trans ?_
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hF_deriv t (hne_on t (by rwa [Set.uIcc_of_le hv1] at ht))) hh_int]
      have h1mc_pos : 0 < 1 - c := by linarith
      have hcalc : -(4 / (Nat.totient q : ℝ) ^ 2) * (1 - c)⁻¹ -
          -(4 / (Nat.totient q : ℝ) ^ 2) * (v - c)⁻¹ =
          4 / ((Nat.totient q : ℝ) ^ 2 * r) - 4 / ((Nat.totient q : ℝ) ^ 2 * (1 - c)) := by
        have hdiff : c + r - c = r := by ring
        rw [hv_eq, hdiff]
        field_simp [hphi.ne', hr.ne', h1mc_pos.ne'] <;> ring
      rw [hcalc]
      have hsub_nonneg : 0 ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * (1 - c)) := by positivity
      linarith
  rw [hsplit1, hsplit2, hmid, zero_add]
  calc
    _ ≤ 4 / ((Nat.totient q : ℝ) ^ 2 * r) + 4 / ((Nat.totient q : ℝ) ^ 2 * r) :=
      by exact add_le_add hleft hright
    _ = _ := by rw [← add_div]; norm_num

private lemma card_coprime_range_succ_le (q : ℕ) (hq : 1 ≤ q) :
    ((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card ≤ 2 * Nat.totient q := by
  have hsub : (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) ⊆
      (Finset.range q).filter (fun a => Nat.Coprime q a) ∪ {q} := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha.1 with hlt | rfl
    · exact Or.inl ⟨hlt, ha.2.symm⟩
    · exact Or.inr rfl
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le ((Finset.range q).filter (fun a => Nat.Coprime q a)) {q}
  have hphi : ((Finset.range q).filter (fun a => Nat.Coprime q a)).card = Nat.totient q := rfl
  have hphi_pos : 1 ≤ Nat.totient q := Nat.totient_pos.mpr (by omega)
  simp only [Finset.card_singleton] at hunion
  omega

private lemma coprime_frac_sep {q a q0 a0 : ℕ} (hq : 1 ≤ q) (hq0 : 1 ≤ q0)
    (hcop : Nat.Coprime a q) (hcop0 : Nat.Coprime a0 q0) (hne : ¬ (q = q0 ∧ a = a0)) :
    1 / ((q : ℝ) * (q0 : ℝ)) ≤ |(a : ℝ) / (q : ℝ) - (a0 : ℝ) / (q0 : ℝ)| := by
  have hne_mul : a * q0 ≠ a0 * q := by
    intro heq
    have hq_dvd : q ∣ q0 := hcop.symm.dvd_of_dvd_mul_left ⟨a0, by linarith⟩
    have hq0_dvd : q0 ∣ q := hcop0.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
    have hqq0 : q = q0 := Nat.dvd_antisymm hq_dvd hq0_dvd
    subst hqq0
    have haa0 : a = a0 := Nat.eq_of_mul_eq_mul_right (by omega) heq
    exact hne ⟨rfl, haa0⟩
  have hdiff : (1 : ℝ) ≤ |(a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hne_mul with hlt | hgt
    · have h1 : ((a * q0 + 1 : ℕ) : ℝ) ≤ ((a0 * q : ℕ) : ℝ) := Nat.cast_le.mpr hlt
      push_cast at h1
      calc (1 : ℝ) ≤ -((a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ)) := by linarith
        _ ≤ |(a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ)| := neg_le_abs _
    · have h1 : ((a0 * q + 1 : ℕ) : ℝ) ≤ ((a * q0 : ℕ) : ℝ) := Nat.cast_le.mpr hgt
      push_cast at h1
      calc (1 : ℝ) ≤ (a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ) := by linarith
        _ ≤ |(a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ)| := le_abs_self _
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq0_pos : (0 : ℝ) < (q0 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmul_pos : (0 : ℝ) < (q : ℝ) * (q0 : ℝ) := mul_pos hq_pos hq0_pos
  have hsub : (a : ℝ) / (q : ℝ) - (a0 : ℝ) / (q0 : ℝ) =
      ((a : ℝ) * (q0 : ℝ) - (a0 : ℝ) * (q : ℝ)) / ((q : ℝ) * (q0 : ℝ)) := by
    field_simp
  rw [hsub, abs_div, abs_of_pos hmul_pos]
  exact div_le_div_of_nonneg_right hdiff hmul_pos.le

private lemma off_diag_peak_le {n Q q a q0 a0 : ℕ} {t : ℝ}
    (hn : 1 ≤ n) (hQ : 1 ≤ Q) (hQn : 2 * Q ^ 6 ≤ n)
    (hq : 1 ≤ q) (hq_le : q ≤ Q ^ 2) (hq0 : 1 ≤ q0) (hq0_le : q0 ≤ Q ^ 2)
    (hcop : Nat.Coprime a q) (hcop0 : Nat.Coprime a0 q0) (hne : ¬ (q = q0 ∧ a = a0))
    (ht : |t - (a0 : ℝ) / (q0 : ℝ)| ≤ ((Q : ℝ) ^ 2) / ((q0 : ℝ) * (n : ℝ))) :
    4 * (n : ℝ) ^ 2 /
      ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)) ≤
      16 * (Q : ℝ) ^ 8 := by
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq0_pos : (0 : ℝ) < (q0 : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsep := coprime_frac_sep hq hq0 hcop hcop0 hne
  have hqq0_le : (q : ℝ) * (q0 : ℝ) ≤ (Q : ℝ) ^ 4 := by
    have h1 : (q : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hq_le
    have h2 : (q0 : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hq0_le
    nlinarith
  have hsep2 : 1 / (Q : ℝ) ^ 4 ≤ |(a : ℝ) / (q : ℝ) - (a0 : ℝ) / (q0 : ℝ)| :=
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hq_pos hq0_pos) hqq0_le).trans hsep
  have hwin : |t - (a0 : ℝ) / (q0 : ℝ)| ≤ 1 / (2 * (Q : ℝ) ^ 4) := by
    have h1 : ((Q : ℝ) ^ 2) / ((q0 : ℝ) * (n : ℝ)) ≤ ((Q : ℝ) ^ 2) / (n : ℝ) := by
      refine div_le_div_of_nonneg_left (by positivity) hn_pos ?_
      have hq0_ge : (1 : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hq0
      nlinarith
    have h2 : ((Q : ℝ) ^ 2) / (n : ℝ) ≤ 1 / (2 * (Q : ℝ) ^ 4) := by
      rw [div_le_div_iff₀ hn_pos (by positivity)]
      have hQn_r : 2 * (Q : ℝ) ^ 6 ≤ (n : ℝ) := by exact_mod_cast hQn
      nlinarith
    exact ht.trans (h1.trans h2)
  have htri : |(a : ℝ) / (q : ℝ) - (a0 : ℝ) / (q0 : ℝ)| ≤
      |t - (a0 : ℝ) / (q0 : ℝ)| + |t - (a : ℝ) / (q : ℝ)| := by
    have heq : (a : ℝ) / (q : ℝ) - (a0 : ℝ) / (q0 : ℝ) =
        (t - (a0 : ℝ) / (q0 : ℝ)) - (t - (a : ℝ) / (q : ℝ)) := by ring
    rw [heq]
    exact abs_sub _ _
  have hdist : 1 / (2 * (Q : ℝ) ^ 4) ≤ |t - (a : ℝ) / (q : ℝ)| := by
    have : 1 / (Q : ℝ) ^ 4 - 1 / (2 * (Q : ℝ) ^ 4) = 1 / (2 * (Q : ℝ) ^ 4) := by
      field_simp; ring
    linarith
  have hdist_sq : (1 / (2 * (Q : ℝ) ^ 4)) ^ 2 ≤ (t - (a : ℝ) / (q : ℝ)) ^ 2 := by
    rw [← sq_abs (t - (a : ℝ) / (q : ℝ))]
    exact pow_le_pow_left₀ (by positivity) hdist 2
  have hden_ge : (n : ℝ) ^ 2 / (4 * (Q : ℝ) ^ 8) ≤
      (Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2) := by
    have hphi1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hphi_sq : (1 : ℝ) ≤ (Nat.totient q : ℝ) ^ 2 := by nlinarith
    have hmul : (n : ℝ) ^ 2 / (4 * (Q : ℝ) ^ 8) ≤
        ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2 := by
      have h1 : (n : ℝ) ^ 2 * (1 / (2 * (Q : ℝ) ^ 4)) ^ 2 ≤
          (n : ℝ) ^ 2 * (t - (a : ℝ) / (q : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hdist_sq (by positivity)
      have heq1 : (n : ℝ) ^ 2 * (1 / (2 * (Q : ℝ) ^ 4)) ^ 2 =
          (n : ℝ) ^ 2 / (4 * (Q : ℝ) ^ 8) := by ring
      rw [heq1, ← mul_pow] at h1
      exact h1
    nlinarith
  have hrew : 16 * (Q : ℝ) ^ 8 =
      4 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 / (4 * (Q : ℝ) ^ 8)) := by
    field_simp
    ring
  rw [hrew]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge

private lemma geom_sum_le_div_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (e : ℕ) :
    ∑ k ∈ Finset.range e, r ^ k ≤ 1 / (1 - r) := by
  have hmul : (1 - r) * ∑ k ∈ Finset.range e, r ^ k = 1 - r ^ e := by
    induction e with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  have h1r : 0 < 1 - r := by linarith
  rw [le_div_iff₀ h1r, mul_comm]
  have hrpow : 0 ≤ r ^ e := pow_nonneg hr0 e
  linarith

private lemma prime_pow_sum_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (e : ℕ) :
    ∑ k ∈ Finset.range (e + 1), Real.sqrt ((p ^ k : ℕ) : ℝ) / (Nat.totient (p ^ k) : ℝ) ≤
      1 + 5 / Real.sqrt (p : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.cast_one, Real.sqrt_one, Nat.totient_one, div_one]
  set s : ℝ := Real.sqrt (p : ℝ)
  have hp_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs_sq : s ^ 2 = (p : ℝ) := Real.sq_sqrt (by linarith)
  have hs_ge : (3 : ℝ) / 2 ≤ s := by nlinarith
  have hsqrt_pow (k : ℕ) : Real.sqrt ((p : ℝ) ^ k) = s ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      change Real.sqrt ((p : ℝ) ^ k * (p : ℝ)) = s ^ k * s
      rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg p) k), ih]
  have hterm : ∀ k : ℕ,
      Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ) / (Nat.totient (p ^ (k + 1)) : ℝ) =
        (s / ((p : ℝ) - 1)) * (1 / s) ^ k := by
    intro k
    rw [Nat.totient_prime_pow hp (Nat.succ_pos k)]
    rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    rw [hsqrt_pow]
    change s ^ (k + 1) / ((p : ℝ) ^ k * ((p : ℝ) - 1)) = (s / ((p : ℝ) - 1)) * (1 / s) ^ k
    rw [← hs_sq, pow_succ, one_div, inv_pow]
    have hsk : s ^ k ≠ 0 := pow_ne_zero k hs_pos.ne'
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hsq : (s ^ 2) ^ k = s ^ k * s ^ k := by
      rw [← pow_mul, mul_comm 2 k, pow_mul, sq]
    rw [hsq]
    field_simp
  have hsum_eq :
      ∑ k ∈ Finset.range e,
        Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ) / (Nat.totient (p ^ (k + 1)) : ℝ) =
      (s / ((p : ℝ) - 1)) * ∑ k ∈ Finset.range e, (1 / s) ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum_eq]
  have hr0 : 0 ≤ 1 / s := by positivity
  have hr1 : 1 / s < 1 := by
    rw [div_lt_one hs_pos]
    linarith
  have hgeom := geom_sum_le_div_one_sub hr0 hr1 e
  have hcoef_nonneg : 0 ≤ s / ((p : ℝ) - 1) := div_nonneg hs_pos.le (by linarith)
  have hle1 : (s / ((p : ℝ) - 1)) * ∑ k ∈ Finset.range e, (1 / s) ^ k ≤
      (s / ((p : ℝ) - 1)) * (1 / (1 - 1 / s)) :=
    mul_le_mul_of_nonneg_left hgeom hcoef_nonneg
  have hle2 : (s / ((p : ℝ) - 1)) * (1 / (1 - 1 / s)) ≤ 5 / s := by
    have h1ms : 0 < 1 - 1 / s := by linarith
    have hsm1 : 0 < s - 1 := by linarith
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have hrew : (s / ((p : ℝ) - 1)) * (1 / (1 - 1 / s)) =
        (p : ℝ) / (((p : ℝ) - 1) * (s - 1)) := by
      have : 1 - 1 / s = (s - 1) / s := by field_simp
      rw [this]
      field_simp
      rw [hs_sq]
    rw [hrew, div_le_div_iff₀ (mul_pos hp1 hsm1) hs_pos]
    nlinarith
  linarith

private lemma split_prime_pow {p M : ℕ} (hp : p.Prime) (hM : 0 < M) (hdvd : p ∣ M) :
    ∃ e M', 1 ≤ e ∧ M = p ^ e * M' ∧ ¬ (p ∣ M') ∧ 0 < M' ∧ M' < M := by
  induction M using Nat.strongRecOn with
  | ind M ih =>
    rcases hdvd with ⟨k, rfl⟩
    have hk_pos : 0 < k := Nat.pos_of_mul_pos_left hM
    have hk_lt : k < p * k := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    by_cases hpk : p ∣ k
    · obtain ⟨e, M', he, hk_eq, hndvd, hM'_pos, hM'_lt⟩ := ih k hk_lt hk_pos hpk
      refine ⟨e + 1, M', by omega, ?_, hndvd, hM'_pos, lt_trans hM'_lt hk_lt⟩
      rw [hk_eq, pow_succ', mul_assoc]
    · exact ⟨1, k, le_rfl, by simp, hpk, hk_pos, hk_lt⟩

private lemma sum_divisors_sqrt_div_totient_le {M : ℕ} (hM : 0 < M) (hodd : Odd M) :
    ∑ q ∈ M.divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ) ≤
      ∏ p ∈ M.primeFactors, (1 + 5 / Real.sqrt (p : ℝ)) := by
  induction M using Nat.strongRecOn with
  | ind M ih =>
    by_cases hM1 : M = 1
    · subst hM1
      simp [Nat.totient_one]
    · set p : ℕ := M.minFac
      have hp : p.Prime := Nat.minFac_prime hM1
      have hp_dvd : p ∣ M := Nat.minFac_dvd M
      have hp_ne2 : p ≠ 2 := by
        intro hp2
        have h2M : 2 ∣ M := hp2 ▸ hp_dvd
        rcases hodd with ⟨r, hr⟩
        rcases h2M with ⟨s, hs⟩
        omega
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      obtain ⟨e, M', he, hM_eq, hndvd, hM'_pos, hM'_lt⟩ := split_prime_pow hp hM hp_dvd
      have hM'_odd : Odd M' := by
        rcases Nat.even_or_odd M' with ⟨r, hr⟩ | ho
        · exfalso
          rcases hodd with ⟨s, hs⟩
          have : 2 ∣ M := by
            rw [hM_eq, hr]
            exact ⟨p ^ e * r, by ring⟩
          rcases this with ⟨t, ht⟩
          omega
        · exact ho
      have hcop_p : Nat.Coprime p M' := hp.coprime_iff_not_dvd.mpr hndvd
      have hcop_pe : Nat.Coprime (p ^ e) M' := hcop_p.pow_left e
      set g : ℕ → ℝ := fun q => Real.sqrt (q : ℝ) / (Nat.totient q : ℝ)
      have hsub : M.divisors ⊆
          ((Finset.range (e + 1)) ×ˢ M'.divisors).image (fun x => p ^ x.1 * x.2) := by
        intro q hq
        rw [Nat.mem_divisors] at hq
        have hq_dvd : q ∣ p ^ e * M' := hM_eq ▸ hq.1
        set a := Nat.gcd q (p ^ e)
        set d := Nat.gcd q M'
        have ha_dvd_q : a ∣ q := Nat.gcd_dvd_left q (p ^ e)
        have ha_dvd_pe : a ∣ p ^ e := Nat.gcd_dvd_right q (p ^ e)
        have hd_dvd_q : d ∣ q := Nat.gcd_dvd_left q M'
        have hd_dvd_M' : d ∣ M' := Nat.gcd_dvd_right q M'
        have hcop_ad : Nat.Coprime a d :=
          (hcop_pe.coprime_dvd_left ha_dvd_pe).coprime_dvd_right hd_dvd_M'
        have had_dvd_q : a * d ∣ q := hcop_ad.mul_dvd_of_dvd_of_dvd ha_dvd_q hd_dvd_q
        have hq_dvd_ad : q ∣ a * d := by
          have ha_pos : 0 < a := Nat.gcd_pos_of_pos_right q (pow_pos hp.pos e)
          have hcop_div : Nat.Coprime (q / a) (p ^ e / a) := Nat.coprime_div_gcd_div_gcd ha_pos
          have hq_eq : a * (q / a) = q := Nat.mul_div_cancel' ha_dvd_q
          have hpe_eq : a * (p ^ e / a) = p ^ e := Nat.mul_div_cancel' ha_dvd_pe
          have hdvd_mul : q / a ∣ (p ^ e / a) * M' := by
            have : a * (q / a) ∣ a * ((p ^ e / a) * M') := by
              rw [hq_eq, ← mul_assoc, hpe_eq]
              exact hq_dvd
            exact (Nat.mul_dvd_mul_iff_left ha_pos).mp this
          have hqa_dvd_M' : q / a ∣ M' := hcop_div.dvd_of_dvd_mul_left hdvd_mul
          have hqa_dvd_q : q / a ∣ q := ⟨a, by rw [mul_comm, hq_eq]⟩
          have hqa_dvd_d : q / a ∣ d := Nat.dvd_gcd hqa_dvd_q hqa_dvd_M'
          rw [← hq_eq]
          exact Nat.mul_dvd_mul_left a hqa_dvd_d
        have hq_eq_ad : q = a * d := Nat.dvd_antisymm hq_dvd_ad had_dvd_q
        obtain ⟨k, hk_le, ha_eq⟩ := (Nat.dvd_prime_pow hp).mp ha_dvd_pe
        rw [Finset.mem_image]
        refine ⟨(k, d), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Nat.mem_divisors.mpr ⟨hd_dvd_M', by omega⟩⟩, ?_⟩
        dsimp
        rw [← ha_eq, hq_eq_ad]
      have hinj : Set.InjOn (fun x : ℕ × ℕ => p ^ x.1 * x.2)
          (((Finset.range (e + 1)) ×ˢ M'.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro x hx y hy hxy
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
          Nat.mem_divisors] at hx hy
        have hnd1 : ¬ (p ∣ x.2) := fun h => hndvd (dvd_trans h hx.2.1)
        have hnd2 : ¬ (p ∣ y.2) := fun h => hndvd (dvd_trans h hy.2.1)
        have hk_eq : x.1 = y.1 := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · have h1 : p ^ x.1 * x.2 = p ^ x.1 * (p ^ (y.1 - x.1) * y.2) := by
              rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
              exact hxy
            have h2 : x.2 = p ^ (y.1 - x.1) * y.2 :=
              Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos x.1) h1
            have hp_dvd_x2 : p ∣ x.2 := by
              rw [h2]
              exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) y.2
            exact hnd1 hp_dvd_x2
          · have h1 : p ^ y.1 * y.2 = p ^ y.1 * (p ^ (x.1 - y.1) * x.2) := by
              rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_of_lt hgt)]
              exact hxy.symm
            have h2 : y.2 = p ^ (x.1 - y.1) * x.2 :=
              Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos y.1) h1
            have hp_dvd_y2 : p ∣ y.2 := by
              rw [h2]
              exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) x.2
            exact hnd2 hp_dvd_y2
        have hd_eq : x.2 = y.2 := by
          change p ^ x.1 * x.2 = p ^ y.1 * y.2 at hxy
          rw [hk_eq] at hxy
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos y.1) hxy
        exact Prod.ext hk_eq hd_eq
      have hsum_le : ∑ q ∈ M.divisors, g q ≤
          (∑ k ∈ Finset.range (e + 1), g (p ^ k)) * (∑ d ∈ M'.divisors, g d) := by
        calc ∑ q ∈ M.divisors, g q
            ≤ ∑ q ∈ ((Finset.range (e + 1)) ×ˢ M'.divisors).image (fun x => p ^ x.1 * x.2), g q :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by dsimp [g]; positivity)
          _ = ∑ x ∈ (Finset.range (e + 1)) ×ˢ M'.divisors, g (p ^ x.1 * x.2) :=
              Finset.sum_image hinj
          _ = ∑ x ∈ (Finset.range (e + 1)) ×ˢ M'.divisors, g (p ^ x.1) * g x.2 := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [Finset.mem_product] at hx
              have hd_dvd : x.2 ∣ M' := (Nat.mem_divisors.mp hx.2).1
              have hcop_x : Nat.Coprime (p ^ x.1) x.2 :=
                (hcop_p.pow_left x.1).coprime_dvd_right hd_dvd
              dsimp [g]
              rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Nat.totient_mul hcop_x,
                Nat.cast_mul, div_mul_div_comm]
          _ = (∑ k ∈ Finset.range (e + 1), g (p ^ k)) * (∑ d ∈ M'.divisors, g d) := by
              rw [Finset.sum_product, Finset.sum_mul_sum]
      have hpf : M.primeFactors = insert p M'.primeFactors := by
        ext r
        simp only [Nat.mem_primeFactors, Finset.mem_insert, ne_eq]
        constructor
        · rintro ⟨hr, hr_dvd, -⟩
          rw [hM_eq] at hr_dvd
          rcases hr.dvd_mul.mp hr_dvd with h1 | h2
          · left
            exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h1)
          · right
            exact ⟨hr, h2, by omega⟩
        · rintro (rfl | ⟨hr, hr_dvd, -⟩)
          · exact ⟨hp, hp_dvd, by omega⟩
          · exact ⟨hr, hM_eq ▸ dvd_mul_of_dvd_right hr_dvd _, by omega⟩
      have hp_notin : p ∉ M'.primeFactors := by
        rw [Nat.mem_primeFactors]
        intro h
        exact hndvd h.2.1
      rw [hpf, Finset.prod_insert hp_notin]
      have h1 := prime_pow_sum_le hp hp3 e
      have h2 := ih M' hM'_lt hM'_pos hM'_odd
      have hsum1_nn : 0 ≤ ∑ k ∈ Finset.range (e + 1), g (p ^ k) :=
        Finset.sum_nonneg (fun _ _ => by dsimp [g]; positivity)
      have hsum2_nn : 0 ≤ ∑ d ∈ M'.divisors, g d :=
        Finset.sum_nonneg (fun _ _ => by dsimp [g]; positivity)
      exact hsum_le.trans (mul_le_mul h1 h2 hsum2_nn (by positivity))

private lemma sum_inv_sqrt_Icc_le (P : ℕ) :
    ∑ k ∈ Finset.Icc 1 P, 1 / Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt (P : ℝ) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ P + 1)]
    have hP1_pos : 0 < Real.sqrt ((P + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos P))
    have hstep : 2 * Real.sqrt (P : ℝ) + 1 / Real.sqrt ((P + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((P + 1 : ℕ) : ℝ) := by
      have hsq1 : Real.sqrt (P : ℝ) ^ 2 = (P : ℝ) := Real.sq_sqrt (Nat.cast_nonneg P)
      have hsq2 : Real.sqrt ((P + 1 : ℕ) : ℝ) ^ 2 = (P : ℝ) + 1 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg (P + 1)), Nat.cast_succ]
      have hmul : 2 * Real.sqrt (P : ℝ) * Real.sqrt ((P + 1 : ℕ) : ℝ) + 1 ≤
          2 * Real.sqrt ((P + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt ((P + 1 : ℕ) : ℝ) - Real.sqrt (P : ℝ))]
      have hdiv := (div_le_div_of_nonneg_right hmul hP1_pos.le)
      have hL : (2 * Real.sqrt (P : ℝ) * Real.sqrt ((P + 1 : ℕ) : ℝ) + 1) /
          Real.sqrt ((P + 1 : ℕ) : ℝ) =
          2 * Real.sqrt (P : ℝ) + 1 / Real.sqrt ((P + 1 : ℕ) : ℝ) := by
        field_simp
      have hR : 2 * Real.sqrt ((P + 1 : ℕ) : ℝ) ^ 2 / Real.sqrt ((P + 1 : ℕ) : ℝ) =
          2 * Real.sqrt ((P + 1 : ℕ) : ℝ) := by
        field_simp
      linarith
    linarith

private lemma prod_primes_dvd_of_dvd {M : ℕ} (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, p ∣ M) :
    (∏ p ∈ s, p) ∣ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hp_prime : p.Prime := hprime p (Finset.mem_insert_self p s)
    have hp_dvd : p ∣ M := hdvd p (Finset.mem_insert_self p s)
    have hs_dvd : (∏ q ∈ s, q) ∣ M :=
      ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
         (fun q hq => hdvd q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      have hq_prime : q.Prime := hprime q (Finset.mem_insert_of_mem hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr (fun heq => hp (heq ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd hp_dvd hs_dvd

private lemma sum_divisors_le_exp {M J m : ℕ} (hM_pos : 0 < M) (hM_odd : Odd M)
    (hM_lt : M < 2 ^ J) (hm : 1 ≤ m) :
    ∑ q ∈ M.divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ) ≤
      Real.exp (10 * (2 : ℝ) ^ m + 5 * (J : ℝ) / (2 * (m : ℝ) * (2 : ℝ) ^ m)) := by
  have h1 := sum_divisors_sqrt_div_totient_le hM_pos hM_odd
  have h2 : ∏ p ∈ M.primeFactors, (1 + 5 / Real.sqrt (p : ℝ)) ≤
      Real.exp (∑ p ∈ M.primeFactors, 5 / Real.sqrt (p : ℝ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
    linarith [Real.add_one_le_exp (5 / Real.sqrt (p : ℝ))]
  refine h1.trans (h2.trans (Real.exp_le_exp.mpr ?_))
  set P : ℕ := 2 ^ (2 * m)
  have hP_sqrt : Real.sqrt (P : ℝ) = (2 : ℝ) ^ m := by
    have hP_eq : (P : ℝ) = ((2 : ℝ) ^ m) ^ 2 := by
      dsimp [P]
      push_cast
      rw [← pow_mul, mul_comm 2 m]
    rw [hP_eq, Real.sqrt_sq (by positivity)]
  rw [← Finset.sum_filter_add_sum_filter_not M.primeFactors (fun p => p ≤ P)]
  have hle_part :
      ∑ p ∈ M.primeFactors.filter (fun p => p ≤ P), 5 / Real.sqrt (p : ℝ) ≤
        10 * (2 : ℝ) ^ m := by
    have hsub : M.primeFactors.filter (fun p => p ≤ P) ⊆ Finset.Icc 1 P := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact Finset.mem_Icc.mpr ⟨hp.1.1.one_lt.le, hp.2⟩
    have hsum1 :
        ∑ p ∈ M.primeFactors.filter (fun p => p ≤ P), 5 / Real.sqrt (p : ℝ) ≤
        ∑ k ∈ Finset.Icc 1 P, 5 / Real.sqrt (k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hfactor :
        ∑ k ∈ Finset.Icc 1 P, 5 / Real.sqrt (k : ℝ) =
        5 * ∑ k ∈ Finset.Icc 1 P, 1 / Real.sqrt (k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [hfactor] at hsum1
    have hIcc := sum_inv_sqrt_Icc_le P
    rw [hP_sqrt] at hIcc
    linarith
  have hgt_part :
      ∑ p ∈ M.primeFactors.filter (fun p => ¬ p ≤ P), 5 / Real.sqrt (p : ℝ) ≤
        5 * (J : ℝ) / (2 * (m : ℝ) * (2 : ℝ) ^ m) := by
    set Sgt := M.primeFactors.filter (fun p => ¬ p ≤ P)
    have hprod_dvd : (∏ p ∈ Sgt, p) ∣ M := by
      refine prod_primes_dvd_of_dvd Sgt ?_ ?_
      · intro p hp
        exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
      · intro p hp
        exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
    have hprod_le : ∏ p ∈ Sgt, p ≤ M := Nat.le_of_dvd hM_pos hprod_dvd
    have hP_pow_le : P ^ Sgt.card ≤ ∏ p ∈ Sgt, p := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod' (fun p hp => ?_)
      have := (Finset.mem_filter.mp hp).2
      omega
    have h2_lt : 2 ^ (2 * m * Sgt.card) < 2 ^ J := by
      have : 2 ^ (2 * m * Sgt.card) = P ^ Sgt.card := by
        dsimp [P]; rw [pow_mul]
      rw [this]
      exact lt_of_le_of_lt (hP_pow_le.trans hprod_le) hM_lt
    have hcard_nat : 2 * m * Sgt.card < J :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2_lt
    have hcard_r : (Sgt.card : ℝ) ≤ (J : ℝ) / (2 * (m : ℝ)) := by
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [le_div_iff₀ (by positivity)]
      have : ((2 * m * Sgt.card : ℕ) : ℝ) ≤ (J : ℝ) := Nat.cast_le.mpr (le_of_lt hcard_nat)
      push_cast at this
      linarith
    have hterm_le : ∀ p ∈ Sgt, 5 / Real.sqrt (p : ℝ) ≤ 5 / (2 : ℝ) ^ m := by
      intro p hp
      have hPp : P < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
      have hsqrt_le : (2 : ℝ) ^ m ≤ Real.sqrt (p : ℝ) := by
        rw [← hP_sqrt]
        exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (le_of_lt hPp))
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt_le
    calc ∑ p ∈ Sgt, 5 / Real.sqrt (p : ℝ)
        ≤ ∑ _ ∈ Sgt, (5 / (2 : ℝ) ^ m) := Finset.sum_le_sum hterm_le
      _ = (Sgt.card : ℝ) * (5 / (2 : ℝ) ^ m) := by simp
      _ ≤ ((J : ℝ) / (2 * (m : ℝ))) * (5 / (2 : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_right hcard_r (by positivity)
      _ = 5 * (J : ℝ) / (2 * (m : ℝ) * (2 : ℝ) ^ m) := by ring
  linarith

private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hinter_nn : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b :=
      Finset.sum_nonneg (fun b _ => hf b)
    linarith

private lemma pow_20_le_two_pow {k : ℕ} (hk : 1000 ≤ k) : k ^ 20 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    calc (1000 : ℕ) ^ 20 ≤ (2 ^ 10) ^ 20 := Nat.pow_le_pow_left (by norm_num) 20
      _ = 2 ^ 200 := by rw [← pow_mul]
      _ ≤ 2 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    have hstep : (k + 1) ^ 20 ≤ 2 * k ^ 20 := by
      have h1 : ((k + 1) * 1000) ^ 20 ≤ (1001 * k) ^ 20 :=
        Nat.pow_le_pow_left (by omega) 20
      have h2 : (1001 : ℕ) ^ 20 ≤ 2 * 1000 ^ 20 := by norm_num
      have h3 : (k + 1) ^ 20 * 1000 ^ 20 ≤ (2 * k ^ 20) * 1000 ^ 20 := by
        calc (k + 1) ^ 20 * 1000 ^ 20 = ((k + 1) * 1000) ^ 20 := by rw [mul_pow]
          _ ≤ (1001 * k) ^ 20 := h1
          _ = 1001 ^ 20 * k ^ 20 := by rw [mul_pow]
          _ ≤ (2 * 1000 ^ 20) * k ^ 20 := Nat.mul_le_mul_right _ h2
          _ = (2 * k ^ 20) * 1000 ^ 20 := by ring
      exact Nat.le_of_mul_le_mul_right h3 (by positivity)
    calc (k + 1) ^ 20 ≤ 2 * k ^ 20 := hstep
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [pow_succ']

private lemma pow_32_le_two_pow_sub {k : ℕ} (hk : 1000 ≤ k) : k ^ 32 ≤ 2 ^ (k - 21) := by
  induction k, hk using Nat.le_induction with
  | base =>
    calc (1000 : ℕ) ^ 32 ≤ (2 ^ 10) ^ 32 := Nat.pow_le_pow_left (by norm_num) 32
      _ = 2 ^ 320 := by rw [← pow_mul]
      _ ≤ 2 ^ (1000 - 21) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    have hstep : (k + 1) ^ 32 ≤ 2 * k ^ 32 := by
      have h1 : ((k + 1) * 1000) ^ 32 ≤ (1001 * k) ^ 32 :=
        Nat.pow_le_pow_left (by omega) 32
      have h2 : (1001 : ℕ) ^ 32 ≤ 2 * 1000 ^ 32 := by norm_num
      have h3 : (k + 1) ^ 32 * 1000 ^ 32 ≤ (2 * k ^ 32) * 1000 ^ 32 := by
        calc (k + 1) ^ 32 * 1000 ^ 32 = ((k + 1) * 1000) ^ 32 := by rw [mul_pow]
          _ ≤ (1001 * k) ^ 32 := h1
          _ = 1001 ^ 32 * k ^ 32 := by rw [mul_pow]
          _ ≤ (2 * 1000 ^ 32) * k ^ 32 := Nat.mul_le_mul_right _ h2
          _ = (2 * k ^ 32) * 1000 ^ 32 := by ring
      exact Nat.le_of_mul_le_mul_right h3 (by positivity)
    have hsub : k + 1 - 21 = (k - 21) + 1 := by omega
    rw [hsub, pow_succ' 2 (k - 21)]
    exact hstep.trans (Nat.mul_le_mul_left 2 ih)

private lemma shortOrderThreshold :
    ∃ A B N : ℕ, 1000 ≤ A ∧ 100 * 2 ^ 6000 ≤ A ∧ B = 2 ^ A ∧ N = 2 ^ B := by
  let A : ℕ := 100 * 2 ^ 6000
  have hA : 1000 ≤ A := by
    calc
      1000 ≤ 2 ^ 10 := by decide
      _ ≤ 2 ^ 6000 := Nat.pow_le_pow_right (by decide) (by decide)
      _ = 1 * 2 ^ 6000 := by rw [one_mul]
      _ ≤ A := Nat.mul_le_mul_right _ (by decide)
  exact ⟨A, 2 ^ A, 2 ^ (2 ^ A), hA, le_rfl, rfl, rfl⟩

private lemma log_div_ge (k l : ℕ) (hl : 100 * 2 ^ k ≤ l) :
    k ≤ Nat.log 2 (l / 100) := by
  refine Nat.le_log_of_pow_le (by decide) ((Nat.le_div_iff_mul_le (by decide)).mpr ?_)
  exact (Nat.mul_comm (2 ^ k) 100).le.trans hl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 3000 in
theorem Conjectures.Goldbach.PacketShortOrderPeakOverlap :
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608 := by
  classical
  intro Q arcs L K B W o G m
  obtain ⟨A0, B0, N0, hA0_ge, hA0_large, hB0, hN0⟩ := shortOrderThreshold
  refine ⟨N0, ?_⟩
  intro n hn _heven
  have hk_ge_B0 : B0 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [← hN0]
    exact hn.trans (Nat.le_add_right n 2)
  have hB0_ge : 1000 ≤ B0 := by
    rw [hB0]
    calc
      1000 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ A0 := Nat.pow_le_pow_right (by norm_num) (by omega)
  set k : ℕ := Nat.log 2 (n + 2)
  have hk_ge : 1000 ≤ k := le_trans hB0_ge hk_ge_B0
  have hQ_eq : Q n = k ^ 2 := rfl
  have hQ_ge_pow : 2 ^ A0 ≤ Q n := by
    rw [hQ_eq]
    calc 2 ^ A0 ≤ (2 ^ A0) ^ 2 := Nat.le_self_pow (by norm_num) _
      _ = B0 ^ 2 := by rw [hB0]
      _ ≤ k ^ 2 := Nat.pow_le_pow_left hk_ge_B0 2
  have hQ_pos : 1 ≤ Q n := le_trans (Nat.one_le_pow A0 2 (by norm_num)) hQ_ge_pow
  set LQ : ℕ := Nat.log 2 (Q n) + 1
  have hLQ_ge_A0 : A0 ≤ LQ := by
    have hlogQ : A0 ≤ Nat.log 2 (Q n) := Nat.le_log_of_pow_le (by norm_num) hQ_ge_pow
    omega
  have hLQ_ge : 1000 ≤ LQ := le_trans hA0_ge hLQ_ge_A0
  have hn_ge_pow : 2 ^ (k - 1) ≤ n := by
    have h2k : 2 ^ k ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
    have h2km1 : 2 ^ (k - 1) * 2 = 2 ^ k := by
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
    have h2km1_ge : 2 ≤ 2 ^ (k - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hQn_big : 589824 * (Q n) ^ 16 ≤ n := by
    have hQ16 : (Q n) ^ 16 = k ^ 32 := by rw [hQ_eq, ← pow_mul]
    rw [hQ16]
    have h32 := pow_32_le_two_pow_sub hk_ge
    calc 589824 * k ^ 32 ≤ 2 ^ 20 * 2 ^ (k - 21) :=
          Nat.mul_le_mul (by norm_num) h32
      _ = 2 ^ (20 + (k - 21)) := by rw [← pow_add]
      _ = 2 ^ (k - 1) := by congr 1; omega
      _ ≤ n := hn_ge_pow
  have hn_pos : 1 ≤ n := by
    have : 1 ≤ (Q n) ^ 16 := one_le_pow₀ hQ_pos
    omega
  have h2Q6_le_n : 2 * (Q n) ^ 6 ≤ n := by
    have hQ6 : (Q n) ^ 6 ≤ (Q n) ^ 16 := Nat.pow_le_pow_right hQ_pos (by norm_num)
    omega
  -- Peak function and continuity/nonnegativity of G n
  set g : ℕ → ℕ → ℝ → ℝ := fun q a t =>
    4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))
  have hG_cont : Continuous (G n) := by
    dsimp only [G]
    refine continuous_finsetSum _ (fun q hq => continuous_finsetSum _ (fun a _ => ?_))
    exact peak_continuous n q a (Finset.mem_Icc.mp hq).1
  have hG_int : IntervalIntegrable (G n) MeasureTheory.volume 0 1 :=
    hG_cont.intervalIntegrable 0 1
  have hG_nonneg : ∀ t : ℝ, 0 ≤ G n t := fun t =>
    Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun a _ => peak_nonneg n q a t))
  -- Measurability of the target set S
  have hK_cont : Continuous (K n) := by
    dsimp only [K]
    have hcos : Continuous (fun t : ℝ => ∑ j ∈ Finset.range (L n),
        Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) :=
      continuous_finsetSum _ (fun _ _ => Real.continuous_cos.comp (continuous_const.mul continuous_id))
    exact hcos.div_const _
  have hB_meas : MeasurableSet (B n) := by
    change MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1 : ℝ) / 2 < K n t})
    exact (measurableSet_arcs n (Q n)).compl.inter
      (isOpen_lt continuous_const hK_cont).measurableSet
  have hS_meas : MeasurableSet ((B n ∩ W n (fun _ => True)) ∩ W n (o n)) :=
    (hB_meas.inter (measurableSet_W n (Q n) (fun _ => True))).inter
      (measurableSet_W n (Q n) (o n))
  -- Window sets E_win q0 a0
  set E_win : ℕ → ℕ → Set ℝ := fun q0 a0 =>
    (arcs n)ᶜ ∩ {t : ℝ | |t - (a0 : ℝ) / (q0 : ℝ)| ≤ ((Q n : ℝ) ^ 2) / ((q0 : ℝ) * (n : ℝ))}
  have hE_meas : ∀ q0 a0, MeasurableSet (E_win q0 a0) := fun q0 a0 =>
    (measurableSet_arcs n (Q n)).compl.inter (closed_ball_measurable _ _)
  set Q_ord : Finset ℕ := (Finset.Icc 1 ((Q n) ^ 2)).filter (o n)
  set A_set : ℕ → Finset ℕ := fun q => (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)
  -- Pointwise cover of S.indicator (G n) by sum over (q0, a0)
  have hcover : ∀ t : ℝ,
      ((B n ∩ W n (fun _ => True)) ∩ W n (o n)).indicator (G n) t ≤
      ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0, (E_win q0 a0).indicator (G n) t := by
    intro t
    by_cases ht : t ∈ (B n ∩ W n (fun _ => True)) ∩ W n (o n)
    · rw [Set.indicator_of_mem ht]
      have ht_arcs : t ∉ arcs n := ht.1.1.1
      obtain ⟨q0, a0, hq0_1, hq0_le, ha0_le, hcop0, ho0, hwin0⟩ := ht.2
      have hq0_mem : q0 ∈ Q_ord := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq0_1, hq0_le⟩, ho0⟩
      have ha0_mem : a0 ∈ A_set q0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcop0⟩
      have ht_E : t ∈ E_win q0 a0 := ⟨ht_arcs, hwin0⟩
      have hinner : G n t ≤ ∑ a0' ∈ A_set q0, (E_win q0 a0').indicator (G n) t := by
        have h1 := Finset.single_le_sum
          (f := fun a0' => (E_win q0 a0').indicator (G n) t)
          (fun a0' _ => Set.indicator_nonneg (fun _ _ => hG_nonneg _) t) ha0_mem
        rwa [Set.indicator_of_mem ht_E] at h1
      have houter := Finset.single_le_sum
        (f := fun q0' => ∑ a0' ∈ A_set q0', (E_win q0' a0').indicator (G n) t)
        (fun q0' _ => Finset.sum_nonneg (fun a0' _ =>
          Set.indicator_nonneg (fun _ _ => hG_nonneg _) t)) hq0_mem
      exact hinner.trans houter
    · simp only [Set.indicator, ht, ↓reduceIte]
      exact Finset.sum_nonneg (fun q0 _ => Finset.sum_nonneg (fun a0 _ =>
        Set.indicator_nonneg (fun _ _ => hG_nonneg _) t))
  -- Integrate the cover on [0, 1]
  have hinner_int (q0 : ℕ) : IntervalIntegrable
      (fun t : ℝ => ∑ a0 ∈ A_set q0, (E_win q0 a0).indicator (G n) t)
      MeasureTheory.volume 0 1 := by
    exact intervalIntegrable_finsetSum (A_set q0) fun a0 _ =>
      intervalIntegrable_indicator_of_measurable (hE_meas q0 a0) hG_int
  have hsum_int : IntervalIntegrable
      (fun t : ℝ => ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0, (E_win q0 a0).indicator (G n) t)
      MeasureTheory.volume 0 1 := by
    exact intervalIntegrable_finsetSum Q_ord fun q0 _ => hinner_int q0
  have hstep1 : m ((B n ∩ W n (fun _ => True)) ∩ W n (o n)) (G n) ≤
      ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
        intervalIntegral ((E_win q0 a0).indicator (G n)) (0 : ℝ) 1 MeasureTheory.volume := by
    dsimp [m]
    calc intervalIntegral (((B n ∩ W n (fun _ => True)) ∩ W n (o n)).indicator (G n))
            (0 : ℝ) 1 MeasureTheory.volume
        ≤ intervalIntegral
            (fun t => ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0, (E_win q0 a0).indicator (G n) t)
            (0 : ℝ) 1 MeasureTheory.volume :=
          intervalIntegral.integral_mono_on (by norm_num)
            (intervalIntegrable_indicator_of_measurable hS_meas hG_int) hsum_int
            (fun t _ => hcover t)
      _ = ∑ q0 ∈ Q_ord, intervalIntegral
            (fun t => ∑ a0 ∈ A_set q0, (E_win q0 a0).indicator (G n) t)
            (0 : ℝ) 1 MeasureTheory.volume :=
          intervalIntegral.integral_finsetSum (fun q0 _ => hinner_int q0)
      _ = ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
            intervalIntegral ((E_win q0 a0).indicator (G n)) (0 : ℝ) 1 MeasureTheory.volume := by
          refine Finset.sum_congr rfl (fun q0 _ => ?_)
          exact intervalIntegral.integral_finsetSum (fun a0 _ =>
            intervalIntegrable_indicator_of_measurable (hE_meas q0 a0) hG_int)
  -- Split each (E_win q0 a0).indicator (G n) into diagonal + off-diagonal constant 32 * Q^12
  have hdiag_off : ∀ q0 ∈ Q_ord, ∀ a0 ∈ A_set q0,
      intervalIntegral ((E_win q0 a0).indicator (G n)) (0 : ℝ) 1 MeasureTheory.volume ≤
        intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume +
          32 * (Q n : ℝ) ^ 12 := by
    intro q0 hq0 a0 ha0
    have hq0_Icc := (Finset.mem_filter.mp hq0).1
    have hq0_1 : 1 ≤ q0 := (Finset.mem_Icc.mp hq0_Icc).1
    have hq0_le : q0 ≤ (Q n) ^ 2 := (Finset.mem_Icc.mp hq0_Icc).2
    have ha0_f := Finset.mem_filter.mp ha0
    have hcop0 : Nat.Coprime a0 q0 := ha0_f.2
    have hpt : ∀ t : ℝ, (E_win q0 a0).indicator (G n) t ≤
        (E_win q0 a0).indicator (g q0 a0) t + 32 * (Q n : ℝ) ^ 12 := by
      intro t
      by_cases ht : t ∈ E_win q0 a0
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        have hG_split : G n t = g q0 a0 t +
            ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), ∑ a ∈ A_set q,
              (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) := by
          have hsub_eq :
              G n t - ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), ∑ a ∈ A_set q,
                (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) = g q0 a0 t := by
            dsimp [G]
            rw [← Finset.sum_sub_distrib]
            have hinner : ∀ q ∈ Finset.Icc 1 ((Q n) ^ 2),
                (∑ a ∈ A_set q, g q a t) -
                  (∑ a ∈ A_set q, if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) =
                if q = q0 then g q0 a0 t else 0 := by
              intro q _
              rw [← Finset.sum_sub_distrib]
              by_cases hqq : q = q0
              · subst hqq
                have : ∀ a ∈ A_set q,
                    g q a t - (if q = q ∧ a = a0 then (0 : ℝ) else g q a t) =
                    if a = a0 then g q a0 t else 0 := by
                  intro a _
                  by_cases haa : a = a0 <;> simp [haa]
                rw [Finset.sum_congr rfl this, Finset.sum_ite_eq', if_pos ha0, if_pos rfl]
              · have : ∀ a ∈ A_set q,
                    g q a t - (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) = 0 := by
                  intro a _
                  simp [hqq]
                rw [Finset.sum_congr rfl this, Finset.sum_const_zero, if_neg hqq]
            rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos hq0_Icc]
          linarith
        rw [hG_split]
        have hoff : ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), ∑ a ∈ A_set q,
            (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) ≤ 32 * (Q n : ℝ) ^ 12 := by
          have hinner_le : ∀ q ∈ Finset.Icc 1 ((Q n) ^ 2),
              ∑ a ∈ A_set q, (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) ≤
                2 * (Q n : ℝ) ^ 2 * (16 * (Q n : ℝ) ^ 8) := by
            intro q hq
            have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
            have hqle : q ≤ (Q n) ^ 2 := (Finset.mem_Icc.mp hq).2
            have hterm : ∀ a ∈ A_set q,
                (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t) ≤ 16 * (Q n : ℝ) ^ 8 := by
              intro a ha
              by_cases hqa : q = q0 ∧ a = a0
              · rw [if_pos hqa]; positivity
              · rw [if_neg hqa]
                exact off_diag_peak_le hn_pos hQ_pos h2Q6_le_n hq1 hqle hq0_1 hq0_le
                  (Finset.mem_filter.mp ha).2 hcop0 hqa ht.2
            calc ∑ a ∈ A_set q, (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t)
                ≤ ∑ _ ∈ A_set q, (16 * (Q n : ℝ) ^ 8) := Finset.sum_le_sum hterm
              _ = ((A_set q).card : ℝ) * (16 * (Q n : ℝ) ^ 8) := by simp
              _ ≤ (2 * (Q n : ℝ) ^ 2) * (16 * (Q n : ℝ) ^ 8) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  have hcard : (A_set q).card ≤ 2 * (Q n) ^ 2 := by
                    have h1 : (A_set q).card ≤ q + 1 := by
                      simpa [Finset.card_range] using
                        Finset.card_filter_le (Finset.range (q + 1)) (fun a => Nat.Coprime a q)
                    have hQ2_ge : 1 ≤ (Q n) ^ 2 := one_le_pow₀ hQ_pos
                    omega
                  exact_mod_cast hcard
          calc ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), ∑ a ∈ A_set q,
                (if q = q0 ∧ a = a0 then (0 : ℝ) else g q a t)
              ≤ ∑ _ ∈ Finset.Icc 1 ((Q n) ^ 2), (2 * (Q n : ℝ) ^ 2 * (16 * (Q n : ℝ) ^ 8)) :=
                Finset.sum_le_sum hinner_le
            _ = (((Finset.Icc 1 ((Q n) ^ 2)).card : ℝ)) *
                  (2 * (Q n : ℝ) ^ 2 * (16 * (Q n : ℝ) ^ 8)) := by simp
            _ = (Q n : ℝ) ^ 2 * (2 * (Q n : ℝ) ^ 2 * (16 * (Q n : ℝ) ^ 8)) := by
                have hc : (Finset.Icc 1 ((Q n) ^ 2)).card = (Q n) ^ 2 := by simp
                rw [hc]; push_cast; rfl
            _ = 32 * (Q n : ℝ) ^ 12 := by ring
        linarith
      · simp only [Set.indicator, ht, ↓reduceIte]
        positivity
    have hg0_int : IntervalIntegrable ((E_win q0 a0).indicator (g q0 a0))
        MeasureTheory.volume 0 1 :=
      intervalIntegrable_indicator_of_measurable (hE_meas q0 a0)
        ((peak_continuous n q0 a0 hq0_1).intervalIntegrable 0 1)
    have hconst_int : IntervalIntegrable (fun _ : ℝ => 32 * (Q n : ℝ) ^ 12)
        MeasureTheory.volume 0 1 := intervalIntegrable_const
    calc intervalIntegral ((E_win q0 a0).indicator (G n)) (0 : ℝ) 1 MeasureTheory.volume
        ≤ intervalIntegral (fun t => (E_win q0 a0).indicator (g q0 a0) t + 32 * (Q n : ℝ) ^ 12)
            (0 : ℝ) 1 MeasureTheory.volume :=
          intervalIntegral.integral_mono_on (by norm_num)
            (intervalIntegrable_indicator_of_measurable (hE_meas q0 a0) hG_int)
            (hg0_int.add hconst_int) (fun t _ => hpt t)
      _ = intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume +
            intervalIntegral (fun _ : ℝ => 32 * (Q n : ℝ) ^ 12) (0 : ℝ) 1 MeasureTheory.volume :=
          intervalIntegral.integral_add hg0_int hconst_int
      _ = intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume +
            32 * (Q n : ℝ) ^ 12 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  -- Combine hstep1 and hdiag_off into diagonal sum + off-diagonal sum
  have hstep2 :
      ∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
        intervalIntegral ((E_win q0 a0).indicator (G n)) (0 : ℝ) 1 MeasureTheory.volume ≤
      (∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
        intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume) +
      (∑ q0 ∈ Q_ord, ∑ _ ∈ A_set q0, (32 * (Q n : ℝ) ^ 12)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun q0 hq0 => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun a0 ha0 => hdiag_off q0 hq0 a0 ha0)
  -- Bound the off-diagonal sum by 64 * Q^16 ≤ n / 9216
  have hoff_total :
      (∑ q0 ∈ Q_ord, ∑ _ ∈ A_set q0, (32 * (Q n : ℝ) ^ 12)) ≤ (n : ℝ) / 9216 := by
    have h1 : (∑ q0 ∈ Q_ord, ∑ _ ∈ A_set q0, (32 * (Q n : ℝ) ^ 12)) ≤
        64 * (Q n : ℝ) ^ 16 := by
      have hinner : ∀ q0 ∈ Q_ord,
          (∑ _ ∈ A_set q0, (32 * (Q n : ℝ) ^ 12)) ≤
            2 * (Q n : ℝ) ^ 2 * (32 * (Q n : ℝ) ^ 12) := by
        intro q0 hq0
        have hq0_le : q0 ≤ (Q n) ^ 2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq0).1).2
        simp only [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hcard : (A_set q0).card ≤ 2 * (Q n) ^ 2 := by
          have h1 : (A_set q0).card ≤ q0 + 1 := by
            simpa [Finset.card_range] using
              Finset.card_filter_le (Finset.range (q0 + 1)) (fun a => Nat.Coprime a q0)
          have hQ2_ge : 1 ≤ (Q n) ^ 2 := one_le_pow₀ hQ_pos
          omega
        exact_mod_cast hcard
      calc (∑ q0 ∈ Q_ord, ∑ _ ∈ A_set q0, (32 * (Q n : ℝ) ^ 12))
          ≤ ∑ _ ∈ Q_ord, (2 * (Q n : ℝ) ^ 2 * (32 * (Q n : ℝ) ^ 12)) :=
            Finset.sum_le_sum hinner
        _ = (Q_ord.card : ℝ) * (2 * (Q n : ℝ) ^ 2 * (32 * (Q n : ℝ) ^ 12)) := by simp
        _ ≤ ((Q n : ℝ) ^ 2) * (2 * (Q n : ℝ) ^ 2 * (32 * (Q n : ℝ) ^ 12)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hcard : Q_ord.card ≤ (Q n) ^ 2 := by
              have h1 := Finset.card_filter_le (Finset.Icc 1 ((Q n) ^ 2)) (o n)
              simpa using h1
            exact_mod_cast hcard
        _ = 64 * (Q n : ℝ) ^ 16 := by ring
    have h2 : 64 * (Q n : ℝ) ^ 16 ≤ (n : ℝ) / 9216 := by
      have hQn_r : 589824 * (Q n : ℝ) ^ 16 ≤ (n : ℝ) := by exact_mod_cast hQn_big
      linarith
    exact h1.trans h2
  -- Bound each q0 diagonal contribution by 32 * n / sqrt(Q) * (sqrt(q0) / phi(q0))
  have hdiag_q0 : ∀ q0 ∈ Q_ord,
      (∑ a0 ∈ A_set q0,
        intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume) ≤
      (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * (Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) := by
    intro q0 hq0
    have hq0_Icc := (Finset.mem_filter.mp hq0).1
    have hq0_1 : 1 ≤ q0 := (Finset.mem_Icc.mp hq0_Icc).1
    have hphi_pos : (0 : ℝ) < (Nat.totient q0 : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    have hQ_r_pos : (0 : ℝ) < (Q n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hq0_r_pos : (0 : ℝ) < (q0 : ℝ) := Nat.cast_pos.mpr (by omega)
    have hcard_a : ((A_set q0).card : ℝ) ≤ 2 * (Nat.totient q0 : ℝ) := by
      exact_mod_cast card_coprime_range_succ_le q0 hq0_1
    by_cases hq0_small : q0 ≤ Q n
    · -- Case B: 1 ≤ q0 ≤ Q n, use tail integral
      have hterm : ∀ a0 ∈ A_set q0,
          intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume ≤
            8 * (q0 : ℝ) * (n : ℝ) / ((Nat.totient q0 : ℝ) ^ 2 * (Q n : ℝ)) := by
        intro a0 ha0
        have ha0_f := Finset.mem_filter.mp ha0
        have ha0_le : a0 ≤ q0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha0_f.1)
        have hcop0 : Nat.Coprime a0 q0 := ha0_f.2
        set r : ℝ := (Q n : ℝ) / ((q0 : ℝ) * (n : ℝ))
        have hr_pos : 0 < r := by positivity
        have hE_sub : ∀ t ∈ E_win q0 a0, r < |t - (a0 : ℝ) / (q0 : ℝ)| := by
          intro t ht
          by_contra hle
          push_neg at hle
          exact ht.1 ⟨q0, a0, hq0_1, hq0_small, ha0_le, hcop0, hle⟩
        have htail := peak_tail_integral_le n q0 a0 r (E_win q0 a0) hn_pos hq0_1 ha0_le
          hr_pos (hE_meas q0 a0) hE_sub
        refine htail.trans_eq ?_
        dsimp [r]
        field_simp
      calc (∑ a0 ∈ A_set q0,
            intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume)
          ≤ ∑ _ ∈ A_set q0,
              (8 * (q0 : ℝ) * (n : ℝ) / ((Nat.totient q0 : ℝ) ^ 2 * (Q n : ℝ))) :=
            Finset.sum_le_sum hterm
        _ = ((A_set q0).card : ℝ) *
              (8 * (q0 : ℝ) * (n : ℝ) / ((Nat.totient q0 : ℝ) ^ 2 * (Q n : ℝ))) := by simp
        _ ≤ (2 * (Nat.totient q0 : ℝ)) *
              (8 * (q0 : ℝ) * (n : ℝ) / ((Nat.totient q0 : ℝ) ^ 2 * (Q n : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard_a (by positivity)
        _ = 16 * (n : ℝ) * ((q0 : ℝ) / (Q n : ℝ)) / (Nat.totient q0 : ℝ) := by
            field_simp; ring
        _ ≤ 32 * (n : ℝ) * (Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ)) / (Nat.totient q0 : ℝ) := by
            have hsqrt_le : Real.sqrt (q0 : ℝ) ≤ Real.sqrt (Q n : ℝ) :=
              Real.sqrt_le_sqrt (Nat.cast_le.mpr hq0_small)
            have hratio : (q0 : ℝ) / (Q n : ℝ) ≤ Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ) := by
              let u := Real.sqrt (q0 : ℝ)
              let v := Real.sqrt (Q n : ℝ)
              have h1 : u / v ≤ 1 :=
                (div_le_one (Real.sqrt_pos.mpr hQ_r_pos)).mpr hsqrt_le
              calc
                (q0 : ℝ) / (Q n : ℝ) = (u / v) * (u / v) := by
                  rw [div_mul_div_comm]
                  dsimp only [u, v]
                  rw [Real.mul_self_sqrt hq0_r_pos.le, Real.mul_self_sqrt hQ_r_pos.le]
                _ ≤ u / v := mul_le_of_le_one_right (by dsimp [u, v]; positivity) h1
            refine div_le_div_of_nonneg_right ?_ hphi_pos.le
            have hn_r : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            have hr_nn : 0 ≤ Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ) := by positivity
            calc
              _ ≤ 16 * (n : ℝ) * (Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by norm_num) hn_r) hr_nn
        _ = (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * (Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) := by
            ring
    · -- Case A: Q n < q0, use full peak integral
      have hterm : ∀ a0 ∈ A_set q0,
          intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume ≤
            16 * (n : ℝ) / (Nat.totient q0 : ℝ) ^ 2 := by
        intro a0 _
        have hle1 : intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1
              MeasureTheory.volume ≤
            intervalIntegral (g q0 a0) (0 : ℝ) 1 MeasureTheory.volume := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            (intervalIntegrable_indicator_of_measurable (hE_meas q0 a0)
              ((peak_continuous n q0 a0 hq0_1).intervalIntegrable 0 1))
            ((peak_continuous n q0 a0 hq0_1).intervalIntegrable 0 1) (fun t _ => ?_)
          by_cases ht : t ∈ E_win q0 a0
          · rw [Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht]
            exact peak_nonneg n q0 a0 t
        exact hle1.trans (peak_full_integral_le n q0 a0 hn_pos hq0_1)
      have hQ_lt_q0 : (Q n : ℝ) ≤ (q0 : ℝ) := Nat.cast_le.mpr (by omega)
      have h1_le_ratio : (1 : ℝ) ≤ Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ) :=
        (one_le_div (Real.sqrt_pos.mpr hQ_r_pos)).mpr (Real.sqrt_le_sqrt hQ_lt_q0)
      calc (∑ a0 ∈ A_set q0,
            intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume)
          ≤ ∑ _ ∈ A_set q0, (16 * (n : ℝ) / (Nat.totient q0 : ℝ) ^ 2) :=
            Finset.sum_le_sum hterm
        _ = ((A_set q0).card : ℝ) * (16 * (n : ℝ) / (Nat.totient q0 : ℝ) ^ 2) := by simp
        _ ≤ (2 * (Nat.totient q0 : ℝ)) * (16 * (n : ℝ) / (Nat.totient q0 : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcard_a (by positivity)
        _ = 32 * (n : ℝ) / (Nat.totient q0 : ℝ) := by field_simp; ring
        _ ≤ (32 * (n : ℝ) / (Nat.totient q0 : ℝ)) *
              (Real.sqrt (q0 : ℝ) / Real.sqrt (Q n : ℝ)) :=
            le_mul_of_one_le_right (by positivity) h1_le_ratio
        _ = (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * (Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) := by
            ring
  -- Sum the diagonal bound over q0 ∈ Q_ord and cover by divisors of 2^j - 1
  set J : ℕ := LQ ^ 2
  have hdiag_sum :
      (∑ q0 ∈ Q_ord, Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) ≤
      (LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5) := by
    have hsub_biUnion : Q_ord ⊆ (Finset.Icc 1 J).biUnion (fun j => (2 ^ j - 1 : ℕ).divisors) := by
      intro q hq
      have horder : ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ q ∣ 2 ^ j - 1 :=
        ((Finset.mem_filter.mp hq).2).2
      obtain ⟨j, hj1, hj2, hdvd⟩ := horder
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩, Nat.mem_divisors.mpr ⟨hdvd, ?_⟩⟩
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      omega
    have hcov1 : (∑ q0 ∈ Q_ord, Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) ≤
        ∑ j ∈ Finset.Icc 1 J,
          ∑ q ∈ (2 ^ j - 1 : ℕ).divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ) := by
      calc (∑ q0 ∈ Q_ord, Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ))
          ≤ ∑ q0 ∈ (Finset.Icc 1 J).biUnion (fun j => (2 ^ j - 1 : ℕ).divisors),
              Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_biUnion (fun _ _ _ => by positivity)
        _ ≤ ∑ j ∈ Finset.Icc 1 J,
              ∑ q ∈ (2 ^ j - 1 : ℕ).divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ) :=
            sum_biUnion_le_of_nonneg _ _ _ (fun _ => by positivity)
    set m_exp : ℕ := Nat.log 2 (LQ / 100)
    have hm_ge : 6000 ≤ m_exp :=
      log_div_ge 6000 LQ (hA0_large.trans hLQ_ge_A0)
    have h2m_le : (2 : ℝ) ^ m_exp ≤ (LQ : ℝ) / 100 := by
      have h1 : 2 ^ m_exp ≤ LQ / 100 := Nat.pow_log_le_self 2 (by omega)
      have h2 : 100 * 2 ^ m_exp ≤ LQ := by omega
      have h3 : (100 : ℝ) * (2 : ℝ) ^ m_exp ≤ (LQ : ℝ) := by exact_mod_cast h2
      linarith
    have hLQ_le_2m : (LQ : ℝ) ≤ 201 * (2 : ℝ) ^ m_exp := by
      have h1 : LQ / 100 < 2 ^ (m_exp + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : 1 ≤ 2 ^ m_exp := Nat.one_le_pow m_exp 2 (by norm_num)
      have h3 : LQ ≤ 201 * 2 ^ m_exp := by
        rw [pow_succ'] at h1
        omega
      exact_mod_cast h3
    have hexp_bound : 10 * (2 : ℝ) ^ m_exp + 5 * (J : ℝ) / (2 * (m_exp : ℝ) * (2 : ℝ) ^ m_exp) ≤
        (LQ : ℝ) / 5 := by
      have h1 : 10 * (2 : ℝ) ^ m_exp ≤ (LQ : ℝ) / 10 := by linarith
      have h2 : 5 * (J : ℝ) / (2 * (m_exp : ℝ) * (2 : ℝ) ^ m_exp) ≤ (LQ : ℝ) / 10 := by
        have hm_r : (6000 : ℝ) ≤ (m_exp : ℝ) := by exact_mod_cast hm_ge
        have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m_exp := by positivity
        rw [div_le_iff₀ (by positivity)]
        have hJ_r : (J : ℝ) = (LQ : ℝ) * (LQ : ℝ) := by dsimp [J]; push_cast; ring
        rw [hJ_r]
        have hprod : 50 * (LQ : ℝ) ≤ 2 * (m_exp : ℝ) * (2 : ℝ) ^ m_exp := by
          calc
            _ ≤ 50 * (201 * (2 : ℝ) ^ m_exp) :=
              mul_le_mul_of_nonneg_left hLQ_le_2m (by norm_num)
            _ = 10050 * (2 : ℝ) ^ m_exp := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hm_r]) h2m_pos.le
        calc
          _ = ((LQ : ℝ) / 10) * (50 * (LQ : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
      linarith only [h1, h2]
    have hj_bound : ∀ j ∈ Finset.Icc 1 J,
        (∑ q ∈ (2 ^ j - 1 : ℕ).divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ)) ≤
          Real.exp ((LQ : ℝ) / 5) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj2 : j ≤ J := (Finset.mem_Icc.mp hj).2
      have h2j_ge : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      have hM_pos : 0 < 2 ^ j - 1 := by omega
      have hM_odd : Odd (2 ^ j - 1) := by
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        refine ⟨2 ^ r - 1, ?_⟩
        have : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by norm_num)
        rw [pow_succ']
        omega
      have hM_lt : 2 ^ j - 1 < 2 ^ J := by
        have hle : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hj2
        omega
      exact (sum_divisors_le_exp hM_pos hM_odd hM_lt (by omega)).trans
        (Real.exp_le_exp.mpr hexp_bound)
    calc (∑ q0 ∈ Q_ord, Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 J,
            ∑ q ∈ (2 ^ j - 1 : ℕ).divisors, Real.sqrt (q : ℝ) / (Nat.totient q : ℝ) := hcov1
      _ ≤ ∑ _ ∈ Finset.Icc 1 J, Real.exp ((LQ : ℝ) / 5) := Finset.sum_le_sum hj_bound
      _ = ((Finset.Icc 1 J).card : ℝ) * Real.exp ((LQ : ℝ) / 5) := by simp
      _ = (LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5) := by
          have hc : (Finset.Icc 1 J).card = J := by simp
          rw [hc]
          dsimp [J]
          push_cast
          rfl
  -- Show 32 * n / sqrt(Q) * (LQ^2 * exp(LQ/5)) ≤ n / 9216
  have hdiag_total :
      (∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
        intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume) ≤
      (n : ℝ) / 9216 := by
    have h1 :
        (∑ q0 ∈ Q_ord, ∑ a0 ∈ A_set q0,
          intervalIntegral ((E_win q0 a0).indicator (g q0 a0)) (0 : ℝ) 1 MeasureTheory.volume) ≤
        (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * ((LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5)) := by
      calc _ ≤ ∑ q0 ∈ Q_ord,
              (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) *
                (Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ)) := Finset.sum_le_sum hdiag_q0
        _ = (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) *
              ∑ q0 ∈ Q_ord, Real.sqrt (q0 : ℝ) / (Nat.totient q0 : ℝ) := by rw [← Finset.mul_sum]
        _ ≤ (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * ((LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_left hdiag_sum (by positivity)
    have hkey : 294912 * (LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5) ≤ Real.sqrt (Q n : ℝ) := by
      refine le_of_pow_le_pow_left₀ (by norm_num : 10 ≠ 0) (Real.sqrt_nonneg _) ?_
      have hexp10 : (Real.exp ((LQ : ℝ) / 5)) ^ 10 ≤ (2 : ℝ) ^ (3 * LQ) := by
        rw [← Real.exp_nat_mul]
        have hmul_eq : (10 : ℕ) * ((LQ : ℝ) / 5) = ((2 * LQ : ℕ) : ℝ) * 1 := by
          push_cast; ring
        rw [hmul_eq, Real.exp_nat_mul, pow_mul (Real.exp 1) 2 LQ]
        have he2 : (Real.exp 1) ^ 2 ≤ (2 : ℝ) ^ 3 := by
          have he_le : Real.exp 1 ≤ (11 : ℝ) / 4 :=
            (Real.exp_one_lt_d9.trans (by norm_num)).le
          calc
            _ ≤ ((11 : ℝ) / 4) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le he_le 2
            _ ≤ _ := by norm_num
        calc ((Real.exp 1) ^ 2) ^ LQ ≤ ((2 : ℝ) ^ 3) ^ LQ :=
              pow_le_pow_left₀ (by positivity) he2 LQ
          _ = (2 : ℝ) ^ (3 * LQ) := by rw [← pow_mul]
      have hLQ20 : (LQ : ℝ) ^ 20 ≤ (2 : ℝ) ^ LQ := by
        exact_mod_cast pow_20_le_two_pow hLQ_ge
      have hQ5 : (2 : ℝ) ^ (5 * (LQ - 1)) ≤ (Real.sqrt (Q n : ℝ)) ^ 10 := by
        have hpow_le : 2 ^ (LQ - 1) ≤ Q n := Nat.pow_log_le_self 2 (by omega)
        have hpow_r : (2 : ℝ) ^ (LQ - 1) ≤ (Q n : ℝ) := by exact_mod_cast hpow_le
        have hsqrt10 : (Real.sqrt (Q n : ℝ)) ^ 10 = (Q n : ℝ) ^ 5 := by
          have : (10 : ℕ) = 2 * 5 := by norm_num
          rw [this, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
        rw [hsqrt10]
        calc (2 : ℝ) ^ (5 * (LQ - 1)) = ((2 : ℝ) ^ (LQ - 1)) ^ 5 := by
              rw [← pow_mul, mul_comm]
          _ ≤ (Q n : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hpow_r 5
      have hconst10 : (294912 : ℝ) ^ 10 ≤ (2 : ℝ) ^ 190 := by
        calc (294912 : ℝ) ^ 10 ≤ ((2 : ℝ) ^ 19) ^ 10 :=
              pow_le_pow_left₀ (by norm_num) (by norm_num) 10
          _ = (2 : ℝ) ^ 190 := by rw [← pow_mul]
      have hLHS : (294912 * (LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5)) ^ 10 =
          (294912 : ℝ) ^ 10 * (LQ : ℝ) ^ 20 * (Real.exp ((LQ : ℝ) / 5)) ^ 10 := by ring
      rw [hLHS]
      calc (294912 : ℝ) ^ 10 * (LQ : ℝ) ^ 20 * (Real.exp ((LQ : ℝ) / 5)) ^ 10
          ≤ (2 : ℝ) ^ 190 * (2 : ℝ) ^ LQ * (2 : ℝ) ^ (3 * LQ) := by
            refine mul_le_mul (mul_le_mul hconst10 hLQ20 (by positivity) (by positivity))
              hexp10 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (190 + LQ + 3 * LQ) := by rw [← pow_add, ← pow_add]
        _ ≤ (2 : ℝ) ^ (5 * (LQ - 1)) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
        _ ≤ (Real.sqrt (Q n : ℝ)) ^ 10 := hQ5
    have h2 : (32 * (n : ℝ) / Real.sqrt (Q n : ℝ)) * ((LQ : ℝ) ^ 2 * Real.exp ((LQ : ℝ) / 5)) ≤
        (n : ℝ) / 9216 := by
      have hsqrtQ_pos : 0 < Real.sqrt (Q n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
      have hn_r_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hsqrtQ_pos (by norm_num : (0 : ℝ) < 9216)]
      have hmul := mul_le_mul_of_nonneg_left hkey hn_r_nn
      linarith
    exact h1.trans h2
  linarith [hstep1, hstep2, hdiag_total, hoff_total]