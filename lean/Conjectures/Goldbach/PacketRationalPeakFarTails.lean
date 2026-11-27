import Mathlib

namespace GoldbachPacket

private theorem primePowerTotientBound (p k c : ℕ) (hp : p.Prime)
    (hc : p ≤ c * (p - 1) ^ 2) :
    p ^ (k + 1) ≤ c * (Nat.totient (p ^ (k + 1))) ^ 2 := by
  have hpow : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  have hsq : p ^ k ≤ (p ^ k) ^ 2 := by
    calc
      p ^ k = p ^ k * 1 := (mul_one _).symm
      _ ≤ p ^ k * p ^ k := Nat.mul_le_mul_left _ hpow
      _ = _ := (pow_two _).symm
  rw [Nat.totient_prime_pow_succ hp, pow_succ, mul_pow]
  calc
    p ^ k * p ≤ p ^ k * (c * (p - 1) ^ 2) := Nat.mul_le_mul_left _ hc
    _ = c * (p ^ k * (p - 1) ^ 2) := by ring
    _ ≤ c * ((p ^ k) ^ 2 * (p - 1) ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsq)

theorem totientSquareBounds (n : ℕ) :
    n ≤ 2 * (Nat.totient n) ^ 2 ∧ (Odd n → n ≤ (Nat.totient n) ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hstrong (hne : p ≠ 2) : p ≤ (p - 1) ^ 2 := by
      have hp2 := hp.two_le
      have htwo : 2 ≤ p - 1 := by omega
      calc
        p ≤ (p - 1) + (p - 1) := by omega
        _ = 2 * (p - 1) := by ring
        _ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ htwo
        _ = (p - 1) ^ 2 := (pow_two _).symm
    constructor
    · apply primePowerTotientBound p k 2 hp
      by_cases h : p = 2
      · norm_num [h]
      · exact (hstrong h).trans (by omega)
    · intro ho
      have hpo : Odd p := (Nat.odd_pow_iff (by omega)).mp ho
      have hne : p ≠ 2 := by
        intro h
        subst p
        norm_num at hpo
      simpa only [one_mul] using primePowerTotientBound p k 1 hp
        (by simpa only [one_mul] using hstrong hne)
  | coprime a b _ _ hc ha hb =>
    rw [Nat.totient_mul hc, mul_pow]
    constructor
    · rcases Nat.even_or_odd a with hEven | hOdd
      · have hbodd : Odd b := (hc.coprime_dvd_left hEven.two_dvd).odd_of_left
        exact (Nat.mul_le_mul ha.1 (hb.2 hbodd)).trans_eq (by ring)
      · exact (Nat.mul_le_mul (ha.2 hOdd) hb.1).trans_eq (by ring)
    · intro ho
      obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp ho
      exact Nat.mul_le_mul (ha.2 hoa) (hb.2 hob)

private theorem inverseTotient_le_gap {q : ℕ} (hq : 1 ≤ q) :
    (Nat.totient q : ℝ)⁻¹ ≤ 4 * (Real.sqrt (q : ℝ) - Real.sqrt ((q - 1 : ℕ) : ℝ)) := by
  let a := Real.sqrt (q : ℝ)
  let b := Real.sqrt ((q - 1 : ℕ) : ℝ)
  let v : ℝ := Nat.totient q
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hv : 0 < v := by
    change (0 : ℝ) < (Nat.totient q : ℝ)
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q))
  have ha : 0 < a := Real.sqrt_pos.2 hqpos
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hVsq : (q : ℝ) ≤ 2 * v ^ 2 := by
    change (q : ℝ) ≤ 2 * (Nat.totient q : ℝ) ^ 2
    exact_mod_cast (totientSquareBounds q).1
  have hA : a ≤ 2 * v := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * v)).2
    nlinarith [sq_nonneg v]
  have hB : b ≤ a := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le q 1)
  have ha_sq : a ^ 2 = (q : ℝ) := Real.sq_sqrt hqpos.le
  have hb_sq : b ^ 2 = ((q - 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hcast : (((q - 1 : ℕ) : ℝ) + 1) = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hq
  have hAB : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hGap : a - b = 1 / (a + b) := by
    apply (eq_div_iff hAB.ne').mpr
    nlinarith [ha_sq, hb_sq, hcast]
  change v⁻¹ ≤ 4 * (a - b)
  calc
    v⁻¹ = 2 / (2 * v) := by field_simp [hv.ne']
    _ ≤ 2 / a := div_le_div_of_nonneg_left (by norm_num) ha hA
    _ = 4 / (2 * a) := by field_simp [ha.ne']; ring
    _ ≤ 4 / (a + b) := div_le_div_of_nonneg_left (by norm_num) hAB (by linarith)
    _ = 4 * (a - b) := by rw [hGap]; ring

theorem inverseTotientSumBound (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, (Nat.totient q : ℝ)⁻¹) ≤ 4 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    have hterm := inverseTotient_le_gap (q := n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hterm
    calc
      _ ≤ 4 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) + 4 * Real.sqrt (n : ℝ) := by
        exact add_le_add hterm ih
      _ = _ := by ring

end GoldbachPacket

private lemma sum_inv_totient_le (M : ℕ) :
    ∑ q ∈ Finset.Icc 1 M, (1 : ℝ) / (Nat.totient q : ℝ) ≤ 4 * Real.sqrt (M : ℝ) := by
  simpa only [one_div] using GoldbachPacket.inverseTotientSumBound M

private lemma card_coprime_range_succ_le (q : ℕ) (hq : 0 < q) :
    ((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card ≤ 2 * Nat.totient q := by
  have hsub : (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) ⊆
      insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    by_cases haq : a = q
    · left; exact haq
    · right; exact ⟨by omega, ha.2⟩
  have htot : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
    rw [Nat.totient]
    congr 1
    ext a
    simp only [Finset.mem_filter, Nat.coprime_comm]
  have hpos : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hq
  calc ((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card
      ≤ (insert q ((Finset.range q).filter (fun a => Nat.Coprime a q))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range q).filter (fun a => Nat.Coprime a q)).card + 1 :=
        Finset.card_insert_le _ _
    _ = Nat.totient q + 1 := by rw [htot]
    _ ≤ 2 * Nat.totient q := by omega

private lemma intervalIntegrable_indicator_of_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {s : Set ℝ} (hs : MeasurableSet s) (u v : ℝ) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume u v := by
  have h : IntervalIntegrable f MeasureTheory.volume u v := hf.intervalIntegrable u v
  exact ⟨h.1.indicator hs, h.2.indicator hs⟩

private lemma integral_inv_sq_sub (a b c : ℝ) (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b, x - c ≠ 0) :
    intervalIntegral (fun x : ℝ => (1 : ℝ) / (x - c) ^ 2) a b MeasureTheory.volume
      = -(b - c)⁻¹ - -(a - c)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(t - c)⁻¹) ((1 : ℝ) / (x - c) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxne : x - c ≠ 0 := hne x hx
    have hx' : HasDerivAt (fun t : ℝ => t - c) 1 x := (hasDerivAt_id x).sub_const c
    convert (hx'.inv hxne).neg using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / (x - c) ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero 2 (hne x hx))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma left_tail_bound {f : ℝ → ℝ} (hf : Continuous f) {c r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, t < c - r → f t ≤ K * ((1 : ℝ) / (t - c) ^ 2)) :
    intervalIntegral ((Set.Iio (c - r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤ K / r := by
  by_cases hcr : c - r ≤ 0
  · have hzero : intervalIntegral ((Set.Iio (c - r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun _ => (0 : ℝ)) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have hnot : ¬ (t < c - r) := by linarith [ht.1]
      simp [Set.indicator, hnot]
    rw [hzero, intervalIntegral.integral_zero]
    exact div_nonneg hK (le_of_lt hr)
  · push_neg at hcr
    let b : ℝ := min 1 (c - r)
    have hb_pos : 0 < b := lt_min (by norm_num) hcr
    have hb_le1 : b ≤ 1 := min_le_left 1 (c - r)
    have hb_lecr : b ≤ c - r := min_le_right 1 (c - r)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_indicator_of_continuous hf (s := Set.Iio (c-r)) measurableSet_Iio 0 b)
      (intervalIntegrable_indicator_of_continuous hf (s := Set.Iio (c-r)) measurableSet_Iio b 1)
    rw [← hsplit]
    have hzero : intervalIntegral ((Set.Iio (c - r)).indicator f) b 1 MeasureTheory.volume =
        intervalIntegral (fun _ => (0 : ℝ)) b 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le hb_le1] at ht
      have hnot : ¬ (t < c - r) := by
        rcases min_lt_iff.mp ht.1 with h | h <;> linarith [ht.2]
      simp [Set.indicator, hnot]
    rw [hzero, intervalIntegral.integral_zero, add_zero]
    have hne : ∀ x ∈ Set.Icc (0 : ℝ) b, x - c ≠ 0 := fun x hx => by linarith [hx.2]
    have hg_int : IntervalIntegrable (fun t : ℝ => K * ((1 : ℝ) / (t - c) ^ 2))
        MeasureTheory.volume 0 b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (le_of_lt hb_pos)]
      exact continuousOn_const.mul
        (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
          (fun x hx => pow_ne_zero 2 (hne x hx)))
    have hmono :
        intervalIntegral ((Set.Iio (c - r)).indicator f) (0 : ℝ) b MeasureTheory.volume ≤
          intervalIntegral (fun t : ℝ => K * ((1 : ℝ) / (t - c) ^ 2))
            (0 : ℝ) b MeasureTheory.volume := by
      apply intervalIntegral.integral_mono_on (le_of_lt hb_pos)
        (intervalIntegrable_indicator_of_continuous hf (s := Set.Iio (c-r)) measurableSet_Iio 0 b) hg_int
      intro t _
      by_cases hlt : t < c - r
      · simp only [Set.indicator, Set.mem_Iio, hlt, ↓reduceIte]
        exact hbound t hlt
      · simp only [Set.indicator, Set.mem_Iio, hlt, ↓reduceIte]
        positivity
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_sub 0 b c (le_of_lt hb_pos) hne]
    have hinv1 : -(b - c)⁻¹ = (c - b)⁻¹ := by
      rw [neg_inv] <;> congr 1 <;> ring
    have hinv2 : -(0 - c)⁻¹ = c⁻¹ := by
      rw [neg_inv] <;> congr 1 <;> ring
    have h1 : (c - b)⁻¹ ≤ 1 / r := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hr (by linarith)
    have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr (by linarith)
    calc K * (-(b - c)⁻¹ - -(0 - c)⁻¹)
        = K * ((c - b)⁻¹ - c⁻¹) := by rw [hinv1, hinv2]
      _ ≤ K * (1 / r) := mul_le_mul_of_nonneg_left (by linarith) hK
      _ = K / r := by ring

private lemma right_tail_bound {f : ℝ → ℝ} (hf : Continuous f) {c r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, c + r < t → f t ≤ K * ((1 : ℝ) / (t - c) ^ 2)) :
    intervalIntegral ((Set.Ioi (c + r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤ K / r := by
  by_cases hcr : 1 ≤ c + r
  · have hzero : intervalIntegral ((Set.Ioi (c + r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun _ => (0 : ℝ)) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have hnot : ¬ (c + r < t) := by linarith [ht.2]
      simp [Set.indicator, hnot]
    rw [hzero, intervalIntegral.integral_zero]
    exact div_nonneg hK (le_of_lt hr)
  · push_neg at hcr
    let d : ℝ := max 0 (c + r)
    have hd_nonneg : 0 ≤ d := le_max_left 0 (c + r)
    have hd_lt1 : d < 1 := max_lt (by norm_num) hcr
    have hcr_led : c + r ≤ d := le_max_right 0 (c + r)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_indicator_of_continuous hf (s := Set.Ioi (c+r)) measurableSet_Ioi 0 d)
      (intervalIntegrable_indicator_of_continuous hf (s := Set.Ioi (c+r)) measurableSet_Ioi d 1)
    rw [← hsplit]
    have hzero : intervalIntegral ((Set.Ioi (c + r)).indicator f) (0 : ℝ) d MeasureTheory.volume =
        intervalIntegral (fun _ => (0 : ℝ)) (0 : ℝ) d MeasureTheory.volume := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le hd_nonneg] at ht
      have hnot : ¬ (c + r < t) := by
        rcases le_max_iff.mp ht.2 with h | h <;> linarith [ht.1]
      simp [Set.indicator, hnot]
    rw [hzero, intervalIntegral.integral_zero, zero_add]
    have hne : ∀ x ∈ Set.Icc d (1 : ℝ), x - c ≠ 0 := fun x hx => by linarith [hx.1]
    have hg_int : IntervalIntegrable (fun t : ℝ => K * ((1 : ℝ) / (t - c) ^ 2))
        MeasureTheory.volume d 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (le_of_lt hd_lt1)]
      exact continuousOn_const.mul
        (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
          (fun x hx => pow_ne_zero 2 (hne x hx)))
    have hmono :
        intervalIntegral ((Set.Ioi (c + r)).indicator f) d (1 : ℝ) MeasureTheory.volume ≤
          intervalIntegral (fun t : ℝ => K * ((1 : ℝ) / (t - c) ^ 2))
            d (1 : ℝ) MeasureTheory.volume := by
      apply intervalIntegral.integral_mono_on (le_of_lt hd_lt1)
        (intervalIntegrable_indicator_of_continuous hf (s := Set.Ioi (c+r)) measurableSet_Ioi d 1) hg_int
      intro t _
      by_cases hgt : c + r < t
      · simp only [Set.indicator, Set.mem_Ioi, hgt, ↓reduceIte]
        exact hbound t hgt
      · simp only [Set.indicator, Set.mem_Ioi, hgt, ↓reduceIte]
        positivity
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_sub d 1 c (le_of_lt hd_lt1) hne]
    have h1 : (d - c)⁻¹ ≤ 1 / r := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hr (by linarith)
    have h2 : 0 ≤ (1 - c)⁻¹ := inv_nonneg.mpr (by linarith)
    calc K * (-(1 - c)⁻¹ - -(d - c)⁻¹)
        = K * ((d - c)⁻¹ - (1 - c)⁻¹) := by ring
      _ ≤ K * (1 / r) := mul_le_mul_of_nonneg_left (by linarith) hK
      _ = K / r := by ring

private lemma tail_integral_bound (n : ℕ) (hn : 0 < n) (q : ℕ) (hq : 0 < q) (a : ℕ)
    (r : ℝ) (hr : 0 < r) :
    intervalIntegral
      (({t : ℝ | r < |t - (a : ℝ) / (q : ℝ)|}).indicator
        (fun t => 4 * (n : ℝ) ^ 2 /
          ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))))
      (0 : ℝ) 1 MeasureTheory.volume
    ≤ 8 / ((Nat.totient q : ℝ) ^ 2 * r) := by
  let c : ℝ := (a : ℝ) / (q : ℝ)
  let K : ℝ := 4 / (Nat.totient q : ℝ) ^ 2
  let f : ℝ → ℝ := fun t =>
    4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2))
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hφ_pos : (0 : ℝ) < (Nat.totient q : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hK : 0 ≤ K := div_nonneg (by norm_num) (sq_nonneg _)
  have hf : Continuous f := by
    refine continuous_const.div ?_ (fun t => ?_)
    · exact continuous_const.mul
        (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2))
    · change (Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2) ≠ 0
      exact ne_of_gt (mul_pos (sq_pos_of_pos hφ_pos) (by positivity))
  have hpt : ∀ t : ℝ, t - c ≠ 0 → f t ≤ K * ((1 : ℝ) / (t - c) ^ 2) := by
    intro t htc
    have htc_sq : 0 < (t - c) ^ 2 := sq_pos_of_ne_zero htc
    have hdenom_pos : 0 < (Nat.totient q : ℝ) ^ 2 * ((n : ℝ) * (t - c)) ^ 2 :=
      mul_pos (sq_pos_of_pos hφ_pos) (mul_pow (n : ℝ) (t - c) 2 ▸ mul_pos (sq_pos_of_pos hn_pos) htc_sq)
    have hdenom_le :
        (Nat.totient q : ℝ) ^ 2 * ((n : ℝ) * (t - c)) ^ 2 ≤
          (Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - c)) ^ 2) := by
      nlinarith [sq_nonneg (Nat.totient q : ℝ)]
    calc f t
        ≤ 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 * ((n : ℝ) * (t - c)) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_le
      _ = K * ((1 : ℝ) / (t - c) ^ 2) := by
          dsimp only [K]
          field_simp <;> ring
  have hind : ∀ t : ℝ,
      ({t : ℝ | r < |t - c|}).indicator f t =
        (Set.Iio (c - r)).indicator f t + (Set.Ioi (c + r)).indicator f t := by
    intro t
    by_cases h1 : t < c - r
    · have h2 : ¬ (c + r < t) := by linarith
      have h3 : r < |t - c| := by rw [lt_abs]; right; linarith
      simp [Set.indicator, h1, h2, h3]
    · by_cases h2 : c + r < t
      · have h3 : r < |t - c| := by rw [lt_abs]; left; linarith
        simp [Set.indicator, h1, h2, h3]
      · have h3 : ¬ (r < |t - c|) := by rw [lt_abs]; push_neg; constructor <;> linarith
        simp [Set.indicator, h1, h2, h3]
  have hcongr :
      intervalIntegral (({t : ℝ | r < |t - c|}).indicator f) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (Set.Iio (c - r)).indicator f t + (Set.Ioi (c + r)).indicator f t)
          (0 : ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.integral_congr (fun t _ => hind t)
  change intervalIntegral (({t : ℝ | r < |t - c|}).indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤ _
  rw [hcongr, intervalIntegral.integral_add
    (intervalIntegrable_indicator_of_continuous hf (s := Set.Iio (c-r)) measurableSet_Iio 0 1)
    (intervalIntegrable_indicator_of_continuous hf (s := Set.Ioi (c+r)) measurableSet_Ioi 0 1)]
  have hL : intervalIntegral ((Set.Iio (c - r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤ K / r :=
    left_tail_bound hf hr hK (fun t ht => hpt t (by linarith))
  have hR : intervalIntegral ((Set.Ioi (c + r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤ K / r :=
    right_tail_bound hf hr hK (fun t ht => hpt t (by linarith))
  calc intervalIntegral ((Set.Iio (c - r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume +
         intervalIntegral ((Set.Ioi (c + r)).indicator f) (0 : ℝ) 1 MeasureTheory.volume
      ≤ K / r + K / r := add_le_add hL hR
    _ = 8 / ((Nat.totient q : ℝ) ^ 2 * r) := by
        dsimp only [K]
        ring

theorem Conjectures.Goldbach.PacketRationalPeakFarTails :
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), m {t : ℝ | (Q n:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} (fun t => 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))) ≤ ε*(n:ℝ) := by
  intro Q m ε hε
  let K : ℕ := Nat.ceil (64 / ε) + 1
  refine ⟨2 ^ K, fun n hn => ?_⟩
  have hK_pos : 1 ≤ K := Nat.le_add_left 1 _
  have hn_pos : 0 < n := by
    have h2K : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by norm_num)
    omega
  have hlog : K ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hQ_ge_K : K ≤ Q n := by
    change K ≤ (Nat.log 2 (n + 2)) ^ 2
    calc K ≤ Nat.log 2 (n + 2) := hlog
      _ ≤ (Nat.log 2 (n + 2)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQ_pos : 0 < Q n := lt_of_lt_of_le (by omega) hQ_ge_K
  have hQ_rpos : (0 : ℝ) < (Q n : ℝ) := Nat.cast_pos.mpr hQ_pos
  have hn_rpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  let r : ℝ := (Q n : ℝ) ^ 2 / (n : ℝ)
  have hr_pos : 0 < r := div_pos (sq_pos_of_pos hQ_rpos) hn_rpos
  have hsum_le :
      (∑ q ∈ Finset.Icc 1 ((Q n) ^ 2),
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          m {t : ℝ | r < |t - (a : ℝ) / (q : ℝ)|}
            (fun t => 4 * (n : ℝ) ^ 2 /
              ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))))
        ≤ (16 / r) * ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), (1 : ℝ) / (Nat.totient q : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ_pos : (0 : ℝ) < (Nat.totient q : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq_pos)
    have hinner :
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          m {t : ℝ | r < |t - (a : ℝ) / (q : ℝ)|}
            (fun t => 4 * (n : ℝ) ^ 2 /
              ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))
          ≤ ∑ _a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
            8 / ((Nat.totient q : ℝ) ^ 2 * r) := by
      apply Finset.sum_le_sum
      intro a _
      exact tail_integral_bound n hn_pos q hq_pos a r hr_pos
    refine hinner.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card : ℝ)
        ≤ 2 * (Nat.totient q : ℝ) := by
      exact_mod_cast card_coprime_range_succ_le q hq_pos
    calc (((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card : ℝ) *
           (8 / ((Nat.totient q : ℝ) ^ 2 * r))
        ≤ (2 * (Nat.totient q : ℝ)) * (8 / ((Nat.totient q : ℝ) ^ 2 * r)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (16 / r) * ((1 : ℝ) / (Nat.totient q : ℝ)) := by
          field_simp
          ring
  have htot_sum :
      ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), (1 : ℝ) / (Nat.totient q : ℝ) ≤ 4 * (Q n : ℝ) := by
    have h := sum_inv_totient_le ((Q n) ^ 2)
    have hsq : Real.sqrt ((((Q n) ^ 2 : ℕ) : ℝ)) = (Q n : ℝ) := by
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg _)
    rwa [hsq] at h
  have hbound64 :
      (∑ q ∈ Finset.Icc 1 ((Q n) ^ 2),
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          m {t : ℝ | r < |t - (a : ℝ) / (q : ℝ)|}
            (fun t => 4 * (n : ℝ) ^ 2 /
              ((Nat.totient q : ℝ) ^ 2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2))))
        ≤ 64 * (n : ℝ) / (Q n : ℝ) := by
    refine hsum_le.trans ?_
    calc (16 / r) * ∑ q ∈ Finset.Icc 1 ((Q n) ^ 2), (1 : ℝ) / (Nat.totient q : ℝ)
        ≤ (16 / r) * (4 * (Q n : ℝ)) := mul_le_mul_of_nonneg_left htot_sum (by positivity)
      _ = 64 * (n : ℝ) / (Q n : ℝ) := by
          dsimp only [r]
          field_simp
          ring
  refine hbound64.trans ?_
  have hceil : 64 / ε ≤ (Q n : ℝ) := by
    have h1 : 64 / ε ≤ (Nat.ceil (64 / ε) : ℝ) := Nat.le_ceil (64 / ε)
    have h2 : (Nat.ceil (64 / ε) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.le_succ (Nat.ceil (64 / ε))
    have h3 : (K : ℝ) ≤ (Q n : ℝ) := by
      exact_mod_cast hQ_ge_K
    linarith
  have h64 : 64 ≤ ε * (Q n : ℝ) := by
    have := (div_le_iff₀ hε).mp hceil
    linarith
  rw [div_le_iff₀ hQ_rpos]
  nlinarith
