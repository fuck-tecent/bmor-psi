import Mathlib

namespace Conjectures.Goldbach.PacketModelFromCenterCounts_aux

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private def gridQ (n : ℕ) := (Nat.log 2 (n + 2))^2

private def packet (m : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * t)

private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

private def arcs (n : ℕ) : Set ℝ :=
  let Q := gridQ n
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))}

private def resonant (n : ℕ) : Set ℝ :=
  {t : ℝ | t ∉ arcs n ∧
    (1 : ℝ) / 2 < packet (length n) t / (length n : ℝ)}

private def integralOn (s : Set ℝ) (f : ℝ → ℝ) :=
  intervalIntegral (s.indicator f) (0 : ℝ) 1 MeasureTheory.volume

private def profile (n q : ℕ) (c t : ℝ) :=
  4 * (n : ℝ)^2 /
    ((q.totient : ℝ)^2 * (1 + ((n : ℝ) * (t - c))^2))

private def lorentz (r c t : ℝ) := 1 / (r^2 + (t - c)^2)

private theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) :
    Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

private theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0 : ℝ)..1, lorentz r c t) ≤ Real.pi / r := by
  let F := fun t : ℝ => Real.arctan ((t - c) / r) / r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t - c) / r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t - c) / r)^2) * (1 / r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1 - c) / r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0 - c) / r)
  linarith

private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := gridQ n
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t - (i.val.2 : ℝ) / (i.val.1 : ℝ)| ≤
        (Q : ℝ) / ((i.val.1 : ℝ) * (n : ℝ))} := by
    ext t
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hQ, ha, hc⟩, ht⟩
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1, i.property.2.2.1,
        i.property.2.2.2, hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet

private theorem measurableMask (n : ℕ) : MeasurableSet (resonant n) := by
  have hk : Continuous (fun t => packet (length n) t / (length n : ℝ)) := by
    unfold packet
    fun_prop
  exact (measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ) / 2)) hk).measurableSet

private theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0 : ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

private theorem onSubset {s v : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hv : MeasurableSet v) (h : s ⊆ v) (hc : Continuous f) (hpos : ∀ t, 0 ≤ f t) :
    integralOn s f ≤ integralOn v f := by
  apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc) (onRegion hv hc)
  intro t _
  by_cases ht : t ∈ s
  · simp [ht, h ht]
  · by_cases ht' : t ∈ v <;> simp [ht, ht', hpos]

private theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n)
    (hd : 0 < d) (hQ : d ≤ gridQ n) (hk : k ≤ d) (hm : t ∉ arcs n) :
    (gridQ n : ℝ) / (d * (n : ℝ)) < |t - (k : ℝ) / d| := by
  obtain ⟨g, a, q, hg, hcop, hk', hq'⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_right k hd)
  have hq : 0 < q := by
    by_contra! hz
    have he : q = 0 := by omega
    rw [he, zero_mul] at hq'
    omega
  have hqd : q ≤ d := Nat.le_of_dvd hd ⟨g, hq'⟩
  have haq : a ≤ q := by
    exact (Nat.mul_le_mul_right_iff hg).mp (show a * g ≤ q * g by omega)
  have eq : (k : ℝ) / d = (a : ℝ) / (q : ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have cross : k * q = a * d := by rw [hk', hq']; ring
    exact_mod_cast cross
  by_contra! h
  apply hm
  refine ⟨q, a, hq, hqd.trans hQ, haq, hcop, ?_⟩
  rw [← eq]
  exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqd : (q : ℝ) ≤ d) (Nat.cast_nonneg _)))

private theorem profileContinuous (n q : ℕ) (hq : 0 < q) (c : ℝ) :
    Continuous (profile n q c) := by
  have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold profile
  fun_prop (disch := intro t; positivity)

private theorem profileNonneg (n q : ℕ) (c t : ℝ) : 0 ≤ profile n q c t := by
  unfold profile
  positivity

private theorem peakOutside (n q : ℕ) (hq : 0 < q) (c r : ℝ) (hr : 0 < r) :
    integralOn {t : ℝ | r < |t - c|} (profile n q c) ≤
      (8 / (q.totient : ℝ)^2) * (Real.pi / r) := by
  let f : ℝ := q.totient
  let s := {t : ℝ | r < |t - c|}
  have fp : 0 < f := by
    dsimp [f]
    exact_mod_cast Nat.totient_pos.mpr hq
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const
      (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
  have hd : Continuous (fun t : ℝ => f^2 * (1 + ((n : ℝ) * (t - c))^2)) := by
    fun_prop
  have hc : Continuous (profile n q c) :=
    (continuous_const : Continuous (fun _ : ℝ => 4 * (n : ℝ)^2)).div hd
      (fun t => ne_of_gt (mul_pos (by positivity) (by positivity)))
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (8 / f^2) * lorentz r c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc)
        (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
      intro t _
      change s.indicator (profile n q c) t ≤ _
      by_cases ht : t ∈ s
      · rw [Set.indicator_of_mem ht]
        have d : r ≤ |t - c| := le_of_lt ht
        have sq := pow_le_pow_left₀ hr.le d 2
        rw [sq_abs] at sq
        have bound : (n : ℝ)^2 / (1 + ((n : ℝ) * (t - c))^2) ≤
            2 / (r^2 + (t - c)^2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left sq (sq_nonneg (n : ℝ))]
        calc
          profile n q c t =
              (4 / f^2) * ((n : ℝ)^2 / (1 + ((n : ℝ) * (t - c))^2)) := by
                unfold profile
                dsimp [f]
                field_simp <;> ring
          _ ≤ (4 / f^2) * (2 / (r^2 + (t - c)^2)) :=
            mul_le_mul_of_nonneg_left bound (by positivity)
          _ = _ := by unfold lorentz; ring
      · rw [Set.indicator_of_notMem ht]
        unfold lorentz
        positivity
    _ = (8 / f^2) * (∫ t in (0 : ℝ)..1, lorentz r c t) :=
      intervalIntegral.integral_const_mul ..
    _ ≤ (8 / f^2) * (Real.pi / r) :=
      mul_le_mul_of_nonneg_left (lorentzIntegral hr c) (by positivity)

private theorem oneCenterMass (n q a : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hQ : 0 < gridQ n) (ha : a ≤ q) :
    integralOn (resonant n) (profile n q ((a : ℝ) / (q : ℝ))) ≤
      8 * Real.pi * (n : ℝ) * min 1 ((q : ℝ) / (gridQ n : ℝ)) /
        (q.totient : ℝ)^2 := by
  let c := (a : ℝ) / (q : ℝ)
  have hc := profileContinuous n q hq c
  have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have nr : 0 < (n : ℝ) := by exact_mod_cast hn
  have qr : 0 < (gridQ n : ℝ) := by exact_mod_cast hQ
  by_cases small : q ≤ gridQ n
  · let r := (gridQ n : ℝ) / ((q : ℝ) * (n : ℝ))
    have hr : 0 < r := by dsimp [r]; positivity
    have hs : MeasurableSet {t : ℝ | r < |t - c|} :=
      (isOpen_lt continuous_const
        (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
    have sub : resonant n ⊆ {t : ℝ | r < |t - c|} :=
      fun _ h => denominatorExclusion hn hq small ha h.1
    apply (onSubset (measurableMask n) hs sub hc (profileNonneg n q c)).trans
    apply (peakOutside n q hq c r hr).trans_eq
    rw [min_eq_right ((div_le_one qr).mpr (by exact_mod_cast small))]
    dsimp [r]
    field_simp <;> ring
  · have ht : 1 ≤ (q : ℝ) / (gridQ n : ℝ) :=
      (one_le_div qr).mpr (by exact_mod_cast (by omega : gridQ n ≤ q))
    rw [min_eq_left ht, mul_one]
    let r := 1 / (n : ℝ)
    have hr : 0 < r := by dsimp [r]; positivity
    have id (t : ℝ) : profile n q c t =
        (4 / (q.totient : ℝ)^2) * lorentz r c t := by
      dsimp [profile, lorentz, r]
      field_simp <;> ring
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, (4 / (q.totient : ℝ)^2) * lorentz r c t := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (onRegion (measurableMask n) hc)
          (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
        intro t _
        by_cases h : t ∈ resonant n
        · rw [Set.indicator_of_mem h, id]
        · rw [Set.indicator_of_notMem h]
          unfold lorentz
          positivity
      _ = (4 / (q.totient : ℝ)^2) * _ :=
        intervalIntegral.integral_const_mul ..
      _ ≤ (4 / (q.totient : ℝ)^2) * (Real.pi / r) :=
        mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by positivity)
      _ ≤ _ := by
        dsimp [r]
        field_simp <;> nlinarith only [mul_pos Real.pi_pos nr]

private def farPeak (n q : ℕ) (a : ℕ) :=
  integralOn {t : ℝ | (gridQ n : ℝ)^2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}
    (profile n q ((a : ℝ) / (q : ℝ)))

private theorem singleFarPeak (n q : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hQ : 0 < gridQ n) (a : ℕ) :
    farPeak n q a ≤
      (8 * Real.pi * ((n : ℝ) / (gridQ n : ℝ)^2)) / (q.totient : ℝ)^2 := by
  have hr : 0 < (gridQ n : ℝ)^2 / (n : ℝ) := by positivity
  apply (peakOutside n q hq ((a : ℝ) / (q : ℝ)) _ hr).trans_eq
  field_simp <;> ring

private def numerators (q : ℕ) :=
  (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)

private theorem countNumerators (q : ℕ) (hq : 0 < q) :
    (numerators q).card ≤ 2 * q.totient := by
  have card : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]
  have sub : numerators q ⊆
      insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp ha
    rcases eq_or_ne a q with rfl | h
    · simp
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hr; omega), hc⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  rw [card] at bound
  have hp := Nat.totient_pos.mpr hq
  omega

private theorem totientSquare (q : ℕ) :
    q ≤ 2 * q.totient^2 ∧ (¬ 2 ∣ q → q ≤ q.totient^2) := by
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    rcases eq_or_ne q 0 with rfl | h0
    · simp
    rcases eq_or_ne q 1 with rfl | h1
    · simp
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
    have hp2 := hp.two_le
    have hm : 0 < m := Nat.pos_of_ne_zero (fun hz => h0 (by simp [hz]))
    have lt : m < p * m := by nlinarith [Nat.mul_le_mul_right m hp2]
    obtain ⟨all, odd⟩ := ih m lt
    have lift (f c : ℕ) (eq : (p * m).totient = f * m.totient) (hf : p ≤ f^2)
        (h : m ≤ c * m.totient^2) : p * m ≤ c * (p * m).totient^2 := by
      calc
        _ ≤ f^2 * (c * m.totient^2) := Nat.mul_le_mul hf h
        _ = _ := by rw [eq]; ring
    have both (f : ℕ) (eq : (p * m).totient = f * m.totient) (hf : p ≤ f^2) :
        p * m ≤ 2 * (p * m).totient^2 ∧
          (¬ 2 ∣ p * m → p * m ≤ (p * m).totient^2) := by
      refine ⟨lift f 2 eq hf all, ?_⟩
      intro hn
      have hodd := odd (fun h => hn (dvd_mul_of_dvd_right h p))
      simpa only [one_mul] using lift f 1 eq hf (by simpa using hodd)
    by_cases divides : p ∣ m
    · exact both p (Nat.totient_mul_of_dvd divides) (by nlinarith [Nat.le_mul_self p])
    · have eq := Nat.totient_mul_of_prime_of_not_dvd hp divides
      by_cases two : p = 2
      · subst p
        simp only [Nat.reduceSub, one_mul] at eq
        constructor
        · rw [eq]
          exact Nat.mul_le_mul_left 2 (odd divides)
        · simp
      · apply both (p - 1) eq
        have e : p = (p - 1) + 1 := by omega
        have g : 2 ≤ p - 1 := by omega
        nlinarith [Nat.mul_le_mul_right (p - 1) g]

private theorem totientSum (m : ℕ) :
    (∑ j ∈ Finset.range m, 1 / ((j + 1).totient : ℝ)) ≤
      4 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let u := Real.sqrt (m : ℝ)
    let v := Real.sqrt ((m : ℝ) + 1)
    let f : ℝ := (m + 1).totient
    have fp : 0 < f := by
      dsimp [f]
      exact_mod_cast (Nat.totient_pos.mpr (Nat.succ_pos m))
    have hb : (m : ℝ) + 1 ≤ 2 * f^2 := by
      dsimp [f]
      exact_mod_cast (totientSquare (m + 1)).1
    have hu : u^2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hv : v^2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have uv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
    have pos : 0 ≤ v := Real.sqrt_nonneg _
    have v2 : v ≤ 2 * f := by
      by_contra! hh
      have h := mul_pos (sub_pos.mpr hh) (show 0 < v + 2 * f by linarith)
      nlinarith only [hb, hv, h, sq_nonneg f]
    have bound : v + u ≤ 4 * f := by linarith
    have step : 1 / f ≤ 4 * (v - u) := by
      apply (div_le_iff₀ fp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right bound (sub_nonneg.mpr uv), hu, hv]
    rw [Finset.sum_range_succ, Nat.cast_succ]
    change _ ≤ 4 * v
    linarith only [ih, step]

theorem farTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 0 < gridQ n) :
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤
      64 * Real.pi * (n : ℝ) / (gridQ n : ℝ) := by
  let Q := gridQ n
  let C := 8 * Real.pi * ((n : ℝ) / (Q : ℝ)^2)
  have pos : 0 ≤ C := by dsimp [C]; positivity
  have bb (q : ℕ) (hq : 0 < q) :
      (∑ a ∈ numerators q, farPeak n q a) ≤
        (2 * C) * (1 / (q.totient : ℝ)) := by
    have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    calc
      _ ≤ ∑ _a ∈ numerators q, C / (q.totient : ℝ)^2 :=
        Finset.sum_le_sum fun a _ => singleFarPeak n q hn hq hQ a
      _ = ((numerators q).card : ℝ) * (C / (q.totient : ℝ)^2) := by simp
      _ ≤ (2 * (q.totient : ℝ)) * (C / (q.totient : ℝ)^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast countNumerators q hq
      _ = _ := by field_simp <;> ring
  have index : Finset.Icc 1 (Q^2) =
      (Finset.range (Q^2)).map (addRightEmbedding 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, h, rfl⟩
      omega
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (Q^2), (2 * C) * (1 / (q.totient : ℝ)) :=
      Finset.sum_le_sum fun q h => bb q (Finset.mem_Icc.mp h).1
    _ = (2 * C) * (∑ j ∈ Finset.range (Q^2), 1 / ((j + 1).totient : ℝ)) := by
      rw [index, ← Finset.mul_sum, Finset.sum_map]
      rfl
    _ ≤ (2 * C) * (4 * Real.sqrt ((Q^2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (totientSum (Q^2)) (by positivity)
    _ = _ := by
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
      dsimp [C, Q]
      field_simp <;> ring

theorem farTails (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2),
        ∑ a ∈ numerators q, farPeak n q a) ≤ ε * (n : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (64 * Real.pi / ε)
  let B := max 1 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^B) hn
  have hb : B ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by
    unfold gridQ
    nlinarith [Nat.le_mul_self (Nat.log 2 (n + 2))]
  have hQ : 0 < gridQ n := lt_of_lt_of_le (by dsimp [B]; omega) hq
  apply (farTailQuantitative n hn' hQ).trans
  have hM' : 64 * Real.pi / ε ≤ (gridQ n : ℝ) :=
    hM.trans (by exact_mod_cast (le_trans (le_max_right 1 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM')
    (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

private theorem packetVariation (m : ℕ) (hm : 0 < m) (x y : ℝ) :
    |packet m x / (m : ℝ) - packet m y / (m : ℝ)| ≤
      2 * Real.pi * (2 : ℝ)^m * |x - y| := by
  have mr : (0 : ℝ) < m := by exact_mod_cast hm
  let C := 2 * Real.pi * (2 : ℝ)^m * |x - y|
  rw [← sub_div, abs_div, abs_of_pos mr]
  apply (div_le_iff₀ mr).mpr
  unfold packet
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range m,
        |Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * x) -
          Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * y)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _j ∈ Finset.range m, C := by
      apply Finset.sum_le_sum
      intro j hj
      let f := 2 * Real.pi * (2 : ℝ)^(j + 1)
      apply (Real.abs_cos_sub_cos_le (f * x) (f * y)).trans
      rw [← mul_sub, abs_mul, abs_of_nonneg (by dsimp [f]; positivity : 0 ≤ f)]
      dsimp [f, C]
      gcongr <;> first | exact Finset.mem_range.mp hj | norm_num
    _ = _ := by simp [C] <;> ring

private theorem exponentialRoom (m : ℕ) (hm : 128 ≤ m) :
    48 * (2 * (m : ℝ) + 3)^4 ≤ (2 : ℝ)^m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      _ ≤ 2 * (48 * (2 * ((128 + k : ℕ) : ℝ) + 3)^4) := by
        apply sub_nonneg.mp
        push_cast
        ring_nf
        positivity
      _ ≤ 2 * (2 : ℝ)^(128 + k) := by linarith only [ih]
      _ = _ := by
        rw [show 128 + (k + 1) = (128 + k) + 1 by omega, pow_succ]
        ring

theorem rationalCenterStability :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ,
      |x - y| ≤ (gridQ n : ℝ)^2 / (n : ℝ) →
      (1 : ℝ) / 2 < packet (length n) x / (length n : ℝ) →
      (1 : ℝ) / 3 < packet (length n) y / (length n : ℝ) := by
  refine ⟨2^256, ?_⟩
  intro n hn x y hxy hpeak
  let k := Nat.log 2 n
  let m := length n
  have hk : 256 ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hlen : m = k / 2 := by dsimp [m, k, length]; omega
  have hm : 128 ≤ m := by omega
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^256) hn
  have nr : (0 : ℝ) < n := by exact_mod_cast hn'
  have top := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have base : 2^k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have next : Nat.log 2 (n + 2) ≤ k + 1 := by
    by_contra! tooBig
    have pw := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show k + 2 ≤ Nat.log 2 (n + 2) by omega)
    have up := Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
    change n < 2^(k + 1) at top
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at pw
    have one : 2 ≤ 2^(k + 1) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k + 1 by omega)
    omega
  have qbound : (gridQ n : ℝ)^2 ≤ (2 * (m : ℝ) + 3)^4 := by
    have h : Nat.log 2 (n + 2) ≤ 2 * m + 3 := by omega
    have h' : (Nat.log 2 (n + 2) : ℝ) ≤ 2 * (m : ℝ) + 3 := by exact_mod_cast h
    unfold gridQ
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h' 4
  have pn : ((2 : ℝ)^m)^2 ≤ n := by
    rw [← pow_mul]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show m * 2 ≤ k by omega)).trans base
  have hq : 48 * (gridQ n : ℝ)^2 ≤ (2 : ℝ)^m := by
    linarith only [exponentialRoom m hm, qbound]
  have coeff : 12 * Real.pi * (gridQ n : ℝ)^2 ≤ (2 : ℝ)^m := by
    linarith only [hq,
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg (gridQ n : ℝ))]
  have cost : 2 * Real.pi * (2 : ℝ)^m * |x - y| ≤ 1 / 6 := by
    apply (mul_le_mul_of_nonneg_left hxy
      (by positivity : 0 ≤ 2 * Real.pi * (2 : ℝ)^m)).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ nr).mpr
    linarith only [mul_le_mul_of_nonneg_right coeff
      (by positivity : 0 ≤ (2 : ℝ)^m), pn]
  have bound := (packetVariation m (by omega) x y).trans cost
  change (1 : ℝ) / 2 < packet m x / (m : ℝ) at hpeak
  change (1 : ℝ) / 3 < packet m y / (m : ℝ)
  linarith only [le_abs_self (packet m x / (m : ℝ) - packet m y / (m : ℝ)),
    bound, hpeak]

private def peaks (n : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((gridQ n)^2),
    ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      4 * (n : ℝ)^2 /
        ((Nat.totient q : ℝ)^2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ)))^2))

private theorem onFiniteSum {ι : Type*} (T : Finset ι) {s : Set ℝ}
    (hs : MeasurableSet s) (f : ι → ℝ → ℝ) (hc : ∀ i ∈ T, Continuous (f i)) :
    integralOn s (fun t => ∑ i ∈ T, f i t) = ∑ i ∈ T, integralOn s (f i) := by
  have eq : s.indicator (fun t => ∑ i ∈ T, f i t) =
      fun t => ∑ i ∈ T, s.indicator (f i) t := by
    funext t
    by_cases h : t ∈ s <;> simp [h]
  unfold integralOn
  rw [eq, intervalIntegral.integral_finsetSum (fun i hi => onRegion hs (hc i hi))]

private abbrev detected (n q a : ℕ) :=
  (1 : ℝ) / 3 < packet (length n) ((a : ℝ) / (q : ℝ)) / (length n : ℝ)

private def centerWeight (n q : ℕ) :=
  min (1 : ℝ) ((q : ℝ) / (gridQ n : ℝ)) *
    (((Finset.range (q + 1)).filter
      (fun a => Nat.Coprime a q ∧ detected n q a)).card : ℝ) /
        (q.totient : ℝ)^2

theorem modelFromCenters
    (counts : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      integralOn (resonant n) (peaks n) ≤ ε * (n : ℝ) := by
  intro ε hε
  obtain ⟨C, hC⟩ := counts (ε / (16 * Real.pi)) (by positivity)
  obtain ⟨F, hF⟩ := farTails (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := rationalCenterStability
  refine ⟨max 1 (max K (max F C)), ?_⟩
  intro n hn
  have hn' : 0 < n := by omega
  have g : 1 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num <;> omega)
  have hQ : 0 < gridQ n := by unfold gridQ; positivity
  let D := Finset.Icc 1 ((gridQ n)^2)
  let P := 8 * Real.pi * (n : ℝ)
  let V := fun q : ℕ =>
    P * min 1 ((q : ℝ) / (gridQ n : ℝ)) / (q.totient : ℝ)^2
  have bound (q : ℕ) (hq : 0 < q) (a : ℕ) (ha : a ≤ q) :
      integralOn (resonant n) (profile n q ((a : ℝ) / (q : ℝ))) ≤
        farPeak n q a + (if detected n q a then V q else 0) := by
    let c := (a : ℝ) / (q : ℝ)
    let r := (gridQ n : ℝ)^2 / (n : ℝ)
    by_cases h : detected n q a
    · rw [if_pos h]
      apply (oneCenterMass n q a hn' hq hQ ha).trans
      apply le_add_of_nonneg_left
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t _
      change 0 ≤ ({t : ℝ | r < |t - c|}.indicator (profile n q c)) t
      by_cases ht : t ∈ {t : ℝ | r < |t - c|}
      · rw [Set.indicator_of_mem ht]
        exact profileNonneg n q c t
      · rw [Set.indicator_of_notMem ht]
    · rw [if_neg h, add_zero]
      have sub : resonant n ⊆ {t : ℝ | r < |t - c|} := by
        intro t ht
        change r < |t - c|
        by_contra! hh
        exact h (hK n (by omega) t c hh ht.2)
      have hs : MeasurableSet {t : ℝ | r < |t - c|} :=
        (isOpen_lt continuous_const
          (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
      exact onSubset (measurableMask n) hs sub (profileContinuous n q hq c)
        (profileNonneg n q c)
  have accumulate (q : ℕ) (hq : q ∈ D) :
      integralOn (resonant n)
          (fun t => ∑ a ∈ numerators q, profile n q ((a : ℝ) / (q : ℝ)) t) ≤
        (∑ a ∈ numerators q, farPeak n q a) + P * centerWeight n q := by
    have pos := (Finset.mem_Icc.mp hq).1
    rw [onFiniteSum (numerators q) (measurableMask n) _
      (fun a _ => profileContinuous n q pos _)]
    apply (Finset.sum_le_sum (fun a (ha : a ∈ numerators q) =>
      bound q pos a
        (by have h := Finset.mem_range.mp (Finset.mem_filter.mp ha).1; omega))).trans_eq
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    congr 1
    simp only [numerators, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul,
      centerWeight, V]
    ring
  calc
    _ = ∑ q ∈ D, integralOn (resonant n)
        (fun t => ∑ a ∈ numerators q, profile n q ((a : ℝ) / (q : ℝ)) t) := by
      apply onFiniteSum D (measurableMask n)
      intro q hq
      apply continuous_finsetSum
      intro a _
      exact profileContinuous n q (Finset.mem_Icc.mp hq).1 _
    _ ≤ ∑ q ∈ D,
        ((∑ a ∈ numerators q, farPeak n q a) + P * centerWeight n q) :=
      Finset.sum_le_sum accumulate
    _ = (∑ q ∈ D, ∑ a ∈ numerators q, farPeak n q a) +
        P * (∑ q ∈ D, centerWeight n q) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ε / 2 * (n : ℝ) + P * (ε / (16 * Real.pi)) := by
      apply add_le_add (hF n (by omega))
        (mul_le_mul_of_nonneg_left (hC n (by omega))
          (by dsimp [P]; positivity))
    _ = _ := by
      dsimp [P]
      field_simp <;> ring

private abbrev lowOrderTest (n q : ℕ) := q % 2 = 1 ∧
  ((Finset.Icc 1 ((Nat.log 2 (gridQ n) + 1)^2)).filter
    (fun j => q ∣ 2^j - 1)).Nonempty

theorem combineCenterCounts
    (slow : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter
        (fun q => lowOrderTest n q), centerWeight n q) ≤ ε)
    (rest : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter
        (fun q => ¬ lowOrderTest n q), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨A, hA⟩ := slow (ε / 2) (by positivity)
  obtain ⟨B, hB⟩ := rest (ε / 2) (by positivity)
  refine ⟨max A B, ?_⟩
  intro n hn
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 ((gridQ n)^2)) (lowOrderTest n)]
  linarith only [hA n (by omega), hB n (by omega)]

end
end Conjectures.Goldbach.PacketModelFromCenterCounts_aux

theorem Conjectures.Goldbach.PacketModelFromCenterCounts :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let o := fun n q : ℕ => q % 2 = 1 ∧
       ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter
         (fun j => q ∣ 2^j-1)).Nonempty;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q),
         min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
           (((Finset.range (q+1)).filter (fun a =>
             Nat.Coprime a q ∧
             (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
             (Nat.totient q:ℝ)^2) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let o := fun n q : ℕ => q % 2 = 1 ∧
       ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter
         (fun j => q ∣ 2^j-1)).Nonempty;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => ¬ o n q),
         min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
           (((Finset.range (q+1)).filter (fun a =>
             Nat.Coprime a q ∧
             (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
             (Nat.totient q:ℝ)^2) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ,
       1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
       |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
     let G := fun (n : ℕ) (t : ℝ) =>
       ∑ q ∈ Finset.Icc 1 ((Q n)^2),
         ∑ a ∈ (Finset.range (q+1)).filter
           (fun a => Nat.Coprime a q),
           4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 *
             (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2));
     let m := fun (s : Set ℝ) (f : ℝ → ℝ) =>
       intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       m (B n) (G n) ≤ ε*(n:ℝ)) := by
  intro slow rest
  apply Conjectures.Goldbach.PacketModelFromCenterCounts_aux.modelFromCenters
  exact Conjectures.Goldbach.PacketModelFromCenterCounts_aux.combineCenterCounts slow rest
