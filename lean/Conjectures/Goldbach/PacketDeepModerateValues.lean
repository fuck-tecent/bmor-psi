import Mathlib

namespace Conjectures.Goldbach.PacketDeepModerateValues_aux

noncomputable section

def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n + 2)) ^ 2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))}

private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := (Nat.log 2 (n + 2)) ^ 2
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

private theorem pairHalves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..(1 / 2), f t + f (t + 1 / 2) := by
  have hs : Continuous (fun t : ℝ => f (t + 1 / 2)) :=
    hf.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)).symm

private theorem scaleHalf (g : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..(1 / 2), g (2 * t)) = (1 / 2) * ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

private theorem doublePeriod (g : ℝ → ℝ) (hc : Continuous g) (hp : Function.Periodic g 1) :
    (∫ t in (0 : ℝ)..1, g (2 * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hd : Continuous (fun t : ℝ => g (2 * t)) :=
    hc.comp (continuous_const.mul continuous_id)
  rw [pairHalves _ hd]
  simp only [show ∀ t : ℝ, 2 * (t + 1 / 2) = 2 * t + 1 by intro t; ring,
    show ∀ y : ℝ, g (y + 1) = g y from hp]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable ..) (hd.intervalIntegrable ..),
    scaleHalf]
  ring

private theorem doublingTilt (s : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hp : Function.Periodic g 1) (hn : ∀ t, 0 ≤ g t) :
    (∫ t in (0 : ℝ)..1, Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t)) ≤
      Real.cosh s * ∫ t in (0 : ℝ)..1, g t := by
  let f := fun t : ℝ => Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hs : Continuous (fun t : ℝ => f (t + 1 / 2)) :=
    hf.comp (continuous_id.add continuous_const)
  have hd : Continuous (fun t : ℝ => (2 * Real.cosh s) * g (2 * t)) := by fun_prop
  change (∫ t in (0 : ℝ)..1, f t) ≤ _
  rw [pairHalves f hf]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2), (2 * Real.cosh s) * g (2 * t) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hf.add hs).intervalIntegrable ..) (hd.intervalIntegrable ..)
      intro t _
      have hcos : Real.cosh (s * Real.cos (2 * Real.pi * t)) ≤ Real.cosh s := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left
          (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg s)).trans_eq
          (mul_one _)
      change Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t) +
        Real.exp (s * Real.cos (2 * Real.pi * (t + 1 / 2))) * g (2 * (t + 1 / 2)) ≤ _
      rw [show 2 * Real.pi * (t + 1 / 2) = 2 * Real.pi * t + Real.pi by ring,
        Real.cos_add_pi, show 2 * (t + 1 / 2) = 2 * t + 1 by ring, hp (2 * t),
        mul_neg, ← add_mul]
      rw [Real.cosh_eq] at hcos
      exact mul_le_mul_of_nonneg_right (by linarith) (hn _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, scaleHalf]; ring

def series (m : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ) ^ j * t)

def packet (m : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)

private theorem periodSeries (m : ℕ) : Function.Periodic (series m) 1 := by
  intro t
  unfold series
  apply Finset.sum_congr rfl
  intro j _
  have heq : 2 * Real.pi * (2 : ℝ) ^ j * (t + 1) =
      2 * Real.pi * (2 : ℝ) ^ j * t + ((2 ^ j : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [heq, Real.cos_add_nat_mul_two_pi]

private theorem seriesSucc (m : ℕ) (t : ℝ) :
    series (m + 1) t = Real.cos (2 * Real.pi * t) + series m (2 * t) := by
  unfold series
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm (∑ j ∈ Finset.range m, _) _]
  apply congrArg (fun u : ℝ => Real.cos (2 * Real.pi * t) + u)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [pow_succ]
  ring

private theorem exponentialMoment (m : ℕ) (s : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.exp (s * packet m t)) ≤ (Real.cosh s) ^ m := by
  have hc (k : ℕ) : Continuous (fun t => Real.exp (s * series k t)) := by
    unfold series
    fun_prop
  have hp (k : ℕ) : Function.Periodic (fun t => Real.exp (s * series k t)) 1 :=
    fun t => congrArg (fun u : ℝ => Real.exp (s * u)) (periodSeries k t)
  have h (k : ℕ) :
      (∫ t in (0 : ℝ)..1, Real.exp (s * series k t)) ≤ (Real.cosh s) ^ k := by
    induction k with
    | zero => simp [series]
    | succ k ih =>
      simp only [seriesSucc, mul_add, Real.exp_add]
      exact (doublingTilt s _ (hc k) (hp k) (fun t => (Real.exp_pos _).le)).trans
        ((mul_le_mul_of_nonneg_left ih (Real.cosh_pos _).le).trans_eq (pow_succ' ..).symm)
  have shift (t : ℝ) : packet m t = series m (2 * t) := by
    unfold packet series
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [pow_succ]
    ring
  simp only [shift]
  exact (doublePeriod _ (hc m) (hp m)).le.trans (h m)

private theorem upperTail (m : ℕ) (_hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, if (m : ℝ) / 2 < packet m t then (1 : ℝ) else 0) ≤
      Real.exp (-(m : ℝ) / 8) := by
  let A := {t : ℝ | (m : ℝ) / 2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m : ℝ) / 2)) hc).measurableSet
  have hi : IntervalIntegrable (A.indicator (fun _ => (1 : ℝ)))
      MeasureTheory.volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1 : ℝ))
        MeasureTheory.volume 0 1)).indicator hA
  have he : Continuous
      (fun t => Real.exp (-(m : ℝ) / 4) * Real.exp ((1 / 2 : ℝ) * packet m t)) := by
    fun_prop
  change (∫ t in (0 : ℝ)..1, A.indicator (fun _ => (1 : ℝ)) t) ≤ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,
        Real.exp (-(m : ℝ) / 4) * Real.exp ((1 / 2 : ℝ) * packet m t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi (he.intervalIntegrable ..)
      intro t _
      rw [← Real.exp_add]
      by_cases ht : t ∈ A
      · rw [Set.indicator_of_mem ht]
        change (m : ℝ) / 2 < packet m t at ht
        exact (Real.one_le_exp_iff.mpr (by linarith))
      · rw [Set.indicator_of_notMem ht]
        exact (Real.exp_pos _).le
    _ ≤ Real.exp (-(m : ℝ) / 4) * (Real.cosh (1 / 2 : ℝ)) ^ m := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (exponentialMoment m (1 / 2 : ℝ))
        (Real.exp_pos _).le
    _ ≤ Real.exp (-(m : ℝ) / 4) * (Real.exp (1 / 8 : ℝ)) ^ m := by
      have hs := Real.cosh_le_exp_half_sq (1 / 2 : ℝ)
      norm_num at hs
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

def resonant (n : ℕ) :=
  {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < packet (length n) t / (length n : ℝ)}

theorem measurableResonant (n : ℕ) : MeasurableSet (resonant n) := by
  have hc : Continuous (packet (length n)) := by unfold packet; fun_prop
  have hA : MeasurableSet {t : ℝ | (1 : ℝ) / 2 < packet (length n) t / (length n : ℝ)} :=
    measurableSet_lt measurable_const (hc.measurable.div_const _)
  have heq : resonant n = (arcs n)ᶜ ∩
      {t : ℝ | (1 : ℝ) / 2 < packet (length n) t / (length n : ℝ)} := by
    ext t
    rfl
  rw [heq]
  exact (measurableArcs n).compl.inter hA

private theorem maskedArea (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (resonant n).indicator (fun _ => (1 : ℝ)) t) ≤
      Real.exp (-(length n : ℝ) / 8) := by
  let m := length n
  have hm : 0 < m := by dsimp [m, length]; omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let A := {t : ℝ | (m : ℝ) / 2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m : ℝ) / 2)) hc).measurableSet
  have heq : resonant n = (arcs n)ᶜ ∩ A := by
    ext t
    change (_ ∧ (1 : ℝ) / 2 < packet m t / (m : ℝ)) ↔ (_ ∧ (m : ℝ) / 2 < packet m t)
    rw [lt_div_iff₀ hmr, show (1 : ℝ) / 2 * (m : ℝ) = (m : ℝ) / 2 by ring]
    rfl
  have integ {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator (fun _ => (1 : ℝ)))
        MeasureTheory.volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1 : ℝ))
        MeasureTheory.volume 0 1)).indicator hs
  rw [heq]
  apply le_trans _ (upperTail m hm)
  change (∫ t in (0 : ℝ)..1,
    ((arcs n)ᶜ ∩ A).indicator (fun _ => (1 : ℝ)) t) ≤
    ∫ t in (0 : ℝ)..1, A.indicator (fun _ => (1 : ℝ)) t
  apply intervalIntegral.integral_mono_on (by norm_num)
    (integ ((measurableArcs n).compl.inter hA)) (integ hA)
  intro t _
  by_cases ht : t ∈ A <;> by_cases hs : t ∈ (arcs n)ᶜ <;> simp [ht, hs]

theorem maskLogDecay (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (1 + Real.log (n : ℝ)) ^ d *
      (∫ t in (0 : ℝ)..1, (resonant n).indicator (fun _ => (1 : ℝ)) t) ≤ ε := by
  have ht : Filter.Tendsto (fun x : ℝ => x ^ d * Real.exp (-(1 / 8 : ℝ) * x))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) (1 / 8) (by norm_num)
  have hε' : 0 < ε / (5 : ℝ) ^ d := by positivity
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε')
  obtain ⟨M, hM⟩ := exists_nat_ge R
  refine ⟨max 1 (2 ^ (2 * M)), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2 ^ (2 * M) ≤ n by omega)
  have hl1 : 1 ≤ length n := le_max_left _ _
  have hlM : M ≤ length n := by unfold length; omega
  have htM := hR (length n : ℝ) (hM.trans (by exact_mod_cast hlM))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hln := Real.log_le_log hn0 hx.le
  rw [Real.log_pow] at hln
  have hceil : Nat.log 2 n + 1 ≤ 2 * length n + 2 := by unfold length; omega
  have hrceil : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * (length n : ℝ) + 2 := by
    exact_mod_cast hceil
  have ht2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpoly : 1 + Real.log (n : ℝ) ≤ 5 * (length n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht2
      (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n + 1))
    have hl : (1 : ℝ) ≤ length n := by exact_mod_cast hl1
    linarith
  have hnon : 0 ≤ 1 + Real.log (n : ℝ) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn1)]
  calc
    _ ≤ (1 + Real.log (n : ℝ)) ^ d * Real.exp (-(length n : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left (maskedArea n) (pow_nonneg hnon _)
    _ ≤ (5 * (length n : ℝ)) ^ d * Real.exp (-(length n : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnon hpoly _)
        (Real.exp_pos _).le
    _ ≤ ε := by
      rw [mul_pow, mul_assoc,
        show -(length n : ℝ) / 8 = -(1 / 8 : ℝ) * (length n : ℝ) by ring]
      have hh := (lt_div_iff₀ (by positivity : 0 < (5 : ℝ) ^ d)).mp htM
      linarith only [hh]

end

end Conjectures.Goldbach.PacketDeepModerateValues_aux

private theorem measurable_rational_arcs (M : ℕ) (R : ℝ) (nn : ℕ) (p : ℕ → Prop) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (nn : ℝ))} := by
  have cover : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ R / ((q : ℝ) * (nn : ℝ))} =
      ⋃ i : {pr : ℕ × ℕ // 1 ≤ pr.1 ∧ pr.1 ≤ M ∧ pr.2 ≤ pr.1 ∧ Nat.Coprime pr.2 pr.1 ∧ p pr.1},
        {t : ℝ | |t - (i.val.2 : ℝ) / (i.val.1 : ℝ)| ≤
          R / ((i.val.1 : ℝ) * (nn : ℝ))} := by
    ext t
    constructor
    · rintro ⟨q, a, hq, hM, ha, hc, hp, ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hM, ha, hc, hp⟩, ht⟩
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1, i.property.2.2.1,
        i.property.2.2.2.1, i.property.2.2.2.2, hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet

private theorem indicator_ceiling_bound (D B : Set ℝ) (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hDB : D ⊆ B) (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) (hc : 0 ≤ c) (h : ∀ t ∈ D, f t ≤ c) :
    intervalIntegral (D.indicator f) (0 : ℝ) 1 MeasureTheory.volume ≤
      c * intervalIntegral (B.indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1 MeasureTheory.volume := by
  have h1 : IntervalIntegrable (D.indicator f) MeasureTheory.volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hf.intervalIntegrable 0 1)).indicator hD
  have h2 : IntervalIntegrable (B.indicator (fun _ : ℝ => (1 : ℝ)))
      MeasureTheory.volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 1)).indicator hB
  have h3 : IntervalIntegrable (fun t => c * B.indicator (fun _ : ℝ => (1 : ℝ)) t)
      MeasureTheory.volume (0 : ℝ) 1 := h2.const_mul c
  calc intervalIntegral (D.indicator f) (0 : ℝ) 1 MeasureTheory.volume
      ≤ intervalIntegral (fun t => c * B.indicator (fun _ : ℝ => (1 : ℝ)) t) (0 : ℝ) 1
          MeasureTheory.volume := by
        apply intervalIntegral.integral_mono_on (by norm_num) h1 h3
        intro t _
        by_cases ht : t ∈ D
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hDB ht), mul_one]
          exact h t ht
        · rw [Set.indicator_of_notMem ht]
          exact mul_nonneg hc (by by_cases hB' : t ∈ B <;> simp [hB'])
    _ = c * intervalIntegral (B.indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1
        MeasureTheory.volume := by
        rw [intervalIntegral.integral_const_mul]

theorem Conjectures.Goldbach.PacketDeepModerateValues :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, m ((B n \ (W n (fun _ => True))) \ {t : ℝ | T n < F n t}) (F n) ≤ ε*(n:ℝ)
 := by
  intro w E S Q arcs low high L K B W F T m ε hε
  obtain ⟨N1, hN1⟩ :=
    Conjectures.Goldbach.PacketDeepModerateValues_aux.maskLogDecay 4 ε hε
  refine ⟨N1, fun n hn => ?_⟩
  have hFc : Continuous (F n) := by
    simp only [F, S, E]
    fun_prop
  have hBeq : B n = Conjectures.Goldbach.PacketDeepModerateValues_aux.resonant n := rfl
  have hB : MeasurableSet (B n) := by
    rw [hBeq]
    exact Conjectures.Goldbach.PacketDeepModerateValues_aux.measurableResonant n
  have hW : MeasurableSet (W n (fun _ => True)) :=
    measurable_rational_arcs ((Q n) ^ 2) ((Q n : ℝ) ^ 2) n (fun _ => True)
  have hD : MeasurableSet ((B n \ (W n (fun _ => True))) \ {t : ℝ | T n < F n t}) :=
    (hB.diff hW).diff (measurableSet_lt measurable_const hFc.measurable)
  have hT : T n = (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 4 := rfl
  have hT0 : 0 ≤ T n := by
    rw [hT]
    positivity
  have hI : intervalIntegral
      (((B n \ (W n (fun _ => True))) \ {t : ℝ | T n < F n t}).indicator (F n))
      (0 : ℝ) 1 MeasureTheory.volume ≤
      T n * intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1
        MeasureTheory.volume :=
    indicator_ceiling_bound _ (B n) hD hB (fun t ht => ht.1.1) (F n) hFc (T n) hT0
      (fun t ht => not_lt.mp ht.2)
  have hM : (1 + Real.log (n : ℝ)) ^ 4 *
      intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1
        MeasureTheory.volume ≤ ε := by
    rw [hBeq]
    exact hN1 n hn
  show intervalIntegral
      (((B n \ (W n (fun _ => True))) \ {t : ℝ | T n < F n t}).indicator (F n))
      (0 : ℝ) 1 MeasureTheory.volume ≤ ε * (n : ℝ)
  calc _ ≤ T n * intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1
        MeasureTheory.volume := hI
    _ = (n : ℝ) * ((1 + Real.log (n : ℝ)) ^ 4 *
        intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1
          MeasureTheory.volume) := by
          rw [hT]
          ring
    _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg n)
    _ = ε * (n : ℝ) := by ring
