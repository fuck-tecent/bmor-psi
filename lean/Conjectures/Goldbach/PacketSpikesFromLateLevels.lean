import Mathlib

namespace Conjectures.Goldbach.PacketSpikesFromLateLevels_aux

noncomputable section

private def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
private def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
private def low (n k : ℕ) := if k^3 ≤ n then w k else 0
private def high (n k : ℕ) := w k - low n k
private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := (Nat.log 2 (n+2))^2
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t-(i.val.2:ℝ)/(i.val.1:ℝ)| ≤ (Q:ℝ)/((i.val.1:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hQ,ha,hc,ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q,a),hq,hQ,ha,hc⟩,ht⟩
    · intro ht
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1,i.val.2,i.property.1,i.property.2.1,i.property.2.2.1,i.property.2.2.2,hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
private def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2
private theorem phaseUnit (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]
private theorem pairHalves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..(1/2), f t + f (t+1/2) := by
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show (1/2:ℝ)+1/2 = 1 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)).symm

private theorem scaleHalf (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..(1/2), g (2*t)) = (1/2) * ∫ t in (0:ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

private theorem doublePeriod (g : ℝ → ℝ) (hc : Continuous g) (hp : Function.Periodic g 1) :
    (∫ t in (0:ℝ)..1, g (2*t)) = ∫ t in (0:ℝ)..1, g t := by
  have hd : Continuous (fun t : ℝ => g (2*t)) := hc.comp (continuous_const.mul continuous_id)
  rw [pairHalves _ hd]
  simp only [show ∀ t : ℝ, 2*(t+1/2) = 2*t+1 by intro t; ring, show ∀ y : ℝ, g (y+1) = g y from hp]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable ..) (hd.intervalIntegrable ..), scaleHalf]
  ring

/-- The two inverse branches of doubling give opposite first cosines and the same remaining weight. -/
theorem doublingTilt (s : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hp : Function.Periodic g 1) (hn : ∀ t, 0 ≤ g t) :
    (∫ t in (0:ℝ)..1, Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) ≤
      Real.cosh s * ∫ t in (0:ℝ)..1, g t := by
  let f := fun t : ℝ => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  have hd : Continuous (fun t : ℝ => (2*Real.cosh s)*g (2*t)) := by fun_prop
  change (∫ t in (0:ℝ)..1, f t) ≤ _
  rw [pairHalves f hf]
  calc
    _ ≤ ∫ t in (0:ℝ)..(1/2), (2*Real.cosh s)*g (2*t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hf.add hs).intervalIntegrable ..)
        (hd.intervalIntegrable ..)
      intro t _
      have hcos : Real.cosh (s*Real.cos (2*Real.pi*t)) ≤ Real.cosh s := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (abs_le.mpr
          ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg s)).trans_eq (mul_one _)
      change Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t) +
        Real.exp (s*Real.cos (2*Real.pi*(t+1/2)))*g (2*(t+1/2)) ≤ _
      rw [show 2*Real.pi*(t+1/2) = 2*Real.pi*t+Real.pi by ring, Real.cos_add_pi,
        show 2*(t+1/2) = 2*t+1 by ring, hp (2*t), mul_neg, ← add_mul]
      rw [Real.cosh_eq] at hcos
      exact mul_le_mul_of_nonneg_right (by linarith) (hn _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, scaleHalf]; ring

private def series (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*t)
private def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)

private theorem periodSeries (m : ℕ) : Function.Periodic (series m) 1 := by
  intro t
  unfold series
  apply Finset.sum_congr rfl
  intro j _
  have heq : 2*Real.pi*(2:ℝ)^j*(t+1) = 2*Real.pi*(2:ℝ)^j*t + ((2^j:ℕ):ℝ)*(2*Real.pi) := by
    push_cast
    ring
  rw [heq, Real.cos_add_nat_mul_two_pi]

private theorem seriesSucc (m : ℕ) (t : ℝ) :
    series (m+1) t = Real.cos (2*Real.pi*t) + series m (2*t) := by
  unfold series
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm (∑ j ∈ Finset.range m, _) _]
  apply congrArg (fun u : ℝ => Real.cos (2*Real.pi*t) + u)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [pow_succ]
  ring

/-- Laplace transform of the actual unnormalised real packet, starting at frequency two. -/
theorem exponentialMoment (m : ℕ) (s : ℝ) :
    (∫ t in (0:ℝ)..1, Real.exp (s*packet m t)) ≤ (Real.cosh s)^m := by
  have hc (k : ℕ) : Continuous (fun t => Real.exp (s*series k t)) := by unfold series; fun_prop
  have hp (k : ℕ) : Function.Periodic (fun t => Real.exp (s*series k t)) 1 :=
    fun t => congrArg (fun u : ℝ => Real.exp (s*u)) (periodSeries k t)
  have h (k : ℕ) : (∫ t in (0:ℝ)..1, Real.exp (s*series k t)) ≤ (Real.cosh s)^k := by
    induction k with
    | zero => simp [series]
    | succ k ih =>
      simp only [seriesSucc, mul_add, Real.exp_add]
      exact (doublingTilt s _ (hc k) (hp k) (fun t => (Real.exp_pos _).le)).trans
        ((mul_le_mul_of_nonneg_left ih (Real.cosh_pos _).le).trans_eq (pow_succ' ..).symm)
  have shift (t : ℝ) : packet m t = series m (2*t) := by
    unfold packet series
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [pow_succ]
    ring
  simp only [shift]
  exact (doublePeriod _ (hc m) (hp m)).le.trans (h m)

/-- Exponential Markov at s=1/2, for the one-sided real exceptional set. -/
theorem upperTail (m : ℕ) (_hm : 0 < m) :
    (∫ t in (0:ℝ)..1, if (m:ℝ)/2 < packet m t then (1:ℝ) else 0) ≤ Real.exp (-(m:ℝ)/8) := by
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have hi : IntervalIntegrable (A.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hA
  have he : Continuous (fun t : ℝ => Real.exp (-(m:ℝ)/4) * Real.exp ((1/2)*packet m t)) := by fun_prop
  change (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t) ≤ _
  calc
    _ ≤ ∫ t in (0:ℝ)..1, Real.exp (-(m:ℝ)/4) * Real.exp ((1/2)*packet m t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi (he.intervalIntegrable ..)
      intro t _
      rw [← Real.exp_add]
      by_cases ht : t ∈ A
      · rw [Set.indicator_of_mem ht]
        change (m:ℝ)/2 < packet m t at ht
        exact (Real.one_le_exp_iff.mpr (by linarith))
      · rw [Set.indicator_of_notMem ht]
        exact (Real.exp_pos _).le
    _ ≤ Real.exp (-(m:ℝ)/4) * (Real.cosh (1/2))^m := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (exponentialMoment m (1/2)) (Real.exp_pos _).le
    _ ≤ Real.exp (-(m:ℝ)/4) * (Real.exp (1/8))^m := by
      have hs := Real.cosh_le_exp_half_sq (1/2)
      norm_num at hs
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)
private def resonant (n : ℕ) := {t : ℝ | t ∉ arcs n ∧
  (1:ℝ)/2 < packet (length n) t / (length n:ℝ)}

private theorem maskedArea (n : ℕ) :
    (∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t) ≤
      Real.exp (-(length n:ℝ)/8) := by
  let m := length n
  have hm : 0 < m := by dsimp [m, length]; omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have heq : resonant n = (arcs n)ᶜ ∩ A := by
    ext t
    change (_ ∧ (1:ℝ)/2 < packet m t / (m:ℝ)) ↔ (_ ∧ (m:ℝ)/2 < packet m t)
    rw [lt_div_iff₀ hmr, show (1:ℝ)/2*(m:ℝ) = (m:ℝ)/2 by ring] <;> rfl
  have integ {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hs
  rw [heq]
  apply le_trans _ (upperTail m hm)
  change (∫ t in (0:ℝ)..1, ((arcs n)ᶜ ∩ A).indicator (fun _ => (1:ℝ)) t) ≤
    ∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t
  apply intervalIntegral.integral_mono_on (by norm_num)
    (integ ((measurableArcs n).compl.inter hA)) (integ hA)
  intro t _
  by_cases ht : t ∈ A <;> by_cases hs : t ∈ (arcs n)ᶜ <;> simp [ht,hs]

/-- The real one-sided exception remains small after multiplying by any fixed log power. -/
theorem maskLogDecay (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (1+Real.log (n:ℝ))^d *
      (∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t) ≤ ε := by
  have ht : Filter.Tendsto (fun x : ℝ => x^d * Real.exp (-(1/8:ℝ)*x))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ) (1/8) (by norm_num)
  have hε' : 0 < ε/(5:ℝ)^d := by positivity
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε')
  obtain ⟨M,hM⟩ := exists_nat_ge R
  refine ⟨max 1 (2^(2*M)), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) (show 2^(2*M) ≤ n by omega)
  have hl1 : 1 ≤ length n := le_max_left _ _
  have hlM : M ≤ length n := by unfold length; omega
  have htM := hR (length n:ℝ) (hM.trans (by exact_mod_cast hlM))
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx : (n:ℝ) < (2:ℝ)^((Nat.log 2 n)+1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have hln := Real.log_le_log hn0 hx.le
  rw [Real.log_pow] at hln
  have hceil : Nat.log 2 n + 1 ≤ 2*length n+2 := by unfold length; omega
  have hrceil : ((Nat.log 2 n + 1:ℕ):ℝ) ≤ 2*(length n:ℝ)+2 := by exact_mod_cast hceil
  have ht2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpoly : 1+Real.log (n:ℝ) ≤ 5*(length n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n + 1))
    have hl : (1:ℝ) ≤ length n := by exact_mod_cast hl1
    linarith
  have hnon : 0 ≤ 1+Real.log (n:ℝ) := by linarith [Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn1)]
  calc
    _ ≤ (1+Real.log (n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (maskedArea n) (pow_nonneg hnon _)
    _ ≤ (5*(length n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnon hpoly _) (Real.exp_pos _).le
    _ ≤ ε := by
      rw [mul_pow, mul_assoc, show -(length n:ℝ)/8 = -(1/8:ℝ)*(length n:ℝ) by ring]
      have hh := (lt_div_iff₀ (by positivity : 0 < (5:ℝ)^d)).mp htM
      linarith only [hh]

private def rationalWindows (n : ℕ) (eligible : ℕ → Prop) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (gridQ n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ eligible q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ ((gridQ n:ℝ)^2)/((q:ℝ)*(n:ℝ))}
private def shortOrder (n q : ℕ) : Prop :=
  Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (gridQ n)+1)^2 ∧ q ∣ 2^j-1
private def density (n : ℕ) (t : ℝ) := ‖spec n (high n) t‖^2
private def ceilingEnergy (n : ℕ) := (n:ℝ)*(1+Real.log (n:ℝ))^4
private def regionMass (n : ℕ) (s : Set ℝ) :=
  ∫ t in (0:ℝ)..1, s.indicator (density n) t

private theorem measurableWindows (n : ℕ) (p : ℕ → Prop) : MeasurableSet (rationalWindows n p) := by
  let Index := {i : ℕ × ℕ // 1 ≤ i.1 ∧ i.1 ≤ (gridQ n)^2 ∧ i.2 ≤ i.1 ∧ i.2.Coprime i.1 ∧ p i.1}
  have eq : rationalWindows n p = ⋃ i : Index,
      {t : ℝ | |t-(i.val.2:ℝ)/(i.val.1:ℝ)| ≤ ((gridQ n:ℝ)^2)/((i.val.1:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,hq,hQ,ha,hc,hp,ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q,a),hq,hQ,ha,hc,hp⟩,ht⟩
    · intro ht
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1,i.val.2,i.property.1,i.property.2.1,i.property.2.2.1,
        i.property.2.2.2.1,i.property.2.2.2.2,hi⟩
  rw [eq]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

private theorem measurableMask (n : ℕ) : MeasurableSet (resonant n) := by
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  exact (measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet

private theorem continuousDensity (n : ℕ) : Continuous (density n) := by
  unfold density spec phase
  fun_prop

private theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

private theorem regionSplit (n : ℕ) {s a : Set ℝ} (hs : MeasurableSet s) (ha : MeasurableSet a) :
    regionMass n s = regionMass n (s ∩ a) + regionMass n (s \ a) := by
  have he : s.indicator (density n) =
      fun t => (s ∩ a).indicator (density n) t + (s \ a).indicator (density n) t := by
    funext t
    by_cases h : t ∈ s <;> by_cases k : t ∈ a <;> simp [h,k]
  unfold regionMass
  rw [he, intervalIntegral.integral_add (onRegion (hs.inter ha) (continuousDensity n))
    (onRegion (hs.diff ha) (continuousDensity n))]

private def deep (n : ℕ) := resonant n \ rationalWindows n (fun _ => True)
private def spikes (n : ℕ) := {t : ℝ | ceilingEnergy n < density n t}
private def integralOn (s : Set ℝ) (f : ℝ → ℝ) := ∫ t in (0:ℝ)..1, s.indicator f t
private def level (n j : ℕ) := (2:ℝ)^j * ceilingEnergy n
private def firstLevel (n : ℕ) := length n / 16
private def lastLevel (n : ℕ) := Nat.log 2 n + 3
private def above (n j : ℕ) := deep n ∩ {t | level n j < density n t}
private def bin (n j : ℕ) := deep n ∩ {t | level n j < density n t ∧ density n t ≤ 2*level n j}
private def smallPeaks (n : ℕ) := resonant n ∩ {t | density n t ≤ level n (firstLevel n)}

private theorem heightPositive (n j : ℕ) : 0 ≤ level n j := by
  unfold level ceilingEnergy
  positivity

private theorem heightSucc (n j : ℕ) : level n (j+1) = 2*level n j := by
  unfold level; rw [pow_succ]; ring

private theorem measurableDeep (n : ℕ) : MeasurableSet (deep n) :=
  (measurableMask n).diff (measurableWindows n _)

private theorem measurableAbove (n j : ℕ) : MeasurableSet (above n j) :=
  (measurableDeep n).inter (isOpen_lt continuous_const (continuousDensity n)).measurableSet

private theorem measurableBin (n j : ℕ) : MeasurableSet (bin n j) :=
  (measurableDeep n).inter ((isOpen_lt continuous_const (continuousDensity n)).measurableSet.inter
    (isClosed_le (continuousDensity n) continuous_const).measurableSet)

/-- The entire resonant mask is inexpensive even at a polynomially raised amplitude cutoff. -/
theorem lowPeaksSublinear (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n ≥ N,
    regionMass n (smallPeaks n) ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 8 (ε^2) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn
  let x := 1+Real.log (n:ℝ)
  let A := integralOn (resonant n) (fun _ => (1:ℝ))
  let m := firstLevel n
  have hx : 1 ≤ x := by
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    dsimp [x]; linarith [Real.log_nonneg h1]
  have ha : 0 ≤ A := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _; by_cases ht : t ∈ resonant n <;> simp [ht]
  have h₁ : x^8*A ≤ ε^2 := hN n (by omega)
  have h₂ : A ≤ Real.exp (-(length n:ℝ)/8) := maskedArea n
  have hm : 16*m ≤ length n := by unfold m firstLevel; omega
  have hmr : 2*(m:ℝ) ≤ (length n:ℝ)/8 := by
    have hr : 16*(m:ℝ) ≤ (length n:ℝ) := by exact_mod_cast hm
    linarith
  have hmexp : (2:ℝ)^m ≤ Real.exp (m:ℝ) := by
    have ht := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (by linarith [Real.add_one_le_exp (1:ℝ)] : (2:ℝ) ≤ Real.exp 1) m
    simpa only [← Real.exp_nat_mul, mul_one] using ht
  have damp : ((2:ℝ)^m)^2*A ≤ 1 := by
    calc
      _ ≤ (Real.exp (m:ℝ))^2 * Real.exp (-(length n:ℝ)/8) := by gcongr
      _ = Real.exp (2*(m:ℝ)-(length n:ℝ)/8) := by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; push_cast; ring
      _ ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have prod := mul_le_mul h₁ damp (by positivity) (sq_nonneg ε)
  have hs : (2:ℝ)^m*x^4*A ≤ ε := by
    by_contra! h
    have hdiff := mul_pos (sub_pos.mpr h) (by linarith : 0 < (2:ℝ)^m*x^4*A+ε)
    nlinarith only [prod,hdiff]
  let C := level n m
  have hc := heightPositive n m
  have hmS : MeasurableSet (smallPeaks n) :=
    (measurableMask n).inter (isClosed_le (continuousDensity n) continuous_const).measurableSet
  calc
    _ ≤ ∫ t in (0:ℝ)..1, C * (resonant n).indicator (fun _ => (1:ℝ)) t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hmS (continuousDensity n))
        ((onRegion (measurableMask n) continuous_const).const_mul _)
      intro t _
      change (smallPeaks n).indicator (density n) t ≤ C * (resonant n).indicator _ t
      by_cases ht : t ∈ smallPeaks n
      · have hr := ht.1
        simpa only [Set.indicator_of_mem ht,Set.indicator_of_mem hr,mul_one] using (show density n t ≤ C from ht.2)
      · by_cases hr : t ∈ resonant n <;> simp [ht,hr,C,hc]
    _ = C*A := intervalIntegral.integral_const_mul ..
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
      change (2:ℝ)^m*((n:ℝ)*x^4)*A ≤ _
      linarith only [hb]

private theorem lastHeight (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : density n t ≤ level n (lastLevel n) := by
  let x := 1+Real.log (n:ℝ)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ x := by dsimp [x]; linarith [Real.log_nonneg hn']
  have coeff (k : ℕ) (hk : k ≤ n) : |high n k| ≤ x := by
    unfold high low
    by_cases hl : k^3 ≤ n
    · simp [hl]; linarith
    · simp only [hl, if_false, sub_zero, w]
      by_cases hp : k.Prime
      · have hpos : (1:ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
        rw [if_pos hp,abs_of_nonneg (Real.log_nonneg hpos)]
        have h := Real.log_le_log (by positivity : 0<(k:ℝ)) (show (k:ℝ)≤n by exact_mod_cast hk)
        dsimp [x]; linarith
      · simp [hp]; linarith
  have mag : ‖spec n (high n) t‖ ≤ 2*(n:ℝ)*x := by
    unfold spec
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖((high n k:ℝ):ℂ)*phase ((k:ℝ)*t)‖ := norm_sum_le ..
      _ ≤ ∑ _k ∈ Finset.range (n+1), x := Finset.sum_le_sum fun k hk => by
        simpa only [norm_mul,phaseUnit,mul_one,Complex.norm_real,Real.norm_eq_abs] using coeff k (by have := Finset.mem_range.mp hk; omega)
      _ ≤ _ := by simp; nlinarith only [mul_nonneg (sub_nonneg.mpr hn') (by linarith : 0≤x)]
  have he : (n:ℝ) ≤ (2:ℝ)^(Nat.log 2 n+1) := by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  have hp : 4*(n:ℝ) ≤ (2:ℝ)^lastLevel n := by
    change _ ≤ (2:ℝ)^((Nat.log 2 n+1)+2)
    rw [pow_add]; nlinarith only [he]
  have xx : x^2 ≤ x^4 := by
    have hu : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg x)]
  calc
    _ ≤ (2*(n:ℝ)*x)^2 := pow_le_pow_left₀ (norm_nonneg _) mag 2
    _ = (4*(n:ℝ))*((n:ℝ)*x^2) := by ring
    _ ≤ (2:ℝ)^lastLevel n * ((n:ℝ)*x^4) := by gcongr
    _ = _ := rfl

private theorem bandStep (n j : ℕ) : regionMass n (above n j) =
    regionMass n (above n (j+1)) + regionMass n (bin n j) := by
  let s := {t : ℝ | level n (j+1) < density n t}
  have hm : MeasurableSet s := (isOpen_lt continuous_const (continuousDensity n)).measurableSet
  have nested : above n j ∩ s = above n (j+1) := by
    ext t
    change ((_ ∧ level n j < density n t) ∧ level n (j+1) < density n t) ↔ _
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      have hi : level n (j+1) < density n t := h.2
      rw [heightSucc] at hi
      exact ⟨⟨h.1,by linarith [heightPositive n j]⟩,h.2⟩
  have lower : above n j \ s = bin n j := by
    ext t
    change ((_ ∧ level n j < density n t) ∧ ¬level n (j+1) < density n t) ↔ _
    rw [heightSucc,not_lt]
    exact and_assoc
  simpa only [nested,lower] using regionSplit n (measurableAbove n j) hm

private theorem binEnergy (n j : ℕ) : regionMass n (bin n j) ≤
    2*level n j * integralOn (bin n j) (fun _ => (1:ℝ)) := by
  let C := 2*level n j
  have hm := measurableBin n j
  unfold regionMass integralOn
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hm (continuousDensity n))
    ((onRegion hm continuous_const).const_mul _)
  intro t _
  by_cases ht : t ∈ bin n j
  · simpa [ht] using (show density n t ≤ 2*level n j from ht.2.2)
  · simp [ht]

private theorem sumBins (n i J : ℕ) (hi : i ≤ J) (b : ℝ)
    (last : ∀ t, density n t ≤ level n J)
    (bounds : ∀ j, i ≤ j → j < J → regionMass n (bin n j) ≤ b) :
    regionMass n (above n i) ≤ (J-i:ℕ)*b := by
  have partialSum : ∀ l j : ℕ, i ≤ j → j+l ≤ J → regionMass n (above n j) ≤
      regionMass n (above n (j+l)) + (l:ℝ)*b := by
    intro l
    induction l with
    | zero => intro j _ _; simp
    | succ l ih =>
      intro j hj hJ
      have prev := ih (j+1) (by omega) (by omega)
      have cur := bounds j hj (by omega)
      have eq := bandStep n j
      rw [show j+(l+1)=(j+1)+l by omega]
      push_cast
      linarith
  have empty : above n J = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_lt.mpr (last t)) ht.2
  have h := partialSum (J-i) i le_rfl (by omega)
  rw [show i+(J-i)=J by omega,empty] at h
  simpa [regionMass] using h
theorem spikesFromLateLevels
    (late : ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ j : ℕ, firstLevel n ≤ j → j < lastLevel n →
      level n j * integralOn (bin n j) (fun _ => (1:ℝ)) ≤ (n:ℝ)/(100000*(1+Real.log (n:ℝ))^2)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n (deep n ∩ spikes n) ≤ (n:ℝ)/2304 := by
  obtain ⟨N,hN⟩ := late
  obtain ⟨M,hM⟩ := lowPeaksSublinear (1/4608) (by norm_num)
  refine ⟨max 1 (max N M), ?_⟩
  intro n hn he
  let x := 1+Real.log (n:ℝ)
  let b := (n:ℝ)/(100000*x^2)
  let i := firstLevel n
  let J := lastLevel n
  have hn1 : 1 ≤ n := by omega
  have hx : 1 ≤ x := by dsimp [x]; linarith [Real.log_nonneg (by exact_mod_cast hn1 : (1:ℝ) ≤ n)]
  have hi : i ≤ J := by dsimp [i,J,firstLevel,lastLevel,length]; omega
  have hJ : (J:ℝ) ≤ 3*x := by
    have hp : (2:ℝ)^Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n≠0)
    have h := Real.log_le_log (by positivity : 0<(2:ℝ)^Nat.log 2 n) hp
    rw [Real.log_pow] at h
    have half : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have aux := mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))
    dsimp [J,lastLevel,x]; push_cast; linarith [Real.log_nonneg (by exact_mod_cast hn1 : (1:ℝ) ≤ n)]
  have band (j : ℕ) (hj : i ≤ j) (h : j<J) : regionMass n (bin n j) ≤ 2*b := by
    have h' := hN n (by omega) he j hj h
    change level n j * integralOn (bin n j) (fun _ => (1:ℝ)) ≤ b at h'
    linarith only [binEnergy n j,h']
  have tall := sumBins n i J hi (2*b) (lastHeight n hn1) band
  have ht : regionMass n (above n i) ≤ (n:ℝ)/4608 := by
    have count : ((J-i:ℕ):ℝ) ≤ 3*x := (by exact_mod_cast Nat.sub_le J i : ((J-i:ℕ):ℝ) ≤ (J:ℝ)).trans hJ
    have bb : 0 ≤ 2*b := by dsimp [b]; positivity
    apply tall.trans ((mul_le_mul_of_nonneg_right count bb).trans ?_)
    dsimp [b]
    have x0 : 0 < x := by linarith
    field_simp
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hx),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (x-1))]
  have hs : MeasurableSet (deep n ∩ spikes n) :=
    (measurableDeep n).inter (isOpen_lt continuous_const (continuousDensity n)).measurableSet
  have hm : MeasurableSet (smallPeaks n) :=
    (measurableMask n).inter (isClosed_le (continuousDensity n) continuous_const).measurableSet
  have maj : regionMass n (deep n ∩ spikes n) ≤ regionMass n (smallPeaks n) + regionMass n (above n i) := by
    unfold regionMass
    rw [← intervalIntegral.integral_add (onRegion hm (continuousDensity n)) (onRegion (measurableAbove n i) (continuousDensity n))]
    apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs (continuousDensity n))
      ((onRegion hm (continuousDensity n)).add (onRegion (measurableAbove n i) (continuousDensity n)))
    intro t _
    have nn : 0 ≤ density n t := sq_nonneg _
    by_cases hh : t ∈ deep n ∩ spikes n
    · by_cases h : density n t ≤ level n i
      · have small : t ∈ smallPeaks n := ⟨hh.1.1,h⟩
        have outside : t ∉ above n i := fun h' => (not_lt.mpr h) h'.2
        simp [hh,small,outside]
      · have top : t ∈ above n i := ⟨hh.1,lt_of_not_ge h⟩
        have small : t ∉ smallPeaks n := fun h' => h h'.2
        simp [hh,small,top]
    · by_cases a : t ∈ above n i <;> by_cases c : t ∈ smallPeaks n <;> simp [hh,a,c,nn]
  linarith only [maj,ht,hM n (by omega)]

end

end Conjectures.Goldbach.PacketSpikesFromLateLevels_aux

theorem Conjectures.Goldbach.PacketSpikesFromLateLevels :
(let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ j : ℕ, L n / 16 ≤ j → j < Nat.log 2 n + 3 → let y := (2:ℝ)^j*T n; y * m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | y < F n t ∧ F n t ≤ 2*y}) (fun _ => (1:ℝ)) ≤ (n:ℝ)/(100000*(1+Real.log (n:ℝ))^2)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n:ℝ)/2304):= by
  intro late
  exact Conjectures.Goldbach.PacketSpikesFromLateLevels_aux.spikesFromLateLevels late
