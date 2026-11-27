import Mathlib

namespace Conjectures.Goldbach.PacketEnergyFromRationalRegions_aux

noncomputable section

namespace GoldbachBudget

def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
def low (n k : ℕ) := if k^3 ≤ n then w k else 0
def high (n k : ℕ) := w k - low n k

theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
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

end GoldbachBudget

namespace GoldbachPacket

theorem pairHalves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..(1/2), f t + f (t+1/2) := by
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show (1/2:ℝ)+1/2 = 1 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)).symm

theorem scaleHalf (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..(1/2), g (2*t)) = (1/2) * ∫ t in (0:ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

theorem doublePeriod (g : ℝ → ℝ) (hc : Continuous g) (hp : Function.Periodic g 1) :
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

def series (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*t)
def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)

theorem periodSeries (m : ℕ) : Function.Periodic (series m) 1 := by
  intro t
  unfold series
  apply Finset.sum_congr rfl
  intro j _
  have heq : 2*Real.pi*(2:ℝ)^j*(t+1) = 2*Real.pi*(2:ℝ)^j*t + ((2^j:ℕ):ℝ)*(2*Real.pi) := by
    push_cast
    ring
  rw [heq, Real.cos_add_nat_mul_two_pi]

theorem seriesSucc (m : ℕ) (t : ℝ) :
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

def length (n : ℕ) := max 1 (Nat.log 2 n / 2)
def resonant (n : ℕ) := {t : ℝ | t ∉ GoldbachBudget.arcs n ∧
  (1:ℝ)/2 < packet (length n) t / (length n:ℝ)}

theorem maskedArea (n : ℕ) :
    (∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t) ≤
      Real.exp (-(length n:ℝ)/8) := by
  let m := length n
  have hm : 0 < m := by dsimp [m, length]; omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have heq : resonant n = (GoldbachBudget.arcs n)ᶜ ∩ A := by
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
  change (∫ t in (0:ℝ)..1, ((GoldbachBudget.arcs n)ᶜ ∩ A).indicator (fun _ => (1:ℝ)) t) ≤
    ∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t
  apply intervalIntegral.integral_mono_on (by norm_num)
    (integ ((GoldbachBudget.measurableArcs n).compl.inter hA)) (integ hA)
  intro t _
  by_cases ht : t ∈ A <;> by_cases hs : t ∈ (GoldbachBudget.arcs n)ᶜ <;> simp [ht,hs]

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


def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2

def rationalWindows (n : ℕ) (eligible : ℕ → Prop) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (gridQ n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ eligible q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ ((gridQ n:ℝ)^2)/((q:ℝ)*(n:ℝ))}
def shortOrder (n q : ℕ) : Prop :=
  Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (gridQ n)+1)^2 ∧ q ∣ 2^j-1
def density (n : ℕ) (t : ℝ) := ‖GoldbachBudget.spec n (GoldbachBudget.high n) t‖^2
def ceilingEnergy (n : ℕ) := (n:ℝ)*(1+Real.log (n:ℝ))^4
def regionMass (n : ℕ) (s : Set ℝ) :=
  ∫ t in (0:ℝ)..1, s.indicator (density n) t

theorem measurableWindows (n : ℕ) (p : ℕ → Prop) : MeasurableSet (rationalWindows n p) := by
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

theorem measurableMask (n : ℕ) : MeasurableSet (resonant n) := by
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  exact (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet

theorem continuousDensity (n : ℕ) : Continuous (density n) := by
  unfold density GoldbachBudget.spec GoldbachBudget.phase
  fun_prop

theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

theorem regionSplit (n : ℕ) {s a : Set ℝ} (hs : MeasurableSet s) (ha : MeasurableSet a) :
    regionMass n s = regionMass n (s ∩ a) + regionMass n (s \ a) := by
  have he : s.indicator (density n) =
      fun t => (s ∩ a).indicator (density n) t + (s \ a).indicator (density n) t := by
    funext t
    by_cases h : t ∈ s <;> by_cases k : t ∈ a <;> simp [h,k]
  unfold regionMass
  rw [he, intervalIntegral.integral_add (onRegion (hs.inter ha) (continuousDensity n))
    (onRegion (hs.diff ha) (continuousDensity n))]

def deep (n : ℕ) := resonant n \ rationalWindows n (fun _ => True)
def spikes (n : ℕ) := {t : ℝ | ceilingEnergy n < density n t}

theorem deepFloorBudget : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    regionMass n (deep n \ spikes n) ≤ ε*(n:ℝ) := by
  intro ε hε
  obtain ⟨N,hN⟩ := maskLogDecay 4 ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hb := measurableMask n
  have hd := hb.diff (measurableWindows n (fun _ => True))
  have hp : MeasurableSet (spikes n) := (isOpen_lt continuous_const (continuousDensity n)).measurableSet
  let f := (resonant n).indicator (fun _ => (1:ℝ))
  have pos : 0 ≤ ceilingEnergy n := by unfold ceilingEnergy; positivity
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ceilingEnergy n * f t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (onRegion (hd.diff hp) (continuousDensity n)) ((onRegion hb continuous_const).const_mul _)
      intro t _
      change (deep n \ spikes n).indicator (density n) t ≤ ceilingEnergy n * f t
      by_cases ht : t ∈ deep n \ spikes n
      · have hh := ht.1.1
        have hle : density n t ≤ ceilingEnergy n := le_of_not_gt ht.2
        simpa [f,ht,hh] using hle
      · by_cases hh : t ∈ resonant n <;> simp [f,ht,hh,pos]
    _ = ceilingEnergy n * (∫ t in (0:ℝ)..1, f t) := intervalIntegral.integral_const_mul ..
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (hN n hn) (Nat.cast_nonneg (α := ℝ) n)
      dsimp only [ceilingEnergy,f]
      linarith only [h]

theorem energyFromRegions
    (slow : ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n
      ((resonant n ∩ rationalWindows n (fun _ => True)) ∩ rationalWindows n (shortOrder n)) ≤ (n:ℝ)/2304)
    (rest : ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n
      ((resonant n ∩ rationalWindows n (fun _ => True)) \ rationalWindows n (shortOrder n)) ≤ (n:ℝ)/2304)
    (large : ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n (deep n ∩ spikes n) ≤ (n:ℝ)/2304) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n (resonant n) ≤ (n:ℝ)/576 := by
  obtain ⟨A,hA⟩ := slow
  obtain ⟨B,hB⟩ := rest
  obtain ⟨C,hC⟩ := large
  obtain ⟨D,hD⟩ := deepFloorBudget (1/2304) (by norm_num)
  refine ⟨max (max A B) (max C D), ?_⟩
  intro n hn he
  have hm := measurableMask n
  have hw := measurableWindows n (fun _ => True)
  have ho := measurableWindows n (shortOrder n)
  have hp : MeasurableSet (spikes n) := (isOpen_lt continuous_const (continuousDensity n)).measurableSet
  have e₁ := regionSplit n hm hw
  have e₂ := regionSplit n (hm.inter hw) ho
  have e₃ := regionSplit n (s := deep n) (hm.diff hw) hp
  change regionMass n (resonant n) = _ + regionMass n (deep n) at e₁
  linarith only [e₁,e₂,e₃,hA n (by omega) he,hB n (by omega) he,hC n (by omega) he,hD n (by omega)]


end GoldbachPacket
end
end Conjectures.Goldbach.PacketEnergyFromRationalRegions_aux

open Conjectures.Goldbach.PacketEnergyFromRationalRegions_aux

theorem Conjectures.Goldbach.PacketEnergyFromRationalRegions :
  (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576)
  := by
    intro slow rest large
    have h := GoldbachPacket.energyFromRegions slow rest large
    dsimp [GoldbachBudget.w, GoldbachBudget.phase, GoldbachBudget.spec,
      GoldbachBudget.arcs, GoldbachBudget.low, GoldbachBudget.high,
      GoldbachPacket.packet, GoldbachPacket.length, GoldbachPacket.resonant,
      GoldbachPacket.gridQ, GoldbachPacket.rationalWindows, GoldbachPacket.shortOrder,
      GoldbachPacket.density, GoldbachPacket.ceilingEnergy, GoldbachPacket.regionMass] at h ⊢
    exact h
