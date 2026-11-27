import Mathlib

noncomputable section

namespace Conjectures.Goldbach.PacketShortWheelError_aux

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

def cosineMoment (n h : ℕ) :=
  ∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => Real.cos (2*Real.pi*(h:ℝ)*u)) t
def correlation (n h : ℕ) (a : ℕ → ℝ) :=
  ∑ k ∈ Finset.range (n+1-h), a k * a (k+h)
def shortPart (n : ℕ) (a : ℕ → ℝ) :=
  correlation n 0 a * cosineMoment n 0 + 2 * ∑ h ∈ Finset.Icc 1 (min n ((length n)^2)),
    correlation n h a * cosineMoment n h
def wheel (k : ℕ) := if Nat.Coprime k 30 then (30:ℝ)/8 else 0

theorem zeroMoment (n : ℕ) :
    cosineMoment n 0 = ∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t := by
  simp [cosineMoment]

theorem cosineMomentBound (n h : ℕ) : |cosineMoment n h| ≤ cosineMoment n 0 := by
  have hc : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hc).measurableSet
  have hi : IntervalIntegrable ((resonant n).indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ)) MeasureTheory.volume 0 1)).indicator hm
  rw [zeroMoment, cosineMoment]
  change ‖∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => Real.cos (2*Real.pi*(h:ℝ)*u)) t‖ ≤ _
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ hi
  apply Filter.Eventually.of_forall
  intro t _
  by_cases ht : t ∈ resonant n
  · simpa [ht, Real.norm_eq_abs] using (abs_le.mpr
      ⟨Real.neg_one_le_cos (2*Real.pi*(h:ℝ)*t), Real.cos_le_one _⟩)
  · simp [ht]

theorem correlationBound (n h : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ k ≤ n, |a k| ≤ M) : |correlation n h a| ≤ ((n:ℝ)+1)*M^2 := by
  unfold correlation
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1-h), M^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [abs_mul, pow_two]
      exact mul_le_mul (ha k (by omega)) (ha (k+h) (by omega)) (abs_nonneg _) hM
    _ = ((n+1-h:ℕ):ℝ) * M^2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
      exact_mod_cast Nat.sub_le (n+1) h

/-- Include lag zero once and each positive lag twice, even if the cutoff exceeds n. -/
theorem shortEnvelope (n : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ k ≤ n, |a k| ≤ M) :
    |shortPart n a| ≤ (1+2*(length n:ℝ)^2)*((n:ℝ)+1)*M^2*cosineMoment n 0 := by
  let H := min n ((length n)^2)
  let B := ((n:ℝ)+1)*M^2*cosineMoment n 0
  have hm0 : 0 ≤ cosineMoment n 0 := (abs_nonneg _).trans (cosineMomentBound n 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have each (h : ℕ) : |correlation n h a * cosineMoment n h| ≤ B := by
    rw [abs_mul]
    exact mul_le_mul (correlationBound n h a M hM ha) (cosineMomentBound n h) (abs_nonneg _) (by positivity)
  have hs : |∑ h ∈ Finset.Icc 1 H, correlation n h a * cosineMoment n h| ≤ (length n:ℝ)^2*B := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ Finset.Icc 1 H, B := Finset.sum_le_sum fun h _ => each h
      _ = (H:ℝ)*B := by simp [Nat.card_Icc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast (min_le_right n ((length n)^2))
  unfold shortPart
  apply (abs_add_le ..).trans
  rw [abs_mul (2:ℝ), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ B + 2*((length n:ℝ)^2*B) := add_le_add (each 0) (by linarith only [hs])
    _ = _ := by dsimp [B]; ring

/-- From n=8 onward the cutoff removes the only even prime. Both lag sequences vanish at odd indices. -/
theorem evenLagSupport (n : ℕ) (hn : 8 ≤ n) (h : ℕ) (hh : Odd h) :
    correlation n h (GoldbachBudget.high n) = 0 ∧ correlation n h wheel = 0 := by
  have highEven (k : ℕ) (hk : k % 2 = 0) : GoldbachBudget.high n k = 0 := by
    by_cases hp : Nat.Prime k
    · have heq := hp.eq_two_or_odd.resolve_right (by omega)
      subst k
      have hcut : 2^3 ≤ n := by omega
      simp only [GoldbachBudget.high, GoldbachBudget.low, if_pos hcut, sub_self]
    · simp [GoldbachBudget.high, GoldbachBudget.low, GoldbachBudget.w, hp]
  have wheelEven (k : ℕ) (hk : k % 2 = 0) : wheel k = 0 := by
    have hnc : ¬Nat.Coprime k 30 := by
      intro hcop
      have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hk) (by decide : 2 ∣ 30)
      rw [hcop.gcd_eq_one] at hd
      norm_num at hd
    simp [wheel, hnc]
  have zero (a : ℕ → ℝ) (ha : ∀ k, k % 2 = 0 → a k = 0) : correlation n h a = 0 := by
    unfold correlation
    apply Finset.sum_eq_zero
    intro k _
    obtain ⟨j,hj⟩ := hh
    by_cases hk : k % 2 = 0
    · rw [ha k hk, zero_mul]
    · rw [ha (k+h) (by omega), mul_zero]
  exact ⟨zero _ highEven, zero _ wheelEven⟩

theorem lengthUpper (n : ℕ) (hn : 1 ≤ n) : (length n:ℝ) ≤ 2*(1+Real.log (n:ℝ)) := by
  have he : (2:ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hl := Real.log_le_log (by positivity : 0 < (2:ℝ)^(Nat.log 2 n)) he
  rw [Real.log_pow] at hl
  have half : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hnat : length n ≤ Nat.log 2 n + 1 := by unfold length; omega
  have hr : (length n:ℝ) ≤ (Nat.log 2 n:ℝ) + 1 := by exact_mod_cast hnat
  linarith [mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))]

/-- The sublinear estimate is uniform over all bounded weights at the prime logarithmic scale. -/
theorem shortAtLogScale (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ k ≤ n, |a k| ≤ 4*(1+Real.log (n:ℝ))) :
    |shortPart n a| ≤ 288*(n:ℝ)*(1+Real.log (n:ℝ))^4*cosineMoment n 0 := by
  let x := 1+Real.log (n:ℝ)
  have hx : 1 ≤ x := by dsimp [x]; linarith [Real.log_nonneg (by exact_mod_cast hn : (1:ℝ) ≤ n)]
  have hl : (length n:ℝ) ≤ 2*x := lengthUpper n hn
  have hl2 : (length n:ℝ)^2 ≤ (2*x)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hl 2
  have hf : 1+2*(length n:ℝ)^2 ≤ 9*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 ≤ cosineMoment n 0 := (abs_nonneg _).trans (cosineMomentBound n 0)
  apply (shortEnvelope n a (4*x) (by linarith) ha).trans
  calc
    _ ≤ (9*x^2)*(2*(n:ℝ))*(4*x)^2*cosineMoment n 0 := by
      gcongr <;> linarith
    _ = _ := by change _ = 288*(n:ℝ)*x^4*cosineMoment n 0; ring

/-- Both absolute short pieces are sublinear, so their difference is sublinear for every n. -/
theorem shortWheelSublinear (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |shortPart n (GoldbachBudget.high n) - shortPart n wheel| ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 4 (ε/576) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  let M := 4*(1+Real.log (n:ℝ))
  have hpr (k : ℕ) (hk : k ≤ n) : |GoldbachBudget.high n k| ≤ M := by
    unfold GoldbachBudget.high GoldbachBudget.low
    by_cases hl : k^3 ≤ n
    · simp [hl]; dsimp [M]; linarith
    · simp only [hl, if_false, sub_zero, GoldbachBudget.w]
      by_cases hp : Nat.Prime k
      · have hpos : (1:ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
        rw [if_pos hp, abs_of_nonneg (Real.log_nonneg hpos)]
        have hle := Real.log_le_log (by positivity : 0 < (k:ℝ)) (show (k:ℝ) ≤ n by exact_mod_cast hk)
        dsimp [M]; linarith
      · simp [hp]; dsimp [M]; linarith
  have hwh (k : ℕ) (_hk : k ≤ n) : |wheel k| ≤ M := by
    dsimp [wheel,M]; split <;> norm_num <;> linarith
  have harea := hN n (by omega)
  rw [← zeroMoment] at harea
  have sum := (abs_sub (shortPart n (GoldbachBudget.high n)) (shortPart n wheel)).trans
    (add_le_add (shortAtLogScale n hn1 _ hpr) (shortAtLogScale n hn1 _ hwh))
  have hx := mul_le_mul_of_nonneg_left harea (Nat.cast_nonneg (α := ℝ) n)
  linarith only [sum,hx]

theorem shortWheelBudget :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      |shortPart n (GoldbachBudget.high n) - shortPart n wheel| ≤ (n:ℝ)/2304 := by
  obtain ⟨N,hN⟩ := shortWheelSublinear (1/2304) (by norm_num)
  exact ⟨N, fun n hn _ => by linarith only [hN n hn]⟩
end GoldbachPacket
end Conjectures.Goldbach.PacketShortWheelError_aux

theorem Conjectures.Goldbach.PacketShortWheelError :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → |short n (high n) - short n model| ≤ (n:ℝ)/2304
  := by
  intro w E S Q arcs low high I L K B U V A model short long
  exact Conjectures.Goldbach.PacketShortWheelError_aux.GoldbachPacket.shortWheelBudget
