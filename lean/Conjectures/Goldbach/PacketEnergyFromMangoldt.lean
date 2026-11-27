import Mathlib

namespace Conjectures.Goldbach.PacketEnergyFromMangoldt_aux
noncomputable section

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

def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

def series (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*t)

def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)

def resonant (n : ℕ) := {t : ℝ | t ∉ arcs n ∧
  (1:ℝ)/2 < packet (length n) t / (length n:ℝ)}

def lambdaSpec (n : ℕ) := spec n ArithmeticFunction.vonMangoldt

def highSpec (n : ℕ) := spec n (high n)

def perturbation (n : ℕ) (t : ℝ) := ‖lambdaSpec n t-highSpec n t‖^2

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

theorem phaseUnit (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem nonnegativePrime (k : ℕ) : 0 ≤ w k := by
  unfold w
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  · exact le_rfl

theorem mangoldtSpectralError (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖lambdaSpec n t-highSpec n t‖ ≤ 4*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
  let Λ := ArithmeticFunction.vonMangoldt
  let lo := low n
  let hi := high n
  let R := Finset.range (n+1)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have dpos (k : ℕ) : 0 ≤ Λ k-w k := by
    dsimp only [Λ,w]
    by_cases hp : k.Prime
    · simp [hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp,ArithmeticFunction.vonMangoldt_nonneg]
  have lpos (k : ℕ) : 0 ≤ lo k := by
    unfold lo low
    split <;> first | exact nonnegativePrime _ | exact le_rfl
  have main (k : ℕ) : |Λ k-hi k| = (Λ k-w k)+lo k := by
    have eq : Λ k-hi k = (Λ k-w k)+lo k := by
      show Λ k - (w k - low n k) = (Λ k - w k) + low n k
      ring
    rw [eq,abs_of_nonneg (add_nonneg (dpos k) (lpos k))]
  have ri : R = Finset.Icc 0 n := by ext k; simp [R]
  have hh : (∑ k ∈ R, (Λ k - w k)) = Chebyshev.psi (n:ℝ)-Chebyshev.theta (n:ℝ) := by
    rw [Finset.sum_sub_distrib,Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,
      Finset.sum_filter,Nat.floor_natCast,ri]
    rfl
  have lowMass : (∑ k ∈ R, lo k) ≤ 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
    let T := R.filter (fun k => k^3≤n)
    have eq : (∑ k ∈ R, lo k) = ∑ k ∈ T, w k := by
      simp [T,Finset.sum_filter,lo,low]
    have subset : T ⊆ Finset.range (n.sqrt+1) := by
      intro k hk
      have bound := (Finset.mem_filter.mp hk).2
      have hk2 : k^2 ≤ n := by
        by_cases h : k=0
        · simp [h]
        · exact (Nat.pow_le_pow_right (by omega : 0<k) (by decide : 2≤3)).trans bound
      exact Finset.mem_range.mpr
        (by have := Nat.le_sqrt.mpr (show k*k≤n by simpa [pow_two] using hk2); omega)
    have wt {k : ℕ} (hk : k ∈ T) : w k ≤ Real.log (n:ℝ) := by
      have hkn := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      dsimp only [w]
      split_ifs with hp
      · have hk' : 0<(k:ℝ) := by exact_mod_cast hp.pos
        exact Real.log_le_log hk' (by exact_mod_cast (show k≤n by omega))
      · exact hlog
    have hr : (n.sqrt:ℝ) ≤ Real.sqrt (n:ℝ) := by
      have hsq : (n.sqrt:ℝ)*(n.sqrt:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sqrt_le n
      exact Real.le_sqrt_of_sq_le (by simpa only [pow_two] using hsq)
    have h1 := Real.one_le_sqrt.mpr hn'
    rw [eq]
    calc
      _ ≤ ∑ _k ∈ T, Real.log (n:ℝ) := Finset.sum_le_sum fun k hk => wt hk
      _ = (T.card:ℝ)*Real.log (n:ℝ) := by simp
      _ ≤ 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have hcard := Finset.card_le_card subset
        rw [Finset.card_range] at hcard
        have h' : (T.card:ℝ) ≤ (n.sqrt:ℝ)+1 := by exact_mod_cast hcard
        linarith
  have dif : lambdaSpec n t-highSpec n t =
      ∑ k ∈ R, ((Λ k-hi k:ℝ):ℂ)*phase ((k:ℝ)*t) := by
    unfold lambdaSpec highSpec spec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.ofReal_sub,sub_mul,Λ,hi]
  rw [dif]
  calc
    _ ≤ ∑ k ∈ R, ‖((Λ k-hi k:ℝ):ℂ)*phase ((k:ℝ)*t)‖ := norm_sum_le ..
    _ = (∑ k ∈ R, (Λ k-w k)) + ∑ k ∈ R, lo k := by
      simp only [norm_mul,phaseUnit,mul_one,Complex.norm_real,Real.norm_eq_abs,main,
        Finset.sum_add_distrib]
    _ ≤ _ := by rw [hh]; linarith only [Chebyshev.psi_sub_theta_le hn',lowMass]

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
  simp only [show ∀ t : ℝ, 2*(t+1/2) = 2*t+1 by intro t; ring,
    show ∀ y : ℝ, g (y+1) = g y from hp]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable ..) (hd.intervalIntegrable ..), scaleHalf]
  ring

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
  have he : Continuous (fun t : ℝ => Real.exp (-(m:ℝ)/4) * Real.exp ((1/2)*packet m t)) := by
    fun_prop
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
  have hx : (n:ℝ) < (2:ℝ)^((Nat.log 2 n)+1) :=
    by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have hln := Real.log_le_log hn0 hx.le
  rw [Real.log_pow] at hln
  have hceil : Nat.log 2 n + 1 ≤ 2*length n+2 := by unfold length; omega
  have hrceil : ((Nat.log 2 n + 1:ℕ):ℝ) ≤ 2*(length n:ℝ)+2 := by exact_mod_cast hceil
  have ht2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpoly : 1+Real.log (n:ℝ) ≤ 5*(length n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht2 (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n + 1))
    have hl : (1:ℝ) ≤ length n := by exact_mod_cast hl1
    linarith
  have hnon : 0 ≤ 1+Real.log (n:ℝ) :=
    by linarith [Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn1)]
  calc
    _ ≤ (1+Real.log (n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (maskedArea n) (pow_nonneg hnon _)
    _ ≤ (5*(length n:ℝ))^d * Real.exp (-(length n:ℝ)/8) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnon hpoly _) (Real.exp_pos _).le
    _ ≤ ε := by
      rw [mul_pow, mul_assoc, show -(length n:ℝ)/8 = -(1/8:ℝ)*(length n:ℝ) by ring]
      have hh := (lt_div_iff₀ (by positivity : 0 < (5:ℝ)^d)).mp htM
      linarith only [hh]

theorem measurableMask (n : ℕ) : MeasurableSet (resonant n) := by
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by
    unfold packet; fun_prop
  exact (measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet

theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

end

theorem contSpec (n : ℕ) (a : ℕ → ℝ) : Continuous (fun t : ℝ => ‖spec n a t‖^2) := by
  have h : Continuous (fun t : ℝ => spec n a t) := by
    unfold spec phase
    fun_prop
  exact h.norm.pow 2

theorem contDiff (n : ℕ) (a b : ℕ → ℝ) :
    Continuous (fun t : ℝ => ‖spec n a t - spec n b t‖^2) := by
  have h1 : Continuous (fun t : ℝ => spec n a t) := by
    unfold spec phase
    fun_prop
  have h2 : Continuous (fun t : ℝ => spec n b t) := by
    unfold spec phase
    fun_prop
  exact (h1.sub h2).norm.pow 2

theorem maskedError (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    intervalIntegral ((resonant n).indicator (perturbation n)) (0:ℝ) 1 MeasureTheory.volume
      ≤ ε * (n:ℝ) := by
  obtain ⟨N, hN⟩ := maskLogDecay 2 (ε/16) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hl := Real.log_nonneg (by exact_mod_cast hn1 : (1:ℝ) ≤ n)
  have hc : Continuous (perturbation n) := by
    unfold perturbation lambdaSpec highSpec spec phase
    fun_prop
  let C := 16*(n:ℝ)*(1+Real.log (n:ℝ))^2
  have pt (t : ℝ) : perturbation n t ≤ C := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (mangoldtSpectralError n hn1 t) 2
    have id : (4*Real.sqrt (n:ℝ)*Real.log (n:ℝ))^2 = 16*(n:ℝ)*Real.log (n:ℝ)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [id] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (by nlinarith : Real.log (n:ℝ)^2 ≤ (1+Real.log (n:ℝ))^2) (by positivity))
  let A := (resonant n).indicator (fun _ => (1:ℝ))
  show ∫ t in (0:ℝ)..1, (resonant n).indicator (perturbation n) t ≤ ε*(n:ℝ)
  calc
    _ ≤ ∫ t in (0:ℝ)..1, C*A t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion (measurableMask n) hc)
        ((onRegion (measurableMask n) continuous_const).const_mul _)
      intro t _
      by_cases ht : t ∈ resonant n <;> simp [ht,A,pt t]
    _ = C * (∫ t in (0:ℝ)..1, A t) := intervalIntegral.integral_const_mul ..
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (hN n (by omega)) (by positivity : 0 ≤ 16*(n:ℝ))
      dsimp only [C,A]; linarith only [h]

theorem indComb (D : Set ℝ) (hD : MeasurableSet D) (f g h : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (α β : ℝ)
    (hpt : ∀ t ∈ D, f t ≤ α * g t + β * h t) :
    intervalIntegral (D.indicator f) (0:ℝ) 1 MeasureTheory.volume ≤
      α * intervalIntegral (D.indicator g) (0:ℝ) 1 MeasureTheory.volume +
      β * intervalIntegral (D.indicator h) (0:ℝ) 1 MeasureTheory.volume := by
  have hfi : IntervalIntegrable (D.indicator f) MeasureTheory.volume (0:ℝ) 1 := onRegion hD hf
  have hgi : IntervalIntegrable (D.indicator g) MeasureTheory.volume (0:ℝ) 1 := onRegion hD hg
  have hhi : IntervalIntegrable (D.indicator h) MeasureTheory.volume (0:ℝ) 1 := onRegion hD hh
  have hkey : intervalIntegral (fun t => α * D.indicator g t + β * D.indicator h t)
      (0:ℝ) 1 MeasureTheory.volume
      = α * intervalIntegral (D.indicator g) (0:ℝ) 1 MeasureTheory.volume
        + β * intervalIntegral (D.indicator h) (0:ℝ) 1 MeasureTheory.volume := by
    have hadd := intervalIntegral.integral_add (hgi.const_mul α) (hhi.const_mul β)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hadd
    exact hadd
  rw [← hkey]
  apply intervalIntegral.integral_mono_on (by norm_num) hfi ((hgi.const_mul α).add (hhi.const_mul β))
  intro t _
  by_cases ht : t ∈ D
  · simp only [Set.indicator_of_mem ht]
    exact hpt t ht
  · simp only [Set.indicator_of_notMem ht]
    simp

end Conjectures.Goldbach.PacketEnergyFromMangoldt_aux

open Conjectures.Goldbach.PacketEnergyFromMangoldt_aux
  (measurableMask onRegion contSpec contDiff maskedError indComb)

theorem Conjectures.Goldbach.PacketEnergyFromMangoldt :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (B n) (fun t => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2) ≤ (n:ℝ)/640) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro hH w E S Q arcs low high I L K B U
  obtain ⟨N1, hN1⟩ := hH
  obtain ⟨N2, hN2⟩ := maskedError (1/1000000) (by norm_num)
  refine ⟨max N1 N2, ?_⟩
  intro n hn he
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hA : intervalIntegral ((B n).indicator
      (fun t => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2))
      (0:ℝ) 1 MeasureTheory.volume ≤ (n:ℝ)/640 := hN1 n hn1 he
  have hD : intervalIntegral ((B n).indicator
      (fun t => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖^2))
      (0:ℝ) 1 MeasureTheory.volume ≤ (1/1000000) * (n:ℝ) := hN2 n hn2
  have hB : MeasurableSet (B n) := measurableMask n
  have hcf : Continuous (fun t : ℝ => ‖S n (high n) t‖^2) := contSpec n (high n)
  have hcg : Continuous (fun t : ℝ => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2) :=
    contSpec n (fun k => ArithmeticFunction.vonMangoldt k)
  have hch : Continuous (fun t : ℝ =>
      ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖^2) :=
    contDiff n (fun k => ArithmeticFunction.vonMangoldt k) (high n)
  have hpt : ∀ t ∈ B n, ‖S n (high n) t‖^2
      ≤ (17/16) * ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2
        + 17 * ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖^2 := by
    intro t _
    have h1 : ‖S n (high n) t‖ ≤ ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖
        + ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖ := by
      have := norm_le_norm_add_norm_sub' (S n (high n) t)
        (S n (fun k => ArithmeticFunction.vonMangoldt k) t)
      have := norm_sub_rev (S n (high n) t) (S n (fun k => ArithmeticFunction.vonMangoldt k) t)
      linarith
    have h2 := norm_nonneg (S n (high n) t)
    have h3 := norm_nonneg (S n (fun k => ArithmeticFunction.vonMangoldt k) t)
    have h4 := norm_nonneg (S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t)
    nlinarith [sq_nonneg (‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖/4
      - 4*‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖)]
  have hI := indComb (B n) hB (fun t : ℝ => ‖S n (high n) t‖^2)
    (fun t : ℝ => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2)
    (fun t : ℝ => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t - S n (high n) t‖^2)
    hcf hcg hch (17/16) 17 hpt
  show intervalIntegral ((B n).indicator (fun t => ‖S n (high n) t‖^2))
    (0:ℝ) 1 MeasureTheory.volume ≤ (n:ℝ)/576
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith
