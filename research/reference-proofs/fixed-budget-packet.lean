import Mathlib

/-- The strong Goldbach conjecture as a proposition. -/
def StrongGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Positive prime-only log mass detects precisely the existence of a prime pair. -/
theorem strongGoldbach_iff_primeMass : StrongGoldbach ↔
    ∀ n : ℕ, 4 ≤ n → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
      0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  have pos {k : ℕ} (hk : Nat.Prime k) : 0 < w k := by
    simp only [w, if_pos hk]
    exact Real.log_pos (by exact_mod_cast hk.one_lt)
  have nn (k : ℕ) : 0 ≤ w k := by
    by_cases h : Nat.Prime k
    · exact (pos h).le
    · simp [w, h]
  constructor
  · intro h n hn he
    obtain ⟨p, q, hp, hq, hpq⟩ := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i)
    have hm : p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have hd : n-p = q := by omega
    have hpos : 0 < w (n-p) := by simpa only [hd] using pos hq
    exact lt_of_lt_of_le (mul_pos (pos hp) hpos)
      (Finset.single_le_sum (f := fun i => w i * w (n-i))
        (fun i _ => mul_nonneg (nn i) (nn (n-i))) hm)
  · intro h n hn he
    have hs := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i) at hs
    by_contra noPair
    have hz : (∑ i ∈ Finset.range (n+1), w i * w (n-i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases hp : Nat.Prime i
      · have hq : ¬ Nat.Prime (n-i) := fun hq => noPair ⟨i,n-i,hp,hq,by omega⟩
        simp [w,hq]
      · simp [w,hp]
    linarith

namespace GoldbachBudget
noncomputable section

private def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
private def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
private def full (n : ℕ) (s : Set ℝ) : ℂ :=
  intervalIntegral (fun t => s.indicator
    (fun u => (spec n w u)^2 * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def pair (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => spec n a u * spec n b u * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def low (n k : ℕ) := if k^3 ≤ n then w k else 0
private def high (n k : ℕ) := w k - low n k
private def mass (n : ℕ) := ∑ p ∈ Finset.range (n+1), w p * w (n-p)

/-- Arithmetic inputs are hypotheses. The conclusion concerns the original frequency n. -/
theorem fixedToDyadic
    (coeff : ∀ n, full n (arcs n) + full n (arcs n)ᶜ = (mass n : ℂ))
    (major : ∃ M : ℕ, ∀ n ≥ M, Even n → (n:ℝ)/144 ≤ (full n (arcs n)).re)
    (split : ∀ n, pair n w w =
      pair n (low n) (low n) + 2*pair n (low n) (high n) + pair n (high n) (high n))
    (ll : ∀ e : ℝ, 0 < e → ∃ U : ℕ, ∀ n ≥ U, ‖pair n (low n) (low n)‖ ≤ e*(n:ℝ))
    (lh : ∀ e : ℝ, 0 < e → ∃ V : ℕ, ∀ n ≥ V, ‖pair n (low n) (high n)‖ ≤ e*(n:ℝ))
    (bulk : ∃ H : ℕ, ∀ n ≥ H, Even n → -(n:ℝ)/288 ≤ (pair n (high n) (high n)).re) :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X →
      Even n → c*(n:ℝ) ≤ mass n := by
  obtain ⟨M,hM⟩ := major
  obtain ⟨H,hH⟩ := bulk
  obtain ⟨U,hU⟩ := ll (1/2304) (by norm_num)
  obtain ⟨V,hV⟩ := lh (1/2304) (by norm_num)
  refine ⟨1/576, max (max M H) (max U V), by norm_num, ?_⟩
  intro X n hX hXn _ hn
  have bound {z : ℂ} {a : ℝ} (hz : ‖z‖ ≤ a) : -a ≤ z.re :=
    le_trans (neg_le_neg hz) (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hm := hM n (by omega) hn
  have hh := hH n (by omega) hn
  have hll := bound (hU n (by omega))
  have hlh := bound (hV n (by omega))
  have eqminor : full n (arcs n)ᶜ = pair n w w := by simp only [full, pair, pow_two]
  have eqc := coeff n
  rw [eqminor, split n, two_mul] at eqc
  have hr := congrArg Complex.re eqc
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  linarith only [hr, hm, hh, hll, hlh, Nat.cast_nonneg (α := ℝ) n]

private def K (n : ℕ) (t : ℝ) : ℝ :=
  let L := max 1 (Nat.log 2 n / 2)
  (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)
private def J (n : ℕ) (v : ℝ → ℝ) :=
  (intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t)
    0 1 MeasureTheory.volume).re

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

private def kernelIntegrand (n : ℕ) (v : ℝ → ℝ) (t : ℝ) :=
  (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t

private theorem kernelIntegrable (n : ℕ) (v : ℝ → ℝ) (hv : Continuous v) :
    IntervalIntegrable (kernelIntegrand n v) MeasureTheory.volume (0:ℝ) 1 := by
  have cont : Continuous (fun u : ℝ => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) := by
    unfold spec phase
    fun_prop
  have h := cont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
  exact h.indicator (measurableArcs n).compl

theorem packetPartition (n : ℕ) :
    (pair n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t) := by
  let F := fun t : ℝ => spec n (high n) t * spec n (high n) t * phase (-(n:ℝ)*t)
  let T := kernelIntegrand n
  have hK : Continuous (K n) := by unfold K; fun_prop
  have partition : (fun t => (arcs n)ᶜ.indicator F t) =
      fun t => T (K n) t + T (fun u => 1-K n u) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [F, T, kernelIntegrand, Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [T, kernelIntegrand, ht]
  unfold pair J
  change (intervalIntegral (fun t => (arcs n)ᶜ.indicator F t) 0 1 MeasureTheory.volume).re = _
  have hD : Continuous (fun t : ℝ => 1 - K n t) := continuous_const.sub hK
  rw [partition, intervalIntegral.integral_add (kernelIntegrable n (K n) hK)
    (kernelIntegrable n (fun t => 1 - K n t) hD)] <;> rfl

private def cutoff (n : ℕ) : ℝ := 1 / (2304 * (1 + (Real.log (n:ℝ))^2))
private def small (n : ℕ) (t : ℝ) :=
  max (-(cutoff n)) (min (cutoff n) (1 - K n t))
private def rest (n : ℕ) (t : ℝ) := 1 - K n t - small n t

theorem restZero (n : ℕ) (t : ℝ) (h : |1-K n t| ≤ cutoff n) : rest n t = 0 := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp only [rest, small, min_eq_right hu, max_eq_right hl, sub_self]

private theorem defectSplit (n : ℕ) :
    J n (fun t => 1-K n t) = J n (small n) + J n (rest n) := by
  have hk : Continuous (K n) := by unfold K; fun_prop
  have hd : Continuous (fun t : ℝ => 1-K n t) := continuous_const.sub hk
  have hs : Continuous (small n) := continuous_const.max (continuous_const.min hd)
  have hr : Continuous (rest n) := hd.sub hs
  have hsum : kernelIntegrand n (fun t => 1-K n t) = fun t =>
      kernelIntegrand n (small n) t + kernelIntegrand n (rest n) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, rest, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [kernelIntegrand, ht]
  change (intervalIntegral (kernelIntegrand n _) 0 1 MeasureTheory.volume).re = _
  rw [hsum, intervalIntegral.integral_add (kernelIntegrable n _ hs) (kernelIntegrable n _ hr)] <;> rfl

private theorem energyControl {n : ℕ} {a : ℝ} (ha : 0 ≤ a) {v : ℝ → ℝ}
    (hv : ∀ t, |v t| ≤ a) :
    |J n v| ≤ a * intervalIntegral (fun t => ‖spec n (high n) t‖^2) 0 1 MeasureTheory.volume := by
  have hp (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have pt (t : ℝ) : ‖kernelIntegrand n v t‖ ≤ a * ‖spec n (high n) t‖^2 := by
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, norm_mul, hp, mul_one, Complex.norm_real,
        Real.norm_eq_abs, pow_two, ← mul_assoc]
      gcongr
      exact hv t
    · simpa [kernelIntegrand, ht] using mul_nonneg ha (sq_nonneg ‖spec n (high n) t‖)
  have hc : Continuous (fun t : ℝ => a * ‖spec n (high n) t‖^2) := by unfold spec phase; fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := kernelIntegrand n v) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t _ => pt t) (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  exact (Complex.abs_re_le_norm _).trans hi

theorem clippedBound
    (energy : ∀ n : ℕ, 2 ≤ n → intervalIntegral (fun t => ‖spec n (high n) t‖^2)
      0 1 MeasureTheory.volume ≤ ((n:ℝ)+1)*(Real.log (n:ℝ))^2) :
    ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152 := by
  intro n hn
  have ht : 0 ≤ cutoff n := by unfold cutoff; positivity
  have cap (t : ℝ) : |small n t| ≤ cutoff n := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  apply (energyControl ht cap).trans
  apply (mul_le_mul_of_nonneg_left (energy n hn) ht).trans
  unfold cutoff
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := sq_nonneg (Real.log (n:ℝ))
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr (show (1:ℝ) ≤ n by linarith)) hlog]

theorem restToDefect
    (cap : ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (rest n)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t) := by
  obtain ⟨N,hN⟩ := far
  refine ⟨max 2 N, ?_⟩
  intro n hn he
  rw [defectSplit]
  linarith only [(abs_le.mp (cap n (by omega))).1, hN n (by omega) he]

theorem packetToBulk
    (packet : ∃ P : ℕ, ∀ n ≥ P, Even n → -(n:ℝ)/576 ≤ J n (K n))
    (defect : ∃ D : ℕ, ∀ n ≥ D, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t))
    (split : ∀ n, (pair n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t)) :
    ∃ H : ℕ, ∀ n ≥ H, Even n → -(n:ℝ)/288 ≤ (pair n (high n) (high n)).re := by
  obtain ⟨P,hP⟩ := packet
  obtain ⟨D,hD⟩ := defect
  refine ⟨max P D, ?_⟩
  intro n hn he
  rw [split]
  linarith only [hP n (by omega) he, hD n (by omega) he]

/-- The clipping loss is dominated by half the energy on the actual resonant minor arcs. -/
theorem capComparison (n : ℕ) :
    let B := {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}
    J n (fun t => min (K n t) (1/2)) -
        intervalIntegral (B.indicator (fun t => ‖spec n (high n) t‖^2)) 0 1 MeasureTheory.volume / 2
      ≤ J n (K n) := by
  let B := {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}
  let cap := fun t => min (K n t) (1/2)
  let excess := fun t => K n t - cap t
  let energy := fun t : ℝ => ‖spec n (high n) t‖^2
  have hk : Continuous (K n) := by unfold K; fun_prop
  have hc : Continuous cap := hk.min continuous_const
  have he : Continuous excess := hk.sub hc
  have hB : MeasurableSet B := by
    change MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t})
    exact (measurableArcs n).compl.inter
      (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have henergy : Continuous energy := by unfold energy spec phase; fun_prop
  have hmask : IntervalIntegrable (B.indicator energy) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (henergy.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hB
  have hKle (t : ℝ) : K n t ≤ 1 := by
    let L := max 1 (Nat.log 2 n / 2)
    have hL : 0 < L := by dsimp [L]; omega
    change (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ) ≤ 1
    apply (div_le_iff₀ (by exact_mod_cast hL : (0:ℝ) < L)).mpr
    calc
      _ ≤ ∑ _j ∈ Finset.range L, (1:ℝ) := Finset.sum_le_sum fun _ _ => Real.cos_le_one _
      _ = _ := by simp
  have unit (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have pt (t : ℝ) : ‖kernelIntegrand n excess t‖ ≤ (1/2:ℝ) * B.indicator energy t := by
    by_cases hm : t ∈ (arcs n)ᶜ
    · by_cases hp : (1:ℝ)/2 < K n t
      · have hb : t ∈ B := ⟨hm,hp⟩
        have hx : |excess t| ≤ 1/2 := by
          simp only [excess, cap, min_eq_right hp.le, abs_of_nonneg (sub_nonneg.mpr hp.le)]
          linarith [hKle t]
        simp only [kernelIntegrand, Set.indicator_of_mem hm, Set.indicator_of_mem hb, norm_mul,
          unit, mul_one, Complex.norm_real, Real.norm_eq_abs, energy, pow_two, ← mul_assoc]
        gcongr <;> exact hx
      · have hb : t ∉ B := fun h => hp h.2
        have hz : excess t = 0 := by
          change K n t - min (K n t) (1/2) = 0
          rw [min_eq_left (le_of_not_gt hp), sub_self]
        simp [kernelIntegrand, hm, hb, hz]
    · have hb : t ∉ B := fun h => hm h.1
      simp [kernelIntegrand, hm, hb]
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := kernelIntegrand n excess) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t _ => pt t) (hmask.const_mul (1/2:ℝ))
  rw [intervalIntegral.integral_const_mul] at hi
  have bound := (Complex.abs_re_le_norm _).trans hi
  have add : kernelIntegrand n (K n) = fun t => kernelIntegrand n cap t + kernelIntegrand n excess t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, excess, Complex.ofReal_sub]
      ring
    · simp [kernelIntegrand, ht]
  have eqSum : J n (K n) = J n cap + J n excess := by
    change (intervalIntegral (kernelIntegrand n (K n)) 0 1 MeasureTheory.volume).re = _
    rw [add, intervalIntegral.integral_add (kernelIntegrable n _ hc) (kernelIntegrable n _ he)]
    rfl
  change J n cap - intervalIntegral (B.indicator energy) 0 1 MeasureTheory.volume / 2 ≤ J n (K n)
  change |J n excess| ≤ _ at bound
  rw [eqSum]
  linarith only [(abs_le.mp bound).1]

/-- Compare two exact lag expansions on a common mask before using the budgets. -/
theorem energyFromLags {U short long : ℕ → (ℕ → ℝ) → ℝ}
    (expand : ∀ n a, U n a = short n a + long n a)
    (wheel : ∃ N : ℕ, ∀ n ≥ N, Even n →
      U n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0) ≤ (n:ℝ)/2304)
    (near : ∃ N : ℕ, ∀ n ≥ N, Even n →
      |short n (high n) - short n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0)| ≤ (n:ℝ)/2304)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n →
      long n (high n) - long n (fun k => if Nat.Coprime k 30 then (30:ℝ)/8 else 0) ≤ (n:ℝ)/1152) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576 := by
  obtain ⟨A,hA⟩ := wheel
  obtain ⟨B,hB⟩ := near
  obtain ⟨C,hC⟩ := far
  refine ⟨max A (max B C), ?_⟩
  intro n hn he
  have hw := hA n (by omega) he
  rw [expand] at hw ⊢
  linarith only [hw, (abs_le.mp (hB n (by omega) he)).2, hC n (by omega) he]

/-- A signed capped-packet floor and a positive masked-energy cap suffice. -/
theorem packetFromCapped {U : ℕ → ℝ}
    (cap : ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => min (K n t) (1/2)))
    (energy : ∃ N : ℕ, ∀ n ≥ N, Even n → U n ≤ (n:ℝ)/576)
    (compareCap : ∀ n, J n (fun t => min (K n t) (1/2)) - U n/2 ≤ J n (K n)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (K n) := by
  obtain ⟨A,hA⟩ := cap
  obtain ⟨B,hB⟩ := energy
  refine ⟨max A B, ?_⟩
  intro n hn he
  linarith only [hA n (by omega) he, hB n (by omega) he, compareCap n]

/-- The finite certificate must reach the very threshold supplied by the analytic bounds. -/
theorem completeAtCommonCutoff (N : ℕ) (c : ℝ) (hc : 0 < c)
    (prefixMass : ∀ n : ℕ, 4 ≤ n → n < N → Even n → 0 < mass n)
    (tailMass : ∀ X n : ℕ, N ≤ X → X ≤ n → n < 2*X → Even n → c*(n:ℝ) ≤ mass n) :
    StrongGoldbach := by
  apply strongGoldbach_iff_primeMass.mpr
  intro n hn he
  change 0 < mass n
  by_cases h : n < N
  · exact prefixMass n hn h he
  · exact lt_of_lt_of_le (mul_pos hc (by exact_mod_cast (show 0 < n by omega)))
      (tailMass n n (by omega) le_rfl (by omega) he)

end
end GoldbachBudget

namespace GoldbachPacket
noncomputable section

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
private def resonant (n : ℕ) := {t : ℝ | t ∉ GoldbachBudget.arcs n ∧
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

private def cosineMoment (n h : ℕ) :=
  ∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => Real.cos (2*Real.pi*(h:ℝ)*u)) t
private def correlation (n h : ℕ) (a : ℕ → ℝ) :=
  ∑ k ∈ Finset.range (n+1-h), a k * a (k+h)
private def shortPart (n : ℕ) (a : ℕ → ℝ) :=
  correlation n 0 a * cosineMoment n 0 + 2 * ∑ h ∈ Finset.Icc 1 (min n ((length n)^2)),
    correlation n h a * cosineMoment n h
private def wheel (k : ℕ) := if Nat.Coprime k 30 then (30:ℝ)/8 else 0

private theorem zeroMoment (n : ℕ) :
    cosineMoment n 0 = ∫ t in (0:ℝ)..1, (resonant n).indicator (fun _ => (1:ℝ)) t := by
  simp [cosineMoment]

private theorem cosineMomentBound (n h : ℕ) : |cosineMoment n h| ≤ cosineMoment n 0 := by
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

private theorem correlationBound (n h : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
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

private theorem lengthUpper (n : ℕ) (hn : 1 ≤ n) : (length n:ℝ) ≤ 2*(1+Real.log (n:ℝ)) := by
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
private theorem shortAtLogScale (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℝ)
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

/-- Any chosen set of lags of this cardinality has sublinear absolute contribution.
    No restriction on the positions of the selected lags is needed. -/
theorem sparseLagBudget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Finset ℕ) (a : ℕ → ℝ),
      (F.card:ℝ) ≤ Real.exp ((length n:ℝ)/16) →
      (∀ k ≤ n, |a k| ≤ 4*(1+Real.log (n:ℝ))) →
      (∑ h ∈ F, |correlation n h a * cosineMoment n h|) ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 4 ((ε/32)^2) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro n hn F a hF ha
  let x := 1+Real.log (n:ℝ)
  let v := cosineMoment n 0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 ≤ x := by dsimp [x]; linarith [Real.log_nonneg hn1]
  have hv : 0 ≤ v := (abs_nonneg _).trans (cosineMomentBound n 0)
  have area := hN n (by omega)
  rw [← zeroMoment] at area
  change x^4*v ≤ (ε/32)^2 at area
  have decay : v ≤ Real.exp (-(length n:ℝ)/8) := (zeroMoment n).le.trans (maskedArea n)
  have count : (F.card:ℝ)^2*v ≤ 1 := by
    calc
      _ ≤ (Real.exp ((length n:ℝ)/16))^2 * Real.exp (-(length n:ℝ)/8) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hF 2) decay hv (by positivity)
      _ = 1 := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  have sq : ((F.card:ℝ)*x^2*v)^2 ≤ (ε/32)^2 := by
    calc
      _ = ((F.card:ℝ)^2*v)*(x^4*v) := by ring
      _ ≤ 1*(ε/32)^2 := mul_le_mul count area (mul_nonneg (by positivity) hv) zero_le_one
      _ = _ := one_mul _
  have small : (F.card:ℝ)*x^2*v ≤ ε/32 := (sq_le_sq₀ (by positivity) (by positivity)).mp sq
  have uniform (h : ℕ) : |correlation n h a * cosineMoment n h| ≤ ((n:ℝ)+1)*(4*x)^2*v := by
    rw [abs_mul]
    exact mul_le_mul (correlationBound n h a (4*x) (by positivity) ha) (cosineMomentBound n h)
      (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ _h ∈ F, ((n:ℝ)+1)*(4*x)^2*v := Finset.sum_le_sum fun h _ => uniform h
    _ = (16*((n:ℝ)+1))*((F.card:ℝ)*x^2*v) := by simp; ring
    _ ≤ (32*(n:ℝ))*(ε/32) := mul_le_mul (by linarith) small (by positivity) (by positivity)
    _ = _ := by ring

private theorem upperTriangleLags (n : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), if i<j then g i j else 0) =
      ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h) := by
  let R := Finset.range (n+1)
  let U := (R ×ˢ R).filter (fun p => p.1 < p.2)
  let D := (Finset.Icc 1 n).sigma (fun h => Finset.range (n+1-h))
  calc
    _ = ∑ p ∈ U, g p.1 p.2 := by
      dsimp [U,R]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ d ∈ D, g d.2 (d.2+d.1) := by
      apply Finset.sum_nbij' (fun p : ℕ × ℕ => (⟨p.2-p.1,p.1⟩ : Σ _ : ℕ, ℕ))
        (fun d => (d.2,d.2+d.1))
      · rintro ⟨i,j⟩ hp
        simp only [U,R,D,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_sigma,
          Finset.mem_Icc] at hp ⊢
        omega
      · rintro ⟨h,k⟩ hd
        simp only [U,R,D,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_sigma,
          Finset.mem_Icc] at hd ⊢
        omega
      · rintro ⟨i,j⟩ hu
        have hij := (Finset.mem_filter.mp hu).2
        change (i,i+(j-i)) = (i,j)
        rw [show i+(j-i)=j by omega]
      · rintro ⟨h,k⟩ _
        change (⟨k+h-k,k⟩ : Σ _ : ℕ, ℕ) = ⟨h,k⟩
        rw [show k+h-k=h by omega]
      · rintro ⟨i,j⟩ hu
        have hij := (Finset.mem_filter.mp hu).2
        change g i j = g i (i+(j-i))
        rw [show i+(j-i)=j by omega]
    _ = _ := Finset.sum_sigma ..

private theorem squareLags (n : ℕ) (g : ℕ → ℕ → ℝ) (hsym : ∀ i j, g i j = g j i) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), g i j) =
      (∑ i ∈ Finset.range (n+1), g i i) +
      2*(∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h)) := by
  let R := Finset.range (n+1)
  let up := fun i j => if i<j then g i j else 0
  let diag := fun i j => if i=j then g i i else 0
  have split (i j : ℕ) : g i j = diag i j + up i j + up j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [diag,up,hij,ne_of_lt hij,not_lt_of_ge hij.le]
    · simp [diag,up]
    · simp [diag,up,hji,ne_of_gt hji,not_lt_of_ge hji.le,hsym i j]
  have hd : (∑ i ∈ R, ∑ j ∈ R, diag i j) = ∑ i ∈ R, g i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [diag,hi]
  have hu : (∑ i ∈ R, ∑ j ∈ R, up j i) = ∑ i ∈ R, ∑ j ∈ R, up i j := Finset.sum_comm
  calc
    _ = ∑ i ∈ R, ∑ j ∈ R, (diag i j + up i j + up j i) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split i j
    _ = (∑ i ∈ R, g i i) + 2*(∑ i ∈ R, ∑ j ∈ R, up i j) := by
      simp only [Finset.sum_add_distrib,hd,hu]; ring
    _ = _ := by rw [show (∑ i ∈ R, ∑ j ∈ R, up i j) = _ from upperTriangleLags n g]

private theorem pointwiseLagEnergy (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ‖GoldbachBudget.spec n a t‖^2 = correlation n 0 a +
      2*∑ h ∈ Finset.Icc 1 n, correlation n h a * Real.cos (2*Real.pi*(h:ℝ)*t) := by
  let angle := fun k : ℕ => 2*Real.pi*((k:ℝ)*t)
  let g := fun i j : ℕ => a i * a j * Real.cos (angle j - angle i)
  have sym (i j : ℕ) : g i j = g j i := by
    dsimp [g]
    rw [← Real.cos_neg (angle i-angle j), neg_sub]
    ring
  calc
    _ = (∑ k ∈ Finset.range (n+1), a k * Real.cos (angle k))^2 +
        (∑ k ∈ Finset.range (n+1), a k * Real.sin (angle k))^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [GoldbachBudget.spec, GoldbachBudget.phase,
        Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, zero_add, add_zero, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, angle, pow_two]
    _ = ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), g i j := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [g]; rw [Real.cos_sub]; ring
    _ = _ := by
      rw [squareLags n g sym]
      have hd : (∑ i ∈ Finset.range (n+1), g i i) = correlation n 0 a := by simp [g,correlation]
      rw [hd]
      congr 2
      apply Finset.sum_congr rfl
      intro h _
      rw [correlation, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [g]
      rw [show angle (k+h)-angle k = 2*Real.pi*(h:ℝ)*t by dsimp [angle]; push_cast; ring]

private def longPart (n : ℕ) (a : ℕ → ℝ) :=
  2*∑ h ∈ Finset.Icc ((length n)^2+1) n, correlation n h a * cosineMoment n h

/-- Exact masked energy of any real weight, including the diagonal and both orders of each pair. -/
theorem lagEnergyIdentity (n : ℕ) (a : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n a u‖^2) t) =
      shortPart n a + longPart n a := by
  let f := fun (h : ℕ) => (resonant n).indicator (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t))
  let A := fun h => correlation n h a
  let H := Finset.Icc 1 n
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have hi (h : ℕ) : IntervalIntegrable (f h) MeasureTheory.volume (0:ℝ) 1 := by
    have hc : Continuous (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t)) := by fun_prop
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hm
  have hiA (h : ℕ) := (hi h).const_mul (A h)
  have ident : (resonant n).indicator (fun t => ‖GoldbachBudget.spec n a t‖^2) =
      fun t => A 0 * f 0 t + 2*∑ h ∈ H, A h * f h t := by
    funext t
    by_cases ht : t ∈ resonant n
    · simpa [f,A,H,ht] using pointwiseLagEnergy n a t
    · simp [f,ht]
  have hs : IntervalIntegrable (fun t => ∑ h ∈ H, A h * f h t) MeasureTheory.volume (0:ℝ) 1 := by
    have eq : (fun t => ∑ h ∈ H, A h * f h t) = ∑ h ∈ H, (fun t => A h * f h t) := by
      funext t; simp
    rw [eq]
    exact IntervalIntegrable.sum H (fun h _ => hiA h)
  have split : H = Finset.Icc 1 (min n ((length n)^2)) ∪ Finset.Icc ((length n)^2+1) n := by
    ext h; simp only [H,Finset.mem_union,Finset.mem_Icc]; omega
  have dis : Disjoint (Finset.Icc 1 (min n ((length n)^2))) (Finset.Icc ((length n)^2+1) n) := by
    rw [Finset.disjoint_left]
    intro h ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [ident, intervalIntegral.integral_add (hiA 0) (hs.const_mul 2)]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun h _ => hiA h)]
  change A 0 * cosineMoment n 0 + 2*(∑ h ∈ H, A h * cosineMoment n h) = _
  rw [split, Finset.sum_union dis]
  unfold shortPart longPart
  dsimp only [A]
  ring

/-- Exact Fourier decomposition of the modulus-30 model, with the endpoint in each residue class. -/
theorem wheelGeometric (n : ℕ) (t : ℝ) :
    GoldbachBudget.spec n wheel t = ((30:ℝ)/8:ℂ) *
      ∑ r ∈ (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n),
        GoldbachBudget.phase ((r:ℝ)*t) *
          ∑ j ∈ Finset.range ((n-r)/30+1), GoldbachBudget.phase ((30:ℝ)*(j:ℝ)*t) := by
  let W := (Finset.range (n+1)).filter (fun k => Nat.Coprime k 30)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let D := R.sigma (fun r => Finset.range ((n-r)/30+1))
  let E := GoldbachBudget.phase
  have cop (k : ℕ) : Nat.Coprime (k%30) 30 ↔ Nat.Coprime k 30 := by
    unfold Nat.Coprime
    rw [← Nat.gcd_rec 30 k, Nat.gcd_comm 30 k]
  have addE (x y : ℝ) : E (x+y) = E x * E y := by
    dsimp [E,GoldbachBudget.phase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have wsum : GoldbachBudget.spec n wheel t = ((30:ℝ)/8:ℂ) * ∑ k ∈ W, E ((k:ℝ)*t) := by
    rw [Finset.mul_sum]
    unfold GoldbachBudget.spec
    dsimp only [W]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hc : Nat.Coprime k 30
    · simp only [wheel, if_pos hc, Complex.ofReal_div, Complex.ofReal_ofNat, E]
    · simp only [wheel, if_neg hc, Complex.ofReal_zero, zero_mul]
  rw [wsum]
  apply congrArg (fun z : ℂ => ((30:ℝ)/8:ℂ)*z)
  calc
    _ = ∑ d ∈ D, E ((d.1:ℝ)*t) * E (30*(d.2:ℝ)*t) := by
      apply Finset.sum_nbij' (fun k : ℕ => (⟨k%30,k/30⟩ : Σ _ : ℕ, ℕ)) (fun d => d.1+30*d.2)
      · intro k hk
        simp only [W,Finset.mem_filter,Finset.mem_range] at hk
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range]
        exact ⟨⟨by omega, (cop k).mpr hk.2, by omega⟩,by omega⟩
      · rintro ⟨r,j⟩ hd
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hd
        simp only [W,Finset.mem_filter,Finset.mem_range]
        refine ⟨by omega,(cop _).mp ?_⟩
        simpa only [show (r+30*j)%30=r by omega] using hd.1.2.1
      · intro k _; dsimp; omega
      · rintro ⟨r,j⟩ hd
        simp only [D,R,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hd
        change (⟨(r+30*j)%30,(r+30*j)/30⟩ : Σ _ : ℕ, ℕ) = ⟨r,j⟩
        rw [show (r+30*j)%30=r by omega, show (r+30*j)/30=j by omega]
      · intro k _
        change E ((k:ℝ)*t) = E (((k%30:ℕ):ℝ)*t) * E (30*((k/30:ℕ):ℝ)*t)
        rw [← addE]
        have he : (k:ℝ) = ((k%30:ℕ):ℝ)+30*((k/30:ℕ):ℝ) := by
          exact_mod_cast (show k=k%30+30*(k/30) by omega)
        congr 1
        linear_combination t * he
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      change (∑ j ∈ Finset.range ((n-r)/30+1), E ((r:ℝ)*t)*E (30*(j:ℝ)*t)) =
        E ((r:ℝ)*t)*(∑ j ∈ Finset.range ((n-r)/30+1), E (30*(j:ℝ)*t))
      rw [Finset.mul_sum]

private def gridDistance (t : ℝ) := ‖GoldbachBudget.phase (30*t) - 1‖
private def gridEnvelope (n : ℕ) (t : ℝ) :=
  ((n:ℝ)+1)^2 / (1+((n:ℝ)+1)^2 * (gridDistance t)^2)

private theorem phaseUnit (x : ℝ) : ‖GoldbachBudget.phase x‖ = 1 := by
  simp [GoldbachBudget.phase, Complex.norm_exp]

private theorem wheelDistanceBound (n : ℕ) (t : ℝ) :
    ‖GoldbachBudget.spec n wheel t‖ * gridDistance t ≤ 60 := by
  let z := GoldbachBudget.phase (30*t)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let G := fun r : ℕ => GoldbachBudget.phase ((r:ℝ)*t) *
    ∑ j ∈ Finset.range ((n-r)/30+1), GoldbachBudget.phase (30*(j:ℝ)*t)
  have hz : ‖z‖ = 1 := phaseUnit _
  have phasePow (j : ℕ) : GoldbachBudget.phase (30*(j:ℝ)*t) = z^j := by
    dsimp [z,GoldbachBudget.phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have gb (r : ℕ) : ‖G r‖*gridDistance t ≤ 2 := by
    simp only [G,gridDistance,norm_mul,phaseUnit,one_mul,phasePow]
    change ‖∑ j ∈ Finset.range ((n-r)/30+1), z^j‖ * ‖z-1‖ ≤ 2
    rw [← norm_mul, geom_sum_mul]
    exact (norm_sub_le ..).trans (by norm_num [norm_pow,hz])
  have card : R.card ≤ 8 := by
    have hsub : R ⊆ (Finset.range 30).filter (fun r => Nat.Coprime r 30) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2.1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  have whole : ‖∑ r ∈ R, G r‖ * gridDistance t ≤ 16 := by
    calc
      _ ≤ (∑ r ∈ R, ‖G r‖)*gridDistance t :=
        mul_le_mul_of_nonneg_right (norm_sum_le ..) (norm_nonneg _)
      _ = ∑ r ∈ R, ‖G r‖*gridDistance t := Finset.sum_mul ..
      _ ≤ ∑ _r ∈ R, (2:ℝ) := Finset.sum_le_sum fun r _ => gb r
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; linarith [show (R.card:ℝ) ≤ 8 by exact_mod_cast card]
  have coeff : ‖((30:ℝ)/8:ℂ)‖ = 30/8 := by norm_num [norm_div]
  rw [wheelGeometric, norm_mul, coeff, mul_assoc]
  change (30/8:ℝ)*(‖∑ r ∈ R, G r‖ * gridDistance t) ≤ _
  linarith only [whole]

/-- A smooth, arithmetic-free upper bound valid even at the exact resonances. -/
theorem wheelEnvelope (n : ℕ) (t : ℝ) :
    ‖GoldbachBudget.spec n wheel t‖^2 ≤ 3616 * gridEnvelope n t := by
  let S := ‖GoldbachBudget.spec n wheel t‖
  let A := (n:ℝ)+1
  let d := gridDistance t
  have hS : 0 ≤ S := norm_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have ht : S ≤ 4*A := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖(wheel k:ℂ)*GoldbachBudget.phase ((k:ℝ)*t)‖ := norm_sum_le ..
      _ ≤ ∑ _k ∈ Finset.range (n+1), (4:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul,phaseUnit,mul_one,Complex.norm_real,Real.norm_eq_abs]
        dsimp [wheel]; split <;> norm_num
      _ = _ := by simp [A]; ring
  have hsd : S*d ≤ 60 := wheelDistanceBound n t
  have h1 := pow_le_pow_left₀ hS ht 2
  have h2 := pow_le_pow_left₀ (mul_nonneg hS hd) hsd 2
  change S^2 ≤ 3616*(A^2/(1+A^2*d^2))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [h1,mul_le_mul_of_nonneg_left h2 (sq_nonneg A)]

theorem wheelLeakageTransfer
    (pointwise : ∀ n t, ‖GoldbachBudget.spec n wheel t‖^2 ≤ 3616 * gridEnvelope n t)
    (leak : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε*(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t)
        ≤ ε*(n:ℝ) := by
  intro ε hε
  obtain ⟨N,hN⟩ := leak (ε/3616) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance GoldbachBudget.phase
    fun_prop (disch := intro t; positivity)
  have hs : Continuous (fun u => ‖GoldbachBudget.spec n wheel u‖^2) := by
    unfold GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have maskInt {f : ℝ → ℝ} (hc : Continuous f) :
      IntervalIntegrable ((GoldbachBudget.arcs n)ᶜ.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (GoldbachBudget.measurableArcs n).compl
  calc
    _ ≤ ∫ t in (0:ℝ)..1, 3616 * (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (maskInt hs) ((maskInt hg).const_mul 3616)
      intro t _
      by_cases ht : t ∈ (GoldbachBudget.arcs n)ᶜ
      · simpa only [Set.indicator_of_mem ht] using pointwise n t
      · simp [ht]
    _ ≤ _ := by rw [intervalIntegral.integral_const_mul]; linarith only [hN n hn]

private def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2
private def lorentz (r c t : ℝ) := 1/(r^2+(t-c)^2)

private theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) : Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

/-- The integral is bounded uniformly in the location of the center, including endpoints. -/
private theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0:ℝ)..1, lorentz r c t) ≤ Real.pi/r := by
  let F := fun t : ℝ => Real.arctan ((t-c)/r)/r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t-c)/r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t-c)/r)^2) * (1/r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1-c)/r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0-c)/r)
  linarith

/-- All rationals with unreduced denominator d ≤ Q are protected by the frozen arcs. -/
private theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n) (hd : 0 < d) (hQ : d ≤ gridQ n)
    (hk : k ≤ d) (hm : t ∉ GoldbachBudget.arcs n) :
    (gridQ n:ℝ)/(d*(n:ℝ)) < |t-(k:ℝ)/d| := by
  obtain ⟨g,a,q,hg,hcop,hk',hq'⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right k hd)
  have hq : 0 < q := by
    by_contra! hz
    have he : q=0 := by omega
    rw [he, zero_mul] at hq'
    omega
  have hqd : q ≤ d := Nat.le_of_dvd hd ⟨g,hq'⟩
  have haq : a ≤ q := by
    exact (Nat.mul_le_mul_right_iff hg).mp (show a*g ≤ q*g by omega)
  have eq : (k:ℝ)/d = (a:ℝ)/(q:ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have cross : k*q = a*d := by rw [hk',hq']; ring
    exact_mod_cast cross
  by_contra! h
  apply hm
  refine ⟨q,a,hq,hqd.trans hQ,haq,hcop,?_⟩
  rw [← eq]
  exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqd : (q:ℝ) ≤ d) (Nat.cast_nonneg _)))

private theorem integerChord (v : ℝ) (k : ℕ) (hk : |v-(k:ℝ)| ≤ 1/2) :
    4*|v-(k:ℝ)| ≤ ‖GoldbachBudget.phase v-1‖ := by
  let u := v-(k:ℝ)
  let x := Real.pi*u
  let y := 2*Real.pi*(v)
  have hangle : y = 2*x + (k:ℝ)*(2*Real.pi) := by dsimp [y,x,u]; ring
  have hs : ‖GoldbachBudget.phase v-1‖ ^ 2 = 2-2*Real.cos y := by
    change ‖Complex.exp ((y:ℂ)*Complex.I)-1‖^2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero,
      Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq y]
  have he : ‖GoldbachBudget.phase v-1‖ = 2*|Real.sin x| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    change ‖GoldbachBudget.phase v-1‖ ^ 2 = (2*|Real.sin x|)^2
    rw [hs,hangle,Real.cos_add_nat_mul_two_pi,Real.cos_two_mul]
    nlinarith only [sq_abs (Real.sin x), Real.sin_sq_add_cos_sq x]
  have hx : |x| ≤ Real.pi/2 := by
    dsimp [x]; rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_left hk Real.pi_pos.le]
  have hj := Real.mul_abs_le_abs_sin hx
  have hxu : |x| = Real.pi*|u| := by dsimp [x]; rw [abs_mul,abs_of_pos Real.pi_pos]
  rw [hxu,show 2/Real.pi*(Real.pi*|u|) = 2*|u| by field_simp] at hj
  rw [he]
  change 4*|u| ≤ _
  linarith only [hj]

private theorem gridChord (t : ℝ) (k : ℕ) (hk : |30*t-(k:ℝ)| ≤ 1/2) :
    |t-(k:ℝ)/30| ≤ gridDistance t := by
  have h := integerChord (30*t) k hk
  have eq : 30*t-(k:ℝ) = 30*(t-(k:ℝ)/30) := by ring
  rw [eq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<30)] at h
  change _ ≤ ‖GoldbachBudget.phase (30*t)-1‖
  linarith [abs_nonneg (t-(k:ℝ)/30)]

private theorem gridPointMajorant {n : ℕ} (hn : 0 < n) (hQ : 30 ≤ gridQ n)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t ≤
      ∑ k ∈ Finset.range 31, 2*lorentz ((gridQ n:ℝ)/(30*(n:ℝ))) ((k:ℝ)/30) t := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have nonneg (k : ℕ) : 0 ≤ 2*lorentz r ((k:ℝ)/30) t := by unfold lorentz; positivity
  by_cases hm : t ∈ (GoldbachBudget.arcs n)ᶜ
  · rw [Set.indicator_of_mem hm]
    let k := ⌊30*t+1/2⌋₊
    obtain ⟨h0,h1⟩ := ht
    have hlo : (k:ℝ) ≤ 30*t+1/2 := Nat.floor_le (by linarith)
    have hhi : 30*t+1/2 < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hk : k ≤ 30 := by
      by_contra! h
      have h' : (31:ℝ) ≤ k := by exact_mod_cast h
      linarith
    have close : |30*t-(k:ℝ)| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hdist := gridChord t k close
    have hcut : r ≤ |t-(k:ℝ)/30| := (denominatorExclusion hn (by decide : 0<30) hQ hk hm).le
    have h1' := pow_le_pow_left₀ hr.le (hcut.trans hdist) 2
    have h2' := pow_le_pow_left₀ (abs_nonneg _) hdist 2
    rw [sq_abs] at h2'
    have bound : gridEnvelope n t ≤ 2*lorentz r ((k:ℝ)/30) t := by
      unfold gridEnvelope lorentz
      rw [← mul_div_assoc, mul_one]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h1' h2') (sq_nonneg ((n:ℝ)+1))]
    exact bound.trans (Finset.single_le_sum (fun k _ => nonneg k) (Finset.mem_range.mpr (by omega : k<31)))
  · rw [Set.indicator_of_notMem hm]
    exact Finset.sum_nonneg fun k _ => nonneg k

/-- The minor-arc tail is bounded by an explicit multiple of n/Q(n). -/
theorem gridTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 30 ≤ gridQ n) :
    (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤
      1860*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let r := (gridQ n:ℝ)/(30*(n:ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance GoldbachBudget.phase
    fun_prop (disch := intro t; positivity)
  have hi : IntervalIntegrable ((GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n)) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (GoldbachBudget.measurableArcs n).compl
  let f := fun (k : ℕ) (t : ℝ) => 2*lorentz r ((k:ℝ)/30) t
  have hf (k : ℕ) : Continuous (f k) := continuous_const.mul (lorentzContinuous hr _)
  have hsum : Continuous (fun t => ∑ k ∈ Finset.range 31, f k t) := by fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ∑ k ∈ Finset.range 31, f k t :=
      intervalIntegral.integral_mono_on (by norm_num) hi (hsum.intervalIntegrable ..)
        (fun t ht => gridPointMajorant hn hQ t ht)
    _ = ∑ k ∈ Finset.range 31, 2*(∫ t in (0:ℝ)..1, lorentz r ((k:ℝ)/30) t) := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => (hf k).intervalIntegrable ..)]
      simp only [f,intervalIntegral.integral_const_mul]
    _ ≤ ∑ _k ∈ Finset.range 31, 2*(Real.pi/r) := Finset.sum_le_sum
      fun k _ => mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by norm_num)
    _ = _ := by simp [r]; field_simp; ring

theorem gridTail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε*(n:ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (1860*Real.pi/ε)
  let B := max 30 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^B) hn
  have hb : B ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by
    unfold gridQ; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  apply (gridTailQuantitative n hn' ((le_max_left ..).trans hq)).trans
  have hq' : 0 < gridQ n := by have : 30 ≤ B := le_max_left ..; omega
  have hM' : 1860*Real.pi/ε ≤ (gridQ n:ℝ) := hM.trans (by exact_mod_cast (le_trans (le_max_right 30 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM') (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

theorem wheelMinorLeakage : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    (∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t) ≤ ε*(n:ℝ) := wheelLeakageTransfer wheelEnvelope gridTail

theorem wheelMaskedBudget :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      (∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n wheel u‖^2) t) ≤ (n:ℝ)/2304 := by
  obtain ⟨N,hN⟩ := wheelMinorLeakage (1/2304) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn _
  let f := fun t : ℝ => ‖GoldbachBudget.spec n wheel t‖^2
  have hc : Continuous f := by unfold f GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have hi {s : Set ℝ} (hs : MeasurableSet s) :
      IntervalIntegrable (s.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs
  have hk : Continuous (fun t => packet (length n) t / (length n:ℝ)) := by unfold packet; fun_prop
  have hm : MeasurableSet (resonant n) := (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet
  have bound : (∫ t in (0:ℝ)..1, (resonant n).indicator f t) ≤
      ∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator f t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hi hm) (hi (GoldbachBudget.measurableArcs n).compl)
    intro t _
    by_cases ht : t ∈ resonant n
    · have ha : t ∈ (GoldbachBudget.arcs n)ᶜ := ht.1
      simp [ht,ha]
    · by_cases ha : t ∈ (GoldbachBudget.arcs n)ᶜ <;> simp [ht,ha,f,sq_nonneg]
  exact bound.trans (by linarith only [hN n hn])

/-- The only remaining argument to this energy reduction is the signed long-lag prime-pair excess. -/
theorem maskedEnergyFromLong
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n →
      longPart n (GoldbachBudget.high n) - longPart n wheel ≤ (n:ℝ)/1152) :
    ∃ N : ℕ, ∀ n ≥ N, Even n →
      (∫ t in (0:ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n (GoldbachBudget.high n) u‖^2) t)
        ≤ (n:ℝ)/576 :=
  GoldbachBudget.energyFromLags lagEnergyIdentity wheelMaskedBudget shortWheelBudget far

private def progression (d M : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.range M, (GoldbachBudget.phase ((d:ℝ)*t))^(j+1)
private def minorMass (n : ℕ) (f : ℝ → ℝ) :=
  ∫ t in (0:ℝ)..1, (GoldbachBudget.arcs n)ᶜ.indicator f t

private theorem minorIntegrable (n : ℕ) {f : ℝ → ℝ} (hc : Continuous f) :
    IntervalIntegrable ((GoldbachBudget.arcs n)ᶜ.indicator f) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (GoldbachBudget.measurableArcs n).compl

private theorem progressionMajorant {n d : ℕ} (hn : 0<n) (hd : 0<d) (hQ : d ≤ gridQ n)
    (M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (GoldbachBudget.arcs n)ᶜ.indicator (fun u => ‖progression d M u‖^2) t ≤
      ∑ k ∈ Finset.range (d+1), lorentz ((gridQ n:ℝ)/((d:ℝ)*n)) ((k:ℝ)/d) t / (d:ℝ)^2 := by
  let r := (gridQ n:ℝ)/((d:ℝ)*n)
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have dr : 0 < (d:ℝ) := by exact_mod_cast hd
  have nonneg (k : ℕ) : 0 ≤ lorentz r ((k:ℝ)/d) t / (d:ℝ)^2 := by unfold lorentz; positivity
  by_cases hm : t ∈ (GoldbachBudget.arcs n)ᶜ
  · rw [Set.indicator_of_mem hm]
    let k := ⌊(d:ℝ)*t+1/2⌋₊
    have hlow : (k:ℝ) ≤ (d:ℝ)*t+1/2 := Nat.floor_le (by have := ht.1; positivity)
    have hhi : (d:ℝ)*t+1/2 < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hk : k ≤ d := by
      by_contra! hh
      have hc : (d:ℝ)+1 ≤ k := by exact_mod_cast hh
      linarith [mul_le_mul_of_nonneg_left ht.2 dr.le]
    let z := GoldbachBudget.phase ((d:ℝ)*t)
    let A := ‖progression d M t‖
    let b := |t-(k:ℝ)/d|
    have hb : 0 ≤ b := abs_nonneg _
    have hA : 0 ≤ A := norm_nonneg _
    have hz : ‖z‖ = 1 := phaseUnit _
    have hprod : A*‖z-1‖ ≤ 2 := by
      have eq : progression d M t = z*(∑ j ∈ Finset.range M, z^j) := by
        simp only [progression,Finset.mul_sum,pow_succ',z]
      dsimp only [A]
      rw [eq,norm_mul,hz,one_mul,← norm_mul,geom_sum_mul]
      exact (norm_sub_le ..).trans (by norm_num [norm_pow,hz])
    have hc := integerChord ((d:ℝ)*t) k (abs_le.mpr ⟨by linarith,by linarith⟩)
    have eq : (d:ℝ)*t-(k:ℝ) = (d:ℝ)*(t-(k:ℝ)/d) := by field_simp <;> ring
    rw [eq,abs_mul,abs_of_pos dr] at hc
    change 4*((d:ℝ)*b) ≤ ‖z-1‖ at hc
    have hAb : (A*d)*b ≤ 1/2 := by linarith only [mul_le_mul_of_nonneg_left hc hA,hprod]
    have hAr : (A*d)*r ≤ 1/2 := (mul_le_mul_of_nonneg_left (denominatorExclusion hn hd hQ hk hm).le (mul_nonneg hA dr.le)).trans hAb
    have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ (A*d)*b) hAb 2
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (A*d)*r) hAr 2
    have hy : (t-(k:ℝ)/d)^2 = b^2 := (sq_abs _).symm
    have bound : A^2 ≤ lorentz r ((k:ℝ)/d) t / (d:ℝ)^2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      unfold lorentz
      apply (le_div_iff₀ (by positivity)).mpr
      rw [hy]
      nlinarith only [h1,h2]
    exact bound.trans (Finset.single_le_sum (fun k _ => nonneg k) (Finset.mem_range.mpr (by omega : k<d+1)))
  · rw [Set.indicator_of_notMem hm]
    exact Finset.sum_nonneg fun k _ => nonneg k

/-- The leakage bound is uniform both in the permissible denominator and in the progression length. -/
theorem progressionLeakage (n d M : ℕ) (hn : 0<n) (hd : 0<d) (hQ : d ≤ gridQ n) :
    minorMass n (fun t => ‖progression d M t‖^2) ≤ 2*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let r := (gridQ n:ℝ)/((d:ℝ)*n)
  have hq : 0 < gridQ n := by omega
  have dr : (0:ℝ) < d := by exact_mod_cast hd
  have hr : 0 < r := by dsimp [r]; positivity
  let f := fun (k : ℕ) (t : ℝ) => ((d:ℝ)^2)⁻¹ * lorentz r ((k:ℝ)/d) t
  have hf (k : ℕ) : Continuous (f k) := continuous_const.mul (lorentzContinuous hr _)
  have hs : Continuous (fun t => ∑ k ∈ Finset.range (d+1), f k t) := by fun_prop
  have hprog : Continuous (fun t => ‖progression d M t‖^2) := by unfold progression GoldbachBudget.phase; fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ∑ k ∈ Finset.range (d+1), f k t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (minorIntegrable n hprog) (hs.intervalIntegrable ..)
      intro t ht
      simpa only [f,r,div_eq_inv_mul] using progressionMajorant hn hd hQ M t ht
    _ = ∑ k ∈ Finset.range (d+1), ((d:ℝ)^2)⁻¹ * ∫ t in (0:ℝ)..1, lorentz r ((k:ℝ)/d) t := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => (hf k).intervalIntegrable ..)]
      simp only [f,intervalIntegral.integral_const_mul]
    _ ≤ ∑ _k ∈ Finset.range (d+1), ((d:ℝ)^2)⁻¹ * (Real.pi/r) := Finset.sum_le_sum
      fun k _ => mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by positivity)
    _ = ((d:ℝ)+1)/d * (Real.pi*(n:ℝ)/(gridQ n:ℝ)) := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_range,Nat.cast_add,Nat.cast_one,r]
      field_simp <;> ring
    _ ≤ _ := by
      have h1 : (1:ℝ) ≤ d := by exact_mod_cast hd
      have h2 : ((d:ℝ)+1)/d ≤ 2 := (div_le_iff₀ dr).mpr (by linarith)
      calc
        _ ≤ 2*(Real.pi*(n:ℝ)/(gridQ n:ℝ)) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring


private def rationalWindows (n : ℕ) (eligible : ℕ → Prop) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (gridQ n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ eligible q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ ((gridQ n:ℝ)^2)/((q:ℝ)*(n:ℝ))}
private def shortOrder (n q : ℕ) : Prop :=
  Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (gridQ n)+1)^2 ∧ q ∣ 2^j-1
private def density (n : ℕ) (t : ℝ) := ‖GoldbachBudget.spec n (GoldbachBudget.high n) t‖^2
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
  exact (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hk).measurableSet

private theorem continuousDensity (n : ℕ) : Continuous (density n) := by
  unfold density GoldbachBudget.spec GoldbachBudget.phase
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


private def mixture (R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) (t : ℝ) :=
  ∑ d ∈ Finset.Icc 1 R, (c d:ℂ) * progression d (M d) t

theorem divisorMixtureLeakage (n R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) (hn : 0<n) (hQ : R ≤ gridQ n) :
    minorMass n (fun t => ‖mixture R c M t‖^2) ≤
      (2*Real.pi*(n:ℝ)/(gridQ n:ℝ))*(∑ d ∈ Finset.Icc 1 R, |c d|)^2 := by
  let T := Finset.Icc 1 R
  let b := ∑ d ∈ T, |c d|
  let f := fun d t => ‖progression d (M d) t‖^2
  let v := fun d => (GoldbachBudget.arcs n)ᶜ.indicator (f d)
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc (d : ℕ) : Continuous (f d) := by unfold f progression GoldbachBudget.phase; fun_prop
  have hv (d : ℕ) : IntervalIntegrable (fun t => |c d| * v d t) MeasureTheory.volume (0:ℝ) 1 :=
    (minorIntegrable n (hc d)).const_mul _
  have hs : IntervalIntegrable (fun t => ∑ d ∈ T, |c d| * v d t) MeasureTheory.volume (0:ℝ) 1 := by
    have eq : (fun t => ∑ d ∈ T, |c d| * v d t) = ∑ d ∈ T, (fun t => |c d| * v d t) := by funext t; simp
    rw [eq]
    exact IntervalIntegrable.sum T (fun d _ => hv d)
  have hmix : Continuous (fun t => ‖mixture R c M t‖^2) := by
    unfold mixture progression GoldbachBudget.phase; fun_prop
  let K := 2*Real.pi*(n:ℝ)/(gridQ n:ℝ)
  calc
    _ ≤ ∫ t in (0:ℝ)..1, b * (∑ d ∈ T, |c d| * v d t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (minorIntegrable n hmix) (hs.const_mul b)
      intro t _
      by_cases ht : t ∈ (GoldbachBudget.arcs n)ᶜ
      · simp only [v,Set.indicator_of_mem ht]
        have htriangle : ‖mixture R c M t‖ ≤ ∑ d ∈ T, |c d| * ‖progression d (M d) t‖ := by
          simpa only [mixture,T,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
            (norm_sum_le T (fun d => (c d:ℂ)*progression d (M d) t))
        apply (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans
        exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T (fun d _ => abs_nonneg (c d))
          (fun d _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun d _ => by dsimp [f]; nlinarith only [])
      · simp [v,ht]
    _ = b * ∑ d ∈ T, |c d| * minorMass n (f d) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun d _ => hv d)]
      simp only [intervalIntegral.integral_const_mul,minorMass,v]
    _ ≤ b * ∑ d ∈ T, |c d| * K := by
      apply mul_le_mul_of_nonneg_left _ hb
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hd
      exact mul_le_mul_of_nonneg_left (progressionLeakage n d (M d) hn hl (hu.trans hQ)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [b,T,K]; ring


/-- A rational peak of width 1/n with its square Ramanujan coefficient bounded by 1/φ(q)^2. -/
private def peaks (n : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
    4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
private def excess (n : ℕ) (t : ℝ) := max 0 (density n t - peaks n t)
private def integralOn (s : Set ℝ) (f : ℝ → ℝ) := ∫ t in (0:ℝ)..1, s.indicator f t
private def shellRegion (n : ℕ) (slow : Bool) :=
  let s := resonant n ∩ rationalWindows n (fun _ => True)
  let o := rationalWindows n (shortOrder n)
  if slow then s ∩ o else s \ o

theorem shellFromModel (slow : Bool)
    (err : ∃ N : ℕ, ∀ n ≥ N, Even n → integralOn (rationalWindows n (fun _ => True)) (excess n) ≤ (n:ℝ)/4608)
    (geom : ∃ N : ℕ, ∀ n ≥ N, Even n → integralOn (shellRegion n slow) (peaks n) ≤ (n:ℝ)/4608) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n (shellRegion n slow) ≤ (n:ℝ)/2304 := by
  obtain ⟨A,hA⟩ := err
  obtain ⟨B,hB⟩ := geom
  refine ⟨max A B, ?_⟩
  intro n hn he
  let s := shellRegion n slow
  let w := rationalWindows n (fun _ => True)
  have hw := measurableWindows n (fun _ => True)
  have hm := (measurableMask n).inter hw
  have ho := measurableWindows n (shortOrder n)
  have hs : MeasurableSet s := by cases slow; exact hm.diff ho; exact hm.inter ho
  have sub : s ⊆ w := by cases slow <;> exact fun _ ht => ht.1.2
  have hc : Continuous (peaks n) := by
    unfold peaks
    apply continuous_finsetSum
    intro q hq
    have hq' : 0<q := (Finset.mem_Icc.mp hq).1
    have hp := Nat.totient_pos.mpr hq'
    apply continuous_finsetSum
    intro a _
    have den : Continuous (fun t : ℝ => (Nat.totient q:ℝ)^2 *
        (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) := by fun_prop
    exact (continuous_const : Continuous (fun _ : ℝ => 4*(n:ℝ)^2)).div den
      (fun t => ne_of_gt (mul_pos (by positivity) (by positivity)))
  have hx : Continuous (excess n) := continuous_const.max ((continuousDensity n).sub hc)
  have hsum := intervalIntegral.integral_add (onRegion hs hc) (onRegion hw hx)
  have ma : regionMass n s ≤ integralOn s (peaks n) + integralOn w (excess n) := by
    unfold integralOn
    rw [← hsum]
    apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs (continuousDensity n))
      ((onRegion hs hc).add (onRegion hw hx))
    intro t _
    change s.indicator (density n) t ≤ s.indicator (peaks n) t + w.indicator (excess n) t
    by_cases ht : t ∈ s
    · simp only [Set.indicator_of_mem ht,Set.indicator_of_mem (sub ht)]
      dsimp [excess]
      linarith only [le_max_right 0 (density n t-peaks n t)]
    · by_cases h : t ∈ w <;> simp [ht,h,excess]
  change regionMass n s ≤ _
  linarith only [ma,hA n (by omega) he,hB n (by omega) he]


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
  have coeff (k : ℕ) (hk : k ≤ n) : |GoldbachBudget.high n k| ≤ x := by
    unfold GoldbachBudget.high GoldbachBudget.low
    by_cases hl : k^3 ≤ n
    · simp [hl]; linarith
    · simp only [hl, if_false, sub_zero, GoldbachBudget.w]
      by_cases hp : k.Prime
      · have hpos : (1:ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
        rw [if_pos hp,abs_of_nonneg (Real.log_nonneg hpos)]
        have h := Real.log_le_log (by positivity : 0<(k:ℝ)) (show (k:ℝ)≤n by exact_mod_cast hk)
        dsimp [x]; linarith
      · simp [hp]; linarith
  have mag : ‖GoldbachBudget.spec n (GoldbachBudget.high n) t‖ ≤ 2*(n:ℝ)*x := by
    unfold GoldbachBudget.spec
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖((GoldbachBudget.high n k:ℝ):ℂ)*GoldbachBudget.phase ((k:ℝ)*t)‖ := norm_sum_le ..
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


private def lambdaSpec (n : ℕ) := GoldbachBudget.spec n ArithmeticFunction.vonMangoldt
private def highSpec (n : ℕ) := GoldbachBudget.spec n (GoldbachBudget.high n)
private def perturbation (n : ℕ) (t : ℝ) := ‖lambdaSpec n t-highSpec n t‖^2

private theorem nonnegativePrime (k : ℕ) : 0 ≤ GoldbachBudget.w k := by
  unfold GoldbachBudget.w
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  · exact le_rfl

/-- Adding prime powers and restoring the low primes has an explicit uniform Fourier cost. -/
theorem mangoldtSpectralError (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖lambdaSpec n t-highSpec n t‖ ≤ 4*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
  let Λ := ArithmeticFunction.vonMangoldt
  let w := GoldbachBudget.w
  let lo := GoldbachBudget.low n
  let hi := GoldbachBudget.high n
  let R := Finset.range (n+1)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have dpos (k : ℕ) : 0 ≤ Λ k-w k := by
    dsimp only [Λ,w,GoldbachBudget.w]
    by_cases hp : k.Prime
    · simp [hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp,ArithmeticFunction.vonMangoldt_nonneg]
  have lpos (k : ℕ) : 0 ≤ lo k := by
    unfold lo GoldbachBudget.low
    split <;> first | exact nonnegativePrime _ | exact le_rfl
  have main (k : ℕ) : |Λ k-hi k| = (Λ k-w k)+lo k := by
    have eq : Λ k-hi k = (Λ k-w k)+lo k := by dsimp [hi,GoldbachBudget.high,lo,w]; ring
    rw [eq,abs_of_nonneg (add_nonneg (dpos k) (lpos k))]
  have ri : R = Finset.Icc 0 n := by ext k; simp [R]
  have hh : (∑ k ∈ R, (Λ k - w k)) = Chebyshev.psi (n:ℝ)-Chebyshev.theta (n:ℝ) := by
    rw [Finset.sum_sub_distrib,Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,
      Finset.sum_filter,Nat.floor_natCast,ri]
    rfl
  have lowMass : (∑ k ∈ R, lo k) ≤ 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
    let T := R.filter (fun k => k^3≤n)
    have eq : (∑ k ∈ R, lo k) = ∑ k ∈ T, w k := by simp [T,Finset.sum_filter,lo,GoldbachBudget.low,w]
    have subset : T ⊆ Finset.range (n.sqrt+1) := by
      intro k hk
      have bound := (Finset.mem_filter.mp hk).2
      have hk2 : k^2 ≤ n := by
        by_cases h : k=0
        · simp [h]
        · exact (Nat.pow_le_pow_right (by omega : 0<k) (by decide : 2≤3)).trans bound
      exact Finset.mem_range.mpr (by have := Nat.le_sqrt.mpr (show k*k≤n by simpa [pow_two] using hk2); omega)
    have wt {k : ℕ} (hk : k ∈ T) : w k ≤ Real.log (n:ℝ) := by
      have hkn := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      dsimp only [w,GoldbachBudget.w]
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
      ∑ k ∈ R, ((Λ k-hi k:ℝ):ℂ)*GoldbachBudget.phase ((k:ℝ)*t) := by
    unfold lambdaSpec highSpec GoldbachBudget.spec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.ofReal_sub,sub_mul,Λ,hi]
  rw [dif]
  calc
    _ ≤ ∑ k ∈ R, ‖((Λ k-hi k:ℝ):ℂ)*GoldbachBudget.phase ((k:ℝ)*t)‖ := norm_sum_le ..
    _ = (∑ k ∈ R, (Λ k-w k)) + ∑ k ∈ R, lo k := by
      simp only [norm_mul,phaseUnit,mul_one,Complex.norm_real,Real.norm_eq_abs,main,Finset.sum_add_distrib]
    _ ≤ _ := by rw [hh]; linarith only [Chebyshev.psi_sub_theta_le hn',lowMass]

theorem mangoldtMaskedError (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n ≥ N,
    integralOn (resonant n) (perturbation n) ≤ ε*(n:ℝ) := by
  obtain ⟨N,hN⟩ := maskLogDecay 2 (ε/16) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : 1≤n := by omega
  have hl := Real.log_nonneg (by exact_mod_cast hn1 : (1:ℝ) ≤ n)
  have hc : Continuous (perturbation n) := by
    unfold perturbation lambdaSpec highSpec GoldbachBudget.spec GoldbachBudget.phase
    fun_prop
  let C := 16*(n:ℝ)*(1+Real.log (n:ℝ))^2
  have pt (t : ℝ) : perturbation n t ≤ C := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (mangoldtSpectralError n hn1 t) 2
    have id : (4*Real.sqrt (n:ℝ)*Real.log (n:ℝ))^2 = 16*(n:ℝ)*Real.log (n:ℝ)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [id] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by nlinarith : Real.log (n:ℝ)^2 ≤ (1+Real.log (n:ℝ))^2) (by positivity))
  let A := (resonant n).indicator (fun _ => (1:ℝ))
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

theorem resonantFromMangoldt
    (hΛ : ∃ N : ℕ, ∀ n ≥ N, Even n →
      integralOn (resonant n) (fun t => ‖lambdaSpec n t‖^2) ≤ (n:ℝ)/640) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → regionMass n (resonant n) ≤ (n:ℝ)/576 := by
  obtain ⟨N,hN⟩ := hΛ
  obtain ⟨M,hM⟩ := mangoldtMaskedError (1/1000000) (by norm_num)
  refine ⟨max N M, ?_⟩
  intro n hn he
  let s := resonant n
  let f := fun t => ‖lambdaSpec n t‖^2
  let d := perturbation n
  have hc : Continuous f := by unfold f lambdaSpec GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have hd : Continuous d := by unfold d perturbation lambdaSpec highSpec GoldbachBudget.spec GoldbachBudget.phase; fun_prop
  have key : regionMass n s ≤ (17/16)*integralOn s f + 17*integralOn s d := by
    unfold integralOn
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((onRegion (measurableMask n) hc).const_mul _) ((onRegion (measurableMask n) hd).const_mul _)]
    apply intervalIntegral.integral_mono_on (by norm_num) (onRegion (measurableMask n) (continuousDensity n))
      (((onRegion (measurableMask n) hc).const_mul _).add ((onRegion (measurableMask n) hd).const_mul _))
    intro t _
    change s.indicator (density n) t ≤ (17/16)*s.indicator f t+17*s.indicator d t
    by_cases ht : t ∈ s
    · simp only [Set.indicator_of_mem ht]
      have tri : ‖highSpec n t‖ ≤ ‖lambdaSpec n t‖+‖lambdaSpec n t-highSpec n t‖ := by
        have eq : highSpec n t = lambdaSpec n t - (lambdaSpec n t-highSpec n t) := by abel
        calc
          _ = ‖lambdaSpec n t - (lambdaSpec n t-highSpec n t)‖ := congrArg norm eq
          _ ≤ _ := norm_sub_le ..
      have hs := pow_le_pow_left₀ (norm_nonneg _) tri 2
      change ‖highSpec n t‖^2 ≤ (17/16)*‖lambdaSpec n t‖^2+17*‖lambdaSpec n t-highSpec n t‖^2
      nlinarith only [hs,sq_nonneg (‖lambdaSpec n t‖/4-4*‖lambdaSpec n t-highSpec n t‖)]
    · simp [ht]
  have h := hN n (by omega) he
  have h' := hM n (by omega)
  change integralOn s f ≤ _ at h
  change integralOn s d ≤ _ at h'
  change regionMass n s ≤ _
  linarith only [key,h,h',Nat.cast_nonneg (α := ℝ) n]


/-- Odd moduli need no factor of two in the elementary square-root lower bound for φ. -/
private theorem totientSquare (q : ℕ) :
    q ≤ 2*q.totient^2 ∧ (¬ 2 ∣ q → q ≤ q.totient^2) := by
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    rcases eq_or_ne q 0 with rfl | h0
    · simp
    rcases eq_or_ne q 1 with rfl | h1
    · simp
    obtain ⟨p,hp,m,rfl⟩ := Nat.exists_prime_and_dvd h1
    have hp2 := hp.two_le
    have hm : 0 < m := Nat.pos_of_ne_zero (fun hz => h0 (by simp [hz]))
    have lt : m < p*m := by nlinarith [Nat.mul_le_mul_right m hp2]
    obtain ⟨all,odd⟩ := ih m lt
    have lift (f c : ℕ) (eq : (p*m).totient = f*m.totient) (hf : p ≤ f^2)
        (h : m ≤ c*m.totient^2) : p*m ≤ c*(p*m).totient^2 := by
      calc
        _ ≤ f^2*(c*m.totient^2) := Nat.mul_le_mul hf h
        _ = _ := by rw [eq]; ring
    have both (f : ℕ) (eq : (p*m).totient = f*m.totient) (hf : p ≤ f^2) :
        p*m ≤ 2*(p*m).totient^2 ∧ (¬2 ∣ p*m → p*m ≤ (p*m).totient^2) := by
      refine ⟨lift f 2 eq hf all, ?_⟩
      intro hn
      have hodd := odd (fun h => hn (dvd_mul_of_dvd_right h p))
      simpa only [one_mul] using lift f 1 eq hf (by simpa using hodd)
    by_cases divides : p ∣ m
    · exact both p (Nat.totient_mul_of_dvd divides) (by nlinarith [Nat.le_mul_self p])
    · have eq := Nat.totient_mul_of_prime_of_not_dvd hp divides
      by_cases two : p=2
      · subst p
        simp only [Nat.reduceSub,one_mul] at eq
        constructor
        · rw [eq]; exact Nat.mul_le_mul_left 2 (odd divides)
        · simp
      · apply both (p-1) eq
        have e : p = (p-1)+1 := by omega
        have g : 2 ≤ p-1 := by omega
        nlinarith [Nat.mul_le_mul_right (p-1) g]

/-- A telescoping bound, sufficient for summing the Lorentz tails for all denominators. -/
private theorem totientSum (m : ℕ) :
    (∑ j ∈ Finset.range m, 1/((j+1).totient:ℝ)) ≤ 4*Real.sqrt (m:ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let u := Real.sqrt (m:ℝ)
    let v := Real.sqrt ((m:ℝ)+1)
    let f : ℝ := (m+1).totient
    have fp : 0 < f := by dsimp [f]; exact_mod_cast (Nat.totient_pos.mpr (Nat.succ_pos m))
    have hb : (m:ℝ)+1 ≤ 2*f^2 := by dsimp [f]; exact_mod_cast (totientSquare (m+1)).1
    have hu : u^2 = (m:ℝ) := Real.sq_sqrt (by positivity)
    have hv : v^2 = (m:ℝ)+1 := Real.sq_sqrt (by positivity)
    have uv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
    have pos : 0 ≤ v := Real.sqrt_nonneg _
    have v2 : v ≤ 2*f := by
      by_contra! hh
      have h := mul_pos (sub_pos.mpr hh) (show 0<v+2*f by linarith)
      nlinarith only [hb,hv,h,sq_nonneg f]
    have bound : v+u ≤ 4*f := by linarith
    have step : 1/f ≤ 4*(v-u) := by
      apply (div_le_iff₀ fp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right bound (sub_nonneg.mpr uv),hu,hv]
    rw [Finset.sum_range_succ,Nat.cast_succ]
    change _ ≤ 4*v
    linarith only [ih,step]

private def profile (n q : ℕ) (c t : ℝ) :=
  4*(n:ℝ)^2/((q.totient:ℝ)^2*(1+((n:ℝ)*(t-c))^2))
private def farPeak (n q : ℕ) (a : ℕ) :=
  integralOn {t : ℝ | (gridQ n:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} (profile n q ((a:ℝ)/(q:ℝ)))

private theorem peakOutside (n q : ℕ) (hq : 0<q) (c r : ℝ) (hr : 0<r) :
    integralOn {t : ℝ | r < |t-c|} (profile n q c) ≤
      (8/(q.totient:ℝ)^2)*(Real.pi/r) := by
  let f : ℝ := q.totient
  let s := {t : ℝ | r < |t-c|}
  have fp : 0<f := by dsimp [f]; exact_mod_cast (Nat.totient_pos.mpr hq)
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
  have hd : Continuous (fun t : ℝ => f^2*(1+((n:ℝ)*(t-c))^2)) := by fun_prop
  have hc : Continuous (profile n q c) :=
    (continuous_const : Continuous (fun _ : ℝ => 4*(n:ℝ)^2)).div hd
      (fun t => ne_of_gt (mul_pos (by positivity) (by positivity)))
  calc
    _ ≤ ∫ t in (0:ℝ)..1, (8/f^2)*lorentz r c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc)
        (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
      intro t _
      change s.indicator (profile n q c) t ≤ _
      by_cases ht : t ∈ s
      · rw [Set.indicator_of_mem ht]
        have d : r ≤ |t-c| := le_of_lt ht
        have sq := pow_le_pow_left₀ hr.le d 2
        rw [sq_abs] at sq
        have bound : (n:ℝ)^2/(1+((n:ℝ)*(t-c))^2) ≤ 2/(r^2+(t-c)^2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left sq (sq_nonneg (n:ℝ))]
        calc
          profile n q c t = (4/f^2)*((n:ℝ)^2/(1+((n:ℝ)*(t-c))^2)) := by unfold profile; dsimp [f]; field_simp <;> ring
          _ ≤ (4/f^2)*(2/(r^2+(t-c)^2)) := mul_le_mul_of_nonneg_left bound (by positivity)
          _ = _ := by unfold lorentz; ring
      · rw [Set.indicator_of_notMem ht]; unfold lorentz; positivity
    _ = (8/f^2)*(∫ t in (0:ℝ)..1, lorentz r c t) := intervalIntegral.integral_const_mul ..
    _ ≤ (8/f^2)*(Real.pi/r) := mul_le_mul_of_nonneg_left (lorentzIntegral hr c) (by positivity)

private theorem singleFarPeak (n q : ℕ) (hn : 0<n) (hq : 0<q) (hQ : 0<gridQ n) (a : ℕ) :
    farPeak n q a ≤ (8*Real.pi*((n:ℝ)/(gridQ n:ℝ)^2))/(q.totient:ℝ)^2 := by
  have hr : 0 < (gridQ n:ℝ)^2/(n:ℝ) := by positivity
  apply (peakOutside n q hq ((a:ℝ)/(q:ℝ)) _ hr).trans_eq
  field_simp <;> ring

private def numerators (q : ℕ) := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)

private theorem countNumerators (q : ℕ) (hq : 0<q) : (numerators q).card ≤ 2*q.totient := by
  have card : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime,Nat.coprime_comm]
  have sub : numerators q ⊆ insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp ha
    rcases eq_or_ne a q with rfl | h
    · simp
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega),hc⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  rw [card] at bound
  have hp := Nat.totient_pos.mpr hq
  omega

theorem farTailQuantitative (n : ℕ) (hn : 0<n) (hQ : 0<gridQ n) :
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤
      64*Real.pi*(n:ℝ)/(gridQ n:ℝ) := by
  let Q := gridQ n
  let C := 8*Real.pi*((n:ℝ)/(Q:ℝ)^2)
  have pos : 0≤C := by dsimp [C]; positivity
  have bb (q : ℕ) (hq : 0<q) : (∑ a ∈ numerators q, farPeak n q a) ≤ (2*C)*(1/(q.totient:ℝ)) := by
    have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    calc
      _ ≤ ∑ _a ∈ numerators q, C/(q.totient:ℝ)^2 := Finset.sum_le_sum fun a _ => singleFarPeak n q hn hq hQ a
      _ = ((numerators q).card:ℝ)*(C/(q.totient:ℝ)^2) := by simp
      _ ≤ (2*(q.totient:ℝ))*(C/(q.totient:ℝ)^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast countNumerators q hq
      _ = _ := by field_simp <;> ring
  have index : Finset.Icc 1 (Q^2) = (Finset.range (Q^2)).map (addRightEmbedding 1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨k-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (Q^2), (2*C)*(1/(q.totient:ℝ)) :=
      Finset.sum_le_sum fun q h => bb q (Finset.mem_Icc.mp h).1
    _ = (2*C)*(∑ j ∈ Finset.range (Q^2), 1/((j+1).totient:ℝ)) := by
      rw [index,← Finset.mul_sum,Finset.sum_map]; rfl
    _ ≤ (2*C)*(4*Real.sqrt ((Q^2:ℕ):ℝ)) := mul_le_mul_of_nonneg_left (totientSum (Q^2)) (by positivity)
    _ = _ := by
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
      dsimp [C,Q]; field_simp <;> ring

theorem farTails (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤ ε*(n:ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (64*Real.pi/ε)
  let B := max 1 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0<n := lt_of_lt_of_le (by positivity : 0<2^B) hn
  have hb : B ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by unfold gridQ; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have hQ : 0<gridQ n := lt_of_lt_of_le (by dsimp [B]; omega) hq
  apply (farTailQuantitative n hn' hQ).trans
  have hM' : 64*Real.pi/ε ≤ (gridQ n:ℝ) := hM.trans (by exact_mod_cast (le_trans (le_max_right 1 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM') (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]


private theorem packetVariation (m : ℕ) (hm : 0< m) (x y : ℝ) :
    |packet m x/(m:ℝ)-packet m y/(m:ℝ)| ≤ 2*Real.pi*(2:ℝ)^m*|x-y| := by
  have mr : (0:ℝ)< m := by exact_mod_cast hm
  let C := 2*Real.pi*(2:ℝ)^m*|x-y|
  rw [← sub_div,abs_div,abs_of_pos mr]
  apply (div_le_iff₀ mr).mpr
  unfold packet
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range m, |Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x) - Real.cos (2*Real.pi*(2:ℝ)^(j+1)*y)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _j ∈ Finset.range m, C := by
      apply Finset.sum_le_sum
      intro j hj
      let f := 2*Real.pi*(2:ℝ)^(j+1)
      apply (Real.abs_cos_sub_cos_le (f*x) (f*y)).trans
      rw [← mul_sub,abs_mul,abs_of_nonneg (by dsimp [f]; positivity : 0 ≤ f)]
      dsimp [f,C]
      gcongr <;> first | exact Finset.mem_range.mp hj | norm_num
    _ = _ := by simp [C] <;> ring

private theorem exponentialRoom (m : ℕ) (hm : 128≤ m) :
    48*(2*(m:ℝ)+3)^4 ≤ (2:ℝ)^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      _ ≤ 2*(48*(2*((128+k:ℕ):ℝ)+3)^4) := by
        apply sub_nonneg.mp
        push_cast
        ring_nf
        positivity
      _ ≤ 2*(2:ℝ)^(128+k) := by linarith only [ih]
      _ = _ := by rw [show 128+(k+1)=(128+k)+1 by omega,pow_succ]; ring

theorem rationalCenterStability : ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ,
    |x-y| ≤ (gridQ n:ℝ)^2/(n:ℝ) → (1:ℝ)/2 < packet (length n) x/(length n:ℝ) →
      (1:ℝ)/3 < packet (length n) y/(length n:ℝ) := by
  refine ⟨2^256, ?_⟩
  intro n hn x y hxy hpeak
  let k := Nat.log 2 n
  let m := length n
  have hk : 256 ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hlen : m = k/2 := by dsimp [m,k,length]; omega
  have hm : 128≤ m := by omega
  have hn' : 0<n := lt_of_lt_of_le (by positivity : 0<2^256) hn
  have nr : (0:ℝ)<n := by exact_mod_cast hn'
  have top := Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have base : 2^k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have next : Nat.log 2 (n+2) ≤ k+1 := by
    by_contra! tooBig
    have pw := Nat.pow_le_pow_right (by decide : 0<2) (show k+2 ≤ Nat.log 2 (n+2) by omega)
    have up := Nat.pow_log_le_self 2 (by omega : n+2≠0)
    change n<2^(k+1) at top
    rw [show k+2=(k+1)+1 by omega,pow_succ] at pw
    have one : 2≤2^(k+1) := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤k+1 by omega)
    omega
  have qbound : (gridQ n:ℝ)^2 ≤ (2*(m:ℝ)+3)^4 := by
    have h : Nat.log 2 (n+2) ≤ 2*m+3 := by omega
    have h' : (Nat.log 2 (n+2):ℝ) ≤ 2*(m:ℝ)+3 := by exact_mod_cast h
    unfold gridQ
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h' 4
  have pn : ((2:ℝ)^m)^2 ≤ n := by
    rw [← pow_mul]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (show m*2≤k by omega)).trans base
  have hq : 48*(gridQ n:ℝ)^2 ≤ (2:ℝ)^m := by linarith only [exponentialRoom m hm,qbound]
  have coeff : 12*Real.pi*(gridQ n:ℝ)^2 ≤ (2:ℝ)^m := by
    linarith only [hq,mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg (gridQ n:ℝ))]
  have cost : 2*Real.pi*(2:ℝ)^m*|x-y| ≤ 1/6 := by
    apply (mul_le_mul_of_nonneg_left hxy (by positivity : 0≤2*Real.pi*(2:ℝ)^m)).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ nr).mpr
    linarith only [mul_le_mul_of_nonneg_right coeff (by positivity : 0 ≤ (2:ℝ)^m),pn]
  have bound := (packetVariation m (by omega) x y).trans cost
  change (1:ℝ)/2 < packet m x/(m:ℝ) at hpeak
  change (1:ℝ)/3 < packet m y/(m:ℝ)
  linarith only [le_abs_self (packet m x/(m:ℝ)-packet m y/(m:ℝ)),bound,hpeak]


private theorem profileContinuous (n q : ℕ) (hq : 0<q) (c : ℝ) : Continuous (profile n q c) := by
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold profile
  fun_prop (disch := intro t; positivity)

private theorem profileNonneg (n q : ℕ) (c t : ℝ) : 0 ≤ profile n q c t := by unfold profile; positivity

private theorem onSubset {s v : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s) (hv : MeasurableSet v)
    (h : s ⊆ v) (hc : Continuous f) (hpos : ∀ t, 0≤f t) : integralOn s f ≤ integralOn v f := by
  apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc) (onRegion hv hc)
  intro t _
  by_cases ht : t ∈ s
  · simp [ht,h ht]
  · by_cases ht' : t ∈ v <;> simp [ht,ht',hpos]

private theorem onFiniteSum {ι : Type*} (T : Finset ι) {s : Set ℝ} (hs : MeasurableSet s)
    (f : ι → ℝ → ℝ) (hc : ∀ i ∈ T, Continuous (f i)) :
    integralOn s (fun t => ∑ i ∈ T, f i t) = ∑ i ∈ T, integralOn s (f i) := by
  have eq : s.indicator (fun t => ∑ i ∈ T, f i t) = fun t => ∑ i ∈ T, s.indicator (f i) t := by
    funext t; by_cases h : t ∈ s <;> simp [h]
  unfold integralOn
  rw [eq, intervalIntegral.integral_finsetSum (fun i hi => onRegion hs (hc i hi))]

private abbrev detected (n q a : ℕ) := (1:ℝ)/3 < packet (length n) ((a:ℝ)/(q:ℝ))/(length n:ℝ)
private def centerWeight (n q : ℕ) :=
  min (1:ℝ) ((q:ℝ)/(gridQ n:ℝ)) *
    (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ detected n q a)).card:ℝ)/(q.totient:ℝ)^2

private theorem oneCenterMass (n q a : ℕ) (hn : 0<n) (hq : 0<q) (hQ : 0<gridQ n) (ha : a≤q) :
    integralOn (resonant n) (profile n q ((a:ℝ)/(q:ℝ))) ≤
      8*Real.pi*(n:ℝ)*min 1 ((q:ℝ)/(gridQ n:ℝ))/(q.totient:ℝ)^2 := by
  let c := (a:ℝ)/(q:ℝ)
  have hc := profileContinuous n q hq c
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have nr : 0 < (n:ℝ) := by exact_mod_cast hn
  have qr : 0 < (gridQ n:ℝ) := by exact_mod_cast hQ
  by_cases small : q ≤ gridQ n
  · let r := (gridQ n:ℝ)/((q:ℝ)*(n:ℝ))
    have hr : 0<r := by dsimp [r]; positivity
    have hs : MeasurableSet {t : ℝ | r < |t-c|} :=
      (isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
    have sub : resonant n ⊆ {t : ℝ | r < |t-c|} :=
      fun _ h => denominatorExclusion hn hq small ha h.1
    apply (onSubset (measurableMask n) hs sub hc (profileNonneg n q c)).trans
    apply (peakOutside n q hq c r hr).trans_eq
    rw [min_eq_right ((div_le_one qr).mpr (by exact_mod_cast small))]
    dsimp [r]; field_simp <;> ring
  · have ht : 1 ≤ (q:ℝ)/(gridQ n:ℝ) := (one_le_div qr).mpr (by exact_mod_cast (by omega : gridQ n ≤ q))
    rw [min_eq_left ht,mul_one]
    let r := 1/(n:ℝ)
    have hr : 0<r := by dsimp [r]; positivity
    have id (t : ℝ) : profile n q c t = (4/(q.totient:ℝ)^2)*lorentz r c t := by
      dsimp [profile,lorentz,r]; field_simp <;> ring
    calc
      _ ≤ ∫ t in (0:ℝ)..1, (4/(q.totient:ℝ)^2)*lorentz r c t := by
        apply intervalIntegral.integral_mono_on (by norm_num) (onRegion (measurableMask n) hc)
          (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
        intro t _
        by_cases h : t ∈ resonant n
        · rw [Set.indicator_of_mem h,id]
        · rw [Set.indicator_of_notMem h]; unfold lorentz; positivity
      _ = (4/(q.totient:ℝ)^2)*_ := intervalIntegral.integral_const_mul ..
      _ ≤ (4/(q.totient:ℝ)^2)*(Real.pi/r) := mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by positivity)
      _ ≤ _ := by dsimp [r]; field_simp <;> nlinarith only [mul_pos Real.pi_pos nr]

/-- Count all active rational centers; away from a center only its unconditional tail is charged. -/
theorem modelFromCenters
    (counts : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, integralOn (resonant n) (peaks n) ≤ ε*(n:ℝ) := by
  intro ε hε
  obtain ⟨C,hC⟩ := counts (ε/(16*Real.pi)) (by positivity)
  obtain ⟨F,hF⟩ := farTails (ε/2) (by positivity)
  obtain ⟨K,hK⟩ := rationalCenterStability
  refine ⟨max 1 (max K (max F C)), ?_⟩
  intro n hn
  have hn' : 0<n := by omega
  have g : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by norm_num <;> omega)
  have hQ : 0<gridQ n := by unfold gridQ; positivity
  let D := Finset.Icc 1 ((gridQ n)^2)
  let P := 8*Real.pi*(n:ℝ)
  let V := fun q : ℕ => P*min 1 ((q:ℝ)/(gridQ n:ℝ))/(q.totient:ℝ)^2
  have bound (q : ℕ) (hq : 0<q) (a : ℕ) (ha : a≤q) :
      integralOn (resonant n) (profile n q ((a:ℝ)/(q:ℝ))) ≤ farPeak n q a + (if detected n q a then V q else 0) := by
    let c := (a:ℝ)/(q:ℝ)
    let r := (gridQ n:ℝ)^2/(n:ℝ)
    by_cases h : detected n q a
    · rw [if_pos h]
      apply (oneCenterMass n q a hn' hq hQ ha).trans
      apply le_add_of_nonneg_left
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t _
      change 0 ≤ ({t : ℝ | r < |t-c|}.indicator (profile n q c)) t
      by_cases ht : t ∈ {t : ℝ | r < |t-c|}
      · rw [Set.indicator_of_mem ht]; exact profileNonneg n q c t
      · rw [Set.indicator_of_notMem ht]
    · rw [if_neg h,add_zero]
      have sub : resonant n ⊆ {t : ℝ | r < |t-c|} := by
        intro t ht
        change r < |t-c|
        by_contra! hh
        exact h (hK n (by omega) t c hh ht.2)
      have hs : MeasurableSet {t : ℝ | r < |t-c|} :=
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
      exact onSubset (measurableMask n) hs sub (profileContinuous n q hq c) (profileNonneg n q c)
  have accumulate (q : ℕ) (hq : q ∈ D) :
      integralOn (resonant n) (fun t => ∑ a ∈ numerators q, profile n q ((a:ℝ)/(q:ℝ)) t)
      ≤ (∑ a ∈ numerators q, farPeak n q a) + P*centerWeight n q := by
    have pos := (Finset.mem_Icc.mp hq).1
    rw [onFiniteSum (numerators q) (measurableMask n) _ (fun a _ => profileContinuous n q pos _)]
    apply (Finset.sum_le_sum (fun a (ha : a ∈ numerators q) => bound q pos a
      (by have h := Finset.mem_range.mp (Finset.mem_filter.mp ha).1; omega))).trans_eq
    rw [Finset.sum_add_distrib,← Finset.sum_filter]
    congr 1
    simp only [numerators,Finset.filter_filter,Finset.sum_const,nsmul_eq_mul,centerWeight,V]
    ring
  calc
    _ = ∑ q ∈ D, integralOn (resonant n) (fun t => ∑ a ∈ numerators q, profile n q ((a:ℝ)/(q:ℝ)) t) := by
      apply onFiniteSum D (measurableMask n)
      intro q hq
      apply continuous_finsetSum
      intro a _
      exact profileContinuous n q (Finset.mem_Icc.mp hq).1 _
    _ ≤ ∑ q ∈ D, ((∑ a ∈ numerators q, farPeak n q a) + P*centerWeight n q) := Finset.sum_le_sum accumulate
    _ = (∑ q ∈ D, ∑ a ∈ numerators q, farPeak n q a) + P*(∑ q ∈ D, centerWeight n q) := by rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ε/2*(n:ℝ)+P*(ε/(16*Real.pi)) := add_le_add (hF n (by omega))
      (mul_le_mul_of_nonneg_left (hC n (by omega)) (by dsimp [P]; positivity))
    _ = _ := by dsimp [P]; field_simp <;> ring


private abbrev lowOrderTest (n q : ℕ) := q % 2 = 1 ∧
  ((Finset.Icc 1 ((Nat.log 2 (gridQ n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty

theorem combineCenterCounts
    (slow : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q), centerWeight n q) ≤ ε)
    (rest : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => ¬lowOrderTest n q), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨A,hA⟩ := slow (ε/2) (by positivity)
  obtain ⟨B,hB⟩ := rest (ε/2) (by positivity)
  refine ⟨max A B, ?_⟩
  intro n hn
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ((gridQ n)^2)) (lowOrderTest n)]
  linarith only [hA n (by omega),hB n (by omega)]

theorem modelRegionFromFull (slow : Bool)
    (model : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, integralOn (resonant n) (peaks n) ≤ ε*(n:ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → integralOn (shellRegion n slow) (peaks n) ≤ (n:ℝ)/4608 := by
  obtain ⟨N,hN⟩ := model (1/4608) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn _
  have hm := (measurableMask n).inter (measurableWindows n (fun _ => True))
  have ho := measurableWindows n (shortOrder n)
  have hs : MeasurableSet (shellRegion n slow) := by cases slow; exact hm.diff ho; exact hm.inter ho
  have sub : shellRegion n slow ⊆ resonant n := by cases slow <;> exact fun _ ht => ht.1.1
  have hc : Continuous (peaks n) := by
    apply continuous_finsetSum
    intro q hq
    apply continuous_finsetSum
    intro a _
    exact profileContinuous n q (Finset.mem_Icc.mp hq).1 _
  have pos (t : ℝ) : 0 ≤ peaks n t := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun a _ => profileNonneg n q _ t
  apply (onSubset hs (measurableMask n) sub hc pos).trans
  linarith only [hN n hn]


private abbrev smoothTest (n q : ℕ) :=
  ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (gridQ n))^8
private def denominatorWeight (n q : ℕ) := min (1:ℝ) ((q:ℝ)/(gridQ n:ℝ))/(q.totient:ℝ)

theorem shortCentersFromModuli
    (smooth : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => smoothTest n q), denominatorWeight n q) ≤ ε)
    (large : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q), denominatorWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q), centerWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨A,hA⟩ := smooth (ε/4) (by positivity)
  obtain ⟨B,hB⟩ := large (ε/4) (by positivity)
  refine ⟨max A B, ?_⟩
  intro n hn
  let D := Finset.Icc 1 ((gridQ n)^2)
  let U := D.filter (fun q => lowOrderTest n q)
  have nonneg (q : ℕ) : 0≤denominatorWeight n q := by unfold denominatorWeight; positivity
  have bound (q : ℕ) (hq : q∈U) : centerWeight n q ≤ 2*denominatorWeight n q := by
    have hq' : 0<q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq'
    let good := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ detected n q a)
    have sub : good ⊆ numerators q := by
      intro a h; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2.1⟩
    have card : (good.card:ℝ) ≤ 2*(q.totient:ℝ) := by exact_mod_cast (Finset.card_le_card sub).trans (countNumerators q hq')
    let w := min (1:ℝ) ((q:ℝ)/(gridQ n:ℝ))
    have pos : 0≤w := by dsimp [w]; positivity
    change w*(good.card:ℝ)/(q.totient:ℝ)^2 ≤ 2*(w/(q.totient:ℝ))
    apply ((div_le_div_iff_of_pos_right (by positivity)).mpr (mul_le_mul_of_nonneg_left card pos)).trans_eq
    field_simp <;> ring
  have sub : U.filter (smoothTest n) ⊆ D.filter (smoothTest n) := by
    intro q h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1,(Finset.mem_filter.mp h).2⟩
  have sm : (∑ q ∈ U.filter (smoothTest n), denominatorWeight n q) ≤ ε/4 :=
    (Finset.sum_le_sum_of_subset_of_nonneg sub (fun q _ _ => nonneg q)).trans (hA n (by omega))
  have lg : (∑ q ∈ U.filter (fun q => ¬smoothTest n q), denominatorWeight n q) ≤ ε/4 := by
    simpa only [U,D,Finset.filter_filter] using hB n (by omega)
  have eq := Finset.sum_filter_add_sum_filter_not U (smoothTest n) (denominatorWeight n)
  calc
    _ ≤ ∑ q ∈ U, 2*denominatorWeight n q := Finset.sum_le_sum bound
    _ = 2*∑ q ∈ U, denominatorWeight n q := (Finset.mul_sum ..).symm
    _ ≤ ε := by linarith only [sm,lg,eq]


/-- Prime factors witnessing short multiplicative order are sparse in reciprocal weight,
even when counted repeatedly for different periods. -/
theorem periodPrimeBudget (H Y : ℕ) (hY : 0<Y) :
    (∑ j ∈ Finset.Icc 1 H, ∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)),
      1/((p:ℝ)-1)) ≤ (H:ℝ)^2/Y := by
  have one (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
      (∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)), 1/((p:ℝ)-1)) ≤ (H:ℝ)/(Y:ℝ) := by
    let M : ℕ := 2^j-1
    let primes := M.primeFactors
    let T := primes.filter (fun p => Y<p)
    have jpos := (Finset.mem_Icc.mp hj).1
    have jle := (Finset.mem_Icc.mp hj).2
    have Mpos : 0<M := by
      have two : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) jpos
      dsimp [M]; omega
    have hc : 2^primes.card ≤ M := by
      calc
        _ = ∏ _p ∈ primes, (2:ℕ) := by simp
        _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod' (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
        _ ≤ M := Nat.le_of_dvd Mpos (Nat.prod_primeFactors_dvd M)
    have card : primes.card ≤ j := by
      by_contra! hh
      have lower := Nat.pow_le_pow_right (by decide : 0<2) (show j+1 ≤ primes.card by omega)
      rw [pow_succ] at lower
      dsimp [M] at hc
      omega
    have cr : (T.card:ℝ) ≤ (H:ℝ) := by exact_mod_cast
      ((Finset.card_le_card (Finset.filter_subset _ primes)).trans card).trans jle
    change (∑ p ∈ T, _) ≤ _
    calc
      _ ≤ ∑ _p ∈ T, 1/(Y:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi : (Y:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (T.card:ℝ)/(Y:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (H:ℝ)/(Y:ℝ) := Finset.sum_le_sum one
    _ = _ := by simp [pow_two] <;> ring


private theorem fractionProduct (S : Finset ℕ) (hs : ∀ p ∈ S, 2≤p) :
    (∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)) ≤ (S.card:ℝ)+1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := hs a (Finset.mem_insert_self ..)
    have old (p : ℕ) (hp : p∈S) := hs p (Finset.mem_insert_of_mem hp)
    have ha' : 0 < (a:ℝ)-1 := by
      have h : (2:ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have notMem : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have sub : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨old p hp,hmax p hp⟩
    have count := Finset.card_le_card sub
    rw [Nat.card_Ico] at count
    have cr : (S.card:ℝ)+2 ≤ (a:ℝ) := by exact_mod_cast (show S.card+2≤a by omega)
    rw [Finset.prod_insert notMem,Finset.card_insert_of_notMem notMem,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left (ih old) (div_nonneg (Nat.cast_nonneg _) ha'.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha').mpr
    linarith

private theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' hs
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have id : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by
    rw [Finset.prod_div_distrib]
    have pos : 0 < ∏ p ∈ S, ((p:ℝ)-1) := Finset.prod_pos (fun p hp => by
      have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
      linarith)
    apply (div_eq_div_iff hf.ne' pos.ne').mpr
    have formula := congrArg (fun k : ℕ => (k:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul,Nat.cast_prod] at formula
    change (q:ℝ)*_ = _*(q.totient:ℝ)
    rw [mul_comm _ (q.totient:ℝ)]
    dsimp [S]
    rw [formula]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have h := hs p hp; omega),Nat.cast_one]
  rw [id]
  exact (fractionProduct S hs).trans (by exact_mod_cast (show S.card+1≤Nat.log 2 q+1 by omega))

private theorem harmonicBlock (k : ℕ) :
    (∑ m ∈ Finset.range (2^k), 1/((m:ℝ)+1)) ≤ (k:ℝ)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have block : (∑ j ∈ Finset.range (2^k), 1/(((2^k+j:ℕ):ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), 1/((2:ℝ)^k) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = _ := by simp
    push_cast at block ⊢
    linarith only [ih,block]

theorem reciprocalTotientLogBound (X : ℕ) (hX : 0<X) :
    (∑ m ∈ Finset.Icc 1 X, 1/(m.totient:ℝ)) ≤ ((Nat.log 2 X:ℝ)+2)^2 := by
  let k := Nat.log 2 X
  have idx : Finset.Icc 1 X = (Finset.range X).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨m-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  have upper := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have harm : (∑ m ∈ Finset.range X, 1/((m:ℝ)+1)) ≤ (k:ℝ)+2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono upper) (fun m _ _ => by positivity)).trans
    convert harmonicBlock (k+1) using 1 <;> push_cast <;> ring
  rw [idx,Finset.sum_map]
  calc
    _ ≤ ∑ j ∈ Finset.range X, ((k:ℝ)+1)*(1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have le : j+1 ≤ X := Finset.mem_range.mp hj
      have hk : Nat.log 2 (j+1) ≤ k := Nat.log_mono_right le
      have b := totientLogLower (j+1) (by omega)
      have h : (((j+1:ℕ):ℝ)/((j+1).totient:ℝ)) ≤ (k:ℝ)+1 := b.trans (by exact_mod_cast (Nat.add_le_add_right hk 1))
      change 1/((j+1).totient:ℝ) ≤ _
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      push_cast at h
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
    _ = ((k:ℝ)+1)*_ := (Finset.mul_sum ..).symm
    _ ≤ ((k:ℝ)+1)*((k:ℝ)+2) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ _ := by dsimp [k]; nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.log 2 X)]


private theorem chargeWitnesses {α β : Type*} [DecidableEq β]
    (S : Finset β) (T : Finset α) (key : α → β) (w : β → ℝ) (v : α → ℝ)
    (pos : ∀ a∈T, 0≤v a) (charge : ∀ b∈S, ∃ a∈T, key a=b ∧ w b≤v a) :
    (∑ b ∈ S, w b) ≤ ∑ a ∈ T, v a := by
  calc
    _ ≤ ∑ b ∈ S, ∑ a ∈ T, if key a=b then v a else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a,ha,e,h⟩ := charge b hb
      apply h.trans
      simpa only [e,if_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]

private theorem largePeriodWeightFinite (n : ℕ) :
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤
      (∑ m ∈ Finset.Icc 1 ((gridQ n)^2), 1/(m.totient:ℝ)) *
        (((1+Nat.log 2 (gridQ n):ℕ):ℝ)^4 / ((1+Nat.log 2 (gridQ n):ℕ):ℝ)^8) := by
  classical
  let u := 1+Nat.log 2 (gridQ n)
  let H := u^2
  let Y := u^8
  let X := (gridQ n)^2
  let D := Finset.Icc 1 X
  let J := Finset.Icc 1 H
  let Ps := fun j : ℕ => (2^j-1:ℕ).primeFactors.filter (fun p => Y<p)
  let T : Finset (Σ _j : ℕ, ℕ × ℕ) := J.sigma (fun j => Ps j ×ˢ D)
  let S := D.filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q)
  let v := fun a : (Σ _j : ℕ, ℕ × ℕ) => (1/((a.2.1:ℝ)-1))*(1/(a.2.2.totient:ℝ))
  let M := ∑ m ∈ D, 1/(m.totient:ℝ)
  have vpos (a : Σ _j : ℕ, ℕ × ℕ) (ha : a∈T) : 0≤v a := by
    have h := (Finset.mem_product.mp (Finset.mem_sigma.mp ha).2).1
    have hp := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1).two_le
    have hp' : (2:ℝ)≤a.2.1 := by exact_mod_cast hp
    exact mul_nonneg (one_div_nonneg.mpr (by linarith)) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have witnesses (q : ℕ) (hq : q∈S) : ∃ a∈T, a.2.1*a.2.2=q ∧ denominatorWeight n q≤v a := by
    obtain ⟨hd,hshort,hnsm⟩ := Finset.mem_filter.mp hq
    change ¬∀ p ∈ q.primeFactors, p≤Y at hnsm
    push_neg at hnsm
    obtain ⟨p,hp,hY⟩ := hnsm
    obtain ⟨j,hj⟩ := hshort.2
    obtain ⟨hjrange,dvd⟩ := Finset.mem_filter.mp hj
    have hj' : j ∈ J := by simpa only [J,H,u,Nat.add_comm 1] using hjrange
    have pPrime := Nat.prime_of_mem_primeFactors hp
    have dp := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨m,eq⟩ := dp
    have qpos : 0<q := (Finset.mem_Icc.mp hd).1
    have mpos : 0< m := Nat.pos_of_ne_zero (fun e => (Nat.ne_of_gt qpos) (by simp [eq,e]))
    have mQ : m≤q := Nat.le_of_dvd qpos ⟨p,by simpa only [mul_comm] using eq⟩
    have hpos : 0<(2^j-1:ℕ) := by
      have two : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (Finset.mem_Icc.mp hj').1
      omega
    have pm : p∈Ps j := Finset.mem_filter.mpr ⟨pPrime.mem_primeFactors ((Nat.dvd_of_mem_primeFactors hp).trans dvd) hpos.ne',hY⟩
    refine ⟨⟨j,(p,m)⟩, Finset.mem_sigma.mpr ⟨hj', Finset.mem_product.mpr ⟨pm,Finset.mem_Icc.mpr ⟨mpos,mQ.trans (Finset.mem_Icc.mp hd).2⟩⟩⟩,eq.symm, ?_⟩
    have phip : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr pPrime.pos
    have phim : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mpos
    have phi : (p.totient:ℝ)*(m.totient:ℝ) ≤ (q.totient:ℝ) := by rw [eq]; exact_mod_cast Nat.totient_super_multiplicative p m
    have phiq : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr qpos
    have primeId : (p.totient:ℝ)=(p:ℝ)-1 := by
      rw [Nat.totient_prime pPrime,Nat.cast_sub (by have := pPrime.two_le; omega),Nat.cast_one]
    calc
      _ ≤ 1/(q.totient:ℝ) := div_le_div_of_nonneg_right (min_le_left ..) phiq.le
      _ ≤ 1/((p.totient:ℝ)*(m.totient:ℝ)) := one_div_le_one_div_of_le (mul_pos phip phim) phi
      _ = _ := by dsimp [v]; rw [primeId]; simp only [one_div,mul_inv_rev,mul_comm]
  have eq : (∑ a ∈ T, v a) = M*(∑ j ∈ J, ∑ p ∈ Ps j, 1/((p:ℝ)-1)) := by
    dsimp only [T]
    rw [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [v]
    rw [← Finset.mul_sum,mul_comm]
  have ub := periodPrimeBudget H Y (by dsimp [H,Y,u]; positivity)
  have conv : (H:ℝ)^2/(Y:ℝ) = (u:ℝ)^4/(u:ℝ)^8 := by dsimp [H,Y]; push_cast; ring
  rw [conv] at ub
  apply (chargeWitnesses S T (fun a => a.2.1*a.2.2) (denominatorWeight n) v vpos witnesses).trans
  rw [eq]
  exact mul_le_mul_of_nonneg_left ub (Finset.sum_nonneg fun _ _ => by positivity)

theorem shortPeriodLargePrimeWeight : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_ge (16/ε)
  refine ⟨2^(2^M), ?_⟩
  intro n hn
  let Q := gridQ n
  let u := 1+Nat.log 2 Q
  have hlog : 2^M ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 2^M ≤ Q := by dsimp [Q,gridQ]; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have qpos : 0<Q := lt_of_lt_of_le (by positivity : 0<2^M) hQ
  have hu : M ≤ u := by have h := Nat.le_log_of_pow_le (by decide : 1<2) hQ; dsimp [u]; omega
  have u1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1≤u by dsimp [u]; omega)
  have upos : (0:ℝ)<u := by linarith
  have cap := Nat.lt_pow_succ_log_self (by decide : 1<2) Q
  have cap' : Q < 2^u := by simpa only [u,Nat.add_comm 1] using cap
  have both : Q^2 < 2^(2*u) := by
    rw [mul_comm 2 u,pow_mul]
    exact Nat.pow_lt_pow_left cap' (by decide)
  have hL : Nat.log 2 (Q^2) < 2*u := by
    by_contra! hh
    have power := Nat.pow_le_pow_right (by decide : 0<2) hh
    have b := Nat.pow_log_le_self 2 (by positivity : Q^2≠0)
    omega
  have hR : (Nat.log 2 (Q^2):ℝ)+2 ≤ 4*(u:ℝ) := by exact_mod_cast (show Nat.log 2 (Q^2)+2≤4*u by omega)
  have hb := (reciprocalTotientLogBound (Q^2) (by positivity)).trans (pow_le_pow_left₀ (by positivity) hR 2)
  apply (largePeriodWeightFinite n).trans
  change _ * ((u:ℝ)^4/(u:ℝ)^8) ≤ ε
  apply (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (u:ℝ)^4/(u:ℝ)^8)).trans
  have limit : 16 ≤ ε*(u:ℝ) := by
    have h := (div_le_iff₀ hε).mp (hM.trans (by exact_mod_cast hu : (M:ℝ) ≤ u))
    linarith
  calc
    _ = 16/(u:ℝ)^2 := by field_simp <;> ring
    _ ≤ 16/(u:ℝ) := div_le_div_of_nonneg_left (by norm_num) upos (by nlinarith [sq_nonneg ((u:ℝ)-1)])
    _ ≤ ε := (div_le_iff₀ upos).mpr limit

end
end GoldbachPacket
