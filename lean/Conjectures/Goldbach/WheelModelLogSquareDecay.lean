import Conjectures.Goldbach.PacketLagEnergyIdentity
import Conjectures.Goldbach.PacketShortWheelError
import Conjectures.Goldbach.PacketWheelMinorLeakage
import Conjectures.Goldbach.PacketProgressionLeakage

open scoped BigOperators Interval
open MeasureTheory

namespace GoldbachWheelLongLag

open Conjectures.Goldbach.PacketShortWheelError_aux
open GoldbachPacket

noncomputable section

private abbrev Qgrid : ℕ → ℕ := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridQ
private abbrev minorArcs : ℕ → Set ℝ := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.arcs
private abbrev gridEnvelope : ℕ → ℝ → ℝ := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridEnvelope

private noncomputable def longPart (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  2 * ∑ h ∈ Finset.Icc (length n ^ 2 + 1) n, correlation n h a * cosineMoment n h

private noncomputable def energy (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (resonant n).indicator (fun u => ‖GoldbachBudget.spec n a u‖ ^ 2) t

private lemma maskedIntegrable {f : ℝ → ℝ} {s : Set ℝ}
    (hf : Continuous f) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume (0 : ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (hf.intervalIntegrable 0 1)).indicator hs

private lemma maskedEnergyBound (n : ℕ) (hn : 0 < n) (hq : 30 ≤ Qgrid n) :
    energy n wheel ≤ (3616 * (1860 * Real.pi)) * (n : ℝ) / (Qgrid n : ℝ) := by
  let f : ℝ → ℝ := fun u => ‖GoldbachBudget.spec n wheel u‖ ^ 2
  have hf : Continuous f := by
    unfold f GoldbachBudget.spec GoldbachBudget.phase
    fun_prop
  have hg : Continuous (gridEnvelope n) := by
    change Continuous (Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridEnvelope n)
    unfold Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridEnvelope
      Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridDistance
      Conjectures.Goldbach.PacketWheelMinorLeakage_aux.phase
    fun_prop (disch := intro t; positivity)
  have hminor : MeasurableSet (minorArcs n)ᶜ :=
    (Conjectures.Goldbach.PacketWheelMinorLeakage_aux.measurableArcs n).compl
  have hk : Continuous (fun t => packet (length n) t / (length n : ℝ)) := by
    unfold packet
    fun_prop
  have hres : MeasurableSet (resonant n) :=
    hminor.inter (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ) / 2)) hk).measurableSet
  calc
    energy n wheel ≤ ∫ t in (0 : ℝ)..1, 3616 * (minorArcs n)ᶜ.indicator (gridEnvelope n) t := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (maskedIntegrable hf hres) ((maskedIntegrable hg hminor).const_mul 3616)
      intro t _
      by_cases ht : t ∈ resonant n
      · have hm : t ∈ (minorArcs n)ᶜ := ht.1
        simp only [Set.indicator_of_mem ht, Set.indicator_of_mem hm]
        exact Conjectures.Goldbach.PacketWheelMinorLeakage_aux.wheelEnvelope n t
      · rw [Set.indicator_of_notMem ht]
        apply mul_nonneg (by norm_num)
        by_cases hm : t ∈ (minorArcs n)ᶜ
        · rw [Set.indicator_of_mem hm]
          change 0 ≤ Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridEnvelope n t
          unfold Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridEnvelope
          positivity
        · rw [Set.indicator_of_notMem hm]
    _ ≤ (3616 * (1860 * Real.pi)) * (n : ℝ) / (Qgrid n : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [← mul_div_assoc, ← mul_assoc] using
        mul_le_mul_of_nonneg_left
          (Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridTailQuantitative n hn hq)
          (by norm_num : (0 : ℝ) ≤ 3616)

private lemma gridComparison (n : ℕ) (hn : 64 ≤ n) :
    30 ≤ Qgrid n ∧ (Real.log (n : ℝ)) ^ 2 ≤ 4 * (Qgrid n : ℝ) := by
  let m := Nat.log 2 (n + 2)
  have hm : 6 ≤ m := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : Qgrid n = m ^ 2 := rfl
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnlt : (n : ℝ) < (2 : ℝ) ^ (m + 1) := by
    exact_mod_cast (lt_of_le_of_lt (show n ≤ n + 2 by omega)
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)))
  have hl := Real.log_le_log (zero_lt_one.trans_le hn1) hnlt.le
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hl
  have hl2 : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmr : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : Real.log (n : ℝ) ≤ 2 * (m : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ (m : ℝ) + 1)
    linarith only [hl, hh, hmr]
  rw [hq, Nat.cast_pow]
  constructor
  · nlinarith only [hm]
  · calc
      _ ≤ (2 * (m : ℝ)) ^ 2 := pow_le_pow_left₀ (Real.log_nonneg hn1) hlog 2
      _ = _ := by ring

private lemma shortLogBound (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 4)
    (hm : (1 + Real.log (n : ℝ)) ^ 6 * cosineMoment n 0 ≤ 1) :
    |shortPart n a| ≤ 288 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  let y := Real.log (n : ℝ)
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hy : 0 < y := Real.log_pos hn1
  have hm0 : 0 ≤ cosineMoment n 0 := (abs_nonneg _).trans (cosineMomentBound n 0)
  have hs := shortAtLogScale n (show 1 ≤ n by omega) a (fun k _ => by
    change _ ≤ 4 * (1 + y)
    linarith only [ha k, hy])
  apply hs.trans
  change 288 * (n : ℝ) * (1 + y) ^ 4 * cosineMoment n 0 ≤
    288 * ((n : ℝ) / y ^ 2)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hy 2)).mpr
  calc
    _ ≤ 288 * (n : ℝ) * (1 + y) ^ 4 * cosineMoment n 0 * (1 + y) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ hy.le (by linarith) 2
    _ = 288 * (n : ℝ) * ((1 + y) ^ 6 * cosineMoment n 0) := by ring
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 288 * (n : ℝ))

private lemma longFromEnergy (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ k, |a k| ≤ 4) (hm : (1 + Real.log (n : ℝ)) ^ 6 * cosineMoment n 0 ≤ 1)
    (hE : energy n a ≤ C * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) :
    |longPart n a| ≤ (C + 288) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  have hshort := shortLogBound n hn a ha hm
  have hidentity : energy n a = shortPart n a + longPart n a :=
    Conjectures.Goldbach.PacketLagEnergyIdentity n a
  have hE0 : 0 ≤ energy n a := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t _
    by_cases ht : t ∈ resonant n <;> simp [ht, sq_nonneg]
  have hlong : longPart n a = energy n a - shortPart n a := by linarith only [hidentity]
  rw [hlong]
  calc
    _ ≤ |energy n a| + |shortPart n a| := abs_sub _ _
    _ ≤ C * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) +
        288 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
      rw [abs_of_nonneg hE0]
      exact add_le_add hE hshort
    _ = _ := by ring

private theorem wheelLongLogBound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      |longPart n wheel| ≤ C * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  let D := 3616 * (1860 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := maskLogDecay 6 1 zero_lt_one
  refine ⟨4 * D + 288, by positivity, max N 64, ?_⟩
  intro n hn
  have hn64 : 64 ≤ n := (le_max_right N 64).trans hn
  have hns : N ≤ n := (le_max_left N 64).trans hn
  have hnpos : 0 < n := by omega
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < (Real.log (n : ℝ)) ^ 2 := pow_pos (Real.log_pos hn1) 2
  obtain ⟨hq, hqlog⟩ := gridComparison n hn64
  have hqpos : 0 < (Qgrid n : ℝ) := by exact_mod_cast (show 0 < Qgrid n by omega)
  have hE : energy n wheel ≤ (4 * D) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
    apply (maskedEnergyBound n hnpos hq).trans
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hqpos hlog).mpr
    calc
      _ ≤ (D * (n : ℝ)) * (4 * (Qgrid n : ℝ)) :=
        mul_le_mul_of_nonneg_left hqlog (by positivity)
      _ = _ := by ring
  have hw (k : ℕ) : |wheel k| ≤ 4 := by
    unfold wheel
    split <;> norm_num
  exact longFromEnergy n (by omega) wheel (4 * D) hw
    (by simpa only [zeroMoment] using hN n hns) hE

private def residueWeight (n d r k : ℕ) : ℝ := if k < n ∧ k % d = r then 1 else 0

private lemma residueSum (n d h : ℕ) (hd : 0 < d) (hh : h ≤ n) :
    (∑ r ∈ Finset.range d, correlation n h (residueWeight n d r)) =
      if d ∣ h then (n : ℝ) - h else 0 := by
  unfold correlation
  rw [Finset.sum_comm]
  have hpoint (k : ℕ) :
      (∑ r ∈ Finset.range d, residueWeight n d r k * residueWeight n d r (k + h)) =
        if k + h < n ∧ d ∣ h then (1 : ℝ) else 0 := by
    have hk : k % d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    rw [Finset.sum_eq_single_of_mem (k % d) hk (fun b _ hb => by
      have hkb : k % d ≠ b := Ne.symm hb
      simp [residueWeight, hkb])]
    have hmod : (k + h) % d = k % d ↔ d ∣ h := by
      change Nat.ModEq d (k + h) k ↔ d ∣ h
      calc
        _ ↔ Nat.ModEq d (k + h) (k + 0) := by rw [Nat.add_zero]
        _ ↔ Nat.ModEq d h 0 := (Nat.ModEq.refl k).add_iff_left
        _ ↔ _ := Nat.modEq_zero_iff_dvd
    by_cases ht : k + h < n
    · have ht' : k < n := by omega
      simp [residueWeight, ht, ht', hmod]
    · simp [residueWeight, ht]
  simp only [hpoint]
  by_cases hdv : d ∣ h
  · rw [ite_eq_left hdv, show n + 1 - h = (n - h) + 1 by omega, Finset.sum_range_succ]
    simp only [hdv, and_true, show ¬ n - h + h < n by omega, ite_false, add_zero]
    calc
      _ = ∑ _k ∈ Finset.range (n - h), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ite_eq_left (by have := Finset.mem_range.mp hk; omega)]
      _ = _ := by simp [Nat.cast_sub hh]
  · simp [hdv]

private def rho (h : ℕ) : ℝ :=
  (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) *
    (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))

private lemma rhoResidue (h : ℕ) :
    rho h = 3 * (if 1 ∣ h then 1 else 0) + 3 * (if 3 ∣ h then 1 else 0) +
      (if 5 ∣ h then 1 else 0) + (if 15 ∣ h then 1 else 0) := by
  have hh : 15 ∣ h ↔ 3 ∣ h ∧ 5 ∣ h := by
    constructor
    · intro hd
      exact ⟨dvd_trans (by decide : 3 ∣ 15) hd, dvd_trans (by decide : 5 ∣ 15) hd⟩
    · rintro ⟨h3, h5⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 5) h3 h5
  by_cases h3 : 3 ∣ h <;> by_cases h5 : 5 ∣ h <;> norm_num [rho, hh, h3, h5]

private def progressionLong (n d : ℕ) : ℝ :=
  ∑ r ∈ Finset.range d, longPart n (residueWeight n d r)

private lemma progressionLongMean (n d : ℕ) (hd : 0 < d) :
    progressionLong n d =
      2 * ∑ h ∈ Finset.Icc (length n ^ 2 + 1) n, (if d ∣ h then (n : ℝ) - h else 0) * cosineMoment n h := by
  unfold progressionLong longPart
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_mul, residueSum n d h hd (Finset.mem_Icc.mp hh).2]

private lemma meanIdentity (n : ℕ) :
    (2 * ∑ h ∈ Finset.Icc (length n ^ 2 + 1) n,
      ((n : ℝ) - h) * (15 / 32 : ℝ) * rho h * cosineMoment n h) =
      (15 / 32 : ℝ) *
        (3 * progressionLong n 1 + 3 * progressionLong n 3 + progressionLong n 5 + progressionLong n 15) := by
  simp only [progressionLongMean n 1 (by decide), progressionLongMean n 3 (by decide),
    progressionLongMean n 5 (by decide), progressionLongMean n 15 (by decide)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [rhoResidue]
  by_cases h3 : 3 ∣ h <;> by_cases h5 : 5 ∣ h <;> by_cases h15 : 15 ∣ h <;>
    simp only [one_dvd, ite_true, h3, h5, h15, ite_false] <;> ring

private lemma phaseAdd (x y : ℝ) :
    GoldbachBudget.phase (x + y) = GoldbachBudget.phase x * GoldbachBudget.phase y := by
  unfold GoldbachBudget.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phaseMultiple (x : ℝ) (j : ℕ) :
    GoldbachBudget.phase ((j : ℝ) * x) = GoldbachBudget.phase x ^ j := by
  induction j with
  | zero => simp [GoldbachBudget.phase]
  | succ j ih => rw [Nat.cast_succ, add_mul, one_mul, phaseAdd, ih, pow_succ]

private lemma residueSpecNorm (n d r : ℕ) (hd : 0 < d) (hr : r < d) (hrn : r < n) (t : ℝ) :
    ‖GoldbachBudget.spec n (residueWeight n d r) t‖ =
      ‖Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf d ((n - 1 - r) / d + 1) t‖ := by
  let M := (n - 1 - r) / d + 1
  let F := (Finset.range (n + 1)).filter (fun k => k < n ∧ k % d = r)
  let e := GoldbachBudget.phase
  have hspec : GoldbachBudget.spec n (residueWeight n d r) t =
      ∑ k ∈ F, e ((k : ℝ) * t) := by
    unfold GoldbachBudget.spec F
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k < n ∧ k % d = r <;> simp [residueWeight, hk, e]
  have hsum : (∑ j ∈ Finset.range M, e (((r + d * j : ℕ) : ℝ) * t)) =
      ∑ k ∈ F, e ((k : ℝ) * t) := by
    apply Finset.sum_nbij' (fun j : ℕ => r + d * j) (fun k : ℕ => k / d)
    · intro j hj
      have hj' : j ≤ (n - 1 - r) / d := by
        have := Finset.mem_range.mp hj
        omega
      have hjmul := (Nat.le_div_iff_mul_le hd).mp hj'
      rw [Nat.mul_comm j d] at hjmul
      have hk : r + d * j < n := by omega
      simp only [F, Finset.mem_filter, Finset.mem_range, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hr, and_true]
      exact ⟨by omega, hk⟩
    · intro k hk
      simp only [F, Finset.mem_filter, Finset.mem_range] at hk
      have hkEq : r + d * (k / d) = k := by
        simpa only [hk.2.2] using Nat.mod_add_div k d
      have hkMul : (k / d) * d ≤ n - 1 - r := by
        rw [Nat.mul_comm]
        omega
      have h := (Nat.le_div_iff_mul_le hd).mpr hkMul
      exact Finset.mem_range.mpr (by omega)
    · intro j _
      rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, zero_add]
    · intro k hk
      simp only [F, Finset.mem_filter, Finset.mem_range] at hk
      simpa only [hk.2.2] using Nat.mod_add_div k d
    · intro j _
      rfl
  change _ = ‖Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf d M t‖
  rw [hspec, ← hsum]
  have hphase (j : ℕ) :
      e (((r + d * j : ℕ) : ℝ) * t) * e ((d : ℝ) * t) =
        e ((r : ℝ) * t) * e ((d : ℝ) * t) ^ (j + 1) := by
    dsimp only [e]
    rw [← phaseAdd, ← phaseMultiple, ← phaseAdd]
    push_cast
    congr 1
    ring
  have hshift :
      (∑ j ∈ Finset.range M, e (((r + d * j : ℕ) : ℝ) * t)) * e ((d : ℝ) * t) =
        e ((r : ℝ) * t) * Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf d M t := by
    unfold Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hphase j)
  have hnorm (x : ℝ) : ‖e x‖ = 1 :=
    Conjectures.Goldbach.PacketWheelMinorLeakage_aux.phaseUnit x
  simpa only [norm_mul, hnorm, mul_one, one_mul] using congrArg norm hshift

private lemma residueEnergyBound (n d r : ℕ) (hn : 0 < n) (hq : d ≤ Qgrid n)
    (hr : r < d) (hrn : r < n) :
    energy n (residueWeight n d r) ≤ (2 * Real.pi) * (n : ℝ) / (Qgrid n : ℝ) := by
  let M := (n - 1 - r) / d + 1
  let P := Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf d M
  have hminor : MeasurableSet (minorArcs n)ᶜ :=
    (Conjectures.Goldbach.PacketWheelMinorLeakage_aux.measurableArcs n).compl
  have hk : Continuous (fun t => packet (length n) t / (length n : ℝ)) := by
    unfold packet
    fun_prop
  have hres : MeasurableSet (resonant n) :=
    hminor.inter (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ) / 2)) hk).measurableSet
  have hnorm : ∀ t, ‖GoldbachBudget.spec n (residueWeight n d r) t‖ = ‖P t‖ :=
    residueSpecNorm n d r (by omega) hr hrn
  unfold energy
  simp only [hnorm]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (minorArcs n)ᶜ.indicator (fun u => ‖P u‖ ^ 2) t := by
      have hf : Continuous (fun t => ‖P t‖ ^ 2) :=
        Conjectures.Goldbach.PacketProgressionLeakage_aux.Pf_cont d M
      apply intervalIntegral.integral_mono_on zero_le_one
        (maskedIntegrable hf hres) (maskedIntegrable hf hminor)
      intro t _
      by_cases ht : t ∈ resonant n
      · have hm : t ∈ (minorArcs n)ᶜ := ht.1
        simp [ht, hm]
      · by_cases hm : t ∈ (minorArcs n)ᶜ <;> simp [ht, hm]
    _ ≤ _ := Conjectures.Goldbach.PacketProgressionLeakage_aux.main_bound n d M hn (by omega) hq

private lemma progressionLongLogBound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, 0 < d → d ≤ 30 →
      |progressionLong n d| ≤ (d : ℝ) * (C * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2)) := by
  let D := 2 * Real.pi
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := maskLogDecay 6 1 zero_lt_one
  refine ⟨4 * D + 288, by positivity, max N 64, ?_⟩
  intro n hn d hd hd30
  have hn64 : 64 ≤ n := (le_max_right N 64).trans hn
  have hns : N ≤ n := (le_max_left N 64).trans hn
  have hnpos : 0 < n := by omega
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < (Real.log (n : ℝ)) ^ 2 := pow_pos (Real.log_pos hn1) 2
  obtain ⟨hq, hqlog⟩ := gridComparison n hn64
  have hqpos : 0 < (Qgrid n : ℝ) := by exact_mod_cast (show 0 < Qgrid n by omega)
  have hpoint (r : ℕ) (hr : r ∈ Finset.range d) :
      |longPart n (residueWeight n d r)| ≤
        (4 * D + 288) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
    have hr' : r < d := Finset.mem_range.mp hr
    have hE : energy n (residueWeight n d r) ≤ (4 * D) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
      apply (residueEnergyBound n d r hnpos (hd30.trans hq) hr' (by omega)).trans
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hqpos hlog).mpr
      calc
        _ ≤ (D * (n : ℝ)) * (4 * (Qgrid n : ℝ)) :=
          mul_le_mul_of_nonneg_left hqlog (by positivity)
        _ = _ := by ring
    have hw (k : ℕ) : |residueWeight n d r k| ≤ 4 := by
      unfold residueWeight
      split <;> norm_num
    exact longFromEnergy n (by omega) (residueWeight n d r) (4 * D) hw
      (by simpa only [zeroMoment] using hN n hns) hE
  unfold progressionLong
  calc
    _ ≤ ∑ r ∈ Finset.range d, |longPart n (residueWeight n d r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.range d, (4 * D + 288) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = _ := by simp [nsmul_eq_mul]

private def correction (n : ℕ) : ℝ :=
  2 * ∑ h ∈ Finset.Icc (length n ^ 2 + 1) n,
    (((n : ℝ) - h) * (15 / 32 : ℝ) * rho h - correlation n h wheel) * cosineMoment n h

theorem complete : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    Even n → |correction n| ≤ C * (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨a, ha, N₁, h₁⟩ := wheelLongLogBound
  obtain ⟨b, hb, N₂, h₂⟩ := progressionLongLogBound
  refine ⟨a + 15 * b, by positivity, max 2 (max N₁ N₂), le_max_left .., ?_⟩
  intro n hn _
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  let R := (n : ℝ) / (Real.log (n : ℝ)) ^ 2
  have h1 := abs_le.mp (h₂ n hn₂ 1 (by decide) (by decide))
  have h3 := abs_le.mp (h₂ n hn₂ 3 (by decide) (by decide))
  have h5 := abs_le.mp (h₂ n hn₂ 5 (by decide) (by decide))
  have h15 := abs_le.mp (h₂ n hn₂ 15 (by decide) (by decide))
  have hw := abs_le.mp (h₁ n hn₁)
  have heq : correction n =
      (15 / 32 : ℝ) * (3 * progressionLong n 1 + 3 * progressionLong n 3 +
        progressionLong n 5 + progressionLong n 15) - longPart n wheel := by
    rw [← meanIdentity n]
    simp only [correction, sub_mul, Finset.sum_sub_distrib, mul_sub, longPart]
  rw [heq, mul_div_assoc, abs_le]
  change -((a + 15 * b) * R) ≤ _ ∧ _ ≤ (a + 15 * b) * R
  norm_num at h1 h3 h5 h15
  constructor <;> linarith only [h1.1, h1.2, h3.1, h3.2, h5.1, h5.2, h15.1, h15.2, hw.1, hw.2]

end
end GoldbachWheelLongLag

theorem Conjectures.Goldbach.WheelModelLogSquareDecay : (by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  exact ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |Q n| ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2) :=
  GoldbachWheelLongLag.complete
