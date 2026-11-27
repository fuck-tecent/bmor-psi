import Mathlib

import PEqualNP.Outside.L_twin_primes_unconditional_short

import Conjectures.Goldbach.VaughanHighExactSplit
import Conjectures.Goldbach.VaughanCutoffIdentity
import Conjectures.Goldbach.AnalyticLargeSieve
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4

open Finset Filter

def bpWin (X : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)

def bpPrimes (X : ℕ) : Finset ℕ := (bpWin X).filter Nat.Prime

noncomputable def bpC (d : ℕ) : ℝ := -(ArithmeticFunction.moebius d : ℝ) * Real.log d

noncomputable def bpA (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def bpD (X : ℕ) : ℕ := ⌊Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ)⌋₊

def bpOdd (y : ℕ) : Finset ℕ := (Finset.Icc 1 y).filter (fun d => d % 2 = 1)

noncomputable def bpS (X : ℕ) : Finset ℕ := (bpOdd (bpD X)).filter (fun d => bpA X < d)

noncomputable def bpP (X d : ℕ) : ℝ :=
  ∑ p ∈ bpPrimes X with (p + 2) % d = 0, Real.log (p : ℝ)

noncomputable def bpHard (y : ℕ) : ℝ :=
  ∑ d ∈ bpOdd y, bpC d / (Nat.totient d : ℝ)

noncomputable def bpMain (X : ℕ) : ℝ :=
  ∑ d ∈ bpS X, bpC d / (50 * (Nat.totient d : ℝ))

noncomputable def bpErr (X : ℕ) : ℝ :=
  (∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) / (X : ℝ)

noncomputable def bpCut (X : ℕ) : ℕ := ⌊Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (13 : ℕ)⌋₊

noncomputable def bpLow (X : ℕ) : Finset ℕ := (bpS X).filter (fun d => d ≤ bpCut X)

noncomputable def bpHigh (X : ℕ) : Finset ℕ := (bpS X).filter (fun d => ¬ d ≤ bpCut X)

theorem bpA_atTop : Tendsto bpA atTop atTop := by
  unfold bpA
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop)

theorem bp_cut_eventually : ∀ᶠ X : ℕ in atTop,
    (X : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ) := by
  have hlo : (fun x : ℝ => Real.log x ^ (5 : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 / 6 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (5 : ℝ) (by norm_num)
  have hcomp : (fun X : ℕ => Real.log (2 + (X : ℝ)) ^ (5 : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => (2 + (X : ℝ)) ^ (1 / 6 : ℝ)) :=
    hlo.comp_tendsto (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
  have hbound : ∀ᶠ X : ℕ in atTop,
      Real.log (2 + (X : ℝ)) ^ (5 : ℝ) ≤ (1 / 2 : ℝ) * (2 + (X : ℝ)) ^ (1 / 6 : ℝ) := by
    filter_upwards [hcomp.bound (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop (2 : ℕ)] with X hX _
    have h1 : ‖Real.log (2 + (X : ℝ)) ^ (5 : ℝ)‖ ≤ (1 / 2 : ℝ) * ‖(2 + (X : ℝ)) ^ (1 / 6 : ℝ)‖ := hX
    have hlog0 : 0 ≤ Real.log (2 + (X : ℝ)) ^ (5 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) 5
    have hrp0 : 0 ≤ (2 + (X : ℝ)) ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hrp0] at h1
    exact h1
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with X hX hX2
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX2R : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hlogpos : 0 < Real.log (2 + (X : ℝ)) := Real.log_pos (by linarith)
  have hle : 2 + (X : ℝ) ≤ 2 * (X : ℝ) := by linarith
  have hrp : (2 + (X : ℝ)) ^ (1 / 6 : ℝ) ≤ (2 * (X : ℝ)) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hle (by norm_num)
  have htwo : (2 * (X : ℝ)) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (1 / 6 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ) :=
    Real.mul_rpow (by norm_num) hXR.le
  have h2le : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 6 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  have hL5 : Real.log (2 + (X : ℝ)) ^ (5 : ℕ) ≤ (X : ℝ) ^ (1 / 6 : ℝ) := by
    have hcast : Real.log (2 + (X : ℝ)) ^ (5 : ℕ) = Real.log (2 + (X : ℝ)) ^ (5 : ℝ) :=
      (Real.rpow_natCast _ 5).symm
    rw [hcast]
    calc Real.log (2 + (X : ℝ)) ^ (5 : ℝ) ≤ (1 / 2 : ℝ) * (2 + (X : ℝ)) ^ (1 / 6 : ℝ) := hX
      _ ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ (1 / 6 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ)) := by
          rw [← htwo]; gcongr
      _ ≤ (1 / 2 : ℝ) * (2 * (X : ℝ) ^ (1 / 6 : ℝ)) := by gcongr
      _ = (X : ℝ) ^ (1 / 6 : ℝ) := by ring
  have hL5pos : 0 < Real.log (2 + (X : ℝ)) ^ (5 : ℕ) := by positivity
  have hmul : (X : ℝ) ^ (1 / 3 : ℝ) * Real.log (2 + (X : ℝ)) ^ (5 : ℕ) ≤
      (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ) :=
    mul_le_mul_of_nonneg_left hL5 (Real.rpow_nonneg hXR.le _)
  have hsum : (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt (X : ℝ) := by
    rw [← Real.rpow_add hXR, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  rw [le_div_iff₀ hL5pos]
  linarith

theorem bpD_atTop : Tendsto bpD atTop atTop := by
  have hlower : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hmono : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ))
      atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlower
    filter_upwards [bp_cut_eventually] with X hX
    exact hX
  unfold bpD
  exact tendsto_nat_floor_atTop.comp hmono

theorem bpA_le_bpD : ∀ᶠ X : ℕ in atTop, bpA X ≤ bpD X := by
  filter_upwards [bp_cut_eventually] with X hX
  have hfloor : (bpA X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  exact Nat.le_floor (hfloor.trans hX)

theorem bpS_eq (X : ℕ) :
    bpS X = ((Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d)).filter (fun d => d % 2 = 1) := by
  ext d
  simp only [bpS, bpOdd, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem strip_eq_main_add_err {X : ℕ} (hX : 3 ≤ X) :
    (∑ p ∈ bpPrimes X, Real.log (p : ℝ) *
        (((p + 2).divisors.filter (fun d => bpA X < d ∧ d ≤ bpD X)).sum bpC)) / (X : ℝ)
      = bpMain X + bpErr X := by
  classical
  have hX0 : 0 < X := by omega
  have hinner : ∀ p ∈ bpPrimes X,
      (p + 2).divisors.filter (fun d => bpA X < d ∧ d ≤ bpD X) =
        ((Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d)).filter (fun d => d ∣ p + 2) := by
    intro p _
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdiv, _⟩, hA, hD⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdiv (by omega), hD⟩, hA⟩, hdiv⟩
    · rintro ⟨⟨⟨_, hD⟩, hA⟩, hdiv⟩
      exact ⟨⟨hdiv, by omega⟩, hA, hD⟩
  have hswap : (∑ p ∈ bpPrimes X, Real.log (p : ℝ) *
        (((p + 2).divisors.filter (fun d => bpA X < d ∧ d ≤ bpD X)).sum bpC)) =
      ∑ d ∈ (Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d),
        bpC d * ∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ) := by
    have hterm : ∀ p ∈ bpPrimes X, Real.log (p : ℝ) *
        (((p + 2).divisors.filter (fun d => bpA X < d ∧ d ≤ bpD X)).sum bpC) =
        ∑ d ∈ (Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d),
          (if d ∣ p + 2 then Real.log (p : ℝ) * bpC d else 0) := by
      intro p hp
      rw [hinner p hp, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    have hgoal : (∑ p ∈ bpPrimes X, (if d ∣ p + 2 then Real.log (p : ℝ) * bpC d else 0)) =
        bpC d * ∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : d ∣ p + 2 <;> simp [h, mul_comm]
    exact hgoal
  have hpar : ∀ d ∈ (Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d), d % 2 = 0 →
      (∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ)) = 0 := by
    intro d _ hd
    rw [Finset.sum_eq_zero]
    intro p hp
    have hpd : d ∣ p + 2 := (Finset.mem_filter.mp hp).2
    have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
    have hpr : Nat.Prime p := hp'.2
    have hpX : X < p := (Finset.mem_filter.mp hp'.1).2.1
    have hpodd : Odd p := Nat.Prime.odd_of_ne_two hpr (by omega)
    have hodd : Odd (p + 2) := hpodd.add_even (by decide)
    have hd2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero hd
    exfalso
    have hmod0 : (p + 2) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_trans hd2 hpd)
    have hmod1 : (p + 2) % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hP : ∀ d ∈ bpS X,
      (∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ)) = bpP X d := by
    intro d _
    unfold bpP
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : d ∣ p + 2
    · rw [if_pos h, if_pos (Nat.dvd_iff_mod_eq_zero.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (Nat.dvd_iff_mod_eq_zero.mpr h'))]
  have hdrop : (∑ d ∈ (Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d),
        bpC d * ∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ)) =
      ∑ d ∈ bpS X, bpC d * bpP X d := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d))
      (p := fun d => d % 2 = 1)
      (f := fun d => bpC d * ∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ))]
    have hz : (∑ d ∈ ((Finset.Icc 1 (bpD X)).filter (fun d => bpA X < d)).filter
        (fun d => ¬ d % 2 = 1),
        bpC d * ∑ p ∈ bpPrimes X with d ∣ p + 2, Real.log (p : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdm := Finset.mem_filter.mp hd
      have hev : d % 2 = 0 := by omega
      rw [hpar d hdm.1 hev, mul_zero]
    rw [hz, add_zero, bpS_eq X]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hP d ((bpS_eq X).symm ▸ hd)]
  have hsplit : (∑ d ∈ bpS X, bpC d * bpP X d) =
      (∑ d ∈ bpS X, bpC d * ((X : ℝ) / (50 * (Nat.totient d : ℝ)))) +
      (∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
    have hφ : (Nat.totient d : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hd1).ne'
    field_simp
    ring
  have hmain : (∑ d ∈ bpS X, bpC d * ((X : ℝ) / (50 * (Nat.totient d : ℝ)))) / (X : ℝ) =
      bpMain X := by
    unfold bpMain
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
    have hφ : (Nat.totient d : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hd1).ne'
    have hX0R : (X : ℝ) ≠ 0 := by exact_mod_cast hX0.ne'
    field_simp
  calc (∑ p ∈ bpPrimes X, Real.log (p : ℝ) *
        (((p + 2).divisors.filter (fun d => bpA X < d ∧ d ≤ bpD X)).sum bpC)) / (X : ℝ)
      = (∑ d ∈ bpS X, bpC d * bpP X d) / (X : ℝ) := by rw [hswap, hdrop]
    _ = ((∑ d ∈ bpS X, bpC d * ((X : ℝ) / (50 * (Nat.totient d : ℝ)))) +
        (∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))))) / (X : ℝ) := by
      rw [hsplit]
    _ = bpMain X + bpErr X := by
      unfold bpErr
      rw [add_div, hmain]

theorem bpMain_eq_hard {X : ℕ} (hX : bpA X ≤ bpD X) :
    bpMain X = (bpHard (bpD X) - bpHard (bpA X)) / 50 := by
  have hsub : bpOdd (bpA X) ⊆ bpOdd (bpD X) := by
    apply Finset.filter_subset_filter
    exact Finset.Icc_subset_Icc_right hX
  have hsdiff : bpOdd (bpD X) \ bpOdd (bpA X) = bpS X := by
    ext d
    simp only [bpS, bpOdd, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsum : (∑ d ∈ bpOdd (bpD X), bpC d / (Nat.totient d : ℝ)) =
      (∑ d ∈ bpOdd (bpA X), bpC d / (Nat.totient d : ℝ)) +
      (∑ d ∈ bpS X, bpC d / (Nat.totient d : ℝ)) := by
    rw [← Finset.sum_sdiff hsub, hsdiff, add_comm]
  have hmain : bpMain X = (∑ d ∈ bpS X, bpC d / (Nat.totient d : ℝ)) / 50 := by
    unfold bpMain
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_comm (50 : ℝ), div_div]
  unfold bpHard
  rw [hmain, hsum]
  ring

theorem bpErr_split (X : ℕ) :
    (∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) =
      (∑ d ∈ bpLow X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) +
      (∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) := by
  unfold bpLow bpHigh
  exact (Finset.sum_filter_add_sum_filter_not (s := bpS X) (p := fun d => d ≤ bpCut X)
    (f := fun d => bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))))).symm

theorem hard_limit_exists : ∃ L : ℝ, Tendsto bpHard atTop (nhds L) := by
  obtain ⟨c, K, hK, hrate⟩ := TP35Rate.mertens_log_rate
  have hH : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      TwinShortGlue.B k * TwinShortGlue.C (n / k)) atTop (nhds 0) := by
    apply TP35Hyperbola.hyperbola_log_rate TwinShortGlue.B TwinShortGlue.C
      TwinShortGlue.B_bounded TwinShortGlue.first_moment _ c K hK.le hrate
    intro F L hF
    apply hc_moebius_aux_hyperbola TwinShortGlue.B F TwinShortGlue.B_bounded
      TwinShortGlue.first_moment 0 L
    simpa only [sub_zero] using hF
  exact ⟨2 * TwinShortGlue.twinProduct, TwinShortGlue.hard_limit hH⟩

theorem low_part_error_aux_bv :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x ^ (1/2:ℝ) * (Real.log x) ^ (-((3:ℝ)+10))⌋₊,
        (OAI.LargePrimeGaps.endpointError x q : ℝ)) ≤ M * x * (Real.log x) ^ (-(3:ℝ)) := by
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ :=
    OAI.LargePrimeGaps.siegelWalfisz (2*3+14) (3+11) (by linarith) (by linarith)
  refine ⟨(8*M+192028)*(2:ℝ)^(3:ℝ), by positivity, ?_⟩
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have he : ∀ᶠ x : ℝ in atTop,
      (∑ q∈Finset.Icc 1 ⌊x^(1/2:ℝ)*(Real.log x)^(-((3:ℝ)+10))⌋₊,
        (OAI.LargePrimeGaps.endpointError x q:ℝ)) ≤
        ((8*M+192028)*(2:ℝ)^(3:ℝ))*x*(Real.log x)^(-(3:ℝ)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),
      tendsto_nat_floor_atTop.eventually (eventually_ge_atTop (16:ℕ)),
      (Real.tendsto_log_atTop.comp hf).eventually_ge_atTop 2,
      hf.eventually_ge_atTop x₀,
      hf.eventually (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (3+10)
        (by norm_num : (0:ℝ)<1/32))]
      with x hx hX hL hxsw hp
    apply OAI.LargePrimeGaps.endpoint_errors_real_log_bound (by norm_num) hM.le hx hX hL hp
    intro d hd hdL χ hχ
    convert hSW (⌊x⌋₊:ℝ) hxsw d hd hdL χ hχ using 1
    congr 1
    congr 1
    ring
  obtain ⟨z, hz⟩ := eventually_atTop.mp he
  refine ⟨max z 2, by linarith [le_max_right z (2:ℝ)], ?_⟩
  intro x hx
  exact hz x ((le_max_left z (2:ℝ)).trans hx)

theorem low_part_error_aux_dvd_shift {d n : ℕ} (hd : 1 ≤ d) :
    d ∣ n + 2 ↔ n % d = TwinShortAP.negTwo d % d := by
  have h2 : 2*d - 2 + 2 = 2*d := by omega
  have h0 : 2*d ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left d 2)
  constructor
  · intro h
    have h1 : n+2 ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : n+2 ≡ 2*d-2+2 [MOD d] := by rw [h2]; exact h1.trans h0.symm
    exact Nat.ModEq.add_right_cancel' 2 h3
  · intro h
    have h3 : n+2 ≡ 2*d-2+2 [MOD d] := Nat.ModEq.add_right 2 h
    rw [h2] at h3
    exact Nat.modEq_zero_iff_dvd.mp (h3.trans h0)

theorem low_part_error_aux_negTwo_coprime {d : ℕ} (hd : Odd d) :
    (TwinShortAP.negTwo d % d).Coprime d := by
  have h1 := hd.pos
  have h2 : 2*d-2+2=2*d := by omega
  set g := (2*d-2).gcd d with hg
  have hg1 : g ∣ d := Nat.gcd_dvd_right _ _
  have hg2 : g ∣ 2*d-2 := Nat.gcd_dvd_left _ _
  have hg3 : g ∣ 2*d := dvd_mul_of_dvd_right hg1 2
  have hg4 : g ∣ 2 := by simpa only [show 2*d-(2*d-2)=2 by omega] using Nat.dvd_sub hg3 hg2
  have hc : g=1 := ((Nat.dvd_prime Nat.prime_two).mp hg4).resolve_right
    (fun he => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr (he ▸ hg1)))
  change (TwinShortAP.negTwo d % d).gcd d = 1
  rwa [← Nat.gcd_rec, Nat.gcd_comm]

theorem low_part_error_aux_winTheta (X d : ℕ) (hd : 1 ≤ d) :
    TwinShortAP.winTheta X d =
      ∑ p ∈ (TwinShortAP.ps X).filter (fun p => d ∣ p + 2), Real.log (p : ℝ) := by
  unfold TwinShortAP.winTheta GoldbachRoughFifth.bvAPMass GoldbachRoughFifth.bvPrimeWeight
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [TwinShortAP.ps, TwinShortAP.win, TwinShortAP.upper, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Ioc, low_part_error_aux_dvd_shift hd]
  grind

theorem low_part_error_aux_bpP (X d : ℕ) (hd : 1 ≤ d) :
    bpP X d = TwinShortAP.winTheta X d := by
  have hps : bpPrimes X = TwinShortAP.ps X := rfl
  unfold bpP
  rw [low_part_error_aux_winTheta X d hd]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [hps, Finset.mem_filter, Nat.dvd_iff_mod_eq_zero]

theorem low_part_error_aux_per_modulus {X d : ℕ} (hX : 2 ≤ X) (hd : 1 ≤ d) :
    |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| ≤
      |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 (TwinShortAP.upper X) d
          (TwinShortAP.negTwo d) - (TwinShortAP.upper X : ℝ) / (Nat.totient d : ℝ)| +
      |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 X d
          (TwinShortAP.negTwo d) - (X : ℝ) / (Nat.totient d : ℝ)| +
      (Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1 := by
  rw [low_part_error_aux_bpP X d hd]
  have hXU : X ≤ TwinShortAP.upper X := by unfold TwinShortAP.upper; omega
  have h1n : 50 * TwinShortAP.upper X ≤ 51*X := by unfold TwinShortAP.upper; omega
  have h2n : 51*X ≤ 50 * TwinShortAP.upper X + 50 := by unfold TwinShortAP.upper; omega
  have hr : |((TwinShortAP.upper X : ℝ) - X) - (X : ℝ)/50| ≤ 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : (51:ℝ)*(X:ℝ) ≤ 50 * (TwinShortAP.upper X : ℝ) + 50 := by exact_mod_cast h2n
      linarith
    · have : (50:ℝ)*(TwinShortAP.upper X : ℝ) ≤ 51*(X:ℝ) := by exact_mod_cast h1n
      linarith
  have hφ : (1:ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφpos : (0:ℝ) < (Nat.totient d : ℝ) := by linarith
  have hmove : |((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ) -
      ((X : ℝ)/50)/(Nat.totient d : ℝ)| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hφpos]
    exact (div_le_one hφpos).mpr (hr.trans hφ)
  have he := GoldbachRoughFifth.bvAPMass_prime_error_from_prefix hXU (le_refl (TwinShortAP.upper X)) d
    (TwinShortAP.negTwo d) (fun t => (t : ℝ)/(Nat.totient d : ℝ))
  rw [← sub_div] at he
  have hwin : TwinShortAP.winTheta X d =
      GoldbachRoughFifth.bvAPMass GoldbachRoughFifth.bvPrimeWeight X (TwinShortAP.upper X) d
        (TwinShortAP.negTwo d) := rfl
  have h50 : (X : ℝ) / (50 * (Nat.totient d : ℝ)) = ((X : ℝ)/50)/(Nat.totient d : ℝ) := by
    field_simp
  calc |TwinShortAP.winTheta X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|
      = |TwinShortAP.winTheta X d - ((X : ℝ)/50)/(Nat.totient d : ℝ)| := by rw [h50]
    _ ≤ |TwinShortAP.winTheta X d - ((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ)| +
        |((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ) -
          ((X : ℝ)/50)/(Nat.totient d : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by rw [hwin]; exact add_le_add he hmove

theorem low_part_error_aux_class_le (Y d : ℕ) (hd : Odd d) :
    |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 Y d (TwinShortAP.negTwo d) -
        (Y : ℝ) / (Nat.totient d : ℝ)| ≤
      (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ) :=
  OAI.LargePrimeGaps.endpointClassError_le Y (Nat.mod_lt _ hd.pos)
    (low_part_error_aux_negTwo_coprime hd)

theorem low_part_error_aux_coeff {X d : ℕ} (hd1 : 1 ≤ d) (hdX : (d : ℝ) ≤ X) :
    |bpC d| ≤ Real.log (X : ℝ) := by
  have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [bpC, abs_mul, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg d)]
  calc _ ≤ 1 * Real.log (d : ℝ) :=
        mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg d)
    _ = Real.log (d : ℝ) := one_mul _
    _ ≤ Real.log (X : ℝ) := Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) hdX

theorem low_part_error_aux_eventually :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      (∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
        C * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := by
  obtain ⟨M, hM, x₀, hx₀, hBV⟩ := low_part_error_aux_bv
  have hbundle : ∀ᶠ X : ℕ in atTop,
      (1000000 : ℕ) ≤ X ∧ 1000 ≤ Real.log (2 + (X : ℝ)) ∧ x₀ ≤ (X : ℝ) := by
    filter_upwards [eventually_ge_atTop 1000000,
      (Real.tendsto_log_atTop.comp
        (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1000,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop x₀] with X h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨12 * M + 40, by positivity, ?_⟩
  filter_upwards [hbundle] with X hXb
  obtain ⟨hXbig, hL1000, hX0⟩ := hXb
  have hXbig' : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXbig
  have hX2 : 2 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hLpos : 0 < Real.log (2 + (X : ℝ)) := Real.log_pos (by linarith)
  have hLxpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hLx1 : 1 ≤ Real.log (X : ℝ) := by
    have he : Real.exp 1 ≤ (X : ℝ) := by have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  have hLxle : Real.log (X : ℝ) ≤ Real.log (2 + (X : ℝ)) := Real.log_le_log hXpos (by linarith)
  have hLle : Real.log (2 + (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
    have h1 : Real.log (2 + (X : ℝ)) ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hXpos.ne'] at h1
    have h2 := Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ X)
    linarith

  have huX : (X : ℝ) ≤ (TwinShortAP.upper X : ℝ) := by
    have : X ≤ TwinShortAP.upper X := by unfold TwinShortAP.upper; omega
    exact_mod_cast this
  have hu2X : (TwinShortAP.upper X : ℝ) ≤ 2 * (X : ℝ) := by
    have : TwinShortAP.upper X ≤ 2 * X := by unfold TwinShortAP.upper; omega
    exact_mod_cast this
  have hu1 : (1 : ℝ) ≤ (TwinShortAP.upper X : ℝ) := by linarith
  have hupos : (0 : ℝ) < (TwinShortAP.upper X : ℝ) := by linarith
  have hulogpos : 0 < Real.log (TwinShortAP.upper X : ℝ) := Real.log_pos (by linarith)
  have hu50 : (50 : ℝ) * (TwinShortAP.upper X : ℝ) ≤ 51 * (X : ℝ) := by
    have : 50 * TwinShortAP.upper X ≤ 51 * X := by unfold TwinShortAP.upper; omega
    exact_mod_cast this
  have hu50' : (51 : ℝ) * (X : ℝ) ≤ 50 * (TwinShortAP.upper X : ℝ) + 50 := by
    have : 51 * X ≤ 50 * TwinShortAP.upper X + 50 := by unfold TwinShortAP.upper; omega
    exact_mod_cast this

  have hcut : (bpCut X : ℝ) ≤ Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 13 := by
    unfold bpCut
    exact Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hLpos.le 13))
  have hcutLx : (bpCut X : ℝ) ≤ Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13 := by
    have h := div_le_div_of_nonneg_left (Real.sqrt_nonneg (X : ℝ)) (pow_pos hLxpos 13)
      (pow_le_pow_left₀ hLxpos.le hLxle 13)
    exact hcut.trans h
  have hsqX : (X : ℝ) ≤ (X : ℝ) ^ 2 := by
    calc (X : ℝ) = (X : ℝ) * 1 := by ring
      _ ≤ (X : ℝ) * (X : ℝ) := mul_le_mul_of_nonneg_left hX1 hXpos.le
      _ = (X : ℝ) ^ 2 := by ring
  have hcutXle : (bpCut X : ℝ) ≤ (X : ℝ) := by
    have h1 : (bpCut X : ℝ) ≤ Real.sqrt (X : ℝ) :=
      hcutLx.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hLx1))
    have h2 : Real.sqrt (X : ℝ) ≤ (X : ℝ) := Real.sqrt_le_iff.mpr ⟨hXpos.le, hsqX⟩
    exact h1.trans h2

  have hlogu_ge : Real.log (X : ℝ) ≤ Real.log (TwinShortAP.upper X : ℝ) :=
    Real.log_le_log hXpos huX
  have hlogu_le : Real.log (TwinShortAP.upper X : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    have h1 : Real.log (TwinShortAP.upper X : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_le_log hupos hu2X
    rw [Real.log_mul (by norm_num) hXpos.ne'] at h1
    have h2 := Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ X)
    linarith
  have hdiff : Real.log (TwinShortAP.upper X : ℝ) - Real.log (2 + (X : ℝ)) ≤ 1 / 50 := by
    have h1 : Real.log (TwinShortAP.upper X : ℝ) - Real.log (2 + (X : ℝ)) =
        Real.log ((TwinShortAP.upper X : ℝ) / (2 + (X : ℝ))) := by
      rw [Real.log_div hupos.ne' (by linarith)]
    have h2 : (TwinShortAP.upper X : ℝ) / (2 + (X : ℝ)) ≤ 51 / 50 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 + X)]
      linarith
    have h3 := Real.log_le_log (div_pos hupos (by linarith)) h2
    have h4 : Real.log (51 / 50 : ℝ) ≤ 1 / 50 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51 / 50)
      linarith
    linarith
  have hlogpow : (Real.log (TwinShortAP.upper X : ℝ)) ^ 13 ≤
      (1 + 1 / 1000) * Real.log (2 + (X : ℝ)) ^ 13 := by
    have h1 : Real.log (TwinShortAP.upper X : ℝ) ≤
        Real.log (2 + (X : ℝ)) * (1 + 1 / 50000) := by linarith
    have h2 : (Real.log (TwinShortAP.upper X : ℝ)) ^ 13 ≤
        (Real.log (2 + (X : ℝ)) * (1 + 1 / 50000)) ^ 13 :=
      pow_le_pow_left₀ (Real.log_nonneg hu1) h1 13
    have h3 : (Real.log (2 + (X : ℝ)) * (1 + 1 / 50000)) ^ 13 =
        Real.log (2 + (X : ℝ)) ^ 13 * (1 + 1 / 50000) ^ 13 := mul_pow _ _ 13
    have h4 : (1 + 1 / 50000 : ℝ) ^ 13 ≤ 1 + 1 / 1000 := by norm_num
    have h5 : Real.log (2 + (X : ℝ)) ^ 13 * (1 + 1 / 50000) ^ 13 ≤
        Real.log (2 + (X : ℝ)) ^ 13 * (1 + 1 / 1000) :=
      mul_le_mul_of_nonneg_left h4 (pow_nonneg hLpos.le 13)
    linarith
  have hsq : ((1 + 1 / 1000 : ℝ) * Real.sqrt (X : ℝ)) ^ 2 ≤ (TwinShortAP.upper X : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hXpos.le]
    have h1 : (1 + 1 / 1000 : ℝ) ^ 2 ≤ 1 + 1 / 101 := by norm_num
    have h2 : (1 + 1 / 101 : ℝ) * (X : ℝ) ≤ (TwinShortAP.upper X : ℝ) := by linarith
    have h3 : (1 + 1 / 1000 : ℝ) ^ 2 * (X : ℝ) ≤ (1 + 1 / 101 : ℝ) * (X : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hXpos.le
    linarith
  have hsqrtu : (1 + 1 / 1000 : ℝ) * Real.sqrt (X : ℝ) ≤
      Real.sqrt (TwinShortAP.upper X : ℝ) :=
    (Real.le_sqrt (by positivity) hupos.le).mpr hsq
  have hcmp : Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 13 ≤
      Real.sqrt (TwinShortAP.upper X : ℝ) / (Real.log (TwinShortAP.upper X : ℝ)) ^ 13 := by
    rw [div_le_div_iff₀ (pow_pos hLpos 13) (pow_pos hulogpos 13)]
    calc Real.sqrt (X : ℝ) * (Real.log (TwinShortAP.upper X : ℝ)) ^ 13
        ≤ Real.sqrt (X : ℝ) * ((1 + 1 / 1000) * Real.log (2 + (X : ℝ)) ^ 13) :=
          mul_le_mul_of_nonneg_left hlogpow (Real.sqrt_nonneg _)
      _ = ((1 + 1 / 1000) * Real.sqrt (X : ℝ)) * Real.log (2 + (X : ℝ)) ^ 13 := by ring
      _ ≤ Real.sqrt (TwinShortAP.upper X : ℝ) * Real.log (2 + (X : ℝ)) ^ 13 :=
          mul_le_mul_of_nonneg_right hsqrtu (pow_nonneg hLpos.le 13)

  have hrwX : (X : ℝ) ^ (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (-((3 : ℝ) + 10)) =
      Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13 := by
    have h13 : (-((3 : ℝ) + 10)) = (-((13 : ℕ) : ℝ)) := by norm_num
    rw [h13, Real.rpow_neg (Real.log_nonneg hX1), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    ring
  have hrwU : (TwinShortAP.upper X : ℝ) ^ (1 / 2 : ℝ) *
      (Real.log (TwinShortAP.upper X : ℝ)) ^ (-((3 : ℝ) + 10)) =
      Real.sqrt (TwinShortAP.upper X : ℝ) / (Real.log (TwinShortAP.upper X : ℝ)) ^ 13 := by
    have h13 : (-((3 : ℝ) + 10)) = (-((13 : ℕ) : ℝ)) := by norm_num
    rw [h13, Real.rpow_neg (Real.log_nonneg hu1), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    ring
  have hcutX : bpCut X ≤ ⌊(X : ℝ) ^ (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (-((3 : ℝ) + 10))⌋₊ := by
    apply Nat.le_floor
    rw [hrwX]
    exact hcutLx
  have hcutU : bpCut X ≤ ⌊(TwinShortAP.upper X : ℝ) ^ (1 / 2 : ℝ) *
      (Real.log (TwinShortAP.upper X : ℝ)) ^ (-((3 : ℝ) + 10))⌋₊ := by
    apply Nat.le_floor
    rw [hrwU]
    exact hcut.trans hcmp
  have h3X : (Real.log (X : ℝ)) ^ (-(3 : ℝ)) = ((Real.log (X : ℝ)) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (Real.log_nonneg hX1)]
    congr 1
    exact Real.rpow_natCast _ 3
  have h3U : (Real.log (TwinShortAP.upper X : ℝ)) ^ (-(3 : ℝ)) =
      ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (Real.log_nonneg hu1)]
    congr 1
    exact Real.rpow_natCast _ 3
  have hsumX : (∑ d ∈ Finset.Icc 1 (bpCut X),
      (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) ≤
      M * (X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹ := by
    have h1 : (∑ d ∈ Finset.Icc 1 (bpCut X),
        (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ) *
          (Real.log (X : ℝ)) ^ (-((3 : ℝ) + 10))⌋₊,
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hcutX)
        (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg)
    have h2 := hBV (X : ℝ) hX0
    rw [h3X] at h2
    exact h1.trans h2
  have hsumU : (∑ d ∈ Finset.Icc 1 (bpCut X),
      (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) ≤
      M * (TwinShortAP.upper X : ℝ) * ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹ := by
    have h1 : (∑ d ∈ Finset.Icc 1 (bpCut X),
        (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 ⌊(TwinShortAP.upper X : ℝ) ^ (1 / 2 : ℝ) *
          (Real.log (TwinShortAP.upper X : ℝ)) ^ (-((3 : ℝ) + 10))⌋₊,
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hcutU)
        (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg)
    have h2 := hBV (TwinShortAP.upper X : ℝ) (by linarith)
    rw [h3U] at h2
    exact h1.trans h2

  have hE : (∑ d ∈ bpLow X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      (∑ d ∈ Finset.Icc 1 (bpCut X),
        (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
      (∑ d ∈ Finset.Icc 1 (bpCut X),
        (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
      (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
    have hsub : bpLow X ⊆ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1) := by
      intro d hd
      have hdS : d ∈ bpS X := (Finset.mem_filter.mp hd).1
      have hdcut : d ≤ bpCut X := (Finset.mem_filter.mp hd).2
      have hdodd : d ∈ bpOdd (bpD X) := (Finset.mem_filter.mp hdS).1
      have hdI : d ∈ Finset.Icc 1 (bpD X) := (Finset.mem_filter.mp hdodd).1
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
      have hdm : d % 2 = 1 := (Finset.mem_filter.mp hdodd).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdcut⟩, hdm⟩
    have hper : ∀ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
        |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| ≤
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
      intro d hd
      have hdI : d ∈ Finset.Icc 1 (bpCut X) := (Finset.mem_filter.mp hd).1
      have hdm : d % 2 = 1 := (Finset.mem_filter.mp hd).2
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
      have hodd : Odd d := Nat.odd_iff.mpr hdm
      have h1 := low_part_error_aux_per_modulus hX2 hd1
      have h2 := low_part_error_aux_class_le (TwinShortAP.upper X) d hodd
      have h3 := low_part_error_aux_class_le X d hodd
      linarith
    have hA : (∑ d ∈ bpLow X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
        ∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    have hB : (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
        ∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          ((OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
           (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
           ((Chebyshev.psi (TwinShortAP.upper X) -
             Chebyshev.theta (TwinShortAP.upper X)) + 1)) :=
      Finset.sum_le_sum (fun d hd => hper d hd)
    have hC : (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          ((OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
           (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
           ((Chebyshev.psi (TwinShortAP.upper X) -
             Chebyshev.theta (TwinShortAP.upper X)) + 1))) =
        (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
            (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
            (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (((Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1)).card : ℝ) *
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1)).card ≤ bpCut X := by
      calc _ ≤ (Finset.Icc 1 (bpCut X)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = bpCut X := by simp [Nat.card_Icc]
    have hcr : (((Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1)).card : ℝ) ≤
        (bpCut X : ℝ) := by exact_mod_cast hc
    have hψ : 0 ≤ Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X) :=
      sub_nonneg.mpr (Chebyshev.theta_le_psi _)
    have hD : (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ (Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1),
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (((Finset.Icc 1 (bpCut X)).filter (fun d => d % 2 = 1)).card : ℝ) *
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
        (∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1) := add_le_add
        (add_le_add
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg))
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg)))
        (mul_le_mul_of_nonneg_right hcr (by linarith))
    exact (hA.trans hB).trans (by rw [hC]; exact hD)

  have hweight : (∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      Real.log (X : ℝ) * (∑ d ∈ bpLow X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hdS : d ∈ bpS X := (Finset.mem_filter.mp hd).1
    have hdodd : d ∈ bpOdd (bpD X) := (Finset.mem_filter.mp hdS).1
    have hdI : d ∈ Finset.Icc 1 (bpD X) := (Finset.mem_filter.mp hdodd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdX' : (d : ℝ) ≤ (X : ℝ) := by
      have hdc : (d : ℝ) ≤ (bpCut X : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hd).2
      exact hdc.trans hcutXle
    exact mul_le_mul_of_nonneg_right (low_part_error_aux_coeff hd1 hdX') (abs_nonneg _)

  have hT1 : Real.log (X : ℝ) * (M * (TwinShortAP.upper X : ℝ) *
      ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹) ≤
      2 * M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have hinv : ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹ ≤ (Real.log (X : ℝ) ^ 3)⁻¹ :=
      inv_anti₀ (pow_pos hLxpos 3) (pow_le_pow_left₀ hLxpos.le hlogu_ge 3)
    have hstep : Real.log (X : ℝ) * (M * (TwinShortAP.upper X : ℝ) *
        ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹) ≤
        Real.log (X : ℝ) * (M * (TwinShortAP.upper X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinv (mul_nonneg hM.le hupos.le)) hLxpos.le
    have hid : Real.log (X : ℝ) * (M * (TwinShortAP.upper X : ℝ) *
        ((Real.log (X : ℝ)) ^ 3)⁻¹) = M * (TwinShortAP.upper X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
      field_simp [hLxpos.ne']
    have hfin : M * (TwinShortAP.upper X : ℝ) / (Real.log (X : ℝ)) ^ 2 ≤
        2 * M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg hLxpos.le 2)
      calc M * (TwinShortAP.upper X : ℝ) ≤ M * (2 * (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hu2X hM.le
        _ = 2 * M * (X : ℝ) := by ring
    exact hstep.trans (by rw [hid]; exact hfin)
  have hT2 : Real.log (X : ℝ) * (M * (X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹) ≤
      M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have hid : Real.log (X : ℝ) * (M * (X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹) =
        M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
      field_simp [hLxpos.ne']
    rw [hid]
  have hT3 : Real.log (X : ℝ) * ((bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
      Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤ 9 * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have hψθ : Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X) ≤
        2 * Real.sqrt (TwinShortAP.upper X : ℝ) * Real.log (TwinShortAP.upper X : ℝ) :=
      Chebyshev.psi_sub_theta_le hu1
    have hψnn : 0 ≤ Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X) :=
      sub_nonneg.mpr (Chebyshev.theta_le_psi _)
    have hP1 : (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
        (Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13) *
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1) :=
      mul_le_mul_of_nonneg_right hcutLx (by linarith)
    have hP2 : (Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13) *
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
        (Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13) *
          (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
            Real.log (TwinShortAP.upper X : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hLxpos.le 13))
    have hPbound := hP1.trans hP2
    have h13a : (Real.log (X : ℝ)) ^ 13 * ((bpCut X : ℝ) *
        ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤
        (Real.log (X : ℝ)) ^ 13 * ((Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13) *
          (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
            Real.log (TwinShortAP.upper X : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hPbound (pow_nonneg hLxpos.le 13)
    have h13b : (Real.log (X : ℝ)) ^ 13 * ((Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 13) *
        (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
          Real.log (TwinShortAP.upper X : ℝ) + 1)) =
        Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
          Real.log (TwinShortAP.upper X : ℝ) + 1) := by
      field_simp [hLxpos.ne']
    have hsq2 : Real.sqrt (X : ℝ) * Real.sqrt (TwinShortAP.upper X : ℝ) ≤ 2 * (X : ℝ) := by
      have h : 0 ≤ (Real.sqrt (X : ℝ) - Real.sqrt (TwinShortAP.upper X : ℝ)) ^ 2 := sq_nonneg _
      have h1 : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := Real.sq_sqrt hXpos.le
      have h2 : (Real.sqrt (TwinShortAP.upper X : ℝ)) ^ 2 = (TwinShortAP.upper X : ℝ) :=
        Real.sq_sqrt hupos.le
      nlinarith only [h, h1, h2, hu2X]
    have ha : Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
        Real.log (TwinShortAP.upper X : ℝ)) ≤ 8 * (X : ℝ) * Real.log (X : ℝ) := by
      calc Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
            Real.log (TwinShortAP.upper X : ℝ))
          = 2 * (Real.sqrt (X : ℝ) * Real.sqrt (TwinShortAP.upper X : ℝ)) *
              Real.log (TwinShortAP.upper X : ℝ) := by ring
        _ ≤ 2 * (2 * (X : ℝ)) * (2 * Real.log (X : ℝ)) := by gcongr
        _ = 8 * (X : ℝ) * Real.log (X : ℝ) := by ring
    have hb : Real.sqrt (X : ℝ) ≤ (X : ℝ) := Real.sqrt_le_iff.mpr ⟨hXpos.le, hsqX⟩
    have hmon : Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ 10 := by
      simpa using pow_le_pow_right₀ hLx1 (by norm_num : (1 : ℕ) ≤ 10)
    have hmon1 : (X : ℝ) * Real.log (X : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ 10 :=
      mul_le_mul_of_nonneg_left hmon hXpos.le
    have hmon2 : (X : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ 10 := by
      have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hLx1 (n := 10)) hXpos.le
      linarith
    have h13c : Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
        Real.log (TwinShortAP.upper X : ℝ) + 1) ≤ 9 * (X : ℝ) * (Real.log (X : ℝ)) ^ 10 := by
      have hsplit : Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
          Real.log (TwinShortAP.upper X : ℝ) + 1) =
          Real.sqrt (X : ℝ) * (2 * Real.sqrt (TwinShortAP.upper X : ℝ) *
            Real.log (TwinShortAP.upper X : ℝ)) + Real.sqrt (X : ℝ) := by ring
      have h1 : 8 * (X : ℝ) * Real.log (X : ℝ) ≤ 8 * (X : ℝ) * (Real.log (X : ℝ)) ^ 10 := by
        have := mul_le_mul_of_nonneg_left hmon1 (by norm_num : (0 : ℝ) ≤ 8)
        linarith
      rw [hsplit]
      linarith
    have h13 : (Real.log (X : ℝ)) ^ 13 * ((bpCut X : ℝ) *
        ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤
        9 * (X : ℝ) * (Real.log (X : ℝ)) ^ 10 := h13a.trans (by rw [h13b]; exact h13c)
    have h3 : (Real.log (X : ℝ)) ^ 3 * ((bpCut X : ℝ) *
        ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤ 9 * (X : ℝ) := by
      have key : (Real.log (X : ℝ)) ^ 3 * ((bpCut X : ℝ) *
          ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1)) * (Real.log (X : ℝ)) ^ 10 ≤
          9 * (X : ℝ) * (Real.log (X : ℝ)) ^ 10 := by linarith [h13]
      exact le_of_mul_le_mul_right key (pow_pos hLxpos 10)
    have hkey : Real.log (X : ℝ) * ((bpCut X : ℝ) *
        ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) * (Real.log (X : ℝ)) ^ 2 ≤ 9 * (X : ℝ) := by
      linarith [h3]
    exact (le_div_iff₀ (pow_pos hLxpos 2)).mpr hkey

  have htot : (∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      2 * M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 + M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 +
        9 * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have h1 : Real.log (X : ℝ) * (∑ d ∈ bpLow X,
        |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
        Real.log (X : ℝ) * ((∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) :=
      mul_le_mul_of_nonneg_left hE hLxpos.le
    have h2 : Real.log (X : ℝ) * ((∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (bpCut X),
          (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤
        Real.log (X : ℝ) * (M * (TwinShortAP.upper X : ℝ) *
          ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹) +
        Real.log (X : ℝ) * (M * (X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹) +
        Real.log (X : ℝ) * ((bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1)) := by
      have key : Real.log (X : ℝ) * ((∑ d ∈ Finset.Icc 1 (bpCut X),
            (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
          (∑ d ∈ Finset.Icc 1 (bpCut X),
            (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
          (bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1)) ≤
          Real.log (X : ℝ) * ((M * (TwinShortAP.upper X : ℝ) *
            ((Real.log (TwinShortAP.upper X : ℝ)) ^ 3)⁻¹) +
          (M * (X : ℝ) * ((Real.log (X : ℝ)) ^ 3)⁻¹) +
          ((bpCut X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
            Chebyshev.theta (TwinShortAP.upper X)) + 1))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hsumU hsumX) le_rfl) hLxpos.le
      linarith only [key]
    exact (hweight.trans h1).trans (h2.trans (add_le_add (add_le_add hT1 hT2) hT3))
  have hL2 : Real.log (2 + (X : ℝ)) ^ 2 ≤ 4 * (Real.log (X : ℝ)) ^ 2 := by
    have h := pow_le_pow_left₀ hLpos.le hLle 2
    have h2 : (2 * Real.log (X : ℝ)) ^ 2 = 4 * (Real.log (X : ℝ)) ^ 2 := by ring
    linarith
  have hdiv : (X : ℝ) / (Real.log (X : ℝ)) ^ 2 ≤ 4 * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hLxpos 2) (pow_pos hLpos 2)]
    have h := mul_le_mul_of_nonneg_left hL2 hXpos.le
    linarith
  have hfin1 : (3 * M + 9) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) ≤
      (3 * M + 9) * (4 * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hdiv (by linarith)
  have hfin2 : (3 * M + 9) * (4 * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2) =
      (12 * M + 36) * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 := by ring
  have hfin3 : (12 * M + 36) * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 ≤
      (12 * M + 40) * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 :=
      div_nonneg hXpos.le (pow_nonneg hLpos.le 2)
    have h4 : (12 * M + 36) * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 =
        (12 * M + 36) * ((X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2) := by ring
    have h5 : (12 * M + 40) * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2 =
        (12 * M + 40) * ((X : ℝ) / Real.log (2 + (X : ℝ)) ^ 2) := by ring
    rw [h4, h5]
    linarith
  have htot2 : 2 * M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 + M * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 +
      9 * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 = (3 * M + 9) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by
    ring
  exact (htot.trans (by rw [htot2])).trans (hfin1.trans (by rw [hfin2]; exact hfin3))

theorem low_part_error : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
    (∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      C * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := by
  obtain ⟨C, hC, hev⟩ := low_part_error_aux_eventually
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let S : ℕ → ℝ := fun X =>
    ∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|
  let f : ℕ → ℝ := fun X => S X * (Real.log (2 + (X : ℝ))) ^ 2 / (X : ℝ)
  have hf : ∀ X, f X = S X * (Real.log (2 + (X : ℝ))) ^ 2 / (X : ℝ) := fun _ => rfl
  have hSnn : ∀ X, 0 ≤ S X :=
    fun X => Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hfnn : ∀ X, 0 ≤ f X := by
    intro X
    rw [hf X]
    exact div_nonneg (mul_nonneg (hSnn X) (sq_nonneg _)) (Nat.cast_nonneg _)
  refine ⟨C + ∑ X ∈ Finset.Icc 3 (N - 1), f X, ?_, ?_⟩
  · have hnn : 0 ≤ ∑ X ∈ Finset.Icc 3 (N - 1), f X :=
      Finset.sum_nonneg (fun X _ => hfnn X)
    linarith
  · intro X hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hLpos : 0 < Real.log (2 + (X : ℝ)) := Real.log_pos (by linarith)
    have hnn : 0 ≤ ∑ Y ∈ Finset.Icc 3 (N - 1), f Y :=
      Finset.sum_nonneg (fun Y _ => hfnn Y)
    by_cases h : N ≤ X
    · have h1 : S X ≤ C * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := hN X h
      calc S X ≤ C * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := h1
        _ ≤ (C + ∑ Y ∈ Finset.Icc 3 (N - 1), f Y) * (X : ℝ) /
              (Real.log (2 + (X : ℝ))) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right (by linarith) hXpos.le
    · have hmem : X ∈ Finset.Icc 3 (N - 1) := Finset.mem_Icc.mpr ⟨hX, by omega⟩
      have hle : f X ≤ ∑ Y ∈ Finset.Icc 3 (N - 1), f Y :=
        Finset.single_le_sum (fun Y _ => hfnn Y) hmem
      have heq : S X = f X * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := by
        rw [hf X]
        field_simp [hXpos.ne', hLpos.ne']
      calc S X = f X * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 := heq
        _ ≤ (C + ∑ Y ∈ Finset.Icc 3 (N - 1), f Y) * (X : ℝ) /
              (Real.log (2 + (X : ℝ))) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right (by linarith) hXpos.le

theorem sharp_multiplicative_large_sieve_aux_sum {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℤ → A) :
    (∑ n ∈ Finset.Ioc (-1 : ℤ) (-1 + (N : ℤ)), f n) = ∑ m : Fin N, f (m : ℤ) := by
  classical
  symm
  refine Finset.sum_bij (fun (m : Fin N) _ => (m : ℤ)) ?_ ?_ ?_ ?_
  · intro m _
    rw [Finset.mem_Ioc]
    have hm : (m.val : ℕ) < N := m.isLt
    omega
  · intro x _ y _ hxy
    have h : (x.val : ℤ) = (y.val : ℤ) := hxy
    exact Fin.ext (Int.ofNat_injective h)
  · intro b hb
    rw [Finset.mem_Ioc] at hb
    have hb0 : 0 ≤ b := by omega
    have hbN : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
    refine ⟨⟨b.toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · omega
    · show ((b.toNat : ℕ) : ℤ) = b
      exact hbN
  · intro m _
    rfl

theorem sharp_multiplicative_large_sieve (Q N : ℕ) (a : Fin N → ℂ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) ≤
      64 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    have h0 : OAI.LargePrimeGaps.primitiveCharacterMean 0
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) = 0 := by
      unfold OAI.LargePrimeGaps.primitiveCharacterMean
      simp
    rw [h0]
    positivity
  · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
    let b : ℤ → ℂ := fun n => if h : 0 ≤ n ∧ n < (N : ℤ) then a ⟨n.toNat, by omega⟩ else 0
    have hterm : ∀ m : Fin N, b (m : ℤ) = a m := by
      intro m
      have hm : (m.val : ℕ) < N := m.isLt
      dsimp only [b]
      split_ifs with h
      · congr 1
      · exfalso
        omega
    have hseq : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        BombieriVinogradov.LargeSieve.intervalCharacterSum b (-1) N q χ =
          OAI.LargePrimeGaps.sequenceCharacterSum a χ := by
      intro q χ
      unfold BombieriVinogradov.LargeSieve.intervalCharacterSum
        OAI.LargePrimeGaps.sequenceCharacterSum
      rw [sharp_multiplicative_large_sieve_aux_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [hterm m]
      simp only [Int.cast_natCast]
    have hnorm : (∑ n ∈ Finset.Ioc (-1 : ℤ) (-1 + (N : ℤ)), ‖b n‖ ^ 2) =
        ∑ m : Fin N, ‖a m‖ ^ 2 := by
      rw [sharp_multiplicative_large_sieve_aux_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [hterm m]
    have hL : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters q,
            ‖BombieriVinogradov.LargeSieve.intervalCharacterSum b (-1) N q χ‖ ^ 2) =
        OAI.LargePrimeGaps.primitiveCharacterMean Q
          (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) := by
      unfold OAI.LargePrimeGaps.primitiveCharacterMean
      rw [OAI.LargePrimeGaps.sum_Icc_one_eq_sum_fin]
      refine Finset.sum_congr rfl ?_
      intro q _
      have hinner : (∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters (q.val + 1),
          ‖BombieriVinogradov.LargeSieve.intervalCharacterSum b (-1) N (q.val + 1) χ‖ ^ 2) =
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q.val + 1))).filter
            (fun χ => χ.IsPrimitive),
            ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2 := by
        unfold BombieriVinogradov.LargeSieve.primitiveCharacters
        refine Finset.sum_congr rfl ?_
        intro χ _
        rw [hseq (q.val + 1) χ]
      rw [hinner]
    rw [← hL]
    have hmain := BombieriVinogradov.LargeSieve.characterLargeSieveNat (-1) N Q b hQ1
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters q,
            ‖BombieriVinogradov.LargeSieve.intervalCharacterSum b (-1) N q χ‖ ^ 2)
        ≤ 64 * ((N : ℝ) + (Q : ℝ) ^ 2) *
            ∑ n ∈ Finset.Ioc (-1 : ℤ) (-1 + (N : ℤ)), ‖b n‖ ^ 2 := hmain
      _ = 64 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by rw [hnorm]

section sharp_bilinear_mean_aux_section

open BombieriVinogradov.LargeSieve

noncomputable local instance sharp_bilinear_mean_aux_unitsFintype (q : ℕ) :
    Fintype (ZMod q)ˣ := Fintype.ofFinite _

lemma sharp_bilinear_mean_aux_phase (x : ℝ) :
    additivePhase x = Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex x := by
  unfold additivePhase Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex
  rw [circleMap_zero]
  norm_num

lemma sharp_bilinear_mean_aux_farey_eq (Q N : ℕ) (c : ℕ → ℂ) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample c N i‖ ^ 2 =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖∑ k ∈ range N, c k *
          Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex ((k : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
  classical
  rw [sum_fareyIndices_eq_sum_attach]
  rw [← Finset.sum_attach (Icc 1 Q)
    (fun q => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖∑ k ∈ range N, c k *
        Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex ((k : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro q _
  have hq1 : 1 ≤ q.1 := (Finset.mem_Icc.mp q.2).1
  letI : NeZero q.1 := ⟨Nat.ne_of_gt hq1⟩
  have hval : ∀ u : (ZMod q.1)ˣ,
      (fareyValue (⟨q, u⟩ : FareyIndex Q) : ℝ) = (u.val.val : ℝ) / (q.1 : ℝ) := by
    intro u
    unfold fareyValue unitFraction
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  have hsample : ∀ u : (ZMod q.1)ˣ, fareyAdditiveSample c N (⟨q, u⟩ : FareyIndex Q) =
      ∑ k ∈ range N, c k *
        Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex
          ((k : ℝ) * ((u.val.val : ℝ) / (q.1 : ℝ))) := by
    intro u
    unfold fareyAdditiveSample
    apply Finset.sum_congr rfl
    intro k _
    rw [sharp_bilinear_mean_aux_phase, hval u]
  refine Finset.sum_bij (fun (u : (ZMod q.1)ˣ) _ => u.val.val) ?_ ?_ ?_ ?_
  · intro u _
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt u.val, ?_⟩
    have hu : IsUnit ((u.val.val : ℕ) : ZMod q.1) := by simp [u.isUnit]
    exact (ZMod.isUnit_iff_coprime _ _).mp hu
  · intro u _ v _ huv
    apply Units.ext
    have h1 : ((u.val.val : ℕ) : ZMod q.1) = ((v.val.val : ℕ) : ZMod q.1) :=
      congrArg (fun n : ℕ => (n : ZMod q.1)) huv
    simpa [ZMod.natCast_zmod_val] using h1
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have hunit : IsUnit (a : ZMod q.1) := (ZMod.isUnit_iff_coprime a q.1).mpr ha.2
    refine ⟨hunit.unit, Finset.mem_univ _, ?_⟩
    have hval2 : (hunit.unit : ZMod q.1) = (a : ZMod q.1) := hunit.unit_spec
    have hv := congrArg ZMod.val hval2
    rw [ZMod.val_natCast_of_lt ha.1] at hv
    exact hv
  · intro u _
    rw [hsample u]

lemma sharp_bilinear_mean_aux_farey_le (Q N : ℕ) (c : ℕ → ℂ) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample c N i‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ range N, ‖c k‖ ^ 2 := by
  rw [sharp_bilinear_mean_aux_farey_eq]
  have h := Conjectures.Goldbach.AnalyticLargeSieve_aux.large_sieve 0 N Q c
  simpa using h

lemma sharp_bilinear_mean_aux_char_sieve (M : ℤ) (N Q : ℕ) (a : ℤ → ℂ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum a M N q χ‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
  have hfixed : (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum a M N q χ‖ ^ 2) ≤
      ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := by
    apply Finset.sum_le_sum
    intro q hq
    letI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    rw [modulusAdditiveEnergy_eq]
    exact weightedPrimitiveCharacterSum_le_additive a M N
  calc ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum a M N q χ‖ ^ 2
      ≤ ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := hfixed
    _ = ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 :=
        sum_modulusAdditiveEnergy_eq_fareySamples Q a M N
    _ ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ k ∈ range N, ‖shiftedIntervalCoefficients a M k‖ ^ 2 :=
        sharp_bilinear_mean_aux_farey_le Q N _
    _ = (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
        rw [sum_int_Ioc_eq_sum_range (fun n => ‖a n‖ ^ 2) M N]
        rfl

lemma sharp_bilinear_mean_aux_mean_sq (Q N : ℕ) (a : Fin N → ℂ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) ≤
      4 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  classical
  let a' : ℤ → ℂ := fun n => if h : n.toNat < N ∧ 0 ≤ n then a ⟨n.toNat, h.1⟩ else 0
  have ha' : ∀ k : ℕ, (hk : k < N) → a' (k : ℤ) = a ⟨k, hk⟩ := by
    intro k hk
    have hk' : (k : ℤ).toNat < N ∧ 0 ≤ (k : ℤ) :=
      ⟨by rw [Int.toNat_natCast]; exact hk, by omega⟩
    dsimp [a']
    rw [dif_pos ⟨hk, by omega⟩]
  have hsum_char : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      intervalCharacterSum a' (-1) N q χ = OAI.LargePrimeGaps.sequenceCharacterSum a χ := by
    intro q χ
    unfold intervalCharacterSum OAI.LargePrimeGaps.sequenceCharacterSum
    rw [sum_int_Ioc_eq_sum_range (fun n => a' n * χ (n : ZMod q)) (-1) N]
    rw [Finset.sum_fin_eq_sum_range (fun n : Fin N => a n * χ (n : ZMod q))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [hk, ↓reduceDIte]
    have h1 : (-1 : ℤ) + (k : ℤ) + 1 = (k : ℤ) := by ring
    rw [h1, ha' k hk]
    have h2 : ((k : ℤ) : ZMod q) = ((k : ℕ) : ZMod q) := by simp
    rw [h2]
  have hsum_sq : (∑ n ∈ Ioc (-1 : ℤ) (-1 + (N : ℤ)), ‖a' n‖ ^ 2) = ∑ n : Fin N, ‖a n‖ ^ 2 := by
    rw [sum_int_Ioc_eq_sum_range (fun n => ‖a' n‖ ^ 2) (-1) N]
    rw [Finset.sum_fin_eq_sum_range (fun n : Fin N => ‖a n‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [hk, ↓reduceDIte]
    have h1 : (-1 : ℤ) + (k : ℤ) + 1 = (k : ℤ) := by ring
    rw [h1, ha' k hk]
  have hprim : ∀ q : ℕ,
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive) =
        primitiveCharacters q := by
    intro q
    simp [primitiveCharacters]
  have hmean : (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖intervalCharacterSum a' (-1) N q χ‖ ^ 2) =
      OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) := by
    rw [OAI.LargePrimeGaps.sum_Icc_one_eq_sum_fin]
    unfold OAI.LargePrimeGaps.primitiveCharacterMean
    apply Finset.sum_congr rfl
    intro q _
    simp_rw [hsum_char (q.val + 1)]
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsum : (0 : ℝ) ≤ ∑ n : Fin N, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hπ : Real.pi * (N : ℝ) + (Q : ℝ) ^ 2 ≤ 4 * ((N : ℝ) + (Q : ℝ) ^ 2) := by
    nlinarith [Real.pi_le_four]
  calc OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2)
      = ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖intervalCharacterSum a' (-1) N q χ‖ ^ 2 := hmean.symm
    _ = ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum a' (-1) N q χ‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hprim q]
    _ ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc (-1 : ℤ) (-1 + (N : ℤ)), ‖a' n‖ ^ 2 :=
        sharp_bilinear_mean_aux_char_sieve (-1) N Q a'
    _ = (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by rw [hsum_sq]
    _ ≤ 4 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hπ hsum

end sharp_bilinear_mean_aux_section

theorem sharp_bilinear_mean (Q M N : ℕ) (a : Fin M → ℂ) (b : Fin N → ℂ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
        OAI.LargePrimeGaps.sequenceCharacterSum b χ‖) ≤
      8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b := by
  have hc := OAI.LargePrimeGaps.primitiveCharacterMean_cauchy (Q := Q)
    (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖)
    (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum b χ‖)
  have h' : (OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
        OAI.LargePrimeGaps.sequenceCharacterSum b χ‖)) ^ 2 ≤
      OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) *
      OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum b χ‖ ^ 2) := by
    simpa only [norm_mul] using hc
  have ha := sharp_bilinear_mean_aux_mean_sq Q M a
  have hb := sharp_bilinear_mean_aux_mean_sq Q N b
  have hprod : (OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
        OAI.LargePrimeGaps.sequenceCharacterSum b χ‖)) ^ 2 ≤
      16 * (((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
        (OAI.LargePrimeGaps.sequenceSize a ^ 2 * OAI.LargePrimeGaps.sequenceSize b ^ 2) := by
    calc _ ≤ OAI.LargePrimeGaps.primitiveCharacterMean Q
          (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) *
        OAI.LargePrimeGaps.primitiveCharacterMean Q
          (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum b χ‖ ^ 2) := h'
      _ ≤ (4 * ((M : ℝ) + (Q : ℝ) ^ 2) * OAI.LargePrimeGaps.sequenceSize a ^ 2) *
          (4 * ((N : ℝ) + (Q : ℝ) ^ 2) * OAI.LargePrimeGaps.sequenceSize b ^ 2) := by
          rw [OAI.LargePrimeGaps.sequenceSize_sq, OAI.LargePrimeGaps.sequenceSize_sq]
          exact mul_le_mul ha hb
            (OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _))
            ((OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _
              (fun _ _ => sq_nonneg _)).trans ha)
      _ = 16 * (((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
          (OAI.LargePrimeGaps.sequenceSize a ^ 2 * OAI.LargePrimeGaps.sequenceSize b ^ 2) := by
          ring
  have hsq : (8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
      OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b) ^ 2 =
      64 * (((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
        (OAI.LargePrimeGaps.sequenceSize a ^ 2 * OAI.LargePrimeGaps.sequenceSize b ^ 2) := by
    have h1 : (8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b) ^ 2 =
        64 * (Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2)) ^ 2 *
          (Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2)) ^ 2 *
          OAI.LargePrimeGaps.sequenceSize a ^ 2 * OAI.LargePrimeGaps.sequenceSize b ^ 2 := by
      ring
    rw [h1, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  refine (sq_le_sq₀ ?_ ?_).mp ?_
  · exact OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _ (fun _ _ => norm_nonneg _)
  · have hsa := OAI.LargePrimeGaps.sequenceSize_nonneg a
    have hsb := OAI.LargePrimeGaps.sequenceSize_nonneg b
    positivity
  · rw [hsq]
    have hX : (0 : ℝ) ≤ (((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
        (OAI.LargePrimeGaps.sequenceSize a ^ 2 * OAI.LargePrimeGaps.sequenceSize b ^ 2) := by
      positivity
    linarith

theorem sharp_triangular_mean_aux_hadd (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) (k : ℕ) :
    ZMod.stdAddChar (((k : ℤ) : ZMod q) * (u : ZMod q)) =
      Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex ((k : ℝ) * ((u.val.val : ℝ) / q)) := by
  have h1 : ((k : ℤ) : ZMod q) * (u : ZMod q) = ((k * u.val.val : ℕ) : ZMod q) := by
    rw [Int.cast_natCast, Nat.cast_mul]
    congr 1
    exact (ZMod.natCast_zmod_val u.val).symm
  rw [h1, ← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex
  congr 1
  push_cast
  ring

theorem sharp_triangular_mean_aux_hunits {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q]
    (f : ℕ → M) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f a) =
      ∑ u : (ZMod q)ˣ, f u.val.val := by
  classical
  refine Finset.sum_bij
    (fun (a : ℕ) (ha : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q)) =>
      ((ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2).unit)
    ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have hval : (a : ZMod q) = (b : ZMod q) := by
      have h := congrArg (fun x : (ZMod q)ˣ => (x : ZMod q)) hab
      rwa [IsUnit.unit_spec, IsUnit.unit_spec] at h
    have hlt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hltb : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hvv : (a : ZMod q).val = (b : ZMod q).val := by rw [hval]
    have hinj := ZMod.val_injective q hvv
    calc a = (a : ZMod q).val := (ZMod.val_natCast_of_lt hlt).symm
      _ = (b : ZMod q).val := by rw [hinj]
      _ = b := ZMod.val_natCast_of_lt hltb
  · intro u _
    refine ⟨u.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr u.val.val_lt, ?_⟩, ?_⟩
    · have hiu : IsUnit ((u.val.val : ℕ) : ZMod q) := by
        rw [ZMod.natCast_zmod_val u.val]
        exact Units.isUnit u
      exact (ZMod.isUnit_iff_coprime u.val.val q).mp hiu
    · apply Units.ext
      rw [IsUnit.unit_spec]
      exact ZMod.natCast_zmod_val u.val
  · intro a ha
    have hlt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hspec : ((((ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2).unit :
        (ZMod q)ˣ) : ZMod q) = (a : ZMod q) := IsUnit.unit_spec _
    have hval : ((((ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2).unit.val :
        ZMod q)) = (a : ZMod q) := hspec
    have hv : ((ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2).unit.val.val = a := by
      rw [hval]
      exact ZMod.val_natCast_of_lt hlt
    rw [hv]

theorem sharp_triangular_mean_aux_sieve (Q N : ℕ) (a : Fin N → ℂ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) ≤
      (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  classical
  by_cases hN : N = 0
  · subst hN
    have hz : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2 = 0 := by
      intro q χ
      simp [OAI.LargePrimeGaps.sequenceCharacterSum]
    have hL0 : OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) = 0 := by
      unfold OAI.LargePrimeGaps.primitiveCharacterMean
      apply Finset.sum_eq_zero
      intro q _
      simp [hz]
    rw [hL0]
    simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    by_cases hQ : Q = 0
    · subst hQ
      have hz : OAI.LargePrimeGaps.primitiveCharacterMean 0
          (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) = 0 := by
        simp [OAI.LargePrimeGaps.primitiveCharacterMean]
      rw [hz]
      positivity
    · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
      let a' : ℤ → ℂ := fun n =>
        if 0 ≤ n ∧ n < (N : ℤ) then a ⟨n.toNat % N, Nat.mod_lt _ hNpos⟩ else 0
      have hpad (n : ℕ) (hn : n < N) : a' (n : ℤ) = a ⟨n, hn⟩ := by
        have h : (0 : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < (N : ℤ) := ⟨by omega, by omega⟩
        dsimp only [a']
        simp only [h]
        apply congrArg a
        ext
        simp [Nat.mod_eq_of_lt hn]
      have hsum (q : ℕ) (χ : DirichletCharacter ℂ q) :
          BombieriVinogradov.LargeSieve.intervalCharacterSum a' (-1) N q χ =
            OAI.LargePrimeGaps.sequenceCharacterSum a χ := by
        unfold BombieriVinogradov.LargeSieve.intervalCharacterSum
        rw [BombieriVinogradov.LargeSieve.sum_int_Ioc_eq_sum_range]
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k _
        have hk' : k < N := k.isLt
        have hidx : (-1 : ℤ) + (k : ℤ) + 1 = (k : ℤ) := by ring
        rw [hidx, hpad k hk']
        have hcast : ((k : ℤ) : ZMod q) = ((k : ℕ) : ZMod q) := Int.cast_natCast k
        rw [hcast]
      have hres (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
          ‖BombieriVinogradov.LargeSieve.intervalAdditiveResidueSum a' (-1) N q u‖ =
            ‖∑ k ∈ Finset.Ico 0 N, a' (k : ℤ) *
              Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex
                ((k : ℝ) * ((u.val.val : ℝ) / q))‖ := by
        unfold BombieriVinogradov.LargeSieve.intervalAdditiveResidueSum
        rw [BombieriVinogradov.LargeSieve.sum_int_Ioc_eq_sum_range]
        rw [Finset.range_eq_Ico]
        apply congrArg norm
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < N := (Finset.mem_Ico.mp hk).2
        have hidx : (-1 : ℤ) + (k : ℤ) + 1 = (k : ℤ) := by ring
        rw [hidx, hpad k hk', sharp_triangular_mean_aux_hadd q u k]
      let E : ℕ → ℝ := fun q =>
        if hq : q = 0 then 0 else
          (letI : NeZero q := ⟨hq⟩; ∑ u : (ZMod q)ˣ,
            ‖BombieriVinogradov.LargeSieve.intervalAdditiveResidueSum a' (-1) N q u‖ ^ 2)
      let A : ℕ → ℝ := fun q =>
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∑ k ∈ Finset.Ico 0 N, a' (k : ℤ) *
            Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex ((k : ℝ) * ((a : ℝ) / q))‖ ^ 2
      have h1 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters q,
              ‖BombieriVinogradov.LargeSieve.intervalCharacterSum a' (-1) N q χ‖ ^ 2) ≤
          ∑ q ∈ Finset.Icc 1 Q, E q := by
        apply Finset.sum_le_sum
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hq0 : q ≠ 0 := by omega
        letI : NeZero q := ⟨hq0⟩
        dsimp only [E]
        simp only [hq0]
        refine le_trans
          (BombieriVinogradov.LargeSieve.weightedPrimitiveCharacterSum_le_additive
            (q := q) a' (-1) N) ?_
        apply le_of_eq
        apply Finset.sum_congr
        · ext u
          simp
        · intro u _
          rfl
      have h2 : (∑ q ∈ Finset.Icc 1 Q, E q) = ∑ q ∈ Finset.Icc 1 Q, A q := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hq0 : q ≠ 0 := by omega
        letI : NeZero q := ⟨hq0⟩
        dsimp only [E, A]
        simp only [hq0]
        rw [sharp_triangular_mean_aux_hunits q (fun a => ‖∑ k ∈ Finset.Ico 0 N, a' (k : ℤ) *
            Conjectures.Goldbach.AnalyticLargeSieve_aux.Ex ((k : ℝ) * ((a : ℝ) / q))‖ ^ 2)]
        apply Finset.sum_congr rfl
        intro u _
        rw [hres q u]
      have h3 := Conjectures.Goldbach.AnalyticLargeSieve_aux.large_sieve 0 N Q
        (fun k => a' (k : ℤ))
      have h4 : (∑ k ∈ Finset.Ico 0 N, ‖a' (k : ℤ)‖ ^ 2) = ∑ n : Fin N, ‖a n‖ ^ 2 := by
        rw [← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k _
        rw [hpad k k.isLt]
      simp only [zero_add] at h3
      rw [h4] at h3
      have hL : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters q,
            ‖BombieriVinogradov.LargeSieve.intervalCharacterSum a' (-1) N q χ‖ ^ 2) =
          OAI.LargePrimeGaps.primitiveCharacterMean Q
            (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖ ^ 2) := by
        rw [OAI.LargePrimeGaps.sum_Icc_one_eq_sum_fin]
        unfold OAI.LargePrimeGaps.primitiveCharacterMean
        apply Finset.sum_congr rfl
        intro q _
        simp only [hsum]
        rfl
      rw [hL] at h1
      exact h1.trans (h2 ▸ h3)

theorem sharp_triangular_mean_aux_bilinear (Q M N : ℕ) (a : Fin M → ℂ) (b : Fin N → ℂ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
        OAI.LargePrimeGaps.sequenceCharacterSum b χ‖) ≤
      8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b := by
  have h := OAI.LargePrimeGaps.primitiveCharacterMean_cauchy (Q := Q)
    (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ‖)
    (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum b χ‖)
  simp only [← norm_mul] at h
  have h1 := sharp_triangular_mean_aux_sieve Q M a
  have h2 := sharp_triangular_mean_aux_sieve Q N b
  have hstep : (OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
        OAI.LargePrimeGaps.sequenceCharacterSum b χ‖)) ^ 2 ≤
      ((Real.pi * (M : ℝ) + (Q : ℝ) ^ 2) * ∑ m : Fin M, ‖a m‖ ^ 2) *
      ((Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2) :=
    h.trans (mul_le_mul h1 h2
      (OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _))
      ((OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _)).trans h1))
  have hM : Real.pi * (M : ℝ) + (Q : ℝ) ^ 2 ≤ 4 * ((M : ℝ) + (Q : ℝ) ^ 2) := by
    have hπM : Real.pi * (M : ℝ) ≤ 4 * (M : ℝ) :=
      mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg M)
    linarith [sq_nonneg (Q : ℝ)]
  have hN : Real.pi * (N : ℝ) + (Q : ℝ) ^ 2 ≤ 4 * ((N : ℝ) + (Q : ℝ) ^ 2) := by
    have hπN : Real.pi * (N : ℝ) ≤ 4 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg N)
    linarith [sq_nonneg (Q : ℝ)]
  have hN0 : 0 ≤ Real.pi * (N : ℝ) + (Q : ℝ) ^ 2 := by positivity
  have hM4 : 0 ≤ 4 * ((M : ℝ) + (Q : ℝ) ^ 2) := by positivity
  have hxy : (Real.pi * (M : ℝ) + (Q : ℝ) ^ 2) * (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) ≤
      16 * ((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2) := by
    have h := mul_le_mul hM hN hN0 hM4
    linarith
  have hsa : 0 ≤ ∑ m : Fin M, ‖a m‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsb : 0 ≤ ∑ n : Fin N, ‖b n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hrhs : (8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
      OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b) ^ 2 =
      64 * ((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2) *
        (∑ m : Fin M, ‖a m‖ ^ 2) * (∑ n : Fin N, ‖b n‖ ^ 2) := by
    rw [mul_pow, mul_pow, OAI.LargePrimeGaps.sequenceSize_sq,
      OAI.LargePrimeGaps.sequenceSize_sq]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hle : ((Real.pi * (M : ℝ) + (Q : ℝ) ^ 2) * ∑ m : Fin M, ‖a m‖ ^ 2) *
      ((Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2) ≤
      (8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b) ^ 2 := by
    rw [hrhs]
    calc ((Real.pi * (M : ℝ) + (Q : ℝ) ^ 2) * ∑ m : Fin M, ‖a m‖ ^ 2) *
          ((Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2)
        = ((Real.pi * (M : ℝ) + (Q : ℝ) ^ 2) * (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2)) *
            ((∑ m : Fin M, ‖a m‖ ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2) := by ring
      _ ≤ (16 * ((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
            ((∑ m : Fin M, ‖a m‖ ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hxy (mul_nonneg hsa hsb)
      _ ≤ (64 * ((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2)) *
            ((∑ m : Fin M, ‖a m‖ ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsa hsb)
          have hx0 : 0 ≤ (M : ℝ) + (Q : ℝ) ^ 2 := by positivity
          have hy0 : 0 ≤ (N : ℝ) + (Q : ℝ) ^ 2 := by positivity
          nlinarith
      _ = 64 * ((M : ℝ) + (Q : ℝ) ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2) *
            (∑ m : Fin M, ‖a m‖ ^ 2) * ∑ n : Fin N, ‖b n‖ ^ 2 := by ring
  have hpos : 0 ≤ 8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
      OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b := by
    have hsa' := OAI.LargePrimeGaps.sequenceSize_nonneg a
    have hsb' := OAI.LargePrimeGaps.sequenceSize_nonneg b
    positivity
  exact (sq_le_sq₀
    (OAI.LargePrimeGaps.primitiveCharacterMean_nonneg _ (fun _ _ => norm_nonneg _))
    hpos).mp (hstep.trans hle)

theorem sharp_triangular_mean_aux_dyadic {C : ℝ} (hC : 0 ≤ C) (Q M N k L : ℕ)
    (a : Fin M → ℂ) (b : Fin N → ℂ) (t : Fin M → ℕ)
    (hbil : ∀ (a : Fin M → ℂ) (b : Fin N → ℂ),
      OAI.LargePrimeGaps.primitiveCharacterMean Q
        (fun _ χ => ‖OAI.LargePrimeGaps.sequenceCharacterSum a χ *
          OAI.LargePrimeGaps.sequenceCharacterSum b χ‖) ≤
        C * OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b)
    (hb : ∀ n, b n ≠ 0 → L ≤ n.val ∧ n.val < L + 2 ^ k) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.triangularCharacterSum a b t χ‖) ≤
      ((k : ℝ) + 1) * C * OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b := by
  induction k generalizing L a b with
  | zero =>
    have he (q : Fin Q) (χ : DirichletCharacter ℂ (q.val + 1)) :=
      OAI.LargePrimeGaps.triangularCharacterSum_single a b t χ
        (fun n hn => by have h := hb n hn; simpa using (by omega : n.val = L))
    simp only [he, Nat.cast_zero, zero_add, one_mul]
    exact (hbil _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (OAI.LargePrimeGaps.sequenceMask_size_le _ _) hC)
        (OAI.LargePrimeGaps.sequenceSize_nonneg _))
  | succ k ih =>
    let H := L + 2 ^ k
    let p : Fin M → Prop := fun m => t m ≤ H
    let r : Fin N → Prop := fun n => n.val < H
    let a₀ := OAI.LargePrimeGaps.sequenceMask p a
    let a₁ := OAI.LargePrimeGaps.sequenceMask (fun m => ¬ p m) a
    let b₀ := OAI.LargePrimeGaps.sequenceMask r b
    let b₁ := OAI.LargePrimeGaps.sequenceMask (fun n => ¬ r n) b
    have hb₀ : ∀ n, b₀ n ≠ 0 → L ≤ n.val ∧ n.val < L + 2 ^ k := by
      intro n hn
      have hn' : b n ≠ 0 ∧ n.val < H := by
        dsimp [b₀, OAI.LargePrimeGaps.sequenceMask, r] at hn
        split at hn <;> simp_all
      exact ⟨(hb n hn'.1).1, hn'.2⟩
    have hb₁ : ∀ n, b₁ n ≠ 0 → H ≤ n.val ∧ n.val < H + 2 ^ k := by
      intro n hn
      have hn' : b n ≠ 0 ∧ ¬ n.val < H := by
        dsimp [b₁, OAI.LargePrimeGaps.sequenceMask, r] at hn
        split at hn <;> simp_all
      have h := hb n hn'.1
      simp only [pow_succ] at h
      dsimp [H]
      omega
    have hsplit := OAI.LargePrimeGaps.primitiveCharacterMean_mono (Q := Q)
      (f := fun _ χ => ‖OAI.LargePrimeGaps.triangularCharacterSum a b t χ‖)
      (g := fun _ χ => ‖OAI.LargePrimeGaps.triangularCharacterSum a₀ b₀ t χ‖ +
        ‖OAI.LargePrimeGaps.sequenceCharacterSum a₁ χ *
          OAI.LargePrimeGaps.sequenceCharacterSum b₀ χ‖ +
        ‖OAI.LargePrimeGaps.triangularCharacterSum a₁ b₁ t χ‖) (fun _ χ => by
          rw [OAI.LargePrimeGaps.triangularCharacterSum_split a b t χ H]
          exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    rw [OAI.LargePrimeGaps.primitiveCharacterMean_add,
      OAI.LargePrimeGaps.primitiveCharacterMean_add] at hsplit
    have h0 := ih L a₀ b₀ hb₀
    have h1 := ih H a₁ b₁ hb₁
    have hR := hbil a₁ b₀
    have hpair := OAI.LargePrimeGaps.sequenceMask_cauchy p r a b
    have hcross : OAI.LargePrimeGaps.sequenceSize a₁ * OAI.LargePrimeGaps.sequenceSize b₀ ≤
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b :=
      mul_le_mul (OAI.LargePrimeGaps.sequenceMask_size_le _ _)
        (OAI.LargePrimeGaps.sequenceMask_size_le _ _)
        (OAI.LargePrimeGaps.sequenceSize_nonneg _) (OAI.LargePrimeGaps.sequenceSize_nonneg _)
    have hk : 0 ≤ (k : ℝ) + 1 := by positivity
    have hp := mul_le_mul_of_nonneg_left hpair (mul_nonneg hk hC)
    have hc := mul_le_mul_of_nonneg_left hcross hC
    change OAI.LargePrimeGaps.sequenceSize a₀ * OAI.LargePrimeGaps.sequenceSize b₀ +
      OAI.LargePrimeGaps.sequenceSize a₁ * OAI.LargePrimeGaps.sequenceSize b₁ ≤ _ at hpair
    change ((k : ℝ) + 1) * C *
      (OAI.LargePrimeGaps.sequenceSize a₀ * OAI.LargePrimeGaps.sequenceSize b₀ +
        OAI.LargePrimeGaps.sequenceSize a₁ * OAI.LargePrimeGaps.sequenceSize b₁) ≤ _ at hp
    push_cast
    nlinarith only [hsplit, h0, h1, hR, hp, hc]

theorem sharp_triangular_mean (Q M N k : ℕ) (hk : N ≤ 2 ^ k) (a : Fin M → ℂ)
    (b : Fin N → ℂ) (t : Fin M → ℕ) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q
      (fun _ χ => ‖OAI.LargePrimeGaps.triangularCharacterSum a b t χ‖) ≤
      ((k : ℝ) + 1) *
        (8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) * Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2)) *
        OAI.LargePrimeGaps.sequenceSize a * OAI.LargePrimeGaps.sequenceSize b := by

  have hC : 0 ≤ 8 * Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
      Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) := by positivity
  exact sharp_triangular_mean_aux_dyadic hC Q M N k 0 a b t
    (fun a b => sharp_triangular_mean_aux_bilinear Q M N a b)
    (fun n _ => ⟨Nat.zero_le _, by simpa only [zero_add] using n.isLt.trans_le hk⟩)

theorem sharp_conductor_block_aux_block_mean (Q X U V M N k : ℕ) (hk : N ≤ 2^k)
    (p : Fin M→Prop) (r : Fin N→Prop) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q (fun _ χ=>‖OAI.LargePrimeGaps.triangularCharacterSum
      (OAI.LargePrimeGaps.sequenceMask p (OAI.LargePrimeGaps.vaughanFirstSequence V M))
      (OAI.LargePrimeGaps.sequenceMask r (OAI.LargePrimeGaps.vaughanSecondSequence U N))
      (fun m=>X/m.val+1) χ‖) ≤
      ((k:ℝ)+1)*(8 * Real.sqrt ((M:ℝ) + (Q:ℝ)^2) * Real.sqrt ((N:ℝ) + (Q:ℝ)^2))*
        Real.sqrt M*(Real.sqrt N*Real.log N) := by
  have h:=sharp_triangular_mean Q M N k hk
    (OAI.LargePrimeGaps.sequenceMask p (OAI.LargePrimeGaps.vaughanFirstSequence V M))
    (OAI.LargePrimeGaps.sequenceMask r (OAI.LargePrimeGaps.vaughanSecondSequence U N))
    (fun m=>X/m.val+1)
  apply h.trans
  have hC : 0 ≤ ((k:ℝ)+1)*(8 * Real.sqrt ((M:ℝ) + (Q:ℝ)^2) * Real.sqrt ((N:ℝ) + (Q:ℝ)^2)) := by
    positivity
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      ((OAI.LargePrimeGaps.sequenceMask_size_le _ _).trans
        (OAI.LargePrimeGaps.vaughanFirstSequence_size_le _ _)) hC
  · exact (OAI.LargePrimeGaps.sequenceMask_size_le _ _).trans
      (OAI.LargePrimeGaps.vaughanSecondSequence_size_le _ _)
  · exact OAI.LargePrimeGaps.sequenceSize_nonneg _
  · exact mul_nonneg hC (Real.sqrt_nonneg _)

theorem sharp_conductor_block_aux_hyperbolaBlock_mean (Q X U V D E k : ℕ) (hD : 0 < D)
    (hk : X/D+1 ≤ 2^k) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q (fun _ χ=>‖OAI.LargePrimeGaps.hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(OAI.LargePrimeGaps.vaughanSecondCoefficient U n:ℂ)) χ‖) ≤
      ((k:ℝ)+1)*(8 * Real.sqrt ((E:ℝ) + (Q:ℝ)^2) * Real.sqrt (((X/D+1:ℕ):ℝ) + (Q:ℝ)^2))*
        Real.sqrt E*(Real.sqrt ((X/D+1:ℕ):ℝ)*Real.log ((X/D+1:ℕ):ℝ)) := by
  have h:=sharp_conductor_block_aux_block_mean Q X U V E (X/D+1) k hk
    (fun m=>D ≤ m.val) (fun _=>True)
  have hr : OAI.LargePrimeGaps.sequenceMask (fun _ : Fin (X/D+1)=>True)
      (OAI.LargePrimeGaps.vaughanSecondSequence U (X/D+1))=
      OAI.LargePrimeGaps.vaughanSecondSequence U (X/D+1) := by
    funext n
    simp [OAI.LargePrimeGaps.sequenceMask]
  rw [hr] at h
  have he : (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖OAI.LargePrimeGaps.hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(OAI.LargePrimeGaps.vaughanSecondCoefficient U n:ℂ)) χ‖)=
      (fun (_q : Fin Q) (χ : DirichletCharacter ℂ (_q.val+1))=>‖OAI.LargePrimeGaps.triangularCharacterSum
        (OAI.LargePrimeGaps.sequenceMask (fun m:Fin E=>D ≤ m.val)
          (OAI.LargePrimeGaps.vaughanFirstSequence V E))
        (OAI.LargePrimeGaps.vaughanSecondSequence U (X/D+1)) (fun m=>X/m.val+1) χ‖) := by
    funext q χ
    rw [OAI.LargePrimeGaps.hyperbolaBlock_eq_triangle X D E hD]
    rfl
  rw [he]
  exact h

theorem sharp_conductor_block_aux_active_mean (Q X U V k : ℕ) (hk : X+1 ≤ 2^k) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q (fun _ χ=>‖OAI.LargePrimeGaps.arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-OAI.LargePrimeGaps.arithmeticCutoff V ArithmeticFunction.moebius)*
        OAI.LargePrimeGaps.vaughanSecondCoefficient U) χ‖) ≤
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        ((k:ℝ)+1)*(8 * Real.sqrt (((2^(j+1):ℕ):ℝ) + (Q:ℝ)^2) *
          Real.sqrt (((X/2^j+1:ℕ):ℝ) + (Q:ℝ)^2))*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*
            (Real.sqrt ((X/2^j+1:ℕ):ℝ)*Real.log ((X/2^j+1:ℕ):ℝ)) := by
  have h:=OAI.LargePrimeGaps.primitiveCharacterMean_mono (Q:=Q)
    (f:=fun _ χ=>‖OAI.LargePrimeGaps.arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-OAI.LargePrimeGaps.arithmeticCutoff V ArithmeticFunction.moebius)*
        OAI.LargePrimeGaps.vaughanSecondCoefficient U) χ‖)
    (g:=fun _ χ=>∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
      ‖OAI.LargePrimeGaps.hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(OAI.LargePrimeGaps.vaughanSecondCoefficient U n:ℂ)) χ‖) (fun _ χ=>by
          rw [OAI.LargePrimeGaps.vaughan_typeII_active_dyadic X U V k hk]
          exact norm_sum_le _ _)
  rw [OAI.LargePrimeGaps.primitiveCharacterMean_sum] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  exact sharp_conductor_block_aux_hyperbolaBlock_mean Q X U V (2^j) (2^(j+1)) k
    (pow_pos (by omega) _) ((Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans hk)

theorem sharp_conductor_block_aux_active_bilinear (Q X T j : ℕ)
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    (8 * Real.sqrt (((2^(j+1):ℕ):ℝ) + (Q:ℝ)^2) * Real.sqrt (((X/2^j+1:ℕ):ℝ) + (Q:ℝ)^2))*
      Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ) ≤
      32*(X:ℝ)+64*(Q:ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*(Q:ℝ)^2*Real.sqrt X := by
  obtain ⟨hmn,hmt,hnt⟩:=OAI.LargePrimeGaps.vaughan_active_dimensions X T j hleft hright
  have h : (Real.sqrt (((2^(j+1):ℕ):ℝ)+(Q:ℝ)^2)*Real.sqrt (((X/2^j+1:ℕ):ℝ)+(Q:ℝ)^2))*
      Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ) ≤
      4*(X:ℝ)+Real.sqrt ((Q:ℝ)^2)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+(Q:ℝ)^2*(2*Real.sqrt X) := by
    apply OAI.LargePrimeGaps.sqrt_bilinear_hyperbolic_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (by positivity) (sq_nonneg _)
    · exact_mod_cast hmn
    · exact_mod_cast hmt
    · exact_mod_cast hnt
  calc
    _ = 8*((Real.sqrt (((2^(j+1):ℕ):ℝ)+(Q:ℝ)^2)*Real.sqrt (((X/2^j+1:ℕ):ℝ)+(Q:ℝ)^2))*
        Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ)) := by ring
    _ ≤ 8*(4*(X:ℝ)+Real.sqrt ((Q:ℝ)^2)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        (Q:ℝ)^2*(2*Real.sqrt X)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [Real.sqrt_sq (Nat.cast_nonneg Q)]; ring

theorem sharp_conductor_block_aux_equal_cutoff_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q (fun _ χ=>‖OAI.LargePrimeGaps.arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-OAI.LargePrimeGaps.arithmeticCutoff T ArithmeticFunction.moebius)*
        OAI.LargePrimeGaps.vaughanSecondCoefficient T) χ‖) ≤
      (k:ℝ)*((k:ℝ)+1)*(32*(X:ℝ)+64*(Q:ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*(Q:ℝ)^2*Real.sqrt X)*
        Real.log (X+1:ℕ) := by
  apply (sharp_conductor_block_aux_active_mean Q X T T k hk).trans
  let K:=((k:ℝ)+1)*(32*(X:ℝ)+64*(Q:ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*(Q:ℝ)^2*Real.sqrt X)*
    Real.log (X+1:ℕ)
  have hK : 0 ≤ K := by
    have h:=OAI.LargePrimeGaps.log_nat_nonneg (X+1)
    positivity
  apply le_trans (b:=∑ _j∈(Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j),K)
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hj).2
    have hb:=sharp_conductor_block_aux_active_bilinear Q X T j hl hr
    have hlog : Real.log ((X/2^j+1:ℕ):ℝ) ≤ Real.log (X+1:ℕ) :=
      OAI.LargePrimeGaps.log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
    have hlog0 : 0 ≤ Real.log ((X/2^j+1:ℕ):ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X/2^j+1 by omega))
    calc
      _ = ((k:ℝ)+1)*((8 * Real.sqrt (((2^(j+1):ℕ):ℝ) + (Q:ℝ)^2) *
          Real.sqrt (((X/2^j+1:ℕ):ℝ) + (Q:ℝ)^2))*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ))*
            Real.log ((X/2^j+1:ℕ):ℝ) := by ring
      _ ≤ K := mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hlog hlog0
        (by positivity)
  · rw [Finset.sum_const,nsmul_eq_mul]
    have hc : (((Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j)).card:ℝ) ≤ k := by
      exact_mod_cast (Finset.card_filter_le (Finset.range k) _).trans_eq (Finset.card_range k)
    exact (mul_le_mul_of_nonneg_right hc hK).trans_eq (by dsimp [K]; ring)

theorem sharp_conductor_block_aux_finite_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    OAI.LargePrimeGaps.primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
      ‖OAI.LargePrimeGaps.arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0) ≤
      (Q:ℝ)^2*OAI.LargePrimeGaps.vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*(32*(X:ℝ)+64*(Q:ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*(Q:ℝ)^2*Real.sqrt X)*
          Real.log (X+1:ℕ) := by
  have h:=OAI.LargePrimeGaps.primitiveCharacterMean_mono_primitive (Q:=Q)
    (f:=fun q χ=>if 1 < q.val+1 then
      ‖OAI.LargePrimeGaps.arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0)
    (g:=fun _ χ=>OAI.LargePrimeGaps.vaughanShortBound Q X T+
      ‖OAI.LargePrimeGaps.arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-OAI.LargePrimeGaps.arithmeticCutoff T ArithmeticFunction.moebius)*
          OAI.LargePrimeGaps.vaughanSecondCoefficient T) χ‖) (fun q χ hχ=>by
      by_cases hq:1 < q.val+1
      · rw [ite_eq_left hq]
        exact OAI.LargePrimeGaps.primitive_vaughan_bound_uniform hq (by omega) hχ X T
      · rw [ite_eq_right hq]
        exact add_nonneg (OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _) (norm_nonneg _))
  rw [OAI.LargePrimeGaps.primitiveCharacterMean_add] at h
  exact h.trans (add_le_add (OAI.LargePrimeGaps.primitiveCharacterMean_constant_le _
    (OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _))
    (sharp_conductor_block_aux_equal_cutoff_mean Q X T k hk))

theorem sharp_conductor_block_aux_interval (Q X T k R : ℕ) (hR : 1 ≤ R)
    (hk : X+1 ≤ 2^k) :
    (R:ℝ)*(∑ d∈Finset.Ioc R Q,OAI.LargePrimeGaps.primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (Q:ℝ)^2*OAI.LargePrimeGaps.vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*(32*(X:ℝ)+64*(Q:ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*(Q:ℝ)^2*Real.sqrt X)*
          Real.log (X+1:ℕ) := by
  have hf : (Finset.Icc 1 Q).filter (fun d=>R < d)=Finset.Ioc R Q := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he : (∑ d∈Finset.Ioc R Q,OAI.LargePrimeGaps.primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))=
      ∑ q:Fin Q,if R < q.val+1 then
        OAI.LargePrimeGaps.primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ) else 0 := by
    rw [←hf,Finset.sum_filter,OAI.LargePrimeGaps.sum_Icc_one_eq_sum_fin]
  rw [he,Finset.mul_sum]
  apply le_trans (b:=OAI.LargePrimeGaps.primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
    ‖OAI.LargePrimeGaps.arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0))
  · apply Finset.sum_le_sum
    intro q _
    by_cases hq:R < q.val+1
    · have hq1:1 < q.val+1:=by omega
      simp only [ite_eq_left hq,ite_eq_left hq1]
      rw [←OAI.LargePrimeGaps.primitiveErrorMass_eq_vonMangoldt_sum X hq1]
      have hrq:(R:ℝ) ≤ q.val+1:=by exact_mod_cast hq.le
      calc
        _ ≤ ((q.val+1:ℕ):ℝ)*(OAI.LargePrimeGaps.primitiveErrorMass (X:ℝ) (q.val+1)/
            ((q.val+1).totient:ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hq.le)
            (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _))
        _ = _ := by ring
    · simp only [ite_eq_right hq,mul_zero]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro χ _
      split_ifs <;> positivity
  · exact sharp_conductor_block_aux_finite_mean Q X T k hk

theorem sharp_conductor_block_aux_doubling (Q X T D : ℕ) (hD : 1 ≤ D) (hQ : 2*D ≤ Q) :
    32*(X:ℝ)+64*((2*D:ℕ):ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+16*((2*D:ℕ):ℝ)^2*Real.sqrt X ≤
      (D:ℝ)*(32*(X:ℝ)/(D:ℝ)+128*(X:ℝ)/Real.sqrt (T+1:ℕ)+32*(Q:ℝ)*Real.sqrt X) := by
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hQr : 2*(D:ℝ) ≤ Q := by exact_mod_cast hQ
  have htail : 16*((2*D:ℕ):ℝ)^2*Real.sqrt X ≤ (D:ℝ)*(32*(Q:ℝ)*Real.sqrt X) := by
    calc
      _ = (2*(D:ℝ))*(32*(D:ℝ)*Real.sqrt X) := by push_cast; ring
      _ ≤ (Q:ℝ)*(32*(D:ℝ)*Real.sqrt X) :=
        mul_le_mul_of_nonneg_right hQr (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 32*(X:ℝ)+64*((2*D:ℕ):ℝ)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        (D:ℝ)*(32*(Q:ℝ)*Real.sqrt X) := add_le_add le_rfl htail
    _ = _ := by
      push_cast
      field_simp
      ring

theorem sharp_conductor_block (Q X T k D : ℕ) (hD : 1 ≤ D) (hQ : 2 * D ≤ Q)
    (hk : X + 1 ≤ 2 ^ k) :
    (∑ d ∈ Finset.Ioc D (2 * D),
      OAI.LargePrimeGaps.primitiveErrorMass (X : ℝ) d / (d.totient : ℝ)) ≤
      2 * (Q : ℝ) * OAI.LargePrimeGaps.vaughanShortBound Q X T +
        ((k : ℝ) * ((k : ℝ) + 1) * Real.log (X + 1 : ℕ)) *
          (32 * (X : ℝ) / (D : ℝ) + 128 * (X : ℝ) / Real.sqrt (T + 1 : ℕ) +
            32 * (Q : ℝ) * Real.sqrt (X : ℝ)) := by

  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hdq : ((2*D:ℕ):ℝ) ≤ Q := by exact_mod_cast hQ
  have hsq : (((2*D:ℕ):ℝ)^2) ≤ ((2*D:ℕ):ℝ)*(Q:ℝ) := by
    nlinarith [show (0:ℝ) ≤ ((2*D:ℕ):ℝ) from Nat.cast_nonneg _]
  have hshort : (((2*D:ℕ):ℝ)^2)*OAI.LargePrimeGaps.vaughanShortBound (2*D) X T ≤
      (D:ℝ)*(2*(Q:ℝ)*OAI.LargePrimeGaps.vaughanShortBound Q X T) := by
    calc
      _ ≤ (((2*D:ℕ):ℝ)^2)*OAI.LargePrimeGaps.vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_left (OAI.LargePrimeGaps.vaughanShortBound_mono hQ X T) (sq_nonneg _)
      _ ≤ (((2*D:ℕ):ℝ)*(Q:ℝ))*OAI.LargePrimeGaps.vaughanShortBound Q X T :=
        mul_le_mul_of_nonneg_right hsq (OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _)
      _ = _ := by push_cast; ring
  have hbilin:=sharp_conductor_block_aux_doubling Q X T D hD hQ
  have hC : 0 ≤ (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ) := by
    have h:=OAI.LargePrimeGaps.log_nat_nonneg (X+1)
    positivity
  have h:=(sharp_conductor_block_aux_interval (2*D) X T k D hD hk).trans
    (add_le_add hshort (by
      convert mul_le_mul_of_nonneg_left hbilin hC using 1
      ring))
  apply (mul_le_mul_iff_right₀ hDr).mp
  calc
    _ = (D:ℝ)*(∑ d ∈ Finset.Ioc D (2 * D),
        OAI.LargePrimeGaps.primitiveErrorMass (X : ℝ) d / (d.totient : ℝ)) := by ring
    _ ≤ (D:ℝ)*(2*(Q:ℝ)*OAI.LargePrimeGaps.vaughanShortBound Q X T)+
        (k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ)*
          ((D:ℝ)*(32*(X:ℝ)/(D:ℝ)+128*(X:ℝ)/Real.sqrt (T+1:ℕ)+32*(Q:ℝ)*Real.sqrt X)) := h
    _ = _ := by field_simp

theorem sharp_conductor_weight_aux_harmonic_sq (n : ℕ) :
    ((harmonic n : ℝ)) ^ 2 ≤ (1 + Real.log (n : ℝ)) ^ 2 := by
  have h0 : (0 : ℝ) ≤ (harmonic n : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hle : (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) := harmonic_le_one_add_log n
  nlinarith

theorem sharp_conductor_weight_aux_main (Y : ℝ) (lo hi : ℕ) :
    (∑ q ∈ Finset.Ioc lo hi,
        (∑ f ∈ q.divisors, OAI.LargePrimeGaps.primitiveErrorMass Y f) / (q.totient : ℝ)) ≤
      ∑ f ∈ Finset.Icc 1 hi,
        OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ) *
          (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2 := by
  classical
  let s := (Finset.Ioc lo hi).sigma fun q => q.divisors
  let t := (Finset.Icc 1 hi).sigma fun f => Finset.Icc 1 (hi / f)
  let e : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.2, x.1 / x.2⟩
  have he_mem : ∀ x ∈ s, e x ∈ t := by
    rintro ⟨q, f⟩ hx
    obtain ⟨hq, hf⟩ := Finset.mem_sigma.mp hx
    dsimp only at hq hf
    obtain ⟨hlo, hqhi⟩ := Finset.mem_Ioc.mp hq
    obtain ⟨hdq, hq0⟩ := Nat.mem_divisors.mp hf
    have hqpos : 0 < q := by omega
    have hf0 : 0 < f := Nat.pos_of_dvd_of_pos hdq hqpos
    have hfle : f ≤ q := Nat.le_of_dvd hqpos hdq
    have hdivpos : 0 < q / f := Nat.div_pos hfle hf0
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hf0, hfle.trans hqhi⟩,
      Finset.mem_Icc.mpr ⟨hdivpos, Nat.div_le_div_right hqhi⟩⟩
  have he_inj : Set.InjOn e s := by
    rintro ⟨q, f⟩ hx ⟨q', f'⟩ hy he
    obtain ⟨hq, hf⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq', hf'⟩ := Finset.mem_sigma.mp hy
    dsimp only at hq hf hq' hf'
    have hed : f = f' := congrArg Sigma.fst he
    have heq : q / f = q' / f' := congrArg Sigma.snd he
    have hdq : f ∣ q := (Nat.mem_divisors.mp hf).1
    have hdq' : f' ∣ q' := (Nat.mem_divisors.mp hf').1
    have hqq : q = q' := by
      rw [← Nat.div_mul_cancel hdq, ← Nat.div_mul_cancel hdq', heq, hed]
    subst f'
    subst q'
    rfl
  have hsum : (∑ q ∈ Finset.Ioc lo hi,
        (∑ f ∈ q.divisors, OAI.LargePrimeGaps.primitiveErrorMass Y f) / (q.totient : ℝ)) ≤
      ∑ x ∈ s, OAI.LargePrimeGaps.primitiveErrorMass Y (e x).1 /
        ((e x).1.totient : ℝ) / ((e x).2.totient : ℝ) := by
    dsimp only [s]
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro f hf
    have hdq := (Nat.mem_divisors.mp hf).1
    have hq0 : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
    have hd0 : 0 < f := Nat.pos_of_dvd_of_pos hdq hq0
    have hk0 : 0 < q / f := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
    have ht : (f.totient : ℝ) * (q / f).totient ≤ (q.totient : ℝ) := by
      have hh := Nat.totient_super_multiplicative f (q / f)
      rw [Nat.mul_div_cancel' hdq] at hh
      exact_mod_cast hh
    dsimp only [e]
    rw [div_div]
    exact div_le_div_of_nonneg_left (OAI.LargePrimeGaps.primitiveErrorMass_nonneg Y f)
      (mul_pos (by exact_mod_cast Nat.totient_pos.mpr hd0)
        (by exact_mod_cast Nat.totient_pos.mpr hk0)) ht
  calc
    _ ≤ ∑ x ∈ s, OAI.LargePrimeGaps.primitiveErrorMass Y (e x).1 /
          ((e x).1.totient : ℝ) / ((e x).2.totient : ℝ) := hsum
    _ = ∑ x ∈ s.image e, OAI.LargePrimeGaps.primitiveErrorMass Y x.1 /
          (x.1.totient : ℝ) / (x.2.totient : ℝ) := by
      rw [Finset.sum_image he_inj]
    _ ≤ ∑ x ∈ t, OAI.LargePrimeGaps.primitiveErrorMass Y x.1 /
          (x.1.totient : ℝ) / (x.2.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr he_mem)
        (fun x _ _ => div_nonneg
          (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg Y x.1) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _))
    _ = ∑ f ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ)) *
          (∑ m ∈ Finset.Icc 1 (hi / f), (1 : ℝ) / (m.totient : ℝ)) := by
      dsimp only [t]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro f _
      dsimp only
      simp only [div_eq_mul_inv, one_mul]
      rw [← Finset.mul_sum]
    _ ≤ ∑ f ∈ Finset.Icc 1 hi, OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ) *
          (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro f _
      refine mul_le_mul_of_nonneg_left ?_
        (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg Y f) (Nat.cast_nonneg _))
      exact (OAI.LargePrimeGaps.sum_totient_reciprocal_le (hi / f)).trans
        (sharp_conductor_weight_aux_harmonic_sq (hi / f))

theorem sharp_conductor_weight (Y : ℝ) (lo hi : ℕ) :
    (∑ d ∈ Finset.Ioc lo hi, (OAI.LargePrimeGaps.endpointError Y d : ℝ)) ≤
      (∑ f ∈ Finset.Icc 1 hi,
        OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ) *
          (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2) +
      (hi : ℝ) * (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (hi : ℝ) := by
  have hmain := sharp_conductor_weight_aux_main Y lo hi
  have hlog : (0 : ℝ) ≤ Real.log (hi : ℝ) := by
    rcases Nat.eq_zero_or_pos hi with rfl | hhi
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hhi)
  have hcard : ((Finset.Ioc lo hi).card : ℝ) ≤ (hi : ℝ) := by
    have hsub : Finset.Ioc lo hi ⊆ Finset.Icc 1 hi := by
      intro d hd
      have hd' := Finset.mem_Ioc.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega, hd'.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (Finset.Icc 1 hi).card = hi := by
      rw [Nat.card_Icc]; omega
    exact_mod_cast (h1.trans_eq h2)
  calc
    (∑ d ∈ Finset.Ioc lo hi, (OAI.LargePrimeGaps.endpointError Y d : ℝ))
      ≤ ∑ d ∈ Finset.Ioc lo hi,
          ((∑ f ∈ d.divisors, OAI.LargePrimeGaps.primitiveErrorMass Y f) / (d.totient : ℝ) +
            (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact OAI.LargePrimeGaps.endpointError_le_primitive_conductors Y
          (by have := (Finset.mem_Ioc.mp hd).1; omega)
    _ = (∑ d ∈ Finset.Ioc lo hi,
          (∑ f ∈ d.divisors, OAI.LargePrimeGaps.primitiveErrorMass Y f) / (d.totient : ℝ)) +
        ∑ d ∈ Finset.Ioc lo hi, (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (d : ℝ) :=
      Finset.sum_add_distrib
    _ ≤ (∑ f ∈ Finset.Icc 1 hi,
          OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ) *
            (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2) +
        (hi : ℝ) * (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (hi : ℝ) := add_le_add hmain (by
        calc
          (∑ d ∈ Finset.Ioc lo hi, (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (d : ℝ))
            ≤ ∑ _d ∈ Finset.Ioc lo hi, (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (hi : ℝ) := by
              apply Finset.sum_le_sum
              intro d hd
              have hd' := Finset.mem_Ioc.mp hd
              exact mul_le_mul_of_nonneg_left
                (Real.log_le_log (by exact_mod_cast (by omega : 0 < d))
                  (by exact_mod_cast hd'.2))
                (Nat.cast_nonneg _)
          _ = ((Finset.Ioc lo hi).card : ℝ) * (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (hi : ℝ) := by
              simp [mul_assoc]
          _ ≤ (hi : ℝ) * (Nat.log 2 ⌊Y⌋₊ : ℝ) * Real.log (hi : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)) hlog)

theorem small_conductor_mass_aux_div_le {x M : ℝ} (hM : 0 ≤ M) {d : ℕ} (hd : 0 < d)
    (h : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      ‖OAI.LargePrimeGaps.primeCharacterError x χ‖ ≤ M) :
    OAI.LargePrimeGaps.primitiveErrorMass x d / (d.totient : ℝ) ≤ M := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hphi : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hcard : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  apply (div_le_iff₀ hphi).mpr
  calc
    _ ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive, M := by
      exact Finset.sum_le_sum (fun χ hχ => h χ (Finset.mem_filter.mp hχ).2)
    _ ≤ ∑ _χ : DirichletCharacter ℂ d, M :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp [hcard, mul_comm]

theorem small_conductor_mass_aux_sum_le {x M : ℝ} (hM : 0 ≤ M) (R : ℕ)
    (h : ∀ d : ℕ, 0 < d → d ≤ R → ∀ χ : DirichletCharacter ℂ d,
      χ.IsPrimitive → ‖OAI.LargePrimeGaps.primeCharacterError x χ‖ ≤ M) :
    (∑ d ∈ Finset.Icc 1 R,
      OAI.LargePrimeGaps.primitiveErrorMass x d / (d.totient : ℝ)) ≤ (R : ℝ) * M := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 R, M := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd0, hdR⟩ := Finset.mem_Icc.mp hd
      exact small_conductor_mass_aux_div_le hM (by omega) (h d (by omega) hdR)
    _ = _ := by simp

theorem small_conductor_mass :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ Y : ℝ in atTop, ∀ R : ℕ, (R : ℝ) ≤ (Real.log Y) ^ (8 : ℕ) →
      (∑ f ∈ Finset.Icc 1 R,
        OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ)) ≤
        M * Y * (Real.log Y) ^ (-(12 : ℝ)) * (R : ℝ) := by
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ :=
    OAI.LargePrimeGaps.siegelWalfisz 12 8 (by norm_num) (by norm_num)
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_ge_atTop x₀] with Y hY
  intro R hR
  have hY1 : 1 < Y := lt_of_lt_of_le hx₀ hY
  have hlog0 : 0 < Real.log Y := Real.log_pos hY1
  have hnonneg : 0 ≤ M * Y * (Real.log Y) ^ (-(12 : ℝ)) := by positivity
  have hsum : (∑ f ∈ Finset.Icc 1 R,
        OAI.LargePrimeGaps.primitiveErrorMass Y f / (f.totient : ℝ)) ≤
      (R : ℝ) * (M * Y * (Real.log Y) ^ (-(12 : ℝ))) := by
    refine small_conductor_mass_aux_sum_le hnonneg R ?_
    intro d hd hdR χ hχ
    apply hSW Y hY d hd ?_ χ hχ
    calc
      (d : ℝ) ≤ (R : ℝ) := by exact_mod_cast hdR
      _ ≤ (Real.log Y) ^ (8 : ℕ) := hR
      _ = (Real.log Y) ^ (8 : ℝ) := (Real.rpow_natCast _ _).symm
  calc
    _ ≤ (R : ℝ) * (M * Y * (Real.log Y) ^ (-(12 : ℝ))) := hsum
    _ = _ := by ring

lemma sharp_bv_band_aux_nat_log_le (x : ℕ) (hx : 1 ≤ x) :
    (Nat.log 2 x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  have h1 : (2 : ℝ) ^ Nat.log 2 x ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : Real.log ((2 : ℝ) ^ Nat.log 2 x) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have h3 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : (0 : ℝ) ≤ (Nat.log 2 x : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma sharp_bv_band_aux_geom (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ (j + 1)) ≤ 22 * (2 : ℝ) ^ n := by
  have htel : ∀ m : ℕ, (∑ j ∈ Finset.range m, ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) =
      22 - (2 * (m : ℝ) ^ 2 + 12 * (m : ℝ) + 22) * (1 / 2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : (1 / 2 : ℝ) ^ (m + 1) = (1 / 2 : ℝ) ^ m * (1 / 2) := pow_succ _ _
      rw [h2]
      push_cast
      ring
  have h1 : (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) ≤ 22 := by
    rw [htel n]
    have : 0 ≤ (2 * (n : ℝ) ^ 2 + 12 * (n : ℝ) + 22) * (1 / 2 : ℝ) ^ n := by positivity
    linarith
  have hrew : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ (j + 1)) =
      (2 : ℝ) ^ n * (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    rw [Finset.mul_sum,
      ← Finset.sum_range_reflect (fun j => (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ (j + 1)) n]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < n := Finset.mem_range.mp hj
    have e1 : n - (n - 1 - j) = j + 1 := by omega
    have e2 : n - 1 - j + 1 = n - j := by omega
    rw [e1, e2]
    have e3 : (2 : ℝ) ^ (n - j) = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ j := by
      have h : (2 : ℝ) ^ (n - j) * (2 : ℝ) ^ j = (2 : ℝ) ^ n := by
        rw [← pow_add]; congr 1; omega
      have h2 : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
        rw [← mul_pow]; norm_num
      calc (2 : ℝ) ^ (n - j) = (2 : ℝ) ^ (n - j) * ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) := by rw [h2, mul_one]
        _ = ((2 : ℝ) ^ (n - j) * (2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j := by ring
        _ = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ j := by rw [h]
    rw [e3]
    push_cast
    ring
  rw [hrew]
  nlinarith [h1, pow_pos (by norm_num : (0 : ℝ) < 2) n]

set_option maxHeartbeats 2000000 in

theorem sharp_bv_band : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ Y : ℕ, X ≤ Y → Y ≤ 2 * X → ∀ hi : ℕ, hi ≤ bpD X →
      (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ)) ≤
        C * (Y : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
  obtain ⟨M, hMpos, hM⟩ := small_conductor_mass
  have hlogY : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (40 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    OAI.LargePrimeGaps.eventually_log_rpow_le_rpow 40 (by norm_num)
  have hM' : ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, X ≤ Y → ∀ R : ℕ,
      (R : ℝ) ≤ (Real.log (Y : ℝ)) ^ (8 : ℕ) →
      (∑ f ∈ Finset.Icc 1 R, OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ)) ≤
        M * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (-(12 : ℝ)) * (R : ℝ) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hM
    filter_upwards [eventually_ge_atTop ⌈N⌉₊] with X hX Y hXY R hR
    exact hN (Y : ℝ) (le_trans (Nat.le_ceil N) (by exact_mod_cast le_trans hX hXY)) R hR
  have hlogY' : ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, X ≤ Y →
      (Real.log (Y : ℝ)) ^ (40 : ℝ) ≤ (Y : ℝ) ^ (1 / 4 : ℝ) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hlogY
    filter_upwards [eventually_ge_atTop ⌈N⌉₊] with X hX Y hXY
    exact hN (Y : ℝ) (le_trans (Nat.le_ceil N) (by exact_mod_cast le_trans hX hXY))
  refine ⟨10 ^ 31 * (1 + M), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ 40), hM', hlogY'] with X hX hM hlog
  intro Y hXY hY2X hi hhi
  set L : ℝ := Real.log (2 + (X : ℝ)) with hLdef
  set LY : ℝ := Real.log (Y : ℝ) with hLYdef
  set R : ℕ := ⌊LY ^ (8 : ℕ)⌋₊ with hRdef
  set T : ℕ := ⌊L ^ (20 : ℕ)⌋₊ with hTdef
  set k : ℕ := Nat.log 2 (Y + 1) + 1 with hkdef
  set kfac : ℝ := (k : ℝ) * ((k : ℝ) + 1) * Real.log (Y + 1 : ℕ) with hkfacdef
  set qY : ℝ := (Y : ℝ) ^ (1 / 4 : ℝ) with hqYdef
  set G : ℕ → ℝ := fun f => OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ) *
      (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2 with hGdef

  have hX1n : 1 ≤ X := by omega
  have hY1n : 1 ≤ Y := le_trans hX1n hXY
  have hX1 : (1 : ℝ) ≤ X := Nat.cast_le.mpr hX1n
  have hY1 : (1 : ℝ) ≤ Y := Nat.cast_le.mpr hY1n
  have hXpos : (0 : ℝ) < X := by linarith
  have hYpos : (0 : ℝ) < Y := by linarith
  have hXpow : (2 : ℝ) ^ 40 ≤ (X : ℝ) := by exact_mod_cast hX
  have hL10 : 10 ≤ L := by
    have h1 : (2 : ℝ) ^ 40 ≤ 2 + (X : ℝ) := le_trans hXpow (by linarith)
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, ← hLdef] at h2
    push_cast at h2
    nlinarith [Real.log_two_gt_d9]
  have hLY10 : 10 ≤ LY := by
    have h1 : (2 : ℝ) ^ 40 ≤ (Y : ℝ) := by exact_mod_cast le_trans hX hXY
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, ← hLYdef] at h2
    push_cast at h2
    nlinarith [Real.log_two_gt_d9]
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := by linarith
  have hLY1 : 1 ≤ LY := by linarith
  have hLY0 : 0 < LY := by linarith
  have hLYL : LY ≤ L + 1 := by
    have h1 : (Y : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hY2X
    have h2 := Real.log_le_log hYpos h1
    rw [Real.log_mul (by norm_num) hXpos.ne', ← hLYdef] at h2
    have h3 := Real.log_le_log hXpos (by linarith : (X : ℝ) ≤ 2 + (X : ℝ))
    have h4 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    rw [← hLdef] at h3
    linarith
  have hLle : L ≤ LY + 1 := by
    have h1 : (2 : ℝ) + (X : ℝ) ≤ 2 * (Y : ℝ) := by
      have : (X : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hXY
      linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) hYpos.ne', ← hLdef] at h2
    have h4 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    rw [← hLYdef] at h2
    linarith
  have hLYhalf : L / 2 ≤ LY := by linarith
  have hLY2L : LY ≤ 2 * L := by linarith
  have hL2LY : L ≤ 2 * LY := by linarith

  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact Nat.floor_pos.mpr (one_le_pow₀ hLY1)
  have hRpos : 0 < R := by omega
  have hRle : (R : ℝ) ≤ LY ^ (8 : ℕ) := by rw [hRdef]; exact Nat.floor_le (by positivity)
  have hRge : LY ^ (8 : ℕ) / 2 ≤ (R : ℝ) := by
    have h1 := Nat.lt_floor_add_one (LY ^ (8 : ℕ))
    have h2 : (2 : ℝ) ≤ LY ^ (8 : ℕ) := le_trans (by norm_num)
      (le_trans (pow_le_pow_left₀ (by norm_num) hLY10 8) (by norm_num))
    rw [hRdef]
    linarith
  have hRge8 : L ^ (8 : ℕ) / 512 ≤ (R : ℝ) := by
    have h2 : L ^ (8 : ℕ) / 512 ≤ LY ^ (8 : ℕ) / 2 := by
      have h3 : (L / 2) ^ (8 : ℕ) ≤ LY ^ (8 : ℕ) := pow_le_pow_left₀ (by linarith) hLYhalf 8
      have h4 : (L / 2) ^ (8 : ℕ) = L ^ (8 : ℕ) / 256 := by ring
      linarith
    linarith

  have hTle : (T : ℝ) ≤ L ^ (20 : ℕ) := by rw [hTdef]; exact Nat.floor_le (by positivity)
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Nat.floor_pos.mpr (one_le_pow₀ hL1)
  have hTsq : L ^ (10 : ℕ) ≤ Real.sqrt ((T + 1 : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (L ^ (20 : ℕ))
    have h2 : L ^ (20 : ℕ) ≤ (T : ℝ) + 1 := by rw [hTdef]; linarith
    have h3 : L ^ (20 : ℕ) = (L ^ (10 : ℕ)) ^ 2 := by ring
    calc L ^ (10 : ℕ) = Real.sqrt ((L ^ (10 : ℕ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (L ^ (20 : ℕ)) := by rw [h3]
      _ ≤ Real.sqrt ((T : ℝ) + 1) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt ((T + 1 : ℕ) : ℝ) := by push_cast; rfl

  have hkpow : Y + 1 ≤ 2 ^ k := by
    have h1 : Nat.log 2 (Y + 1) < Nat.log 2 (Y + 1) + 1 := Nat.lt_succ_self _
    have h2 := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega : Y + 1 ≠ 0)).mp h1
    rw [hkdef]; omega
  have hlogY1 : Real.log ((Y + 1 : ℕ) : ℝ) ≤ L + 2 := by
    have h3 : ((Y + 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by push_cast; linarith
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_mul (by norm_num) hYpos.ne', ← hLYdef] at h4
    have h5 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hk_le : (k : ℝ) ≤ 3 * L := by
    have h1 : (Nat.log 2 (Y + 1) : ℝ) ≤ 2 * Real.log ((Y + 1 : ℕ) : ℝ) :=
      sharp_bv_band_aux_nat_log_le (Y + 1) (by omega)
    rw [hkdef]; push_cast
    linarith
  have hlogY2L : Real.log ((Y + 1 : ℕ) : ℝ) ≤ 2 * L := by linarith
  have hkfac : kfac ≤ 24 * L ^ 3 := by
    have h1 : (k : ℝ) + 1 ≤ 4 * L := by linarith
    have h2 : (k : ℝ) * ((k : ℝ) + 1) ≤ 12 * L ^ 2 := by nlinarith
    rw [hkfacdef]
    calc (k : ℝ) * ((k : ℝ) + 1) * Real.log ((Y + 1 : ℕ) : ℝ)
        ≤ (12 * L ^ 2) * (2 * L) := mul_le_mul h2 hlogY2L (by positivity) (by positivity)
      _ = 24 * L ^ 3 := by ring
  have hkfac0 : 0 ≤ kfac := by
    rw [hkfacdef]
    have : 0 ≤ Real.log ((Y + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y + 1))
    positivity

  have hqY1 : 1 ≤ qY := by rw [hqYdef]; exact Real.one_le_rpow hY1 (by norm_num)
  have hqY0 : 0 ≤ qY := by linarith
  have hqY2 : qY ^ 2 = Real.sqrt (Y : ℝ) := by
    rw [hqYdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((Y : ℝ) ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul hYpos.le]
    norm_num
  have hqY4 : qY ^ 4 = (Y : ℝ) := by
    calc qY ^ 4 = (qY ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (Y : ℝ)) ^ 2 := by rw [hqY2]
      _ = (Y : ℝ) := Real.sq_sqrt hYpos.le

  have hhiD : (hi : ℝ) ≤ Real.sqrt (X : ℝ) / L ^ 5 := by
    have h1 : (hi : ℝ) ≤ (bpD X : ℝ) := by exact_mod_cast hhi
    have h2 : (bpD X : ℝ) ≤ Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ) :=
      Nat.floor_le (by positivity)
    rw [← hLdef] at h2
    exact le_trans h1 h2
  have hhiY : (hi : ℝ) ≤ Real.sqrt (Y : ℝ) / L ^ 5 := by
    have h1 : Real.sqrt (X : ℝ) ≤ Real.sqrt (Y : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hXY)
    exact le_trans hhiD (div_le_div_of_nonneg_right h1 (by positivity))
  have hhiX : (hi : ℝ) ≤ (X : ℝ) := by
    have h1 : Real.sqrt (X : ℝ) / L ^ 5 ≤ Real.sqrt (X : ℝ) :=
      div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)
    have h2 : Real.sqrt (X : ℝ) ≤ (X : ℝ) := Real.sqrt_le_iff.mpr ⟨hXpos.le, by nlinarith⟩
    exact le_trans (le_trans hhiD h1) h2
  have hG0 : ∀ f : ℕ, 0 ≤ G f := fun f => mul_nonneg
    (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _)) (sq_nonneg _)

  have hmain : (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ)) ≤
      (∑ f ∈ Finset.Icc 1 hi, G f) + (hi : ℝ) * (Nat.log 2 ⌊(Y : ℝ)⌋₊ : ℝ) * Real.log (hi : ℝ) := by
    have hw := sharp_conductor_weight (Y : ℝ) 0 hi
    have hIoc : Finset.Ioc (0 : ℕ) hi = Finset.Icc 1 hi := by
      ext d; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc] at hw
    exact hw
  rcases Nat.eq_zero_or_pos hi with rfl | hhi1
  · have hz : (∑ d ∈ Finset.Icc 1 0, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ)) = 0 := by
      rw [Finset.Icc_eq_empty_iff.mpr (by omega), Finset.sum_empty]
    rw [hz]
    exact div_nonneg (by positivity) (mul_nonneg hL0.le (Real.sqrt_nonneg _))
  ·
    have hvSB : OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T ≤ 372 * qY * L ^ 42 := by
      have h2hi1 : (1 : ℕ) ≤ 2 * hi := by omega
      have hlog2hi0 : 0 ≤ Real.log ((2 * hi : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast h2hi1)
      have hK : Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)) ≤ 8 * qY * L := by
        have hQ : ((2 * hi : ℕ) : ℝ) ≤ 2 * Real.sqrt (Y : ℝ) := by
          have h1 : Real.sqrt (Y : ℝ) / L ^ 5 ≤ Real.sqrt (Y : ℝ) :=
            div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)
          calc ((2 * hi : ℕ) : ℝ) = 2 * (hi : ℝ) := by push_cast; ring
            _ ≤ 2 * (Real.sqrt (Y : ℝ) / L ^ 5) := mul_le_mul_of_nonneg_left hhiY (by norm_num)
            _ ≤ 2 * Real.sqrt (Y : ℝ) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        have hsqrtq : Real.sqrt (Real.sqrt (Y : ℝ)) = qY := by
          rw [hqYdef, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hYpos.le]
          norm_num
        have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
        have h1 : Real.sqrt ((2 * hi : ℕ) : ℝ) ≤ 2 * qY := by
          calc Real.sqrt ((2 * hi : ℕ) : ℝ) ≤ Real.sqrt (2 * Real.sqrt (Y : ℝ)) := Real.sqrt_le_sqrt hQ
            _ = Real.sqrt 2 * Real.sqrt (Real.sqrt (Y : ℝ)) :=
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt (Y : ℝ))
            _ = Real.sqrt 2 * qY := by rw [hsqrtq]
            _ ≤ 2 * qY := mul_le_mul_of_nonneg_right hs2 hqY0
        have h2 : 1 + Real.log ((2 * hi : ℕ) : ℝ) ≤ 4 * L := by
          have h3 : Real.log ((2 * hi : ℕ) : ℝ) ≤ Real.log (2 * Real.sqrt (Y : ℝ)) :=
            Real.log_le_log (by positivity) hQ
          rw [Real.log_mul (by norm_num) (by positivity)] at h3
          have h4 : Real.log (Real.sqrt (Y : ℝ)) = LY / 2 := by
            rw [Real.sqrt_eq_rpow, Real.log_rpow hYpos, ← hLYdef]; ring
          rw [h4] at h3
          have h5 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
          linarith
        calc Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ))
          ≤ (2 * qY) * (4 * L) := mul_le_mul h1 h2 (by linarith) (by positivity)
          _ = 8 * qY * L := by ring
      have hTlog : Real.log (T : ℝ) ≤ 20 * L := by
        have h := Real.log_le_log (by exact_mod_cast hT1) hTle
        rw [Real.log_pow, Nat.cast_ofNat] at h
        have h2 := Real.log_lt_sub_one_of_pos hL0 (by linarith : L ≠ 1)
        linarith
      have hTT : ((T * T : ℕ) : ℝ) ≤ L ^ (40 : ℕ) := by
        have h4 : ((T * T : ℕ) : ℝ) = (T : ℝ) * (T : ℝ) := by push_cast; ring
        have h5 : (T : ℝ) * (T : ℝ) ≤ L ^ (20 : ℕ) * L ^ (20 : ℕ) :=
          mul_le_mul hTle hTle (Nat.cast_nonneg _) (by positivity)
        calc ((T * T : ℕ) : ℝ) = (T : ℝ) * (T : ℝ) := h4
          _ ≤ L ^ (20 : ℕ) * L ^ (20 : ℕ) := h5
          _ = L ^ (40 : ℕ) := by ring
      have hTT1 : (1 : ℕ) ≤ T * T := le_trans (by norm_num) (Nat.mul_le_mul hT1 hT1)
      have hTTlog : Real.log ((T * T : ℕ) : ℝ) ≤ 40 * L := by
        have h1 : (1 : ℝ) ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast hTT1
        have h := Real.log_le_log (by linarith) hTT
        rw [Real.log_pow, Nat.cast_ofNat] at h
        have h2 := Real.log_lt_sub_one_of_pos hL0 (by linarith : L ≠ 1)
        linarith
      have hK0 : 0 ≤ Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)) :=
        mul_nonneg (Real.sqrt_nonneg _) (by linarith [hlog2hi0])
      have hv : OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T =
          (T : ℝ) * Real.log (T : ℝ) + (T : ℝ) * (2 * Real.log ((Y + 1 : ℕ) : ℝ) *
            (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)))) +
            ((T * T : ℕ) : ℝ) * Real.log ((T * T : ℕ) : ℝ) *
              (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ))) := by
        unfold OAI.LargePrimeGaps.vaughanShortBound; rfl
      have e1 : (T : ℝ) * Real.log (T : ℝ) ≤ L ^ (20 : ℕ) * (20 * L) :=
        mul_le_mul hTle hTlog (Real.log_nonneg (by exact_mod_cast hT1)) (by positivity)
      have e2 : (T : ℝ) * (2 * Real.log ((Y + 1 : ℕ) : ℝ) *
            (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)))) ≤
          L ^ (20 : ℕ) * (2 * (2 * L) * (8 * qY * L)) :=
        mul_le_mul hTle
          (mul_le_mul (mul_le_mul (le_refl (2 : ℝ)) hlogY2L (by positivity) (by positivity))
            hK (by positivity) (by positivity))
          (by positivity) (by positivity)
      have e3 : ((T * T : ℕ) : ℝ) * Real.log ((T * T : ℕ) : ℝ) *
            (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ))) ≤
          L ^ (40 : ℕ) * (40 * L) * (8 * qY * L) :=
        mul_le_mul
          (mul_le_mul hTT hTTlog (Real.log_nonneg (by exact_mod_cast hTT1)) (by positivity))
          hK hK0 (by positivity)
      rw [hv]
      calc (T : ℝ) * Real.log (T : ℝ) + (T : ℝ) * (2 * Real.log ((Y + 1 : ℕ) : ℝ) *
            (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)))) +
            ((T * T : ℕ) : ℝ) * Real.log ((T * T : ℕ) : ℝ) *
              (Real.sqrt ((2 * hi : ℕ) : ℝ) * (1 + Real.log ((2 * hi : ℕ) : ℝ)))
        ≤ L ^ (20 : ℕ) * (20 * L) + L ^ (20 : ℕ) * (2 * (2 * L) * (8 * qY * L)) +
            L ^ (40 : ℕ) * (40 * L) * (8 * qY * L) := add_le_add (add_le_add e1 e2) e3
        _ = 20 * L ^ (21 : ℕ) + 32 * qY * L ^ (22 : ℕ) + 320 * qY * L ^ (42 : ℕ) := by ring
        _ ≤ 372 * qY * L ^ (42 : ℕ) := by
          have f1 : L ^ (21 : ℕ) ≤ L ^ (42 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
          have f2 : L ^ (22 : ℕ) ≤ L ^ (42 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
          have g1 : L ^ (21 : ℕ) ≤ qY * L ^ (42 : ℕ) := by
            calc L ^ (21 : ℕ) ≤ L ^ (42 : ℕ) := f1
              _ = 1 * L ^ (42 : ℕ) := by ring
              _ ≤ qY * L ^ (42 : ℕ) := mul_le_mul_of_nonneg_right hqY1 (by positivity)
          have g2 : qY * L ^ (22 : ℕ) ≤ qY * L ^ (42 : ℕ) :=
            mul_le_mul_of_nonneg_left f2 hqY0
          linarith
    set m : ℕ := min hi R with hmdef
    have hmhi : m ≤ hi := min_le_left hi R
    have hmR : m ≤ R := min_le_right hi R
    have hm1 : 1 ≤ m := le_min hhi1 hR1
    have hIcc : Finset.Icc 1 hi = Finset.Icc 1 m ∪ Finset.Ioc m hi := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioc m hi) := by
      rw [Finset.disjoint_left]; intro a ha hb
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha hb; omega
    have hsplit : (∑ f ∈ Finset.Icc 1 hi, G f) =
        (∑ f ∈ Finset.Icc 1 m, G f) + (∑ f ∈ Finset.Ioc m hi, G f) := by
      rw [hIcc, Finset.sum_union hdisj]

    have hsmall : (∑ f ∈ Finset.Icc 1 m, G f) ≤
        (1 + Real.log (hi : ℝ)) ^ 2 * (∑ f ∈ Finset.Icc 1 m,
          OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun f hf => ?_)
      rw [Finset.mem_Icc] at hf
      have hfh : (hi / f : ℕ) ≤ hi := Nat.div_le_self hi f
      have hw : (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log (hi : ℝ)) ^ 2 := by
        rcases Nat.eq_zero_or_pos (hi / f) with h0 | h0
        · rw [h0]
          have hlog0 : 0 ≤ Real.log (hi : ℝ) := Real.log_nonneg (by exact_mod_cast hhi1)
          calc (1 + Real.log ((0 : ℕ) : ℝ)) ^ 2 = (1 : ℝ) ^ 2 := by norm_num
            _ ≤ (1 + Real.log (hi : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by linarith) 2
        · have h := Real.log_le_log (Nat.cast_pos.mpr h0) (Nat.cast_le.mpr hfh)
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      rw [hGdef]
      exact le_trans (mul_le_mul_of_nonneg_left hw
        (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _)))
        (le_of_eq (mul_comm _ _))
    have hsmall2 : (∑ f ∈ Finset.Icc 1 m, OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f /
        (f.totient : ℝ)) ≤ M * (Y : ℝ) * LY ^ (-(12 : ℝ)) * (R : ℝ) := by
      have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 R := Finset.Icc_subset_Icc_right hmR
      have h1 : (∑ f ∈ Finset.Icc 1 m, OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f /
          (f.totient : ℝ)) ≤ ∑ f ∈ Finset.Icc 1 R,
          OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun f _ _ => div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg (Y : ℝ) f)
            (Nat.cast_nonneg (α := ℝ) f.totient))
      exact le_trans h1 (hM Y hXY R hRle)
    have hloghi : Real.log (hi : ℝ) ≤ L := by
      have h1 : (hi : ℝ) ≤ 2 + (X : ℝ) := le_trans hhiX (by linarith)
      have h2 := Real.log_le_log (by exact_mod_cast hhi1) h1
      rw [← hLdef] at h2
      exact h2
    have hsmall_fin : (∑ f ∈ Finset.Icc 1 m, G f) ≤ (64 * M) * ((Y : ℝ) / L ^ 2) := by
      have hw : (1 + Real.log (hi : ℝ)) ^ 2 ≤ 4 * L ^ 2 := by
        have h1 : 0 ≤ 1 + Real.log (hi : ℝ) := by
          linarith [Real.log_nonneg (by exact_mod_cast hhi1 : (1 : ℝ) ≤ (hi : ℝ))]
        have h2 : 1 + Real.log (hi : ℝ) ≤ 2 * L := by linarith
        calc (1 + Real.log (hi : ℝ)) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ h1 h2 2
          _ = 4 * L ^ 2 := by ring
      have hLYneg : LY ^ (-(12 : ℝ)) * LY ^ (8 : ℕ) = (LY ^ (4 : ℕ))⁻¹ := by
        calc LY ^ (-(12 : ℝ)) * LY ^ (8 : ℕ) = LY ^ (-(12 : ℝ)) * LY ^ ((8 : ℕ) : ℝ) := by
              rw [Real.rpow_natCast]
          _ = LY ^ ((-(12 : ℝ)) + ((8 : ℕ) : ℝ)) := (Real.rpow_add hLY0 _ _).symm
          _ = LY ^ (-((4 : ℕ) : ℝ)) := by norm_num
          _ = (LY ^ ((4 : ℕ) : ℝ))⁻¹ := Real.rpow_neg hLY0.le ((4 : ℕ) : ℝ)
          _ = (LY ^ (4 : ℕ))⁻¹ := by rw [Real.rpow_natCast]
      have hLY4 : (LY ^ (4 : ℕ))⁻¹ ≤ 16 / L ^ 4 := by
        have h1 : (L / 2) ^ (4 : ℕ) ≤ LY ^ (4 : ℕ) := pow_le_pow_left₀ (by linarith) hLYhalf 4
        have h2 : 0 < (L / 2) ^ (4 : ℕ) := by positivity
        have h3 : (LY ^ (4 : ℕ))⁻¹ ≤ ((L / 2) ^ (4 : ℕ))⁻¹ := inv_anti₀ h2 h1
        have h4 : ((L / 2) ^ (4 : ℕ))⁻¹ = 16 / L ^ 4 := by
          have : (L / 2) ^ (4 : ℕ) = L ^ 4 / 16 := by ring
          rw [this, inv_div]
        linarith
      calc (∑ f ∈ Finset.Icc 1 m, G f)
        ≤ (1 + Real.log (hi : ℝ)) ^ 2 * (M * (Y : ℝ) * LY ^ (-(12 : ℝ)) * (R : ℝ)) :=
            le_trans hsmall (mul_le_mul_of_nonneg_left hsmall2 (by positivity))
        _ ≤ 4 * L ^ 2 * (M * (Y : ℝ) * LY ^ (-(12 : ℝ)) * LY ^ (8 : ℕ)) := by
            apply mul_le_mul hw ?_ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hRle (by positivity)
        _ = 4 * L ^ 2 * M * (Y : ℝ) * (LY ^ (-(12 : ℝ)) * LY ^ (8 : ℕ)) := by ring
        _ = 4 * L ^ 2 * M * (Y : ℝ) * ((LY ^ (4 : ℕ))⁻¹) := by rw [hLYneg]
        _ ≤ 4 * L ^ 2 * M * (Y : ℝ) * (16 / L ^ 4) :=
            mul_le_mul_of_nonneg_left hLY4 (by positivity)
        _ = (64 * M) * ((Y : ℝ) / L ^ 2) := by field_simp; ring

    have herr_fin : (hi : ℝ) * (Nat.log 2 ⌊(Y : ℝ)⌋₊ : ℝ) * Real.log (hi : ℝ) ≤
        4 * ((Y : ℝ) / L ^ 2) := by
      rw [Nat.floor_natCast]
      have h1 : (Nat.log 2 Y : ℝ) ≤ 2 * LY := by
        have := sharp_bv_band_aux_nat_log_le Y hY1n
        rwa [← hLYdef] at this
      have h2 : Real.log (hi : ℝ) ≤ 2 * L := le_trans hloghi (by linarith)
      calc (hi : ℝ) * (Nat.log 2 Y : ℝ) * Real.log (hi : ℝ)
        ≤ (Real.sqrt (Y : ℝ) / L ^ 5) * (2 * (2 * L)) * L := by
            apply mul_le_mul
            · exact mul_le_mul hhiY (le_trans h1 (by linarith)) (by positivity) (by positivity)
            · exact hloghi
            · exact Real.log_nonneg (by exact_mod_cast hhi1)
            · positivity
        _ = 4 * Real.sqrt (Y : ℝ) / L ^ 3 := by field_simp; ring
        _ ≤ 4 * ((Y : ℝ) * L) / L ^ 3 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have hsq : Real.sqrt (Y : ℝ) ≤ (Y : ℝ) := Real.sqrt_le_iff.mpr ⟨hYpos.le, by nlinarith⟩
            have hYL : (Y : ℝ) ≤ (Y : ℝ) * L := le_mul_of_one_le_right hYpos.le hL1
            linarith
        _ = 4 * ((Y : ℝ) / L ^ 2) := by field_simp

    have hfin' : ∀ c : ℝ, c ≤ 10 ^ 30 * (1 + M) →
        (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ)) ≤
          c * ((Y : ℝ) / L ^ 2) →
        (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ)) ≤
          10 ^ 31 * (1 + M) * (Y : ℝ) / (L * Real.sqrt L) := by
      intro c hc hle
      calc (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ))
        ≤ c * ((Y : ℝ) / L ^ 2) := hle
        _ ≤ 10 ^ 30 * (1 + M) * ((Y : ℝ) / L ^ 2) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ ≤ 10 ^ 31 * (1 + M) * ((Y : ℝ) / L ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (by norm_num : (10 : ℝ) ^ 30 ≤ 10 ^ 31)
              (by linarith : (0 : ℝ) ≤ 1 + M)
        _ = 10 ^ 31 * (1 + M) * (Y : ℝ) / L ^ 2 := by ring
        _ ≤ 10 ^ 31 * (1 + M) * (Y : ℝ) / (L * Real.sqrt L) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            calc L * Real.sqrt L ≤ L * L :=
                  mul_le_mul_of_nonneg_left
                    (Real.sqrt_le_iff.mpr ⟨hL0.le, by nlinarith⟩) hL0.le
              _ = L ^ 2 := by ring
    rcases le_or_gt hi R with hhiR | hhiR
    ·
      have hm : m = hi := min_eq_left hhiR
      have hempty : Finset.Ioc m hi = ∅ := by
        rw [hm]; exact Finset.Ioc_eq_empty_iff.mpr (by omega)
      have hz : (∑ f ∈ Finset.Ioc m hi, G f) = 0 := by rw [hempty, Finset.sum_empty]
      have hc1 : 64 * M + 4 ≤ 10 ^ 30 * (1 + M) := by
        have h1 : (64 : ℝ) * M ≤ 10 ^ 30 * M :=
          mul_le_mul_of_nonneg_right (by norm_num) hMpos.le
        have h2 : (4 : ℝ) ≤ 10 ^ 30 := by norm_num
        linarith
      refine hfin' (64 * M + 4) hc1 ?_
      calc (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ))
        ≤ (∑ f ∈ Finset.Icc 1 m, G f) + (∑ f ∈ Finset.Ioc m hi, G f) +
            (hi : ℝ) * (Nat.log 2 ⌊(Y : ℝ)⌋₊ : ℝ) * Real.log (hi : ℝ) := by
            rw [← hsplit]; exact hmain
        _ ≤ (64 * M) * ((Y : ℝ) / L ^ 2) + 0 + 4 * ((Y : ℝ) / L ^ 2) := by
            rw [hz]; linarith [hsmall_fin, herr_fin]
        _ = (64 * M + 4) * ((Y : ℝ) / L ^ 2) := by ring
    ·
      have hm : m = R := min_eq_right (le_of_lt hhiR)
      have hex : ∃ n : ℕ, hi ≤ 2 ^ n * R := by
        refine ⟨hi, ?_⟩
        calc hi ≤ 2 ^ hi := (Nat.lt_two_pow_self : hi < 2 ^ hi).le
          _ ≤ 2 ^ hi * R := Nat.le_mul_of_pos_right (2 ^ hi) hRpos
      set n : ℕ := Nat.find hex with hndef
      have hn_ge : hi ≤ 2 ^ n * R := Nat.find_spec hex
      have hn_le : n ≤ Nat.log 2 hi + 1 := by
        apply Nat.find_min' hex
        have h1 : Nat.log 2 hi < Nat.log 2 hi + 1 := Nat.lt_succ_self _
        have h2 := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega : hi ≠ 0)).mp h1
        calc hi ≤ 2 ^ (Nat.log 2 hi + 1) := h2.le
          _ ≤ 2 ^ (Nat.log 2 hi + 1) * R := Nat.le_mul_of_pos_right (2 ^ (Nat.log 2 hi + 1)) hRpos
      have hn1 : 1 ≤ n := by
        by_contra h
        have h0 : n = 0 := by omega
        have hbad : hi ≤ R := by
          have := hn_ge
          rw [h0] at this
          simpa using this
        omega
      have hn2R : 2 ^ n * R ≤ 2 * hi := by
        have hmin : ¬ (hi ≤ 2 ^ (n - 1) * R) := Nat.find_min hex (Nat.sub_lt hn1 Nat.one_pos)
        have hlt : 2 ^ (n - 1) * R < hi := Nat.lt_of_not_ge hmin
        have he : 2 ^ n * R = 2 * (2 ^ (n - 1) * R) := by
          calc 2 ^ n * R = 2 ^ (n - 1 + 1) * R := by rw [Nat.sub_add_cancel hn1]
            _ = (2 ^ (n - 1) * 2) * R := by rw [pow_succ]
            _ = 2 * (2 ^ (n - 1) * R) := by ring
        calc 2 ^ n * R = 2 * (2 ^ (n - 1) * R) := he
          _ ≤ 2 * hi := Nat.mul_le_mul_left 2 (le_of_lt hlt)
      have hn_le_real : (n : ℝ) ≤ 3 * L := by
        have h1 : (Nat.log 2 hi : ℝ) ≤ 2 * Real.log (hi : ℝ) :=
          sharp_bv_band_aux_nat_log_le hi hhi1
        have h2 : (n : ℝ) ≤ (Nat.log 2 hi : ℝ) + 1 := by exact_mod_cast hn_le
        linarith
      have htel : ∀ N : ℕ, (∑ f ∈ Finset.Ioc R (2 ^ N * R), G f) ≤
          ∑ j ∈ Finset.range N, ∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R), G f := by
        intro N; induction N with
        | zero => simp
        | succ N ih =>
          have h1 : R ≤ 2 ^ N * R := Nat.le_mul_of_pos_left R (by positivity : 0 < 2 ^ N)
          have h2 : 2 ^ N * R ≤ 2 ^ (N + 1) * R := by
            rw [pow_succ]
            calc 2 ^ N * R ≤ 2 ^ N * R * 2 := Nat.le_mul_of_pos_right (2 ^ N * R) (by norm_num)
              _ = 2 ^ N * 2 * R := by ring
          have hU : Finset.Ioc R (2 ^ (N + 1) * R) =
              Finset.Ioc R (2 ^ N * R) ∪ Finset.Ioc (2 ^ N * R) (2 ^ (N + 1) * R) :=
            (Finset.Ioc_union_Ioc_eq_Ioc h1 h2).symm
          have hdisj : Disjoint (Finset.Ioc R (2 ^ N * R))
              (Finset.Ioc (2 ^ N * R) (2 ^ (N + 1) * R)) := by
            rw [Finset.disjoint_left]; intro a ha hb
            simp only [Finset.mem_Ioc] at ha hb; omega
          rw [hU, Finset.sum_union hdisj, Finset.sum_range_succ]
          exact add_le_add ih le_rfl
      have hcover : (∑ f ∈ Finset.Ioc R hi, G f) ≤
          ∑ j ∈ Finset.range n, ∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R), G f := by
        have hsub : Finset.Ioc R hi ⊆ Finset.Ioc R (2 ^ n * R) := by
          intro f hf; simp only [Finset.mem_Ioc] at hf ⊢; exact ⟨hf.1, le_trans hf.2 hn_ge⟩
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hG0 f)) (htel n)
      have hblk : ∀ j : ℕ, j < n → (∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R), G f) ≤
          (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T +
              kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ) +
                128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ) +
                32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ))) := by
        intro j hj
        have hw : ∀ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R),
            (1 + Real.log ((hi / f : ℕ) : ℝ)) ^ 2 ≤ (1 + ((n - j : ℕ) : ℝ)) ^ 2 := by
          intro f hf
          simp only [Finset.mem_Ioc] at hf
          have hdiv : hi / f ≤ 2 ^ (n - j) := by
            have h1 : hi / f ≤ hi / (2 ^ j * R) :=
              Nat.div_le_div_left (le_of_lt hf.1) (by positivity)
            have h2 : hi / (2 ^ j * R) ≤ (2 ^ n * R) / (2 ^ j * R) :=
              Nat.div_le_div_right hn_ge
            have h3 : (2 ^ n * R) / (2 ^ j * R) = 2 ^ (n - j) := by
              have he : 2 ^ n * R = 2 ^ (n - j) * (2 ^ j * R) := by
                calc 2 ^ n * R = 2 ^ (n - j + j) * R := by rw [Nat.sub_add_cancel (le_of_lt hj)]
                  _ = (2 ^ (n - j) * 2 ^ j) * R := by rw [pow_add]
                  _ = 2 ^ (n - j) * (2 ^ j * R) := by ring
              rw [he, Nat.mul_div_cancel _ (by positivity)]
            exact le_trans h1 (le_trans h2 (le_of_eq h3))
          have hlog : Real.log ((hi / f : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
            rcases Nat.eq_zero_or_pos (hi / f) with h0 | h0
            · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; exact Nat.cast_nonneg _
            · have h := Real.log_le_log (Nat.cast_pos.mpr h0) (Nat.cast_le.mpr hdiv)
              have h2 : Real.log ((2 ^ (n - j) : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) * Real.log 2 := by
                rw [Nat.cast_pow]; exact Real.log_pow 2 (n - j)
              rw [h2] at h
              have h3 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
              have h4 : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) := Nat.cast_nonneg _
              calc Real.log ((hi / f : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) * Real.log 2 := h
                _ ≤ ((n - j : ℕ) : ℝ) * 1 :=
                    mul_le_mul_of_nonneg_left (by linarith : Real.log 2 ≤ 1) h4
                _ = ((n - j : ℕ) : ℝ) := by ring
          have hnn : 0 ≤ 1 + Real.log ((hi / f : ℕ) : ℝ) := by
            rcases Nat.eq_zero_or_pos (hi / f) with h0 | h0
            · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; norm_num
            · linarith [Real.log_nonneg (Nat.one_le_cast.mpr h0)]
          exact pow_le_pow_left₀ hnn (by linarith) 2
        have hD1 : 1 ≤ 2 ^ j * R :=
          le_trans (by norm_num) (Nat.mul_le_mul Nat.one_le_two_pow hR1)
        have hQ : 2 * (2 ^ j * R) = 2 ^ (j + 1) * R := by rw [pow_succ]; ring
        have hblock := sharp_conductor_block (2 ^ (j + 1) * R) Y T k (2 ^ j * R) hD1
          (le_of_eq hQ) hkpow
        rw [hQ] at hblock
        calc (∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R), G f)
          ≤ ∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R),
              OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ) *
                (1 + ((n - j : ℕ) : ℝ)) ^ 2 :=
            Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hw f hf)
              (div_nonneg (OAI.LargePrimeGaps.primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _)))
          _ = (1 + ((n - j : ℕ) : ℝ)) ^ 2 * ∑ f ∈ Finset.Ioc (2 ^ j * R) (2 ^ (j + 1) * R),
              OAI.LargePrimeGaps.primitiveErrorMass (Y : ℝ) f / (f.totient : ℝ) := by
            rw [← Finset.sum_mul]; ring
          _ ≤ (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                  OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T +
                kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ) +
                  128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ) +
                  32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ))) :=
            mul_le_mul_of_nonneg_left hblock (by positivity)
      have hsumj : (∑ f ∈ Finset.Ioc R hi, G f) ≤
          ∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T +
              kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ) +
                128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ) +
                32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ))) :=
        le_trans hcover (Finset.sum_le_sum (fun j hj => hblk j (Finset.mem_range.mp hj)))
      have hsum4 : (∑ f ∈ Finset.Ioc R hi, G f) ≤
          (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
              OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T)) +
          (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ)))) +
          (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)))) +
          (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
            (kfac * (32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ)))) := by
        refine le_trans hsumj (le_of_eq ?_)
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                  OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T +
                kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ) +
                  128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ) +
                  32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ))))
            = ∑ j ∈ Finset.range n, ((1 + ((n - j : ℕ) : ℝ)) ^ 2 *
                (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                  OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T) +
                (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ))) +
                (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
                  (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))) +
                (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
                  (kfac * (32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ)))) :=
              Finset.sum_congr rfl (fun j _ => by ring)
          _ = _ := by simp only [Finset.sum_add_distrib]

      have hQle : ∀ j ∈ Finset.range n, (2 ^ (j + 1) * R : ℕ) ≤ 2 * hi := by
        intro j hj
        have hj' : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have h1 : 2 ^ (j + 1) * R ≤ 2 ^ n * R :=
          Nat.mul_le_mul_right R (Nat.pow_le_pow_right (by norm_num) hj')
        omega
      have hgeom : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
          ((2 ^ (j + 1) * R : ℕ) : ℝ)) ≤ 22 * (2 : ℝ) ^ n * (R : ℝ) := by
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ))
          = (R : ℝ) * ∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ (j + 1) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              push_cast; ring
          _ ≤ (R : ℝ) * (22 * (2 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (sharp_bv_band_aux_geom n) (Nat.cast_nonneg _)
          _ = 22 * (2 : ℝ) ^ n * (R : ℝ) := by ring
      have hSA : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
          (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
            OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T)) ≤
          88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T := by
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T))
          ≤ ∑ j ∈ Finset.range n, 2 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T *
              ((1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ)) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hmono := OAI.LargePrimeGaps.vaughanShortBound_mono (hQle j hj) Y T
              have hnonneg : 0 ≤ (1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) := by
                positivity
              calc (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) *
                    OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T)
                = 2 * OAI.LargePrimeGaps.vaughanShortBound (2 ^ (j + 1) * R) Y T *
                    ((1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ)) := by ring
                _ ≤ 2 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T *
                    ((1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num))
                    hnonneg
          _ = 2 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T *
              ∑ j ∈ Finset.range n, ((1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ)) := by
              rw [← Finset.mul_sum]
          _ ≤ 2 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T *
              (22 * (2 : ℝ) ^ n * (R : ℝ)) :=
              mul_le_mul_of_nonneg_left hgeom
                (mul_nonneg (by norm_num) (OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _))
          _ ≤ 88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T := by
              have h2nR : (2 : ℝ) ^ n * (R : ℝ) ≤ 2 * (hi : ℝ) := by exact_mod_cast hn2R
              calc 2 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T * (22 * (2 : ℝ) ^ n * (R : ℝ))
                = 44 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T *
                    ((2 : ℝ) ^ n * (R : ℝ)) := by ring
                _ ≤ 44 * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T * (2 * (hi : ℝ)) :=
                  mul_le_mul_of_nonneg_left h2nR
                    (mul_nonneg (by norm_num) (OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _))
                _ = 88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T := by ring
      have hn1sq : ((n : ℝ) + 1) ^ 2 ≤ 16 * L ^ 2 := by
        have h1 : (n : ℝ) + 1 ≤ 4 * L := by linarith
        have h0 : 0 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        calc ((n : ℝ) + 1) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ h0 h1 2
          _ = 16 * L ^ 2 := by ring
      have hSB : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
          (kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ)))) ≤
          kfac * (32 * (Y : ℝ) / (R : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by
        have h1 : ∀ j ∈ Finset.range n,
            (1 + ((n - j : ℕ) : ℝ)) ^ 2 * (kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ))) ≤
              ((n : ℝ) + 1) ^ 2 * (kfac * (32 * (Y : ℝ) / (R : ℝ))) := by
          intro j hj
          have hsq : (1 + ((n - j : ℕ) : ℝ)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
            have : (1 + ((n - j : ℕ) : ℝ)) ≤ (n : ℝ) + 1 := by
              have hnat : 1 + (n - j) ≤ n + 1 := by
                rw [Nat.add_comm 1 (n - j)]
                exact Nat.succ_le_succ (Nat.sub_le n j)
              exact_mod_cast hnat
            exact pow_le_pow_left₀ (by positivity) this 2
          have hdiv : 32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ) ≤ 32 * (Y : ℝ) / (R : ℝ) := by
            apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hRpos)
            exact_mod_cast Nat.le_mul_of_pos_left R (by positivity)
          exact mul_le_mul hsq (mul_le_mul_of_nonneg_left hdiv hkfac0) (by positivity) (by positivity)
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (kfac * (32 * (Y : ℝ) / ((2 ^ j * R : ℕ) : ℝ))))
          ≤ ∑ j ∈ Finset.range n, ((n : ℝ) + 1) ^ 2 * (kfac * (32 * (Y : ℝ) / (R : ℝ))) :=
              Finset.sum_le_sum h1
          _ = ((n : ℝ) + 1) ^ 2 * (kfac * (32 * (Y : ℝ) / (R : ℝ))) * (n : ℝ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          _ = kfac * (32 * (Y : ℝ) / (R : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by ring
      have hSC : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
          (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)))) ≤
          kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by
        have h1 : ∀ j ∈ Finset.range n,
            (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))) ≤
              ((n : ℝ) + 1) ^ 2 * (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))) := by
          intro j hj
          have hsq : (1 + ((n - j : ℕ) : ℝ)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
            have : (1 + ((n - j : ℕ) : ℝ)) ≤ (n : ℝ) + 1 := by
              have hnat : 1 + (n - j) ≤ n + 1 := by
                rw [Nat.add_comm 1 (n - j)]
                exact Nat.succ_le_succ (Nat.sub_le n j)
              exact_mod_cast hnat
            exact pow_le_pow_left₀ (by positivity) this 2
          exact mul_le_mul hsq le_rfl (by positivity) (by positivity)
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))))
          ≤ ∑ j ∈ Finset.range n, ((n : ℝ) + 1) ^ 2 *
              (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))) := Finset.sum_le_sum h1
          _ = ((n : ℝ) + 1) ^ 2 * (kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ))) *
              (n : ℝ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          _ = kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)) *
              ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by ring
      have hSD : (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
          (kfac * (32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ)))) ≤
          kfac * (32 * Real.sqrt (Y : ℝ)) * (22 * (2 : ℝ) ^ n * (R : ℝ)) := by
        calc (∑ j ∈ Finset.range n, (1 + ((n - j : ℕ) : ℝ)) ^ 2 *
              (kfac * (32 * ((2 ^ (j + 1) * R : ℕ) : ℝ) * Real.sqrt (Y : ℝ))))
          = kfac * (32 * Real.sqrt (Y : ℝ)) * ∑ j ∈ Finset.range n,
              (1 + ((n - j : ℕ) : ℝ)) ^ 2 * ((2 ^ (j + 1) * R : ℕ) : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              ring
          _ ≤ kfac * (32 * Real.sqrt (Y : ℝ)) * (22 * (2 : ℝ) ^ n * (R : ℝ)) :=
              mul_le_mul_of_nonneg_left hgeom (by positivity)

      have hA_fin : 88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T ≤
          (32736 * 2 ^ 39) * ((Y : ℝ) / L ^ 2) := by
        have h1 : 88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T ≤
            88 * (Real.sqrt (Y : ℝ) / L ^ 5) * (372 * qY * L ^ 42) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hhiY (by norm_num)
          · exact hvSB
          · exact OAI.LargePrimeGaps.vaughanShortBound_nonneg _ _ _
          · positivity
        have h2 : Real.sqrt (Y : ℝ) * qY = qY ^ 3 := by rw [← hqY2]; ring
        have h3 : L ^ (42 : ℕ) / L ^ (5 : ℕ) = L ^ (37 : ℕ) := by
          have : L ^ (42 : ℕ) = L ^ (37 : ℕ) * L ^ (5 : ℕ) := by ring
          rw [this]; field_simp
        have hL39 : L ^ (39 : ℕ) ≤ 2 ^ 39 * qY := by
          have e1 : L ^ (39 : ℕ) ≤ (2 * LY) ^ (39 : ℕ) := pow_le_pow_left₀ (by linarith) hL2LY 39
          have e2 : (2 * LY) ^ (39 : ℕ) = 2 ^ (39 : ℕ) * LY ^ (39 : ℕ) := mul_pow 2 LY 39
          have e3 : LY ^ (39 : ℕ) ≤ LY ^ (40 : ℕ) := pow_le_pow_right₀ hLY1 (by norm_num)
          have e4 : LY ^ (40 : ℕ) ≤ qY := by
            rw [hqYdef, ← Real.rpow_natCast LY 40]; exact hlog Y hXY
          calc L ^ (39 : ℕ) ≤ (2 * LY) ^ (39 : ℕ) := e1
            _ = 2 ^ (39 : ℕ) * LY ^ (39 : ℕ) := e2
            _ ≤ 2 ^ (39 : ℕ) * LY ^ (40 : ℕ) := mul_le_mul_of_nonneg_left e3 (by positivity)
            _ ≤ 2 ^ (39 : ℕ) * qY := mul_le_mul_of_nonneg_left e4 (by positivity)
        calc 88 * (hi : ℝ) * OAI.LargePrimeGaps.vaughanShortBound (2 * hi) Y T
          ≤ 88 * (Real.sqrt (Y : ℝ) / L ^ 5) * (372 * qY * L ^ 42) := h1
          _ = 88 * 372 * (Real.sqrt (Y : ℝ) * qY) * (L ^ (42 : ℕ) / L ^ (5 : ℕ)) := by
              field_simp
          _ = 32736 * qY ^ 3 * L ^ (37 : ℕ) := by rw [h2, h3]; ring
          _ ≤ (32736 * 2 ^ 39) * ((Y : ℝ) / L ^ 2) := by
              have hrw : (32736 * 2 ^ 39 : ℝ) * ((Y : ℝ) / L ^ 2) =
                  32736 * 2 ^ 39 * (Y : ℝ) / L ^ (2 : ℕ) := by ring
              rw [hrw, le_div_iff₀ (by positivity)]
              calc 32736 * qY ^ 3 * L ^ (37 : ℕ) * L ^ (2 : ℕ)
                = 32736 * qY ^ 3 * L ^ (39 : ℕ) := by ring
                _ ≤ 32736 * qY ^ 3 * (2 ^ 39 * qY) :=
                    mul_le_mul_of_nonneg_left hL39 (by positivity)
                _ = 32736 * 2 ^ 39 * qY ^ 4 := by ring
                _ = 32736 * 2 ^ 39 * (Y : ℝ) := by rw [hqY4]
      have hB_fin : kfac * (32 * (Y : ℝ) / (R : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2) ≤
          18874368 * ((Y : ℝ) / L ^ 2) := by
        have s1 : kfac * (32 * (Y : ℝ) / (R : ℝ)) ≤
            (24 * L ^ 3) * (32 * (Y : ℝ) / (L ^ (8 : ℕ) / 512)) :=
          mul_le_mul hkfac (div_le_div_of_nonneg_left (by positivity) (by positivity) hRge8)
            (by positivity) (by positivity)
        have s2 : (n : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ (3 * L) * (16 * L ^ 2) :=
          mul_le_mul hn_le_real hn1sq (by positivity) (by positivity)
        calc kfac * (32 * (Y : ℝ) / (R : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2)
          ≤ (24 * L ^ 3) * (32 * (Y : ℝ) / (L ^ (8 : ℕ) / 512)) * ((3 * L) * (16 * L ^ 2)) :=
            mul_le_mul s1 s2 (by positivity) (by positivity)
          _ = 18874368 * ((Y : ℝ) / L ^ 2) := by field_simp; ring
      have hC_fin : kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)) *
          ((n : ℝ) * ((n : ℝ) + 1) ^ 2) ≤ 147456 * ((Y : ℝ) / L ^ 2) := by
        have s1 : kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)) ≤
            (24 * L ^ 3) * (128 * (Y : ℝ) / L ^ (10 : ℕ)) :=
          mul_le_mul hkfac (div_le_div_of_nonneg_left (by positivity) (by positivity) hTsq)
            (by positivity) (by positivity)
        have s2 : (n : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ (3 * L) * (16 * L ^ 2) :=
          mul_le_mul hn_le_real hn1sq (by positivity) (by positivity)
        calc kfac * (128 * (Y : ℝ) / Real.sqrt ((T + 1 : ℕ) : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) ^ 2)
          ≤ (24 * L ^ 3) * (128 * (Y : ℝ) / L ^ (10 : ℕ)) * ((3 * L) * (16 * L ^ 2)) :=
            mul_le_mul s1 s2 (by positivity) (by positivity)
          _ = 147456 * ((Y : ℝ) / L ^ 4) := by field_simp; ring
          _ ≤ 147456 * ((Y : ℝ) / L ^ 2) := by
              calc 147456 * ((Y : ℝ) / L ^ 4) = 147456 * (Y : ℝ) / L ^ 4 := by ring
                _ ≤ 147456 * (Y : ℝ) / L ^ 2 :=
                    div_le_div_of_nonneg_left (by positivity) (by positivity)
                      (pow_le_pow_right₀ hL1 (by norm_num))
                _ = 147456 * ((Y : ℝ) / L ^ 2) := by ring
      have hD_fin : kfac * (32 * Real.sqrt (Y : ℝ)) * (22 * (2 : ℝ) ^ n * (R : ℝ)) ≤
          33792 * ((Y : ℝ) / L ^ 2) := by
        have h2nR : (2 : ℝ) ^ n * (R : ℝ) ≤ 2 * (hi : ℝ) := by exact_mod_cast hn2R
        have s1 : 22 * (2 : ℝ) ^ n * (R : ℝ) ≤ 44 * (Real.sqrt (Y : ℝ) / L ^ 5) := by
          calc 22 * (2 : ℝ) ^ n * (R : ℝ) = 22 * ((2 : ℝ) ^ n * (R : ℝ)) := by ring
            _ ≤ 22 * (2 * (hi : ℝ)) := mul_le_mul_of_nonneg_left h2nR (by norm_num)
            _ = 44 * (hi : ℝ) := by ring
            _ ≤ 44 * (Real.sqrt (Y : ℝ) / L ^ 5) := mul_le_mul_of_nonneg_left hhiY (by norm_num)
        have hY : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = (Y : ℝ) := Real.mul_self_sqrt hYpos.le
        calc kfac * (32 * Real.sqrt (Y : ℝ)) * (22 * (2 : ℝ) ^ n * (R : ℝ))
          ≤ (24 * L ^ 3) * (32 * Real.sqrt (Y : ℝ)) * (44 * (Real.sqrt (Y : ℝ) / L ^ 5)) :=
            mul_le_mul (mul_le_mul hkfac le_rfl (by positivity) (by positivity)) s1
              (by positivity) (by positivity)
          _ = 33792 * L ^ 3 * (Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ)) / L ^ 5 := by
              field_simp; ring
          _ = 33792 * L ^ 3 * (Y : ℝ) / L ^ 5 := by rw [hY]
          _ = 33792 * ((Y : ℝ) / L ^ 2) := by field_simp
      have hc2 : 64 * M + 4 + 32736 * 2 ^ 39 + 18874368 + 147456 + 33792 ≤ 10 ^ 30 * (1 + M) := by
        have h1 : (64 : ℝ) * M ≤ 10 ^ 29 * M :=
          mul_le_mul_of_nonneg_right (by norm_num) hMpos.le
        have h2 : (4 : ℝ) + 32736 * 2 ^ 39 + 18874368 + 147456 + 33792 ≤ 10 ^ 29 := by norm_num
        linarith
      refine hfin' (64 * M + 4 + 32736 * 2 ^ 39 + 18874368 + 147456 + 33792) hc2 ?_
      calc (∑ d ∈ Finset.Icc 1 hi, (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ))
        ≤ (∑ f ∈ Finset.Icc 1 m, G f) + (∑ f ∈ Finset.Ioc m hi, G f) +
            (hi : ℝ) * (Nat.log 2 ⌊(Y : ℝ)⌋₊ : ℝ) * Real.log (hi : ℝ) := by
            rw [← hsplit]; exact hmain
        _ ≤ (64 * M) * ((Y : ℝ) / L ^ 2) +
            ((32736 * 2 ^ 39) * ((Y : ℝ) / L ^ 2) + 18874368 * ((Y : ℝ) / L ^ 2) +
              147456 * ((Y : ℝ) / L ^ 2) + 33792 * ((Y : ℝ) / L ^ 2)) +
            4 * ((Y : ℝ) / L ^ 2) := by
            have h1 : (∑ f ∈ Finset.Ioc m hi, G f) ≤
                (32736 * 2 ^ 39) * ((Y : ℝ) / L ^ 2) + 18874368 * ((Y : ℝ) / L ^ 2) +
                  147456 * ((Y : ℝ) / L ^ 2) + 33792 * ((Y : ℝ) / L ^ 2) := by
              calc (∑ f ∈ Finset.Ioc m hi, G f) = (∑ f ∈ Finset.Ioc R hi, G f) := by rw [hm]
                _ ≤ _ := hsum4
                _ ≤ _ := add_le_add (add_le_add (add_le_add (le_trans hSA hA_fin) (le_trans hSB hB_fin))
                      (le_trans hSC hC_fin)) (le_trans hSD hD_fin)
            linarith [hsmall_fin, herr_fin, h1]
        _ = (64 * M + 4 + 32736 * 2 ^ 39 + 18874368 + 147456 + 33792) * ((Y : ℝ) / L ^ 2) := by ring

theorem band_window_error_aux_dvd_shift {d n : ℕ} (hd : 1 ≤ d) :
    d ∣ n + 2 ↔ n % d = TwinShortAP.negTwo d % d := by
  have h2 : 2*d - 2 + 2 = 2*d := by omega
  have h0 : 2*d ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left d 2)
  constructor
  · intro h
    have h1 : n+2 ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : n+2 ≡ 2*d-2+2 [MOD d] := by rw [h2]; exact h1.trans h0.symm
    exact Nat.ModEq.add_right_cancel' 2 h3
  · intro h
    have h3 : n+2 ≡ 2*d-2+2 [MOD d] := Nat.ModEq.add_right 2 h
    rw [h2] at h3
    exact Nat.modEq_zero_iff_dvd.mp (h3.trans h0)

theorem band_window_error_aux_negTwo_coprime {d : ℕ} (hd : Odd d) :
    (TwinShortAP.negTwo d % d).Coprime d := by
  have h1 := hd.pos
  have h2 : 2*d-2+2=2*d := by omega
  set g := (2*d-2).gcd d with hg
  have hg1 : g ∣ d := Nat.gcd_dvd_right _ _
  have hg2 : g ∣ 2*d-2 := Nat.gcd_dvd_left _ _
  have hg3 : g ∣ 2*d := dvd_mul_of_dvd_right hg1 2
  have hg4 : g ∣ 2 := by simpa only [show 2*d-(2*d-2)=2 by omega] using Nat.dvd_sub hg3 hg2
  have hc : g=1 := ((Nat.dvd_prime Nat.prime_two).mp hg4).resolve_right
    (fun he => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr (he ▸ hg1)))
  change (TwinShortAP.negTwo d % d).gcd d = 1
  rwa [← Nat.gcd_rec, Nat.gcd_comm]

theorem band_window_error_aux_winTheta (X d : ℕ) (hd : 1 ≤ d) :
    TwinShortAP.winTheta X d =
      ∑ p ∈ (TwinShortAP.ps X).filter (fun p => d ∣ p + 2), Real.log (p : ℝ) := by
  unfold TwinShortAP.winTheta GoldbachRoughFifth.bvAPMass GoldbachRoughFifth.bvPrimeWeight
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [TwinShortAP.ps, TwinShortAP.win, TwinShortAP.upper, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Ioc, band_window_error_aux_dvd_shift hd]
  grind

theorem band_window_error_aux_bpP (X d : ℕ) (hd : 1 ≤ d) :
    bpP X d = TwinShortAP.winTheta X d := by
  have hps : bpPrimes X = TwinShortAP.ps X := rfl
  unfold bpP
  rw [band_window_error_aux_winTheta X d hd]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [hps, Finset.mem_filter, Nat.dvd_iff_mod_eq_zero]

theorem band_window_error_aux_per_modulus {X d : ℕ} (hX : 2 ≤ X) (hd : 1 ≤ d) :
    |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| ≤
      |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 (TwinShortAP.upper X) d
          (TwinShortAP.negTwo d) - (TwinShortAP.upper X : ℝ) / (Nat.totient d : ℝ)| +
      |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 X d
          (TwinShortAP.negTwo d) - (X : ℝ) / (Nat.totient d : ℝ)| +
      (Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1 := by
  rw [band_window_error_aux_bpP X d hd]
  have hXU : X ≤ TwinShortAP.upper X := by unfold TwinShortAP.upper; omega
  have h1n : 50 * TwinShortAP.upper X ≤ 51*X := by unfold TwinShortAP.upper; omega
  have h2n : 51*X ≤ 50 * TwinShortAP.upper X + 50 := by unfold TwinShortAP.upper; omega
  have hr : |((TwinShortAP.upper X : ℝ) - X) - (X : ℝ)/50| ≤ 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : (51:ℝ)*(X:ℝ) ≤ 50 * (TwinShortAP.upper X : ℝ) + 50 := by exact_mod_cast h2n
      linarith
    · have : (50:ℝ)*(TwinShortAP.upper X : ℝ) ≤ 51*(X:ℝ) := by exact_mod_cast h1n
      linarith
  have hφ : (1:ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφpos : (0:ℝ) < (Nat.totient d : ℝ) := by linarith
  have hmove : |((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ) -
      ((X : ℝ)/50)/(Nat.totient d : ℝ)| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hφpos]
    exact (div_le_one hφpos).mpr (hr.trans hφ)
  have he := GoldbachRoughFifth.bvAPMass_prime_error_from_prefix hXU (le_refl (TwinShortAP.upper X)) d
    (TwinShortAP.negTwo d) (fun t => (t : ℝ)/(Nat.totient d : ℝ))
  rw [← sub_div] at he
  have hwin : TwinShortAP.winTheta X d =
      GoldbachRoughFifth.bvAPMass GoldbachRoughFifth.bvPrimeWeight X (TwinShortAP.upper X) d
        (TwinShortAP.negTwo d) := rfl
  have h50 : (X : ℝ) / (50 * (Nat.totient d : ℝ)) = ((X : ℝ)/50)/(Nat.totient d : ℝ) := by
    field_simp
  calc |TwinShortAP.winTheta X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|
      = |TwinShortAP.winTheta X d - ((X : ℝ)/50)/(Nat.totient d : ℝ)| := by rw [h50]
    _ ≤ |TwinShortAP.winTheta X d - ((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ)| +
        |((TwinShortAP.upper X : ℝ) - X)/(Nat.totient d : ℝ) -
          ((X : ℝ)/50)/(Nat.totient d : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := by rw [hwin]; exact add_le_add he hmove

theorem band_window_error_aux_class_le (Y d : ℕ) (hd : Odd d) :
    |GoldbachRoughFifth.bvAPMass ArithmeticFunction.vonMangoldt 0 Y d (TwinShortAP.negTwo d) -
        (Y : ℝ) / (Nat.totient d : ℝ)| ≤
      (OAI.LargePrimeGaps.endpointError (Y : ℝ) d : ℝ) :=
  OAI.LargePrimeGaps.endpointClassError_le Y (Nat.mod_lt _ hd.pos)
    (band_window_error_aux_negTwo_coprime hd)

theorem band_window_error : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    (∑ d ∈ bpHigh X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      C * (X : ℝ) /
        (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
  obtain ⟨C₀, hC₀, hband⟩ := sharp_bv_band
  refine ⟨3 * C₀ + 9, by positivity, ?_⟩
  have hlog : Tendsto (fun X : ℕ => Real.log (2 + (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
  filter_upwards [hband, eventually_ge_atTop 16, hlog.eventually_ge_atTop 1] with X hB hX16 hL1
  have hX2 : 2 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (2 + (X : ℝ)) := by linarith
  have hUXn : X ≤ TwinShortAP.upper X := by unfold TwinShortAP.upper; omega
  have hU2Xn : TwinShortAP.upper X ≤ 2 * X := by unfold TwinShortAP.upper; omega
  have hU2X : (TwinShortAP.upper X : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hU2Xn
  have hUX : (X : ℝ) ≤ (TwinShortAP.upper X : ℝ) := by exact_mod_cast hUXn
  have hU1 : (1 : ℝ) ≤ (TwinShortAP.upper X : ℝ) := by
    have : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    linarith
  have hUpos : (0 : ℝ) < (TwinShortAP.upper X : ℝ) := by linarith

  have hsub : bpHigh X ⊆ Finset.Icc 1 (bpD X) := by
    intro d hd
    have hdS : d ∈ bpS X := (Finset.mem_filter.mp hd).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hdS).1).1
  have hper : ∀ d ∈ bpHigh X,
      |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| ≤
        (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
        (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
        ((Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
    intro d hd
    have hdI : d ∈ Finset.Icc 1 (bpD X) := hsub hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdI).1
    have hdS : d ∈ bpS X := (Finset.mem_filter.mp hd).1
    have hdm : d % 2 = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hdS).1).2
    have hodd : Odd d := Nat.odd_iff.mpr hdm
    have h1 := band_window_error_aux_per_modulus hX2 hd1
    have h2 := band_window_error_aux_class_le (TwinShortAP.upper X) d hodd
    have h3 := band_window_error_aux_class_le X d hodd
    linarith

  have hsum1 : (∑ d ∈ bpHigh X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      ∑ d ∈ bpHigh X,
        ((OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
         (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
         ((Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1)) :=
    Finset.sum_le_sum (fun d hd => hper d hd)
  have hsum2 : (∑ d ∈ bpHigh X,
        ((OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) +
         (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) +
         ((Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1))) =
      (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
      (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
      ((bpHigh X).card : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hEU : (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 (bpD X),
        (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg)
  have hEX : (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 (bpD X), (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => (OAI.LargePrimeGaps.endpointError _ _).coe_nonneg)
  have hcard : ((bpHigh X).card : ℝ) ≤ (bpD X : ℝ) := by
    have hc : (bpHigh X).card ≤ bpD X := by
      calc _ ≤ (Finset.Icc 1 (bpD X)).card := Finset.card_le_card hsub
        _ = bpD X := by simp [Nat.card_Icc]
    exact_mod_cast hc
  have hψnn : 0 ≤ Chebyshev.psi (TwinShortAP.upper X) -
      Chebyshev.theta (TwinShortAP.upper X) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)

  have hbX := hB X le_rfl (by omega) (bpD X) le_rfl
  have hbU := hB (TwinShortAP.upper X) hUXn hU2Xn (bpD X) le_rfl
  have hUbound : C₀ * (TwinShortAP.upper X : ℝ) /
      (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) ≤
      2 * C₀ * (X : ℝ) /
        (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc C₀ * (TwinShortAP.upper X : ℝ) ≤ C₀ * (2 * (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hU2X hC₀.le
      _ = 2 * C₀ * (X : ℝ) := by ring

  have hψθ : Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X) ≤
      2 * Real.sqrt (TwinShortAP.upper X : ℝ) * Real.log (TwinShortAP.upper X : ℝ) :=
    Chebyshev.psi_sub_theta_le hU1
  have hsqU : Real.sqrt (TwinShortAP.upper X : ℝ) ≤ 2 * Real.sqrt (X : ℝ) := by
    have h1 : Real.sqrt (TwinShortAP.upper X : ℝ) ≤ Real.sqrt (2 * (X : ℝ)) :=
      Real.sqrt_le_sqrt hU2X
    have h2 : Real.sqrt (2 * (X : ℝ)) ≤ 2 * Real.sqrt (X : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hs : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := Real.sq_sqrt hXpos.le
      nlinarith
    exact h1.trans h2
  have hlogU : Real.log (TwinShortAP.upper X : ℝ) ≤ 2 * Real.log (2 + (X : ℝ)) := by
    have h1 : Real.log (TwinShortAP.upper X : ℝ) ≤ Real.log ((2 + (X : ℝ)) ^ 2) :=
      Real.log_le_log hUpos (by nlinarith)
    have h2 : Real.log ((2 + (X : ℝ)) ^ 2) = 2 * Real.log (2 + (X : ℝ)) := by
      rw [Real.log_pow]
      ring
    linarith
  have hsq4 : (4 : ℝ) ≤ Real.sqrt (X : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hX16)
  have hinner : (Chebyshev.psi (TwinShortAP.upper X) - Chebyshev.theta (TwinShortAP.upper X)) + 1 ≤
      9 * Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ)) := by
    have h1 : 2 * Real.sqrt (TwinShortAP.upper X : ℝ) * Real.log (TwinShortAP.upper X : ℝ) ≤
        8 * Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ)) := by
      calc 2 * Real.sqrt (TwinShortAP.upper X : ℝ) * Real.log (TwinShortAP.upper X : ℝ)
          ≤ 2 * (2 * Real.sqrt (X : ℝ)) * (2 * Real.log (2 + (X : ℝ))) := by gcongr
        _ = 8 * Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ)) := by ring
    have h2 : 1 ≤ Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ)) := by
      have : 1 ≤ Real.sqrt (X : ℝ) := by linarith
      nlinarith
    linarith
  have hDle : (bpD X : ℝ) ≤ Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ) := by
    unfold bpD
    exact Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hLpos.le 5))
  have hprod : (bpD X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
      Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
      9 * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 4 := by
    have h1 : (bpD X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
        Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
        (Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ)) *
          (9 * Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ))) :=
      mul_le_mul hDle hinner (by linarith)
        (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hLpos.le 5))
    have h2 : (Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ)) *
        (9 * Real.sqrt (X : ℝ) * Real.log (2 + (X : ℝ))) =
        9 * (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 4 := by
      have hs : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt hXpos.le
      field_simp [hLpos.ne']
      nlinarith [hs]
    linarith
  have hL4 : Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ))) ≤
      Real.log (2 + (X : ℝ)) ^ 4 := by
    have hsqL : Real.sqrt (Real.log (2 + (X : ℝ))) ≤ Real.log (2 + (X : ℝ)) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hL1)
    calc Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))
        ≤ Real.log (2 + (X : ℝ)) * Real.log (2 + (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqL hLpos.le
      _ = Real.log (2 + (X : ℝ)) ^ 2 := by ring
      _ ≤ Real.log (2 + (X : ℝ)) ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hprod2 : (bpD X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
      Chebyshev.theta (TwinShortAP.upper X)) + 1) ≤
      9 * (X : ℝ) / (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
    refine hprod.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hL4

  have hstep1 : (∑ d ∈ bpHigh X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) ≤
      (∑ d ∈ bpHigh X,
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        ((bpHigh X).card : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
    rw [← hsum2]
    exact hsum1
  calc (∑ d ∈ bpHigh X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|)
      ≤ (∑ d ∈ bpHigh X,
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ bpHigh X, (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        ((bpHigh X).card : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1) := hstep1
    _ ≤ (∑ d ∈ Finset.Icc 1 (bpD X),
          (OAI.LargePrimeGaps.endpointError (TwinShortAP.upper X : ℝ) d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (bpD X), (OAI.LargePrimeGaps.endpointError (X : ℝ) d : ℝ)) +
        (bpD X : ℝ) * ((Chebyshev.psi (TwinShortAP.upper X) -
          Chebyshev.theta (TwinShortAP.upper X)) + 1) := by
      refine add_le_add (add_le_add hEU hEX) ?_
      exact mul_le_mul_of_nonneg_right hcard (by linarith)
    _ ≤ C₀ * (TwinShortAP.upper X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) +
        C₀ * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) +
        9 * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
      refine add_le_add (add_le_add hbU hbX) hprod2
    _ ≤ 2 * C₀ * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) +
        C₀ * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) +
        9 * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by
      refine add_le_add ?_ le_rfl
      exact add_le_add hUbound le_rfl
    _ = (3 * C₀ + 9) * (X : ℝ) /
          (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ)))) := by ring

theorem Conjectures.Cuts.Task384f96fed86c001313e32e28 :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℕ → ℝ := fun (x5 : ℕ) => (∑ x6 ∈ x1 x5 with Nat.Prime x6, Real.log (↑x6 : ℝ) * {x7 ∈ (x6 + (2 : ℕ)).divisors | x3 x5 < x7 ∧ x7 ≤ x4 x5}.sum x2) / (↑x5 : ℝ); Filter.Tendsto x5 Filter.atTop (nhds (0 : ℝ)) := by
  dsimp only

  obtain ⟨L, hL⟩ := hard_limit_exists
  have hmain : Tendsto bpMain atTop (nhds 0) := by
    have h1 : Tendsto (fun X : ℕ => (bpHard (bpD X) - bpHard (bpA X)) / 50)
        atTop (nhds ((L - L) / 50)) :=
      ((hL.comp bpD_atTop).sub (hL.comp bpA_atTop)).div_const 50
    simp only [sub_self, zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [bpA_le_bpD] with X hX
    exact (bpMain_eq_hard hX).symm

  obtain ⟨C₁, hC₁, hlow⟩ := low_part_error
  obtain ⟨C₂, hC₂, hhigh⟩ := band_window_error
  have hlog : Tendsto (fun X : ℕ => Real.log (2 + (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
  have herr : Tendsto bpErr atTop (nhds 0) := by
    have hupper : Tendsto (fun X : ℕ => C₁ / (Real.log (2 + (X : ℝ))) ^ 2 +
        C₂ / Real.sqrt (Real.log (2 + (X : ℝ)))) atTop (nhds 0) := by
      have hsq : Tendsto (fun X : ℕ => (Real.log (2 + (X : ℝ))) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
      have hsqrt : Tendsto (fun X : ℕ => Real.sqrt (Real.log (2 + (X : ℝ)))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp hlog
      have h1 : Tendsto (fun X : ℕ => C₁ / (Real.log (2 + (X : ℝ))) ^ 2) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hsq.inv_tendsto_atTop.const_mul C₁
      have h2 : Tendsto (fun X : ℕ => C₂ / Real.sqrt (Real.log (2 + (X : ℝ))))
          atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hsqrt.inv_tendsto_atTop.const_mul C₂
      simpa using h1.add h2
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => abs_nonneg (bpErr X)) ?_ hupper
    filter_upwards [eventually_ge_atTop 3, hhigh] with X hX hhighX
    have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hlowX := hlow X hX
    have hLpos : 0 < Real.log (2 + (X : ℝ)) := Real.log_pos (by linarith)
    have hcX : ∀ d ∈ bpHigh X, |bpC d| ≤ Real.log (2 + (X : ℝ)) := by
      intro d hd
      have hdD : d ≤ bpD X :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hd).1).1).1).2
      have hd1 : 1 ≤ d :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hd).1).1).1).1
      have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
      have hL1 : 1 ≤ Real.log (2 + (X : ℝ)) := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
      have hdX : (d : ℝ) ≤ (X : ℝ) := by
        have h1 : (bpD X : ℝ) ≤ Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ) :=
          Nat.floor_le (by positivity)
        have h2 : Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ (5 : ℕ) ≤ Real.sqrt (X : ℝ) :=
          div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)
        have h3 : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨by positivity, by nlinarith⟩
        have h4 : (d : ℝ) ≤ (bpD X : ℝ) := by exact_mod_cast hdD
        linarith
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
      have hpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hdX' : (d : ℝ) ≤ 2 + (X : ℝ) := by linarith
      unfold bpC
      rw [abs_mul, abs_neg]
      calc |(ArithmeticFunction.moebius d : ℝ)| * |Real.log (d : ℝ)|
          ≤ 1 * |Real.log (d : ℝ)| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ = |Real.log (d : ℝ)| := one_mul _
        _ = Real.log (d : ℝ) := abs_of_nonneg hlogd
        _ ≤ Real.log (2 + (X : ℝ)) := Real.log_le_log hpos hdX'
    have hsum : |∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| ≤
        C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
          C₂ * (X : ℝ) / Real.sqrt (Real.log (2 + (X : ℝ))) := by
      rw [bpErr_split X]
      calc |(∑ d ∈ bpLow X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))) +
            (∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))))|
          ≤ |∑ d ∈ bpLow X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| +
            |∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| :=
            abs_add_le _ _
        _ ≤ (∑ d ∈ bpLow X,
              |bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))|) +
            |∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| := add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
        _ = (∑ d ∈ bpLow X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))|) +
            |∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| := by
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [abs_mul]
        _ ≤ C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            |∑ d ∈ bpHigh X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| := add_le_add hlowX le_rfl
        _ ≤ C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            ∑ d ∈ bpHigh X, |bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| := add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
        _ = C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            ∑ d ∈ bpHigh X, |bpC d| * |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| := by
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [abs_mul]
        _ ≤ C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            ∑ d ∈ bpHigh X, Real.log (2 + (X : ℝ)) *
              |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| := by
            apply add_le_add le_rfl
            apply Finset.sum_le_sum
            intro d hd
            exact mul_le_mul_of_nonneg_right (hcX d hd) (abs_nonneg _)
        _ = C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            Real.log (2 + (X : ℝ)) *
              ∑ d ∈ bpHigh X, |bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ))| := by
            rw [← Finset.mul_sum]
        _ ≤ C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            Real.log (2 + (X : ℝ)) * (C₂ * (X : ℝ) /
              (Real.log (2 + (X : ℝ)) * Real.sqrt (Real.log (2 + (X : ℝ))))) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hhighX hLpos.le)
        _ = C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            C₂ * (X : ℝ) / Real.sqrt (Real.log (2 + (X : ℝ))) := by
            have hL0 : Real.log (2 + (X : ℝ)) ≠ 0 := hLpos.ne'
            have hsq0 : Real.sqrt (Real.log (2 + (X : ℝ))) ≠ 0 :=
              Real.sqrt_ne_zero'.mpr hLpos
            field_simp
    simp only [Function.comp_apply]
    unfold bpErr
    rw [abs_div, abs_of_pos hX0]
    calc |∑ d ∈ bpS X, bpC d * (bpP X d - (X : ℝ) / (50 * (Nat.totient d : ℝ)))| / (X : ℝ)
        ≤ (C₁ * (X : ℝ) / (Real.log (2 + (X : ℝ))) ^ 2 +
            C₂ * (X : ℝ) / Real.sqrt (Real.log (2 + (X : ℝ)))) / (X : ℝ) :=
          div_le_div_of_nonneg_right hsum hX0.le
      _ = C₁ / (Real.log (2 + (X : ℝ))) ^ 2 +
            C₂ / Real.sqrt (Real.log (2 + (X : ℝ))) := by
          have hL0 : Real.log (2 + (X : ℝ)) ≠ 0 := hLpos.ne'
          have hsq0 : Real.sqrt (Real.log (2 + (X : ℝ))) ≠ 0 :=
            Real.sqrt_ne_zero'.mpr hLpos
          have hX0' : (X : ℝ) ≠ 0 := hX0.ne'
          field_simp
  have hsum : Tendsto (fun X : ℕ => bpMain X + bpErr X) atTop (nhds 0) := by
    simpa using hmain.add herr
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with X hX
  exact (strip_eq_main_add_err hX).symm
