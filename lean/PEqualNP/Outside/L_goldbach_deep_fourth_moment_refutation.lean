import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma


/-
MR-8001 uses the counterexample previously reported by DNZJSJ in
CGandGameEngineLearner/goldbach-proofs pull request 1229, comment 7166770405.
The standalone certificate is archived in DNZJSJ/goldbach-proofs at
203c3b480f786b05efc2ec979a7e51e5b7f4bdb8 and in the Zenodo technical note
10.5281/zenodo.24550608. The finite character sum credits DFQDZZ below.
-/

section GoldbachWideArcSeparation

open Filter
open scoped Topology

namespace GoldbachWideArcs

/-- The triangle inequality and spacing of rational centers give this general width condition.
    This uses the rational-separation argument from goldbach-proofs PR 153. -/
theorem reduced_centers_eq_of_common_point {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

theorem eventually_wide_arc_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * Q₁ < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/512 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/512 := hN n hnN
  have hscaled : 512 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 512)).1
      (show Real.log (n : ℝ)^2 < c^2*z/512 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (512 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (512 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 512 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 512 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * Q₁ < n
  rw [show 2 * (256 * Q₁ * Q) * Q₁ = 512 * Q * Q₁^2 by ring]
  exact hnat

end GoldbachWideArcs

end GoldbachWideArcSeparation

section GoldbachDeepFourthGeometry

open Filter
open scoped Topology

private theorem eventuallyExtendedBudget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * (4*Q₁) < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/2048 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/2048 := hN n hnN
  have hscaled : 2048 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2048)).1
      (show Real.log (n : ℝ)^2 < c^2*z/2048 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (2048 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (2048 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 2048 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 2048 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * (4*Q₁) < n
  rw [show 2 * (256 * Q₁ * Q) * (4*Q₁) = 2048 * Q * Q₁^2 by ring]
  exact hnat

open Set

namespace GoldbachFourthGeometry

noncomputable def strip (n q a : ℕ) : Set ℝ :=
  Set.Icc ((a:ℝ)/q - 1/(20*(n:ℝ))) ((a:ℝ)/q + 1/(20*(n:ℝ)))

noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

theorem mem_strip {n q a : ℕ} {t : ℝ} :
    t ∈ strip n q a ↔ |t-(a:ℝ)/q| ≤ 1/(20*(n:ℝ)) := by
  unfold strip
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem center_coprime {q a : ℕ} (hq : q.Prime) (ha : a ∈ Finset.Ico 1 q) :
    a.Coprime q := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha₀ ha₁)).symm

theorem bigger_radius {n q H : ℕ} (hn : 0 < n) (hq : 0 < q) (hqH : q ≤ H) :
    1/(20*(n:ℝ)) ≤ (H:ℝ)/((q:ℝ)*n) := by
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq' : (q:ℝ) ≤ (H:ℝ) := by exact_mod_cast hqH
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hs := mul_le_mul_of_nonneg_right hq' hnr.le
  nlinarith only [hs, mul_nonneg (Nat.cast_nonneg H) hnr.le]

theorem point_in_unit {n q a : ℕ} (hn : 0 < n) (hqn : q ≤ n) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqn' : (q:ℝ) ≤ (n:ℝ) := by exact_mod_cast hqn
  have hδ : 1/(20*(n:ℝ)) ≤ 1/(q:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hq).2
    linarith
  have hlow : 1/(q:ℝ) ≤ (a:ℝ)/q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₀) hq.le
  have hhigh : (a:ℝ)/q ≤ 1-1/(q:ℝ) := by
    have ht : (a:ℝ)+1≤(q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ha₁
    calc
      _ ≤ ((q:ℝ)-1)/q := div_le_div_of_nonneg_right (by linarith) hq.le
      _ = _ := by rw [sub_div, div_self hq.ne']
  obtain ⟨h₁,h₂⟩ := abs_le.mp (mem_strip.mp ht)
  exact ⟨by linarith, by linarith⟩

theorem point_outside_wide {n R H q a : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hqR : R < q) (hq4 : q ≤ 4*R) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ (wide n R H)ᶜ := by
  intro hw
  obtain ⟨r,b,hr,hrR,_,hcb,hradius⟩ := hw
  have hnr : 0 < n := by omega
  have hqa := center_coprime hq ha
  have hδ := (mem_strip.mp ht).trans (bigger_radius hnr hq.pos (hq4.trans hH))
  have ⟨heq,_⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr
    hq4 (hrR.trans (by omega)) hqa hcb hδ hradius
  omega

theorem strip_index_unique {n R H q r a b : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hr : r.Prime) (hq4 : q ≤ 4*R) (hr4 : r ≤ 4*R)
    (ha : a ∈ Finset.Ico 1 q) (hb : b ∈ Finset.Ico 1 r) {t : ℝ}
    (htq : t ∈ strip n q a) (htr : t ∈ strip n r b) : q=r ∧ a=b := by
  have hnr : 0 < n := by omega
  exact GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr.pos hq4 hr4
    (center_coprime hq ha) (center_coprime hr hb)
    ((mem_strip.mp htq).trans (bigger_radius hnr hq.pos (hq4.trans hH)))
    ((mem_strip.mp htr).trans (bigger_radius hnr hr.pos (hr4.trans hH)))

theorem eventually_strip_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let H := 256 * R * (Nat.log 2 (n+2))^2
      2*H*(4*R) < n ∧ 4*R ≤ H ∧ 4*R ≤ n := by
  obtain ⟨N,hN⟩ := eventuallyExtendedBudget
  refine ⟨N, ?_⟩
  intro n hn R H
  have hbudget : 2*H*(4*R) < n := hN n hn
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 4*R ≤ H := calc
    _ ≤ 256*R := Nat.mul_le_mul_right _ (by decide)
    _ = 256*R*1 := by simp
    _ ≤ H := Nat.mul_le_mul_left _ (by
      have hx := Nat.pow_le_pow_left hlog 2
      simpa using hx)
  have hsize : 4*R ≤ n := by
    by_cases hzero : R=0
    · simp [hzero]
    · have hHp : 1 ≤ H := by omega
      exact (Nat.le_mul_of_pos_left _ (show 0<2*H by omega)).trans hbudget.le
  exact ⟨hbudget,hH,hsize⟩

end GoldbachFourthGeometry

end GoldbachDeepFourthGeometry

section GoldbachDeepFourthPrimeDenominator

namespace GoldbachFourthMoment
open Finset

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- Finite character calculation adapted from DFQDZZ, goldbach-proofs PR 316.
theorem full_phase_sum (q h : ℕ) (hq : 0 < q) :
    (∑ a ∈ range q, phase ((h : ℝ) * a / q)) = if q ∣ h then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
      apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
      · intro a ha
        exact mem_univ _
      · intro a ha b hb hab
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
          ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
      · intro x _
        exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
      · intro a _
        have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
        rw [cast_eq, ZMod.stdAddChar_coe]
        dsimp [phase]
        congr 1
        push_cast
        ring
    _ = _ := by
      by_cases hd : q ∣ h
      · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
        simp [hd, hz, ZMod.card]
      · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
        rw [ite_eq_right hd]
        exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)

theorem prime_phase_sum {q : ℕ} (hq : q.Prime) (h : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)) =
      (if q ∣ h then (q : ℂ) else 0) - 1 := by
  have hF : (range q).filter (fun a => a.Coprime q) = range q \ {0} := by
    ext a
    simp only [mem_filter, mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩
      refine ⟨ha, ?_⟩
      rintro rfl
      exact hq.ne_one (by simpa using hc)
    · rintro ⟨ha, hz⟩
      refine ⟨ha, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
      exact fun hd => hz (Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp ha))
  have hsub : ({0} : Finset ℕ) ⊆ range q := by simpa using hq.pos
  rw [hF]
  calc
    _ = (∑ a ∈ range q, phase ((h : ℝ) * a / q)) -
        (∑ a ∈ ({0} : Finset ℕ), phase ((h : ℝ) * a / q)) :=
      eq_sub_of_add_eq (sum_sdiff hsub)
    _ = _ := by rw [full_phase_sum q h hq.pos]; simp [phase]

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

theorem sum_prime_centers {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) (β : ℝ) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), primeSum n ((a : ℝ) / q + β) =
      -primeSum n β + (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β) := by
  let centers := (range q).filter (fun a => a.Coprime q)
  let term (k : ℕ) := (primeWeight k : ℂ) * phase ((k : ℝ) * β)
  have hphase (k a : ℕ) : (primeWeight k : ℂ) * phase ((k : ℝ) * (a / q + β)) =
      term k * phase ((k : ℝ) * a / q) := by
    rw [show (k : ℝ) * (a / q + β) = (k : ℝ) * a / q + k * β by ring, phase_add]
    dsimp [term]
    ring
  have hterm (k : ℕ) :
      term k * (∑ a ∈ centers, phase ((k : ℝ) * a / q)) =
        -term k + if k = q then (q : ℂ) * term q else 0 := by
    rw [prime_phase_sum hq]
    by_cases hk : k.Prime
    · have hd : q ∣ k ↔ k = q := by
        constructor
        · intro h
          exact ((Nat.dvd_prime hk).mp h).resolve_left hq.ne_one |>.symm
        · rintro rfl
          exact dvd_refl _
      by_cases h : k = q
      · subst k
        rw [ite_eq_left (dvd_refl _), ite_eq_left rfl]
        ring
      · rw [ite_eq_right (fun hh => h (hd.mp hh)), ite_eq_right h]
        ring
    · have hne : k ≠ q := by
        rintro rfl
        exact hk hq
      simp [term, primeWeight, hk, hne]
  unfold primeSum
  simp_rw [hphase]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ k ∈ range (n + 1), term k * ∑ a ∈ centers, phase ((k : ℝ) * a / q)) = _
  simp_rw [hterm, sum_add_distrib, sum_neg_distrib]
  have hqmem : q ∈ range (n + 1) := mem_range.mpr (by omega)
  simp [hqmem, term, primeWeight, hq, mul_assoc]

theorem fourth_power_of_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  let x := ∑ i ∈ s, ‖f i‖
  let y := ∑ i ∈ s, ‖f i‖ ^ 2
  let z := ∑ i ∈ s, ‖f i‖ ^ 4
  let k : ℝ := s.card
  have hx : ‖∑ i ∈ s, f i‖ ≤ x := norm_sum_le _ _
  have h₁ : x ^ 2 ≤ k * y := by
    simpa [x, y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have h₂ : y ^ 2 ≤ k * z := by
    calc
      y ^ 2 ≤ k * ∑ i ∈ s, (‖f i‖ ^ 2) ^ 2 := by
        simpa [y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖ ^ 2)
      _ = k * z := by
        congr 1
        exact sum_congr rfl (fun i _ => by ring)
  change _ ≤ k ^ 3 * z
  calc
    _ ≤ x ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hx 4
    _ = (x ^ 2) ^ 2 := by ring
    _ ≤ (k * y) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = k ^ 2 * y ^ 2 := by ring
    _ ≤ k ^ 2 * (k * z) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring


theorem reduced_eq_Ico {q : ℕ} (hq : q.Prime) :
    (range q).filter (fun a => a.Coprime q) = Ico 1 q := by
  ext a
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨?_, ha⟩
    by_contra! hz
    obtain rfl : a = 0 := by omega
    exact hq.ne_one (by simpa using hc)
  · rintro ⟨ha₁, ha₂⟩
    refine ⟨ha₂, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
    intro hd
    have := Nat.eq_zero_of_dvd_of_lt hd ha₂
    omega

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem primeSum_re (n : ℕ) (β : ℝ) : (primeSum n β).re =
    ∑ k ∈ range (n + 1), primeWeight k * Real.cos (2 * Real.pi * (k : ℝ) * β) := by
  unfold primeSum
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    phase, Complex.exp_ofReal_mul_I_re, mul_assoc]

theorem one_prime_denominator {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n)
    (β : ℝ) (hβ : |β| ≤ 1 / (20 * (n : ℝ)))
    (hθ : (n : ℝ) / 4 ≤ ∑ k ∈ range (n + 1), primeWeight k)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    ((n : ℝ) / 16) ^ 4 / (q : ℝ) ^ 3 ≤
      ∑ a ∈ Ico 1 q, ‖primeSum n ((a : ℝ) / q + β)‖ ^ 4 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hq.pos.trans_le hqn
  have hcos (k : ℕ) (hk : k ∈ range (n + 1)) :
      (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) * β) := by
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
    have hangle : |2 * Real.pi * (k : ℝ) * β| ≤ Real.pi / 3 := by
      calc
        _ = 2 * Real.pi * (k : ℝ) * |β| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Real.pi * (n : ℝ) * (1 / (20 * (n : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkN (by positivity)) hβ
            (abs_nonneg _) (by positivity)
        _ = Real.pi / 10 := by
          field_simp
          ring
        _ ≤ Real.pi / 3 := by linarith [Real.pi_pos]
    calc
      _ = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |2 * Real.pi * (k : ℝ) * β| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
      _ = _ := Real.cos_abs _
  have hs : (n : ℝ) / 8 ≤ (primeSum n β).re := by
    rw [primeSum_re]
    calc
      _ ≤ (∑ k ∈ range (n + 1), primeWeight k) * (1 / 2 : ℝ) := by linarith
      _ = ∑ k ∈ range (n + 1), primeWeight k * (1 / 2 : ℝ) := by rw [sum_mul]
      _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcos k hk) (primeWeight_nonneg k)
  let C := Ico 1 q
  let F (a : ℕ) := primeSum n ((a : ℝ) / q + β)
  let Z : ℂ := (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β)
  have hsum : (∑ a ∈ C, F a) = -primeSum n β + Z := by
    simpa only [C, F, ← reduced_eq_Ico hq, Z] using sum_prime_centers hq hqn β
  have hZ : ‖Z‖ = (q : ℝ) * Real.log q := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
    have hphase : ‖phase ((q : ℝ) * β)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [Z, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, hphase, mul_one]
  have hback : ‖primeSum n β‖ ≤ ‖-primeSum n β + Z‖ + ‖Z‖ := by
    simpa only [add_sub_cancel_right, norm_neg] using norm_sub_le (-primeSum n β + Z) Z
  have hnorm : (n : ℝ) / 16 ≤ ‖∑ a ∈ C, F a‖ := by
    have hre : (primeSum n β).re ≤ ‖primeSum n β‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [hZ] at hback
    rw [hsum]
    linarith
  have hC : C.card ≤ q := by
    calc
      _ ≤ (range q).card := card_le_card fun a ha => mem_range.mpr (mem_Ico.mp ha).2
      _ = _ := card_range _
  have hnonneg : 0 ≤ ∑ a ∈ C, ‖F a‖ ^ 4 := sum_nonneg fun _ _ => by positivity
  apply (div_le_iff₀ (pow_pos hqR 3)).2
  change ((n : ℝ) / 16) ^ 4 ≤ (∑ a ∈ C, ‖F a‖ ^ 4) * (q : ℝ) ^ 3
  calc
    _ ≤ ‖∑ a ∈ C, F a‖ ^ 4 := pow_le_pow_left₀ (by positivity) hnorm 4
    _ ≤ (C.card : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 := fourth_power_of_sum_le C F
    _ ≤ (q : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hC) 3) hnonneg
    _ = _ := mul_comm _ _

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeDenominator

section GoldbachDeepFourthPrimeCount

open Filter Finset
open scoped BigOperators

namespace GoldbachFourthMoment

theorem theta_eq_prime_log_sum (n : ℕ) :
    Chebyshev.theta n =
      ∑ k ∈ Finset.range (n + 1), if Nat.Prime k then Real.log (k : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
    Nat.range_succ_eq_Icc_zero]

theorem eventually_theta_half : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have h := Chebyshev.isLittleO_psi_sub_theta_id.def (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [h.natCast_atTop, eventually_ge_atTop 7] with n hn h7
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hn'] at hn
  have hlog : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlo := mul_le_mul_of_nonneg_left hlog hn'
  linarith [Chebyshev.psi_ge_of_seven_le h7, (abs_le.mp hn).2]

theorem eventually_theta_quarter : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  filter_upwards [eventually_theta_half] with n hn
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem prime_denominators_log_floor :
    ∀ᶠ R : ℕ in atTop,
      (R : ℝ) / 2 ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_theta_half
  filter_upwards [eventually_ge_atTop N] with R hR
  have hR4 : R ≤ 4 * R := by omega
  have hhigh := hN (4 * R) (hR.trans hR4)
  push_cast at hhigh
  have hlow := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg R)
  have hlog : Real.log 4 ≤ (3 / 2 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hlow' := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg R : 0 ≤ (R : ℝ))
  have hsplit : Chebyshev.theta (R : ℝ) +
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) =
        Chebyshev.theta ((4 * R : ℕ) : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive
      (fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0) (Nat.zero_le R) hR4
  push_cast at hsplit
  have hupper :
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
    apply Real.log_le_log (by exact_mod_cast hpPrime.pos)
    exact_mod_cast (Finset.mem_Ioc.mp hpI).2
  linarith

private theorem eventually_log_le_mul_rpow (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_atTop hs).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
    using (le_abs_self (Real.log (n : ℝ))).trans hn

private theorem cube_root_floor_tendsto :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_atTop.2 fun m =>
    ((tendsto_atTop.1 h) (m : ℝ)).mono fun n hn => Nat.le_floor hn

theorem eventually_many_prime_denominators : ∀ᶠ n : ℕ in atTop,
    let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (((Finset.Ioc R (4*R)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [cube_root_floor_tendsto.eventually prime_denominators_log_floor,
    eventually_log_le_mul_rpow (1 / 12) (1 / 8) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hc hlog hn
  let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  change (R : ℝ) / 2 ≤ _ at hc
  change (n : ℝ) ^ (1 / 4 : ℝ) ≤ _
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 1/3))
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRlo : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (R : ℝ) := by
    have h := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ))
    change (n : ℝ) ^ (1 / 3 : ℝ) < (R : ℝ) + 1 at h
    linarith
  have hRhi : (R : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hnPos.le _)
      _ ≤ _ := by simpa using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1)
  have hlogR : Real.log (4 * (R : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith)
        (by nlinarith only [hRhi, hnR, sq_nonneg ((n : ℝ) - 4)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hnPos]
    congr 1
    norm_num
  apply le_of_mul_le_mul_right _ (Real.log_pos (by linarith : 1 < 4 * (R : ℝ)))
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogR (Real.rpow_nonneg hnPos.le _)
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by rw [← hpow]; ring
    _ ≤ (R : ℝ) / 2 := by linarith
    _ ≤ _ := hc

theorem eventually_small_denominator_log : ∀ᶠ n : ℕ in atTop,
    ∀ q : ℕ, q ≤ 4 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ →
      (q : ℝ) * Real.log (q : ℝ) ≤ (n : ℝ) / 16 := by
  filter_upwards [eventually_log_le_mul_rpow (2 / 3) (1 / 128) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hlog hn
  intro q hq
  rcases q.eq_zero_or_pos with rfl | hqPos
  · simp
    positivity
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hqPos' : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hqHi : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 3 : ℝ) := calc
    _ ≤ 4 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hnPos.le _)) (by norm_num)
  have hqHi' : (q : ℝ) ≤ 4 * (n : ℝ) := hqHi.trans <|
    mul_le_mul_of_nonneg_left
      (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1))
      (by norm_num)
  have hlogq : Real.log (q : ℝ) ≤ 2 * Real.log (n : ℝ) := calc
    _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hqPos'
      (by nlinarith only [hqHi', hnR, sq_nonneg ((n : ℝ) - 4)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnPos]
    norm_num
  calc
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * Real.log (n : ℝ)) := by
      apply mul_le_mul hqHi hlogq
      · exact Real.log_nonneg (by exact_mod_cast hqPos)
      · positivity
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * ((1 / 128 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) / 16 := by ring
    _ = _ := congrArg (fun x : ℝ => x / 16) hpow

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeCount

section GoldbachDeepFourthScaling

namespace GoldbachFourthMoment

theorem cube_denominator_bound {n q : ℕ}
    (hq : q ≤ 4 * ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊) :
    (q : ℝ)^3 ≤ 64 * (n : ℝ) := by
  have hqReal : (q : ℝ) ≤ 4 * (⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ : ℕ) := by
    exact_mod_cast hq
  have hqUpper : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1/3 : ℝ) :=
    hqReal.trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by norm_num))
  calc
    _ ≤ (4 * (n : ℝ) ^ (1/3 : ℝ)) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg q) hqUpper _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        show (1/3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
      norm_num

theorem growth_beats_upper {n : ℕ} (hn : 0 < n)
    (hg : (41943040 : ℝ) < (n : ℝ) ^ (1/8 : ℝ)) :
    (n : ℝ)^(2 + (1/8 : ℝ)) < (n : ℝ)^(1/4 : ℝ) * ((n : ℝ)^2 / 41943040) := by
  have hnReal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hQuarter : (n : ℝ) ^ (1/4 : ℝ) =
      (n : ℝ) ^ (1/8 : ℝ) * (n : ℝ) ^ (1/8 : ℝ) := by
    rw [← Real.rpow_add hnReal, show (1/8 : ℝ) + 1/8 = 1/4 by norm_num]
  rw [Real.rpow_add hnReal, Real.rpow_two, hQuarter, ← mul_div_assoc]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 41943040)).2
  have hFactor : 0 < (n : ℝ)^2 * (n : ℝ) ^ (1/8 : ℝ) :=
    mul_pos (pow_pos hnReal _) (Real.rpow_pos_of_pos hnReal _)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_lt_mul_of_pos_left hg hFactor

theorem eventual_growth_input :
    ∃ N : ℕ, ∀ n ≥ N, (41943040 : ℝ) < (n : ℝ) ^ (1/8 : ℝ) := by
  refine ⟨41943041 ^ 8, fun n hn => ?_⟩
  have hnReal : (41943041 : ℝ)^8 ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    (41943040 : ℝ) < 41943041 := by norm_num
    _ = ((41943041 : ℝ)^8) ^ (1/8 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 41943041),
        show (8 : ℕ) * (1/8 : ℝ) = 1 by norm_num, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) hnReal (by norm_num)

end GoldbachFourthMoment

end GoldbachDeepFourthScaling

section GoldbachDisjointWindowIntegral

open MeasureTheory Set
open scoped BigOperators Interval

/-- Disjoint translated windows contained in a mask contribute at most its full integral. -/
theorem goldbachDisjointWindowIntegral_le {ι : Type*}
    (s : Finset ι) (center : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (D : Set ℝ) (hD : MeasurableSet D) (F : ℝ → ℝ)
    (hF : Continuous F) (hF₀ : ∀ x, 0 ≤ F x)
    (hCover : ∀ i ∈ s, Icc (center i - δ) (center i + δ) ⊆ D ∩ Icc 0 1)
    (hDisj : (↑s : Set ι).PairwiseDisjoint (fun i => Icc (center i - δ) (center i + δ))) :
    (∑ i ∈ s, ∫ β in (-δ)..δ, F (center i + β)) ≤ ∫ t in (0 : ℝ)..1, D.indicator F t := by
  let W (i : ι) := Ioc (center i - δ) (center i + δ)
  have hEnds (i : ι) : center i - δ ≤ center i + δ := by linarith only [hδ]
  have hWindowSub (i : ι) (hi : i ∈ s) : W i ⊆ Ioc (0 : ℝ) 1 ∩ D := by
    intro t ht
    have hl := hCover i hi (left_mem_Icc.mpr (hEnds i))
    have hx := hCover i hi (Ioc_subset_Icc_self ht)
    exact ⟨⟨hl.2.1.trans_lt ht.1, hx.2.2⟩, hx.1⟩
  have hUnionSub : (⋃ i ∈ s, W i) ⊆ Ioc (0 : ℝ) 1 ∩ D := by
    intro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i, hi, ht'⟩ := ht
    exact hWindowSub i hi ht'
  have hWDisjoint : (↑s : Set ι).PairwiseDisjoint W :=
    hDisj.mono fun _ => Ioc_subset_Icc_self
  have hFMask : IntegrableOn F (Ioc (0 : ℝ) 1 ∩ D) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1.mono_set inter_subset_left
  calc
    _ = ∑ i ∈ s, ∫ t in W i, F t := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_comp_add_left, ← sub_eq_add_neg,
        intervalIntegral.integral_of_le (hEnds i)]
    _ = ∫ t in ⋃ i ∈ s, W i, F t := by
      symm
      exact integral_biUnion_finset s (fun _ _ => measurableSet_Ioc) hWDisjoint
        (fun i _ => (hF.intervalIntegrable (center i - δ) (center i + δ)).1)
    _ ≤ ∫ t in Ioc (0 : ℝ) 1 ∩ D, F t :=
      setIntegral_mono_set hFMask (Filter.Eventually.of_forall hF₀) hUnionSub.eventuallySubset
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hD]

end GoldbachDisjointWindowIntegral

section GoldbachDeepFourthMomentRefutation

open Filter Finset MeasureTheory Set
open scoped BigOperators Interval

namespace GoldbachFourthMoment

private theorem wide_measurable (n R H : ℕ) :
    MeasurableSet (GoldbachFourthGeometry.wide n R H) := by
  unfold GoldbachFourthGeometry.wide
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hcont : Continuous fun t : ℝ => |t - (a : ℝ) / (q : ℝ)| := by fun_prop
    have hm : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (H : ℝ) / ((q : ℝ) * n)} :=
      measurableSet_le hcont.measurable measurable_const
    convert hm using 1
    ext t
    exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h₁, h₂, h₃, h₄, ht⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩

private noncomputable def fourth (n : ℕ) (t : ℝ) : ℝ := ‖primeSum n t‖ ^ 4

private theorem fourth_continuous (n : ℕ) : Continuous (fourth n) := by
  unfold fourth primeSum phase
  fun_prop

private theorem one_denominator_integral {n q : ℕ} (hn : 0 < n)
    (hq : q.Prime) (hqn : q ≤ n)
    (hqR : q ≤ 4 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊)
    (hθ : (n : ℝ) / 4 ≤ ∑ k ∈ Finset.range (n + 1), primeWeight k)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    let δ : ℝ := 1 / (20 * (n : ℝ))
    (n : ℝ)^2 / 41943040 ≤
      ∑ a ∈ Finset.Ico 1 q, ∫ b in (-δ)..δ, fourth n ((a : ℝ) / q + b) := by
  intro δ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hends : -δ ≤ δ := by linarith
  have hlocal (b : ℝ) (hb : b ∈ Set.Icc (-δ) δ) :
      (n : ℝ)^3 / 4194304 ≤ ∑ a ∈ Finset.Ico 1 q, fourth n ((a : ℝ) / q + b) := by
    have hb' : |b| ≤ δ := abs_le.mpr hb
    calc
      _ = ((n : ℝ) / 16)^4 / (64 * (n : ℝ)) := by
        field_simp [hnR.ne']
        ring
      _ ≤ ((n : ℝ) / 16)^4 / (q : ℝ)^3 :=
        div_le_div_of_nonneg_left (by positivity)
          (pow_pos (by exact_mod_cast hq.pos) _) (cube_denominator_bound hqR)
      _ ≤ _ := one_prime_denominator hq hqn b hb' hθ hsmall
  have hcont (a : ℕ) : Continuous (fun b : ℝ => fourth n ((a : ℝ) / q + b)) :=
    (fourth_continuous n).comp (continuous_const.add continuous_id)
  have bound := intervalIntegral.integral_mono_on hends
    (continuous_const.intervalIntegrable (-δ) δ :
      IntervalIntegrable (fun _ : ℝ => (n : ℝ)^3 / 4194304) volume (-δ) δ)
    ((continuous_finsetSum _ fun a _ => hcont a).intervalIntegrable (-δ) δ)
    hlocal
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_finsetSum (fun a _ => (hcont a).intervalIntegrable (-δ) δ)] at bound
  convert bound using 1
  dsimp [δ]
  field_simp [hnR.ne']
  ring

private theorem moment_lower {n : ℕ} (hn : 0 < n) :
    let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    let H := 256 * R * (Nat.log 2 (n+2))^2
    2 * H * (4 * R) < n → 4 * R ≤ H → 4 * R ≤ n →
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) →
    ((n : ℝ) / 4 ≤ ∑ k ∈ Finset.range (n + 1), primeWeight k) →
    (∀ q : ℕ, q ≤ 4 * R → (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) →
    (n : ℝ) ^ (1 / 4 : ℝ) * ((n : ℝ)^2 / 41943040) ≤
      ∫ t in (0 : ℝ)..1, (GoldbachFourthGeometry.wide n R H)ᶜ.indicator (fourth n) t := by
  intro R H hcut hH hsize hcount hθ hsmall
  let δ : ℝ := 1 / (20 * (n : ℝ))
  let A := (Finset.Ioc R (4 * R)).filter Nat.Prime
  let indices := A.sigma (fun q => Finset.Ico 1 q)
  let center (i : Σ _ : ℕ, ℕ) : ℝ := (i.2 : ℝ) / i.1
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hidx (i : Σ _ : ℕ, ℕ) (hi : i ∈ indices) :
      i.1.Prime ∧ R < i.1 ∧ i.1 ≤ 4 * R ∧ i.2 ∈ Finset.Ico 1 i.1 := by
    obtain ⟨hA, ha⟩ := Finset.mem_sigma.mp hi
    obtain ⟨hI, hp⟩ := Finset.mem_filter.mp hA
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hI
    exact ⟨hp, hl, hu, ha⟩
  have hcover (i : Σ _ : ℕ, ℕ) (hi : i ∈ indices) :
      Set.Icc (center i - δ) (center i + δ) ⊆
        (GoldbachFourthGeometry.wide n R H)ᶜ ∩ Set.Icc 0 1 := by
    obtain ⟨hp, hlow, hhigh, ha⟩ := hidx i hi
    intro t ht
    exact ⟨GoldbachFourthGeometry.point_outside_wide hcut hH hp hlow hhigh ha ht,
      GoldbachFourthGeometry.point_in_unit hn (hhigh.trans hsize) ha ht⟩
  have hdisj : (↑indices : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint
      (fun i => Set.Icc (center i - δ) (center i + δ)) := by
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro t htI htJ
    obtain ⟨hpi, _, hhi, hai⟩ := hidx i hi
    obtain ⟨hpj, _, hhj, haj⟩ := hidx j hj
    obtain ⟨hden, hnum⟩ := GoldbachFourthGeometry.strip_index_unique hcut hH
      hpi hpj hhi hhj hai haj htI htJ
    exact hne (Sigma.ext hden (heq_of_eq hnum))
  have hwindows := goldbachDisjointWindowIntegral_le indices center δ hδ _
    (wide_measurable n R H).compl (fourth n) (fourth_continuous n)
    (fun t => by unfold fourth; positivity) hcover hdisj
  calc
    _ ≤ (A.card : ℝ) * ((n : ℝ)^2 / 41943040) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ∑ q ∈ A, (n : ℝ)^2 / 41943040 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ A, ∑ a ∈ Finset.Ico 1 q, ∫ b in (-δ)..δ, fourth n ((a : ℝ) / q + b) := by
      apply Finset.sum_le_sum
      intro q hq
      have hp := (Finset.mem_filter.mp hq).2
      have hhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      exact one_denominator_integral hn hp (hhi.trans hsize) hhi hθ (hsmall q hhi)
    _ = ∑ i ∈ indices, ∫ b in (-δ)..δ, fourth n (center i + b) := by
      exact (Finset.sum_sigma A (fun q => Finset.Ico 1 q)
        (fun i => ∫ b in (-δ)..δ, fourth n (center i + b))).symm
    _ ≤ _ := hwindows

/-- The frozen catalogue statement fails at η = 1/8. -/
theorem deep_fourth_moment_false :
    ¬ (
      let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
      let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
      let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t));
      let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
      let H := fun n : ℕ => 256 * Q₁ n * Q n;
      let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))};
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)
    ) := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 8) (by norm_num)
  obtain ⟨Ngeom, hgeom⟩ := GoldbachFourthGeometry.eventually_strip_budget
  obtain ⟨Ngrowth, hgrowth⟩ := eventual_growth_input
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop Ngeom,
      eventually_ge_atTop (1 : ℕ), eventually_theta_quarter, eventually_many_prime_denominators,
      eventually_small_denominator_log, eventually_ge_atTop Ngrowth]
      with n hnN hnG hn htheta hcount hsmall hg
    obtain ⟨hcut, hH, hsize⟩ := hgeom n hnG
    rw [theta_eq_prime_log_sum] at htheta
    have hlow := moment_lower hn hcut hH hsize hcount htheta hsmall
    have hhigh := hN n hnN
    exact (not_lt_of_ge (hlow.trans hhigh)) (growth_beats_upper hn (hgrowth n hg))
  obtain ⟨n, hn⟩ := eventually_atTop.mp hfalse
  exact hn n le_rfl

end GoldbachFourthMoment

theorem PEqualNP.Outside.L_goldbach_deep_fourth_moment_refutation :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) ^ (2 + η)) :=
  GoldbachFourthMoment.deep_fourth_moment_false

end GoldbachDeepFourthMomentRefutation
