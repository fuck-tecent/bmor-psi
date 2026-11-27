import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import Conjectures.Goldbach.DynThinWindowExceptions
import Conjectures.Goldbach.LowSkirtFromShortProgressions

set_option maxRecDepth 100000 in
section
set_option maxHeartbeats 2000000 in
section

/-!
# Uniform central Goldbach exceptional sets in square-root intervals
Research task: L-goldbach-beaumont-one-sided-hole-cluster.
The frozen theorem is proved unconditionally at the end of this file.
SPDX-License-Identifier: Apache-2.0
Source attributions for adapted finite and analytic arguments are retained below.
-/


/- Source: BeaumontLowModulusCore.lean -/
section


/- Source section: BeaumontPolylogZeroFree.lean -/


/-! The actual character Vinogradov--Korobov zero-free theorem already
proved in the accepted R11/#3746 foundation, with an arbitrary fixed
polylogarithmic modulus exponent. No new zero-free hypothesis is used. -/


namespace GoldbachPolylogZeroFree
open Complex Filter
open scoped Topology

/-- The numerical VK width dominates every prescribed logarithmic saving,
uniformly over any fixed polylogarithmic conductor range. -/
theorem vk_width_polylog (A K : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X → ∀ q H : ℝ,
      1≤q → q≤(Real.log X)^K → 1≤H → H≤4*Real.log X →
      V1l.V2j A X≤c*H^(-(2/3:ℝ))/(1+Real.log q+Real.log H) := by
  have hk : 0<(K:ℝ)+1 := by positivity
  obtain ⟨X₀,hcut⟩ := Vjs.V1vq A (c/((K:ℝ)+1)) (div_pos hc hk)
  have hLcut := Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)
  have he : ∀ᶠ X : ℝ in atTop, ∀ q H : ℝ,
      1≤q → q≤(Real.log X)^K → 1≤H → H≤4*Real.log X →
      V1l.V2j A X≤c*H^(-(2/3:ℝ))/(1+Real.log q+Real.log H) := by
    filter_upwards [eventually_ge_atTop X₀,hLcut] with X hX hL
    intro q H hq hqL hH hHL
    let L := Real.log X
    have hL' : 1≤L := hL
    have hLp : 0<L := zero_lt_one.trans_le hL'
    have hLold : L≤2*L^24 := by
      have hp : 1≤L^23 := one_le_pow₀ hL'
      have hm := mul_le_mul_of_nonneg_left hp hLp.le
      nlinarith only [hm,hLp,show L*L^23=L^24 by ring]
    have hb := hcut X hX L H hL' hLold hH hHL
    have hlogq : Real.log q≤(K:ℝ)*Real.log L := by
      calc
        _ ≤ Real.log (L^K) := Real.log_le_log (by linarith) hqL
        _ = _ := by rw [Real.log_pow]
    have hlogL : 0≤Real.log L := Real.log_nonneg hL'
    have hlogH : 0≤Real.log H := Real.log_nonneg hH
    have hden : 1+Real.log q+Real.log H ≤
        ((K:ℝ)+1)*(1+Real.log L+Real.log H) := by
      nlinarith [show 0≤(K:ℝ) by positivity,
        mul_nonneg (show 0≤(K:ℝ) by positivity) hlogH]
    have hdq : 0<1+Real.log q+Real.log H := by
      linarith [Real.log_nonneg hq]
    have hdL : 0<1+Real.log L+Real.log H := by linarith
    apply hb.trans
    rw [show (c/((K:ℝ)+1))*H^(-(2/3:ℝ))/(1+Real.log L+Real.log H) =
        c*H^(-(2/3:ℝ))/(((K:ℝ)+1)*(1+Real.log L+Real.log H)) by
      field_simp]
    exact div_le_div_of_nonneg_left
      (mul_nonneg hc.le (Real.rpow_nonneg (by linarith) _)) hdq hden
  exact eventually_atTop.mp he

/-- Actual high character zeros are uniformly outside any fixed
logarithmic-saving strip when the modulus is at most `log(X)^K`. -/
theorem actual_high_zero_gap_polylog (A K : ℕ) :
    ∃ T₀ : ℝ, 0<T₀ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X →
      ∀ (q : ℕ) [NeZero q], (q:ℝ)≤(Real.log X)^K →
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ),
        T₀≤|z.im| → |z.im|≤X^2 → z.re<1 →
        DirichletCharacter.LFunction χ z=0 → z.re≤1-V1l.V2j A X := by
  obtain ⟨c,C,T₀,hc,hC,hT₀,hstrip⟩ := OAI.Vg.V1bc
  obtain ⟨X₀,hcut⟩ := vk_width_polylog A K c hc
  refine ⟨T₀,hT₀,max X₀ 2,?_⟩
  intro X hX q _ hq χ z ht htX hβ hz
  have hXX : X₀≤X := (le_max_left _ _).trans hX
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  obtain ⟨hH,hHX⟩ := Vjs.V1w7 X z.im hX2 htX
  change 1≤OAI.Vg.V96 (2*z.im) at hH
  change OAI.Vg.V96 (2*z.im)≤4*Real.log X at hHX
  have hgap := hcut X hXX (q:ℝ) (OAI.Vg.V96 (2*z.im)) hq1 hq hH hHX
  change V1l.V2j A X≤c*OAI.Vg.V36 (2*z.im)/OAI.Vg.Vcw q (2*z.im) at hgap
  by_contra hb
  have hnear : 1-V1l.V2j A X<z.re := lt_of_not_ge hb
  have hupper : z.re≤1+OAI.Vg.V36 (2*z.im)/16 := by
    have hr : 0≤OAI.Vg.V36 (2*z.im) :=
      Real.rpow_nonneg (by linarith : 0≤OAI.Vg.V96 (2*z.im)) _
    linarith
  have hn := (hstrip q χ z.im z.re ht (by linarith) hupper).1
  have he : (z.re:ℂ)+I*(z.im:ℂ)=z := by apply Complex.ext <;> simp
  rw [he] at hn
  exact hn hz


end GoldbachPolylogZeroFree


/-! Uniform zero-free logarithmic strips for every fixed polylogarithmic
conductor range. The low-frequency part uses the actual R11 Siegel theorem
and classical complex-zero reduction, both rechecked in the supplement. -/


namespace GoldbachPolylogZeroFree
open Complex Filter OAI.Ostmann
open scoped Topology

private theorem siegel_product_identity (A : ℕ) (C X : ℝ) (hX : 1<X) :
    V1l.V2j A X*(C*(Real.log X)^(1/2:ℝ)) =
      (3*C*(A+14:ℕ))*(Real.log (Real.log X)/(Real.log X)^(1/2:ℝ)) := by
  have hL : 0<Real.log X := Real.log_pos hX
  have hR : 0<(Real.log X)^(1/2:ℝ) := Real.rpow_pos_of_pos hL _
  have hs : ((Real.log X)^(1/2:ℝ))^2=Real.log X := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hL.le]
    norm_num
  dsimp [V1l.V2j]
  field_simp
  rw [hs]
  ring

/-- Siegel's actual real-zero estimate, uniform over `q≤log(X)^K`. -/
theorem siegel_gap_polylog (A K : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X → ∀ e : PrimitiveRealZero,
      (e.modulus:ℝ)≤(Real.log X)^K → e.beta≤1-V1l.V2j A X := by
  let epsilon : ℝ := 1/(2*((K:ℝ)+1))
  have hepsilon : 0<epsilon := by dsimp [epsilon]; positivity
  have hpower : (K:ℝ)*epsilon≤1/2 := by
    dsimp [epsilon]
    have hk : 0<2*((K:ℝ)+1) := by positivity
    rw [mul_one_div,div_le_iff₀ hk]
    linarith
  obtain ⟨C,hC,hSiegel⟩ := V1uy epsilon hepsilon
  have ht : Tendsto
      (fun X : ℝ => Real.log (Real.log X)/(Real.log X)^(1/2:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
      Real.tendsto_log_atTop
  have hm := ht.const_mul (3*C*(A+14:ℕ):ℝ)
  simp only [mul_zero] at hm
  have hsmall := hm.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have he : ∀ᶠ X : ℝ in atTop, ∀ e : PrimitiveRealZero,
      (e.modulus:ℝ)≤(Real.log X)^K → e.beta≤1-V1l.V2j A X := by
    filter_upwards [hsmall,V1l.Vgn A] with X hsmall hX
    intro e heq
    have hL : 0<Real.log X := Real.log_pos hX.1
    have hp : (e.modulus:ℝ)^epsilon≤(Real.log X)^(1/2:ℝ) := by
      calc
        _ ≤ ((Real.log X)^K)^epsilon :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) heq hepsilon.le
        _ = (Real.log X)^((K:ℝ)*epsilon) := by
          rw [←Real.rpow_natCast, ←Real.rpow_mul hL.le]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX.2.1 hpower
    have hb := (hSiegel e).trans (mul_le_mul_of_nonneg_left hp hC.le)
    have hprod : V1l.V2j A X*(1-e.beta)⁻¹≤1 := by
      calc
        _ ≤ V1l.V2j A X*(C*(Real.log X)^(1/2:ℝ)) :=
          mul_le_mul_of_nonneg_left hb hX.2.2.1
        _ = _ := siegel_product_identity A C X hX.1
        _ ≤ 1 := hsmall.le
    have hd : V1l.V2j A X≤1-e.beta := by
      apply (div_le_one (sub_pos.mpr e.beta_lt_one)).mp
      simpa only [div_eq_mul_inv] using hprod
    linarith
  exact eventually_atTop.mp he

/-- At polylogarithmic heights the classical zero-free width is much
larger than any fixed `log log X / log X` strip. -/
theorem classical_width_polylog (A K J : ℕ) (c : ℝ) (hc : 0<c) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X → ∀ q T : ℝ,
      1≤q → q≤(Real.log X)^K → 2≤T → T≤(Real.log X)^J →
      V1l.V2j A X≤c/Real.log (2*q*T) := by
  have ht : Tendsto
      (fun X : ℝ => (Real.log (Real.log X))^2/Real.log X) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      h.comp Real.tendsto_log_atTop
  have hm := ht.const_mul (3*(A+14:ℕ)*((K:ℝ)+(J:ℝ)+1):ℝ)
  simp only [mul_zero] at hm
  have hsmall := hm.eventually (gt_mem_nhds hc)
  have hLcut := Real.tendsto_log_atTop.eventually_ge_atTop (2:ℝ)
  have he : ∀ᶠ X : ℝ in atTop, ∀ q T : ℝ,
      1≤q → q≤(Real.log X)^K → 2≤T → T≤(Real.log X)^J →
      V1l.V2j A X≤c/Real.log (2*q*T) := by
    filter_upwards [hsmall,hLcut,V1l.Vgn A] with X hsmall hL hX
    intro q T hq hqL hT hTL
    have hLp : 0<Real.log X := by linarith
    have hqlog : Real.log q≤(K:ℝ)*Real.log (Real.log X) := by
      calc
        _ ≤ Real.log ((Real.log X)^K) := Real.log_le_log (by linarith) hqL
        _ = _ := by rw [Real.log_pow]
    have hTlog : Real.log T≤(J:ℝ)*Real.log (Real.log X) := by
      calc
        _ ≤ Real.log ((Real.log X)^J) := Real.log_le_log (by linarith) hTL
        _ = _ := by rw [Real.log_pow]
    have htwo : Real.log 2≤Real.log (Real.log X) :=
      Real.log_le_log (by norm_num) hL
    have hden : Real.log (2*q*T)≤((K:ℝ)+(J:ℝ)+1)*Real.log (Real.log X) := by
      rw [Real.log_mul (by positivity : 2*q≠0) (by linarith : T≠0),
        Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : q≠0)]
      linarith
    have hdenpos : 0<Real.log (2*q*T) := Real.log_pos (by nlinarith)
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ V1l.V2j A X*(((K:ℝ)+(J:ℝ)+1)*Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hden hX.2.2.1
      _ = (3*(A+14:ℕ)*((K:ℝ)+(J:ℝ)+1))*
          ((Real.log (Real.log X))^2/Real.log X) := by
        dsimp [V1l.V2j]
        ring
      _ ≤ c := hsmall.le
  exact eventually_atTop.mp he

/-- The actual low zeros of all primitive nonprincipal characters in a
fixed polylogarithmic conductor range obey a uniform logarithmic gap. -/
theorem actual_low_zero_gap_polylog (A K J : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X →
      ∀ χ : PrimitiveComplexCharacter, (χ.modulus:ℝ)≤(Real.log X)^K →
      ∀ i : ℕ, |((V1 χ).zeros i).im|≤(Real.log X)^J →
        ((V1 χ).zeros i).re≤1-V1l.V2j A X := by
  obtain ⟨c,hc,hreduce⟩ := Vta.V10u
  obtain ⟨Xc,hclassic⟩ := classical_width_polylog A K (J+1) c hc
  obtain ⟨Xs,hSiegel⟩ := siegel_gap_polylog A K
  have hLcut := Real.tendsto_log_atTop.eventually_ge_atTop (2:ℝ)
  have he : ∀ᶠ X : ℝ in atTop,
      ∀ χ : PrimitiveComplexCharacter, (χ.modulus:ℝ)≤(Real.log X)^K →
      ∀ i : ℕ, |((V1 χ).zeros i).im|≤(Real.log X)^J →
        ((V1 χ).zeros i).re≤1-V1l.V2j A X := by
    filter_upwards [eventually_ge_atTop Xc,eventually_ge_atTop Xs,hLcut]
      with X hXc hXs hL
    intro χ hq i ht
    let T := max 2 ((Real.log X)^J)
    have hT : 2≤T := le_max_left _ _
    have hTpow : T≤(Real.log X)^(J+1) := by
      have hp : 1≤(Real.log X)^J := one_le_pow₀ (by linarith : 1≤Real.log X)
      dsimp [T]
      rw [pow_succ]
      apply max_le <;> nlinarith
    have hq1 : (1:ℝ)≤χ.modulus := by exact_mod_cast χ.positive
    have hwidth := hclassic X hXc χ.modulus T hq1 hq hT hTpow
    by_contra hb
    have hnear : 1-c/Real.log (2*(χ.modulus:ℝ)*T)≤((V1 χ).zeros i).re := by
      have := lt_of_not_ge hb
      linarith
    obtain ⟨e,heq,hebeta,_heχ⟩ := hreduce χ.modulus χ.positive T hT χ le_rfl i
      (ht.trans (le_max_right _ _)) hnear
    have heqbound : (e.modulus:ℝ)≤(Real.log X)^K := by simpa only [heq] using hq
    have hegap := hSiegel X hXs e heqbound
    rw [hebeta] at hegap
    exact hb hegap
  exact eventually_atTop.mp he

/-- All actual nonprincipal character zeros up to height `X^2` satisfy
the required strip, uniformly for every fixed polylogarithmic conductor
range. This joins the unconditional Siegel and high-frequency VK inputs. -/
theorem actual_all_zero_gap_polylog (A K : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀≤X →
      ∀ χ : PrimitiveComplexCharacter, (χ.modulus:ℝ)≤(Real.log X)^K →
      ∀ i : ℕ, |((V1 χ).zeros i).im|≤X^2 →
        ((V1 χ).zeros i).re≤1-V1l.V2j A X := by
  obtain ⟨T₀,hT₀,Xh,hh⟩ := actual_high_zero_gap_polylog A K
  obtain ⟨Xl,hl⟩ := actual_low_zero_gap_polylog A K 1
  have hLcut := Real.tendsto_log_atTop.eventually_ge_atTop T₀
  have he : ∀ᶠ X : ℝ in atTop,
      ∀ χ : PrimitiveComplexCharacter, (χ.modulus:ℝ)≤(Real.log X)^K →
      ∀ i : ℕ, |((V1 χ).zeros i).im|≤X^2 →
        ((V1 χ).zeros i).re≤1-V1l.V2j A X := by
    filter_upwards [eventually_ge_atTop Xh,eventually_ge_atTop Xl,hLcut]
      with X hXh hXl hL
    intro χ hq i hi
    by_cases hlow : |((V1 χ).zeros i).im|≤T₀
    · exact hl X hXl χ hq i (by simpa only [pow_one] using hlow.trans hL)
    · letI : NeZero χ.modulus := ⟨χ.positive.ne'⟩
      have hz : DirichletCharacter.LFunction χ.character ((V1 χ).zeros i)=0 :=
        (V1 χ).actual_zero i
      exact hh X hXh χ.modulus hq χ.character ((V1 χ).zeros i)
        (le_of_not_ge hlow) hi ((V1 χ).in_strip i).2 hz
  exact eventually_atTop.mp he


end GoldbachPolylogZeroFree

/- Source section: BeaumontPolylogBoundary.lean -/

/-! General conductor range for the actual short progression mean.  The
zero-density moment is reused without changing its exponent; only the
polylogarithmic conductor parameter and the elementary explicit-formula
remainder estimate are generalized. -/


open Finset Filter MeasureTheory Complex
open scoped Topology Interval BigOperators Classical
open OAI.Ostmann V7e Viu V86 V11r Vg1 Vct V6i V1e Vx
open ArithmeticFunction Vel V2h V5d ThinBoundary

namespace BeaumontPolylogBoundary
noncomputable section

open V82 Vex Vbt

private theorem largeModulus_Vja (f : ℝ → ℂ) (E q Q X y h δ : ℝ)
    (hE : 0 ≤ E) (hq : 1 ≤ q) (hqQ : q ≤ Q) (hQX : Q ≤ X)
    (hX : 4 ≤ X) (hy : y ∈ Set.Icc X (2*X)) (hh : 0 ≤ h) (hhX : h ≤ X)
    (hδ : 0 < δ) (hδX : δ ≤ X/2)
    (hf : ∀ u : ℝ, 1 ≤ u → ‖f u‖ ≤ E*Real.sqrt u*(1+Real.log q)) :
    ‖V1c f y h δ‖ ≤ 208*E*(Real.sqrt X*Real.log X/δ) := by
  have hXp : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := V86.V23g X hX
  have hqlog : 1+Real.log q ≤ 2*Real.log X := by
    have hl := Real.log_le_log (by linarith : 0 < q) (hqQ.trans hQX)
    linarith
  have hqlog0 : 0 ≤ 1+Real.log q := by
    have := Real.log_nonneg hq
    linarith
  have hb (u : ℝ) (hu : X/2 ≤ u) (huX : u ≤ 3*X) :
      ‖f u‖ ≤ 52*E*Real.sqrt X*Real.log X := by
    have hu1 : 1 ≤ u := by linarith
    have hsqrt : Real.sqrt u ≤ 2*Real.sqrt X := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hXp.le]
    have hp := mul_le_mul hsqrt hqlog hqlog0 (by positivity : 0 ≤ 2*Real.sqrt X)
    have he := mul_le_mul_of_nonneg_left hp hE
    have hn : 0 ≤ E*Real.sqrt X*Real.log X := by positivity
    apply (hf u hu1).trans
    nlinarith only [he, hn]
  have he := Vun f y h δ (52*E*Real.sqrt X*Real.log X) hδ
    (hb (y+h) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y+h-δ) (by linarith [hy.1]) (by linarith [hy.2]))
    (hb y (by linarith [hy.1]) (by linarith [hy.2]))
    (hb (y-δ) (by linarith [hy.1]) (by linarith [hy.2]))
  exact he.trans_eq (by ring)

theorem largeModulus_V10t :
    ∃ D : ℝ, 0 < D ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ (X y δ U : ℝ) (h : ℕ),
      4 ≤ X → y ∈ Set.Icc X (2*X) → (h : ℝ) ≤ X → 1 ≤ δ → δ ≤ X/2 → 2 ≤ U →
      (Q : ℝ) ≤ X → ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q →
      ‖V4q χ h y + V3q (fun u => ∑ i ∈ (V1 χ).V14 U,
          Ve u (h : ℝ) ((V1 χ).zeros i)) δ y‖ ≤
        D*(δ*Real.log X + Real.sqrt X*Real.log X/δ +
          (Q : ℝ)^2*X^2*Real.log ((Q : ℝ)*U)/(δ*U)) := by
  obtain ⟨E,hE,hbound⟩ := Vt5
  have hT := Vj5
  refine ⟨20+208*E+V38, by positivity, ?_⟩
  intro Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ hχ
  have hX2 : 2 ≤ X := by linarith
  have hδp : 0 < δ := by linarith
  have hyδ : δ < y := by linarith [hy.1]
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqQ : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogU : 0 ≤ Real.log ((Q : ℝ)*U) := Real.log_nonneg (by nlinarith)
  obtain ⟨c,hc⟩ := hbound χ
  have huns := V1co χ h X y δ hX2 hy hhX hδ hδX
  have hrem := largeModulus_Vja (V7p χ c)
    E χ.modulus Q X y h δ hE.le hq hqQ hQX hX hy hh hhX hδp hδX hc
  have hori := V1wr χ X y h δ hX2 hy hh hhX hδ hδX
  have htail := V1t6 Q hQ χ hχ X y h δ U hX2 hy hh hhX hδp hδX hU
  have hid := V172 χ c y h δ U hδp hyδ hh
  have hn := V1gu (V4q χ h y) _ _ _ _ _ hid
  have hs : ‖V4q χ h y + V3q (fun u => ∑ i ∈ (V1 χ).V14 U,
      Ve u (h : ℝ) ((V1 χ).zeros i)) δ y‖ ≤
      18*(δ*Real.log X)+(208*E)*(Real.sqrt X*Real.log X/δ)+
        V38*((Q : ℝ)^2*X^2*Real.log ((Q : ℝ)*U)/(δ*U)) := by linarith
  exact hs.trans (Vwl E (δ*Real.log X) (Real.sqrt X*Real.log X/δ)
    ((Q : ℝ)^2*X^2*Real.log ((Q : ℝ)*U)/(δ*U)) hE
    (by positivity) (by positivity) (by positivity))

variable (J : ℕ)

def characterRaw (B : ℕ) : Prop :=
    ∃ C : ℝ,0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ),1≤Q → ∀ (K : ℕ) (X h : ℝ),
      X₀≤X → 0<h → h≤X → (Q : ℝ)≤2*(Real.log X)^(J+1) →
      (Q : ℝ)^2/(h/X)≤X^(5/9 : ℝ) →
      Real.log ((Q : ℝ)*(2 : ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      (∑ χ∈F,∫ y in X..2*X,
        ‖∑ i∈(V1 χ).V14 ((2 : ℝ)^(K+1)),
          Ve y h ((V1 χ).zeros i)‖^2)≤
        C*h^2*X/(Real.log X)^B



theorem smoothCharacter (B : ℕ) (raw : characterRaw J B) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, ∀ (Q K : ℕ), 1≤Q → ∀ X h δ : ℝ,
    X₀≤X → 0<h → h≤X/2 → 0<δ → δ≤X/2 → (Q:ℝ)≤2*(Real.log (X/2))^(J+1) →
    (Q:ℝ)^2/(h/X) ≤ X^(5/9:ℝ) → Real.log ((Q:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
    ∀ χ : PrimitiveComplexCharacter, χ.modulus≤Q →
    (∫ y in X..2*X, ‖V3q (fun u =>
      ∑ i∈(V1 χ).V14 ((2:ℝ)^(K+1)),Ve u h ((V1 χ).zeros i)) δ y‖^2) ≤
      C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,T,hm⟩ := raw
  refine ⟨((2:ℝ)^B+1)*C,by positivity,max (2*T) 4,?_⟩
  intro Q K hQ X h δ hX hh hupper hd hdX hq hscale height χ hχ
  have hX4 : 4≤X := (le_max_right _ _).trans hX
  have hT : 2*T≤X := (le_max_left _ _).trans hX
  have hlog := Real.log_le_log (by linarith : 0<X/2) (by linarith : X/2≤X)
  have hlog0 : 0≤Real.log (X/2) := Real.log_nonneg (by linarith)
  have hq' : (Q:ℝ) ≤ 2*(Real.log X)^(J+1) := hq.trans (by gcongr)
  let f : ℝ → ℂ := fun u => ∑ i∈(V1 χ).V14 ((2:ℝ)^(K+1)),Ve u h ((V1 χ).zeros i)
  apply average_budget f X h δ C B hX4 hd hdX hC.le
    (Vab _ _ _ _ h (by linarith) hh.le)
  · have hc := hm Q hQ K (X/2) h (by linarith) hh hupper hq (scale_half (by linarith) hscale) height
      {χ} (by intro ξ hξ; simpa only [mem_singleton.mp hξ] using hχ)
    simpa only [sum_singleton] using hc
  · have hc := hm Q hQ K X h (by linarith) hh (by linarith) hq' hscale (by linarith)
      {χ} (by intro ξ hξ; simpa only [mem_singleton.mp hξ] using hχ)
    simpa only [sum_singleton] using hc



theorem eventually_half_cutoff :
    ∀ᶠ X : ℝ in atTop, (Real.log X)^J ≤ 2*(Real.log (X/2))^(J+1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((2:ℝ)^(J+1)),
    eventually_ge_atTop (4:ℝ)] with X hL hX
  have hX0 : 0<X := by linarith
  have hH : 0≤Real.log (X/2) := Real.log_nonneg (by linarith)
  have he : Real.log X = Real.log (X/2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : X/2 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    congr 1; ring
  have hlog : Real.log X ≤ 2 * Real.log (X/2) := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤X/2)
    linarith
  have hLog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hpow := pow_le_pow_left₀ hLog0 hlog (J+1)
  rw [mul_pow] at hpow
  have h1 := mul_le_mul_of_nonneg_left hL (show 0≤(Real.log X)^J by positivity)
  calc (Real.log X)^J ≤ (Real.log (X/2))^(J+1) := by
         have h : (Real.log X)^J * 2^(J+1) ≤ 2^(J+1)*(Real.log (X/2))^(J+1) := by
           refine h1.trans ?_; convert hpow using 1 <;> rw [pow_succ] <;> ring
         exact le_of_mul_le_mul_left
           (by simpa only [mul_comm] using h)
           (by positivity : (0:ℝ)<2^(J+1))
       _ ≤ _ := by linarith [pow_nonneg hH (J+1)]

structure ThinPacket (J B : ℕ) (X Q h : ℝ) (K : ℕ) : Prop where
  X_ge_four : 4 ≤ X
  delta_ge_one : 1 ≤ X^(1/12:ℝ)
  delta_le_half : X^(1/12:ℝ) ≤ X/2
  height_ge_two : 2 ≤ (2:ℝ)^(K+1)
  half_cutoff : Q ≤ 2*(Real.log (X/2))^(J+1)
  height_log : Real.log (Q*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2)
  scale : Q^2/(h/X) ≤ X^(5/9:ℝ)
  residual : (X^(1/12:ℝ)*Real.log X + Real.sqrt X*Real.log X/X^(1/12:ℝ) +
    Q^2*X^2*Real.log (Q*(2:ℝ)^(K+1))/(X^(1/12:ℝ)*(2:ℝ)^(K+1)))^2 * X ≤
    h^2*X/(Real.log X)^B

theorem eventually_parameters (B : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ Q h : ℝ, 1≤Q → Q≤(Real.log X)^J →
      0<h → Q^2*X^(4/9:ℝ)≤h → ∃ K : ℕ, ThinPacket J B X Q h K := by
  filter_upwards [eventually_ge_atTop (4:ℝ),eventually_half_cutoff J,
    eventual_log_power J (1/2) 8 (by norm_num),
    eventual_log_power (B+2) (1/18) 16 (by norm_num)]
    with X hX hcut hpoly habs
  intro Q h hQ hQx hh hlow
  have x0 : 0<X := by linarith
  have x1 : 1≤X := by linarith
  have hd : X^(1/12:ℝ) ≤ X/2 := by
    calc X^(1/12:ℝ) ≤ Real.sqrt X := by
           rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le x1 (by norm_num)
         _ ≤ _ := by
           apply Real.sqrt_le_iff.mpr
           exact ⟨by linarith,by nlinarith [mul_nonneg x0.le (by linarith : 0≤X-4)]⟩
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near
    (Real.one_le_rpow x1 (by norm_num : (0:ℝ)≤3/2)) (by norm_num : (1:ℝ)<2)
  let U : ℝ := 2^(K+1)
  have hunit : 2≤U := by
    dsimp [U];rw [pow_succ];nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=K)]
  have h2Q : 8*Q ≤ X^(1/2:ℝ) := by linarith
  have hprod : (8*Q) * X^(3/2:ℝ) ≤ X^2 := by
    calc _ ≤ X^(1/2:ℝ)*X^(3/2:ℝ) := mul_le_mul_of_nonneg_right h2Q (by positivity)
         _ = _ := by rw [← Real.rpow_add x0];norm_num
  have hup : U ≤ 2*X^(3/2:ℝ) := by dsimp [U];rw [pow_succ];linarith
  have hQU : Q*U ≤ (X/2)^2 := by
    have hhq := mul_le_mul_of_nonneg_left hup (by linarith : 0≤Q)
    linarith only [hhq,hprod] -- normalize products below if needed
  have hlog : Real.log (Q*U) ≤ 2*Real.log (X/2) := by
    have he := Real.log_le_log (by positivity : 0<Q*U) hQU
    simpa only [Real.log_pow,Nat.cast_ofNat] using he
  have hlogle := Real.log_le_log (by linarith : 0<X/2) (by linarith : X/2≤X)
  exact ⟨K, hX, Real.one_le_rpow x1 (by norm_num), hd, hunit, hQx.trans hcut,
    hlog, scale_from_lower x0 hh hlow, residual_budget B hX hQ hhi.le (by linarith) hlow habs⟩


def characterMean (B:ℕ) : Prop :=
  ∃C:ℝ,0<C ∧ ∃X₀:ℕ,∀X h:ℕ,
    X₀≤X → 2≤X → 0<h → (h:ℝ)≤(X:ℝ)/2 →
    (((X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V42 h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^B) ∧
    (∀χ:PrimitiveComplexCharacter,
      (χ.modulus:ℝ)≤(Real.log (X:ℝ))^J →
      (χ.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V4q χ h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^B))
theorem characters_from_density (B : ℕ) (hnraw : characterRaw J B) (hpraw : principalRaw B) : characterMean J B := by
  obtain ⟨Cn,hCn,Xn,hn⟩ := smoothCharacter J B hnraw
  obtain ⟨Cp,hCp,Xp,hp⟩ := smoothPrincipal B hpraw
  obtain ⟨Dn,hDn,hpn⟩ := largeModulus_V10t
  obtain ⟨Dp,hDp,hpp⟩ := V10s
  obtain ⟨Xa,ha⟩ := Filter.eventually_atTop.1 (eventually_parameters J B)
  let C : ℝ := 2*Cp+2*Cn+24*Dp^2+24*Dn^2+1
  obtain ⟨N,hN⟩ := exists_nat_ge (max (max (max Xn Xp) Xa) 4)
  refine ⟨C,by dsimp [C]; positivity,N,?_⟩
  intro X h hNX hX2 hh hhX
  have hXlarge : max (max (max Xn Xp) Xa) 4≤(X : ℝ) :=
    hN.trans (by exact_mod_cast hNX)
  have hX4 : 4≤(X : ℝ) := (le_max_right _ _).trans hXlarge
  have hXpos : 0<(X : ℝ) := by linarith
  have hXa : Xa≤(X : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hXlarge)
  have hXnp : max Xn Xp≤(X : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hXlarge)
  have hXn : Xn≤(X : ℝ) := (le_max_left _ _).trans hXnp
  have hXp : Xp≤(X : ℝ) := (le_max_right _ _).trans hXnp
  have hhr : 0<(h : ℝ) := by exact_mod_cast hh
  have hhXr : (h : ℝ)≤X := by linarith
  have hLX : 1≤Real.log (X : ℝ) := by
    apply (Real.le_log_iff_exp_le hXpos).2
    exact Real.exp_one_lt_three.le.trans (by linarith)
  let M : ℝ := (h : ℝ)^2*(X : ℝ)/(Real.log (X : ℝ))^B
  have hM : 0≤M := by dsimp [M]; positivity
  constructor
  · intro hlower
    have hQpoly : (1 : ℝ)≤(Real.log (X : ℝ))^J := one_le_pow₀ hLX
    obtain ⟨K,p⟩ := ha (X : ℝ) hXa 1 (h : ℝ) (by norm_num) hQpoly hhr
      (by simpa only [one_pow,one_mul] using hlower)
    let δ : ℝ := (X : ℝ)^(1/12 : ℝ)
    let U : ℝ := (2 : ℝ)^(K+1)
    let S := V3b U
    let f : ℝ → ℂ := fun u => ∑ c∈S,Ve u (h : ℝ) c.val.1
    let g : ℝ → ℂ := V3q f δ
    let R : ℝ := δ*Real.log (X : ℝ)+Real.sqrt (X : ℝ)*Real.log (X : ℝ)/δ+
      (X : ℝ)^2*Real.log U/(δ*U)
    have hδp : 0<δ := by dsimp [δ]; linarith [p.delta_ge_one]
    have hlogU : 0≤Real.log U := Real.log_nonneg (by dsimp [U]; linarith [p.height_ge_two])
    have hR : 0≤R := by dsimp [R]; positivity
    have hcont : ContinuousOn f (Set.Icc ((X : ℝ)-δ) (2*(X : ℝ))) :=
      Vab S (fun c => c.val.1) ((X : ℝ)-δ) (2*(X : ℝ)) h
        (by dsimp [δ]; linarith [p.delta_le_half]) hhr.le
    have hg : ContinuousOn g (Set.Icc (X : ℝ) (2*(X : ℝ))) :=
      Vp7 f (X : ℝ) δ hXpos.le hδp.le hcont
    have hmain : (∫ y in (X : ℝ)..2*(X : ℝ),‖g y‖^2)≤Cp*M := by
      have he := hp K (X : ℝ) (h : ℝ) δ hXp hhr hhX hδp p.delta_le_half
        (by simpa only [one_pow] using p.scale)
        (by simpa only [one_mul] using p.height_log)
      apply he.trans_eq
      dsimp [M]
      ring
    have hres : R^2*(X : ℝ)≤12*M := by
      have he : R^2*(X:ℝ) ≤ M := by simpa only [one_pow,one_mul] using p.residual
      linarith
    have hpoint : ∀ y∈Set.Icc (X : ℝ) (2*(X : ℝ)),
        ‖V42 h y+g y‖≤Dp*R := by
      intro y hy
      exact hpp (X : ℝ) y δ U h hX4 hy hhXr p.delta_ge_one p.delta_le_half p.height_ge_two
    have he := V6h.Vmv (V42 h) g (X : ℝ) R M Cp Dp
      hXpos.le hR hDp.le hg hmain hres hpoint
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ (2*Cp+24*Dp^2)*M := he
      _ ≤ C*M := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg Dn]) hM
      _ = _ := by dsimp [M]; ring
  · intro χ hχpoly hlower
    have hQ1 : (1 : ℝ)≤χ.modulus := by exact_mod_cast χ.positive
    obtain ⟨K,p⟩ := ha (X : ℝ) hXa (χ.modulus : ℝ) (h : ℝ) hQ1 hχpoly hhr hlower
    let δ : ℝ := (X : ℝ)^(1/12 : ℝ)
    let U : ℝ := (2 : ℝ)^(K+1)
    let S := (V1 χ).V14 U
    let f : ℝ → ℂ := fun u => ∑ i∈S,Ve u (h : ℝ) ((V1 χ).zeros i)
    let g : ℝ → ℂ := V3q f δ
    let R : ℝ := δ*Real.log (X : ℝ)+Real.sqrt (X : ℝ)*Real.log (X : ℝ)/δ+
      (χ.modulus : ℝ)^2*(X : ℝ)^2*Real.log ((χ.modulus : ℝ)*U)/(δ*U)
    have hδp : 0<δ := by dsimp [δ]; linarith [p.delta_ge_one]
    have hU1 : 1≤U := by dsimp [U]; linarith [p.height_ge_two]
    have hlogU : 0≤Real.log ((χ.modulus : ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ1 hU1)
    have hR : 0≤R := by dsimp [R]; positivity
    have hcont : ContinuousOn f (Set.Icc ((X : ℝ)-δ) (2*(X : ℝ))) :=
      Vab S (V1 χ).zeros
        ((X : ℝ)-δ) (2*(X : ℝ)) h (by dsimp [δ]; linarith [p.delta_le_half]) hhr.le
    have hg : ContinuousOn g (Set.Icc (X : ℝ) (2*(X : ℝ))) :=
      Vp7 f (X : ℝ) δ hXpos.le hδp.le hcont
    have hmain : (∫ y in (X : ℝ)..2*(X : ℝ),‖g y‖^2)≤Cn*M := by
      have he := hn χ.modulus K χ.positive (X : ℝ) (h : ℝ) δ hXn hhr hhX hδp
        p.delta_le_half p.half_cutoff p.scale p.height_log χ le_rfl
      apply he.trans_eq
      dsimp [M]
      ring
    have hres : R^2*(X : ℝ)≤12*M := by linarith only [p.residual, hM]
    have hpoint : ∀ y∈Set.Icc (X : ℝ) (2*(X : ℝ)),
        ‖V4q χ h y+g y‖≤Dn*R := by
      intro y hy
      exact hpn χ.modulus χ.positive (X : ℝ) y δ U h hX4 hy hhXr p.delta_ge_one
        p.delta_le_half p.height_ge_two (by
          have hpow : 1 ≤ (X:ℝ)^(4/9:ℝ) :=
            Real.one_le_rpow (by linarith) (by norm_num)
          have hq2 : (χ.modulus:ℝ)^2 ≤ (h:ℝ) :=
            (le_mul_of_one_le_right (sq_nonneg _) hpow).trans hlower
          nlinarith) χ le_rfl
    have he := V6h.Vmv (V4q χ h) g (X : ℝ) R M Cn Dn
      hXpos.le hR hDn.le hg hmain hres hpoint
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ (2*Cn+24*Dn^2)*M := he
      _ ≤ C*M := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg Dp]) hM
      _ = _ := by dsimp [M]; ring

theorem primitive_L1 (A q:ℕ) [NeZero q] (X h:ℕ) (C:ℝ)
    (hC:0≤C) (hlog:1≤Real.log (X:ℝ))
    (hscale:(q:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ))
    (hsmall:(q:ℝ)≤(Real.log (X:ℝ))^J)
    (hprincipal:(∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V42 h y‖^2)≤
      C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^(2*A))
    (hprimitive:∀χ:PrimitiveComplexCharacter,
      (χ.modulus:ℝ)≤(Real.log (X:ℝ))^J →
      (χ.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) →
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),‖V4q χ h y‖^2)≤
        C*(h:ℝ)^2*(X:ℝ)/(Real.log (X:ℝ))^(2*A)) :
    (∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vbj q h y)≤
      (C+1)*(q.totient:ℝ)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
  have hsingle (χ:DirichletCharacter ℂ q) :
      (∫y in (X:ℝ)..((2*X:ℕ):ℝ),
        ‖V3n (V9a h y) (fun k=>(vonMangoldt k:ℂ)) χ.primitiveCharacter‖)≤
        (C+1)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
    by_cases hχ : χ=1
    · subst χ
      simp_rw [V1jt]
      exact V217 (fun r=>(∑k∈Ioc r (r+h),V1n k)-(h:ℂ)) X h A C _ hC (by linarith) hprincipal
    · let p := Vni χ hχ
      have hpq : (p.modulus:ℝ)≤(q:ℝ) := by exact_mod_cast V18g χ hχ
      have hpsmall : (p.modulus:ℝ)≤(Real.log (X:ℝ))^J := hpq.trans hsmall
      have hpscale : (p.modulus:ℝ)^2*(X:ℝ)^(4/9:ℝ)≤(h:ℝ) := by
        apply le_trans _ hscale
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hpq 2) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [V1ju χ hχ]
      exact V217 (fun r=>∑k∈Ioc r (r+h),Vl p k) X h A C _ hC (by linarith)
        (hprimitive p hpsmall hpscale)
  have hcard : Fintype.card (DirichletCharacter ℂ q)=q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [V19x]
  apply (sum_le_sum (fun χ _=>hsingle χ)).trans_eq
  rw [sum_const,card_univ,nsmul_eq_mul,hcard]
  ring
set_option maxHeartbeats 1000000 in
theorem progression_L1 (A : ℕ) (H : characterMean J (2*A)) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ (q : ℕ) [NeZero q] (X h : ℕ),
      X₀ ≤ X → 2 ≤ X → 0<h → (h:ℝ)≤(X:ℝ)/2 →
      (q:ℝ)^2*(X:ℝ)^(4/9:ℝ) ≤ (h:ℝ) → (q:ℝ) ≤ (Real.log (X:ℝ))^J →
      (∑ r ∈ Ico X (2*X), V3z.V6v q (Ioc r (r+h))) ≤ C*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by
  obtain ⟨C,hC,X₀,hmean⟩ := H
  obtain ⟨N,hN⟩ := eventually_atTop.1 (Vw0 A 1 (by norm_num))
  obtain ⟨P,hP⟩ := eventually_atTop.1
    (V5d.Vqk A 1 (by norm_num))
  obtain ⟨M,hM⟩ := exists_nat_gt (Real.exp (1:ℝ))
  refine ⟨C+3,by positivity,X₀+N+P+M+3,?_⟩
  intro q inst X h hthreshold hX hh hhX hscale hsmall
  have hhXnat : h≤X := by exact_mod_cast (show (h:ℝ)≤(X:ℝ) by linarith)
  rw [V2h.Vdb q h (by omega : X≤2*X)]
  have hX₀ : X₀≤X := by omega
  have hNX : N≤X := by omega
  have hPX : P≤X := by omega
  have hMX : M≤X := by omega
  have hlog : 1≤Real.log (X:ℝ) := by
    have he : Real.exp (1:ℝ)≤(X:ℝ) := hM.le.trans (by exact_mod_cast hMX)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (1:ℝ)) he
  have hq1 : (1:ℝ)≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hx1 : (1:ℝ)≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hpow : 1≤(X:ℝ)^(4/9:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hqX : q≤X := by
    have hhR : (h:ℝ)≤(X:ℝ) := by exact_mod_cast hhXnat
    have hq2 : (q:ℝ)^2≤(h:ℝ) := (le_mul_of_one_le_right (sq_nonneg _) hpow).trans hscale
    exact_mod_cast (show (q:ℝ)≤(X:ℝ) by nlinarith)
  have hscale1 : (X:ℝ)^(4/9:ℝ)≤(h:ℝ) := by
    apply le_trans _ hscale
    exact le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (one_le_pow₀ hq1)
  have hboth := hmean X h hX₀ hX hh hhX
  have hprim := primitive_L1 J A q X h C hC.le hlog hscale hsmall
    (hboth.1 hscale1) hboth.2
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hprimdiv := div_le_div_of_nonneg_right hprim hφ.le
  have he := hN X hNX q (NeZero.pos q) hqX
  have hp := hP X hPX
  simp only [one_mul] at he hp
  have heh := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) h)
  have hph := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) h)
  calc
    _ ≤ (∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vaw q h y)+
        2*(h:ℝ)*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ) :=
      V5d.V1cz q X h (by omega) hhXnat
    _ ≤ ((∫y in (X:ℝ)..((2*X:ℕ):ℝ),Vbj q h y)/(q.totient:ℝ)+
        (h:ℝ)*(Real.log (q:ℝ)+2*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ)))+
        2*(h:ℝ)*Real.sqrt ((3*X:ℕ):ℝ)*Real.log ((3*X:ℕ):ℝ) :=
      (add_le_add) (V17a X h (by omega) hhXnat) le_rfl
    _ ≤ (((C+1)*(q.totient:ℝ)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A)/(q.totient:ℝ)+
        (h:ℝ)*((X:ℝ)/(Real.log (X:ℝ))^A))+
        (h:ℝ)*((X:ℝ)/(Real.log (X:ℝ))^A) := by
      apply add_le_add (add_le_add hprimdiv heh)
      nlinarith only [hph]
    _ = (C+3)*(h:ℝ)*(X:ℝ)/(Real.log (X:ℝ))^A := by field_simp; ring

/-- The true zero-density moment, with an arbitrary fixed conductor exponent. -/
theorem characterRaw_true (B : ℕ) : characterRaw J B := by
  obtain ⟨C,hC,Xm,hm⟩ := V93.Full_Vp9 B
  obtain ⟨Xz,hz⟩ := GoldbachPolylogZeroFree.actual_all_zero_gap_polylog (B+6) (J+2)
  refine ⟨C,hC,max (max Xm Xz) (Real.exp 2),?_⟩
  intro Q hQ K X h hX hh hhX hQX hscale hlog F hF
  have hXm : Xm ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXz : Xz ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := (Real.exp_pos 2).trans_le hXe
  have hLX : 2 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hXe
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hheight : (2 : ℝ)^(K+1) ≤ X^2 := by
    have hprod : (Q : ℝ)*(2 : ℝ)^(K+1) ≤ X^2 := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).1
      simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
    have he := mul_le_mul_of_nonneg_right hQr (by positivity : 0 ≤ (2 : ℝ)^(K+1))
    nlinarith
  apply hm Q hQ K X h hXm hh hhX hscale hlog F hF _ (fun _ _ => Finset.Subset.refl _)
  intro χ hχ i hi
  have hχQ : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hF χ hχ
  have hχpoly : (χ.modulus : ℝ) ≤ (Real.log X)^(J+2) := by
    apply (hχQ.trans hQX).trans
    have hn : 0 ≤ (Real.log X)^(J+1) := by positivity
    calc
      2*(Real.log X)^(J+1) = (Real.log X)^(J+1)*2 := by ring
      _ ≤ (Real.log X)^(J+1)*Real.log X := mul_le_mul_of_nonneg_left hLX hn
      _ = (Real.log X)^(J+2) := by
        conv_rhs => rw [show J+2 = (J+1)+1 by omega, pow_succ]
  have hγ := ((V1 χ).V2r ((2 : ℝ)^(K+1)) i).mp hi
  exact hz X hXz χ hχpoly i (hγ.trans hheight)

theorem characterMean_true (B : ℕ) : characterMean J B :=
  characters_from_density J B (characterRaw_true J B) (Vqx.Full_Vt4 B)

end
end BeaumontPolylogBoundary

/- Source section: BeaumontSmallModuliBudget.lean -/

namespace BeaumontSmallModuli

/-- A version with a variable logarithmic exponent.  The three numerical
conditions respectively absorb the endpoint, bulk, and nonunit terms. -/
theorem energy_charge (A : ℕ) (N H Q L D E : ℝ)
    (hN : 0 ≤ N) (hH : 0 < H) (hQ : 0 ≤ Q) (hL : 0 < L)
    (hsmall : 480*Q^3*H*L^6 ≤ N)
    (hbulk : 96*D*Q^3*L^5 ≤ L^A)
    (hdiagonal : 36*Q^2*L^6 ≤ H^2)
    (hE : H^2/4*E ≤
      40*Q^3*H^3*L^2 + 8*D*Q^3*N*H^2*L/L^A + 3*Q^2*N*L^2) :
    E ≤ N/L^4 := by
  have hfirst : (12*L^4)*(40*Q^3*H^3*L^2) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg H)
    convert hm using 1 <;> ring
  have hsecond : (12*L^4)*(8*D*Q^3*N*H^2*L/L^A) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hbulk (by positivity : 0 ≤ N*H^2)
    have he : (12*L^4)*(8*D*Q^3*N*H^2*L/L^A) =
        (96*D*Q^3*L^5*(N*H^2))/L^A := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < L^A)).2
    convert hm using 1 <;> ring
  have hthird : (12*L^4)*(3*Q^2*N*L^2) ≤ N*H^2 := by
    have hm := mul_le_mul_of_nonneg_right hdiagonal hN
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 12*L^4)
  have hlast : (H^2/4*E)*(12*L^4) ≤ 3*(N*H^2) := by
    nlinarith only [hmul, hfirst, hsecond, hthird]
  apply (le_div_iff₀ (by positivity : 0 < L^4)).2
  apply le_of_mul_le_mul_left (a := 3*H^2) ?_ (by positivity : 0 < 3*H^2)
  nlinarith only [hlast]

/-- Numerical absorption for the local Fourier estimate. -/
theorem energy_budget (N H Q L D E : ℝ)
    (hN : 0 ≤ N) (hH : 0 < H) (hQ : 0 ≤ Q) (hL : 16 ≤ L)
    (hD : 0 ≤ D) (hDL : D ≤ L) (hQL : Q ≤ L^20)
    (hHL : L^100 ≤ H) (hHN : H*L^100 ≤ N)
    (hE : H^2/4*E ≤
      40*Q^3*H^3*L^2 + 8*D*Q^3*N*H^2/L^99 + 3*Q^2*N*L^2) :
    E ≤ N/L^4 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h480 : (480 : ℝ) ≤ L^34 := by
    have hs : (480 : ℝ) ≤ (16 : ℝ)^3 := by norm_num
    exact hs.trans ((pow_le_pow_left₀ (by norm_num) hL 3).trans
      (pow_le_pow_right₀ hL1 (by norm_num)))
  have h96 : (96 : ℝ) ≤ L^34 := by linarith
  have h36 : (36 : ℝ) ≤ L^154 := by
    exact (show (36 : ℝ) ≤ (16 : ℝ)^2 by norm_num).trans
      ((pow_le_pow_left₀ (by norm_num) hL 2).trans
      (pow_le_pow_right₀ hL1 (by norm_num)))
  have hQ3 : Q^3 ≤ L^60 := by
    have hp := pow_le_pow_left₀ hQ hQL 3
    simpa only [← pow_mul] using hp
  have hQ2 : Q^2 ≤ L^40 := by
    have hp := pow_le_pow_left₀ hQ hQL 2
    simpa only [← pow_mul] using hp
  have hfirst : (12*L^4)*(40*Q^3*H^3*L^2) ≤ N*H^2 := by
    have hc : 480*Q^3*L^6 ≤ L^100 := by
      calc
        _ ≤ 480*L^60*L^6 := by gcongr
        _ = 480*L^66 := by ring
        _ ≤ L^34*L^66 := by gcongr
        _ = _ := by ring
    have hm := (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ H^3)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hHN (sq_nonneg H)] :
        L^100*H^3 ≤ N*H^2)
    convert hm using 1 <;> ring
  have hsecond : (12*L^4)*(8*D*Q^3*N*H^2/L^99) ≤ N*H^2 := by
    have hc : 96*D*Q^3*L^4 ≤ L^99 := by
      calc
        _ ≤ 96*L*L^60*L^4 := by gcongr
        _ = 96*L^65 := by ring
        _ ≤ L^34*L^65 := by gcongr
        _ = _ := by ring
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ N*H^2)
    have he : (12*L^4)*(8*D*Q^3*N*H^2/L^99) =
        (96*D*Q^3*L^4*(N*H^2))/L^99 := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < L^99)).2
    convert hm using 1 <;> ring
  have hthird : (12*L^4)*(3*Q^2*N*L^2) ≤ N*H^2 := by
    have hc : 36*Q^2*L^6 ≤ H^2 := by
      calc
        _ ≤ 36*L^40*L^6 := by gcongr
        _ = 36*L^46 := by ring
        _ ≤ L^154*L^46 := by gcongr
        _ = (L^100)^2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hHL 2
    have hm := mul_le_mul_of_nonneg_right hc hN
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 12*L^4)
  have hlast : (H^2/4*E)*(12*L^4) ≤ 3*(N*H^2) := by
    nlinarith only [hmul, hfirst, hsecond, hthird]
  apply (le_div_iff₀ (by positivity : 0 < L^4)).2
  have hh2 : 0 < 3*H^2 := by positivity
  apply le_of_mul_le_mul_left (a := 3*H^2) ?_ hh2
  nlinarith only [hlast]

end BeaumontSmallModuli

/- Source section: BeaumontSmallModuliPolylog.lean -/

/-!
Small-modulus local Fourier energy for the actual prime logarithmic weight.

The analytic input is the proved short-interval character mean square estimate
in `DynThinWindowExceptions`, valid once q^2 X^(4/9) ≤ h.  The passage to
Fourier energy uses the finite Gallagher inequality from
`LowSkirtFromShortProgressions`.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology Interval Classical

namespace BeaumontSmallModuliPolylog
noncomputable section

theorem reducedMax_le_old (q : ℕ) [NeZero q] (I : Finset ℕ) :
    GBSkirtVariance.reducedMax I q ≤ V3z.V6v q I := by
  apply Finset.sup'_le
  intro r _
  split_ifs with hr
  · have he := V3z.V114 I r hr
    change ‖(∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
      GoldbachGRHWindow.primeLog k) -
      (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0)‖ ≤ _
    rw [if_pos hr]
    exact he
  · exact V3z.Vtd q I

/-- An unconditional dyadic L1 estimate with the public prime-window symbol. -/
theorem progression_L1 (J A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ (q : ℕ) [NeZero q] (X h : ℕ),
      T ≤ X → 2 ≤ X → 0 < h → (h : ℝ) ≤ (X : ℝ) / 2 →
      (q : ℝ)^2 * (X : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) →
      (q : ℝ) ≤ (Real.log (X : ℝ))^J →
      (∑ y ∈ Ico X (2*X), GBSkirtVariance.pointError q h y) ≤
        C * (h : ℝ) * (X : ℝ) / (Real.log (X : ℝ))^A := by
  obtain ⟨C, hC, T, hT⟩ := BeaumontPolylogBoundary.progression_L1 J A
    (BeaumontPolylogBoundary.characterMean_true J (2*A))
  refine ⟨C, hC, T, ?_⟩
  intro q inst X h hTX hX hh hhX hscale hq
  apply le_trans _ (hT q X h hTX hX hh hhX hscale hq)
  apply sum_le_sum
  intro y _
  rw [GBSkirtVariance.pointError, dif_neg (NeZero.ne q)]
  have hi : Icc (y+1) (y+h) = Ioc y (y+h) := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hi]
  exact reducedMax_le_old q _

/-- A coarse endpoint bound, retaining the true short length h. -/
theorem initial_rows (n Q h : ℕ) (hn : 2 ≤ n) (hh : h ≤ n) :
    (∑ y ∈ range (4*h), GBSkirtVariance.row Q h y) ≤
      4 * (Q : ℝ) * (h : ℝ)^2 * (Real.log (5*(n : ℝ)) + 1) := by
  let B : ℝ := (h : ℝ) * (Real.log (5*(n : ℝ)) + 1)
  have hB : 0 ≤ B := by
    have hp : (1 : ℝ) ≤ 5*(n : ℝ) := by exact_mod_cast (by omega : 1 ≤ 5*n)
    have := Real.log_nonneg hp
    dsimp [B]
    positivity
  have hy' (y : ℕ) (hy : y ∈ range (4*h)) :
      GBSkirtVariance.row Q h y ≤ (Q : ℝ)*B := by
    unfold GBSkirtVariance.row
    apply le_trans (sum_le_sum (g := fun _ => B) ?_) ?_
    · intro q hq
      have hqn : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
      letI : NeZero q := ⟨hqn⟩
      rw [GBSkirtVariance.pointError, dif_neg hqn]
      apply Finset.sup'_le
      intro r _
      split_ifs
      · have hw : GBSkirtVariance.window (5*n) h (y+h) = Icc (y+1) (y+h) := by
          have hy' := mem_range.mp hy
          unfold GBSkirtVariance.window
          congr 1 <;> omega
        have hT := GBSkirtVariance.trivial_window_error (5*n) h (y+h) (by omega) r
        simpa only [hw, Nat.cast_mul, Nat.cast_ofNat] using hT
      · exact hB
    · simp [Nat.card_Icc]
  apply (sum_le_sum hy').trans_eq
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  dsimp [B]
  ring

/-- Complete initial segment bound obtained from dyadic means.  All analytic hypotheses
are the explicit size restrictions of the already proved progression theorem. -/
theorem fullL1_bound (J A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n Q h : ℕ,
      2 ≤ n → 0 < h → h ≤ n → T ≤ 2*h →
      (n : ℝ) ≤ (2*(h : ℝ))^3 →
      (Q : ℝ)^2 * (n : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) →
      (Q : ℝ) ≤ (Real.log (2*(h : ℝ)))^J →
      GBSkirtVariance.fullL1 n Q h ≤
        4*(Q : ℝ)*(h : ℝ)^2*(Real.log (5*(n : ℝ))+1) +
        2*((n+1 : ℕ) : ℝ)*(C*(Q : ℝ)*(h : ℝ)*3^A/(Real.log (n : ℝ))^A) := by
  obtain ⟨C, hC, T, hT⟩ := progression_L1 J A
  refine ⟨C, hC, T, ?_⟩
  intro n Q h hn hh hhn hTh hcube hscale hQ
  let K : ℝ := C*(Q : ℝ)*(h : ℝ)*3^A/(Real.log (n : ℝ))^A
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 := lt_trans zero_lt_one hn1
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlocal (x : ℕ) (hx : 2*h ≤ x) (hxn : x ≤ n) :
      (∑ y ∈ Ico x (2*x), GBSkirtVariance.row Q h y) ≤ (x : ℝ)*K := by
    have hx2 : 2 ≤ x := by omega
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
    have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxn
    have hhx : 2*(h : ℝ) ≤ x := by exact_mod_cast hx
    have hlog2h : 0 ≤ Real.log (2*(h : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*h))
    have hlogmono : Real.log (2*(h : ℝ)) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hhx
    have hcubeX : (n : ℝ) ≤ (x : ℝ)^3 :=
      hcube.trans (pow_le_pow_left₀ (by positivity) hhx 3)
    have hlogcompare : Real.log (n : ℝ) ≤ 3*Real.log (x : ℝ) := by
      have he := Real.log_le_log hn0 hcubeX
      simpa only [Real.log_pow, Nat.cast_ofNat] using he
    have hpowcompare := pow_le_pow_left₀ hlogn.le hlogcompare A
    rw [mul_pow] at hpowcompare
    have hsingle (q : ℕ) (hq : q ∈ Icc 1 Q) :
        (∑ y ∈ Ico x (2*x), GBSkirtVariance.pointError q h y) ≤
          C*(h : ℝ)*(x : ℝ)*3^A/(Real.log (n : ℝ))^A := by
      obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hq
      letI : NeZero q := ⟨by omega⟩
      have hscaleq : (q : ℝ)^2*(x : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) := by
        apply le_trans _ hscale
        gcongr
      have hqlog : (q : ℝ) ≤ (Real.log (x : ℝ))^J := by
        apply (show (q : ℝ) ≤ Q by exact_mod_cast hqQ).trans
        exact hQ.trans (pow_le_pow_left₀ hlog2h hlogmono J)
      have hp := hT q x h (hTh.trans hx) hx2 hh (by linarith) hscaleq hqlog
      apply hp.trans
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_le_mul_of_nonneg_left hpowcompare
        (by positivity : 0 ≤ C*(h : ℝ)*(x : ℝ))]
    unfold GBSkirtVariance.row
    rw [sum_comm]
    apply (sum_le_sum hsingle).trans_eq
    simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]
    dsimp [K]
    ring
  have hc := GBSkirtVariance.dyadic_cover (GBSkirtVariance.row Q h)
    (GBSkirtVariance.row_nonneg Q h) n (2*h) (by omega) K hK hlocal
  rw [GBSkirtVariance.fullL1_rows]
  apply hc.trans
  exact add_le_add (by
    simpa only [show 2*(2*h) = 4*h by omega] using (initial_rows n Q h hn hhn)) le_rfl

def denominatorError (q n : ℕ) (δ : ℝ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : ZMod q, ∫ β in (-δ)..δ,
      ‖GoldbachWindow.poly (n+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2

def totalError (n Q : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 Q, denominatorError q n δ

theorem totalError_le_variance (n Q h : ℕ) (δ : ℝ)
    (hh : 0 < h) (hd : 0 ≤ δ) (hwidth : 6*(h : ℝ)*δ ≤ 1) :
    (h : ℝ)^2/4 * totalError n Q δ ≤ GBSkirtVariance.variance n Q h := by
  unfold totalError GBSkirtVariance.variance
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro q hq
  have hqn : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
  letI : NeZero q := ⟨hqn⟩
  rw [denominatorError, dif_neg hqn, GBSkirtVariance.mass, dif_neg hqn]
  exact GBSkirtVariance.denominator_bound n h δ hh hd hwidth

/-- Actual local Fourier mean square, uniformly for every rational center in
the indicated modulus range.  The displayed error consists of the short
endpoint contribution and a logarithmically saving bulk contribution. -/
theorem totalError_bound (J A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n Q h : ℕ, ∀ δ : ℝ,
      2 ≤ n → 0 < h → h ≤ n → Q ≤ n → T ≤ 2*h →
      (n : ℝ) ≤ (2*(h : ℝ))^3 →
      (Q : ℝ)^2*(n : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) →
      (Q : ℝ) ≤ (Real.log (2*(h : ℝ)))^J →
      0 ≤ δ → 6*(h : ℝ)*δ ≤ 1 →
      (h : ℝ)^2/4 * totalError n Q δ ≤
        (Q : ℝ)^2*((h : ℝ)*(Real.log (n : ℝ)+1))*
          (4*(Q : ℝ)*(h : ℝ)^2*(Real.log (5*(n : ℝ))+1) +
            2*((n+1 : ℕ) : ℝ)*(C*(Q : ℝ)*(h : ℝ)*3^A/(Real.log (n : ℝ))^A) +
            (Q : ℝ)*2*(h : ℝ)^2*(Real.log (n : ℝ)+1)) +
        (Q : ℝ)^2*((n+1+h : ℕ) : ℝ)*(Real.log (n : ℝ))^2 := by
  obtain ⟨C, hC, T, hT⟩ := fullL1_bound J A
  refine ⟨C, hC, T, ?_⟩
  intro n Q h δ hn hh hhn hQn hTh hcube hscale hQ hd hw
  have hfull := hT n Q h hn hh hhn hTh hcube hscale hQ
  have hclipped := (GBSkirtVariance.clipped_to_full n Q h hn hhn).trans
    (add_le_add hfull le_rfl)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  apply (totalError_le_variance n Q h δ hh hd hw).trans
  apply (GBSkirtVariance.variance_of_L1 n Q h hn hQn).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hclipped (by positivity)) le_rfl

/-- A logarithmically small local error, with all size conditions stated
explicitly so that the same estimate applies uniformly to moving bands. -/
theorem totalError_small (J A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n Q h : ℕ, ∀ δ : ℝ,
      2 ≤ n → 0 < h → h ≤ n → Q ≤ n → T ≤ 2*h →
      (n : ℝ) ≤ (2*(h : ℝ))^3 →
      (Q : ℝ)^2*(n : ℝ)^(4/9 : ℝ) ≤ (h : ℝ) →
      (Q : ℝ) ≤ (Real.log (2*(h : ℝ)))^J →
      0 ≤ δ → 6*(h : ℝ)*δ ≤ 1 → 16 ≤ Real.log (n : ℝ) →
      480*(Q : ℝ)^3*(h : ℝ)*(Real.log (n : ℝ))^6 ≤ (n : ℝ) →
      96*(C*3^A)*(Q : ℝ)^3*(Real.log (n : ℝ))^5 ≤ (Real.log (n : ℝ))^A →
      36*(Q : ℝ)^2*(Real.log (n : ℝ))^6 ≤ (h : ℝ)^2 →
      totalError n Q δ ≤ (n : ℝ)/(Real.log (n : ℝ))^4 := by
  obtain ⟨C,hC,T,hT⟩ := totalError_bound J A
  refine ⟨C,hC,T,?_⟩
  intro n Q h δ hn hh hhn hQn hTh hcube hscale hQ hd hw hlog hsmall hbulk hdiag
  let L := Real.log (n : ℝ)
  have hL : 16 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
  have hn1 : ((n+1 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (by omega : n+1 ≤ 2*n)
  have hn2 : ((n+1+h : ℕ) : ℝ) ≤ 3*(n : ℝ) := by exact_mod_cast (by omega : n+1+h ≤ 3*n)
  have hlogplus : L+1 ≤ 2*L := by linarith
  have hlogfive0 : 0 ≤ Real.log (5*(n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 5*n))
  have hlogfive : Real.log (5*(n : ℝ))+1 ≤ 4*L := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have hf := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    dsimp [L] at *
    linarith
  apply BeaumontSmallModuli.energy_charge A (n : ℝ) (h : ℝ) (Q : ℝ) L (C*3^A)
    (totalError n Q δ) hn0.le hh0 (by positivity) hL0 hsmall hbulk hdiag
  apply (hT n Q h δ hn hh hhn hQn hTh hcube hscale hQ hd hw).trans
  calc
    _ ≤ (Q : ℝ)^2*((h : ℝ)*(2*L))*
          (4*(Q : ℝ)*(h : ℝ)^2*(4*L) +
            2*(2*(n : ℝ))*(C*(Q : ℝ)*(h : ℝ)*3^A/L^A) +
            (Q : ℝ)*2*(h : ℝ)^2*(2*L)) +
          (Q : ℝ)^2*(3*(n : ℝ))*L^2 := by
      change _ ≤ _
      gcongr
    _ = _ := by ring

end
end BeaumontSmallModuliPolylog

/- Source section: BeaumontSmallModuliBand.lean -/

open Finset Filter MeasureTheory
open scoped BigOperators Topology Interval Classical
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace BeaumontSmallModuliBand
noncomputable section

private theorem norm_sub_sq_le (z w : ℂ) : ‖z-w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hp := pow_le_pow_left₀ (norm_nonneg (z-w)) (norm_sub_le z w) 2
  nlinarith only [hp, sq_nonneg (‖z‖-‖w‖)]

theorem integral_sub_sq_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ β in (-δ)..δ, ‖f β-g β‖^2) ≤
      2*(∫ β in (-δ)..δ, ‖f β‖^2) + 2*(∫ β in (-δ)..δ, ‖g β‖^2) := by
  have hfi : IntervalIntegrable (fun β => ‖f β‖^2) volume (-δ) δ :=
    (hf.norm.pow 2).intervalIntegrable (μ := volume) (-δ) δ
  have hgi : IntervalIntegrable (fun β => ‖g β‖^2) volume (-δ) δ :=
    (hg.norm.pow 2).intervalIntegrable (μ := volume) (-δ) δ
  calc
    _ ≤ ∫ β in (-δ)..δ, 2*‖f β‖^2+2*‖g β‖^2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (((hf.sub hg).norm.pow 2).intervalIntegrable _ _) ((hfi.const_mul 2).add (hgi.const_mul 2))
      intro β _
      exact norm_sub_sq_le _ _
    _ = _ := by
      rw [intervalIntegral.integral_add (hfi.const_mul 2) (hgi.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

def denominatorBandError (q L D : ℕ) (δ : ℝ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : ZMod q, ∫ β in (-δ)..δ,
      ‖GoldbachWindow.poly (L+D+2) (GoldbachGRHAnalytic.errorCoeff a) β -
        GoldbachWindow.poly (L+1) (GoldbachGRHAnalytic.errorCoeff a) β‖^2

def totalBandError (L D Q : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 Q, denominatorBandError q L D δ

theorem denominatorBandError_le (q L D : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    denominatorBandError q L D δ ≤
      2*BeaumontSmallModuliPolylog.denominatorError q (L+D+1) δ +
      2*BeaumontSmallModuliPolylog.denominatorError q L δ := by
  by_cases hq : q = 0
  · simp [denominatorBandError, BeaumontSmallModuliPolylog.denominatorError, hq]
  letI : NeZero q := ⟨hq⟩
  rw [denominatorBandError, dif_neg hq,
    BeaumontSmallModuliPolylog.denominatorError, dif_neg hq,
    BeaumontSmallModuliPolylog.denominatorError, dif_neg hq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro a _
  exact integral_sub_sq_le _ _
    (by unfold GoldbachWindow.poly GoldbachFourthMoment.phase; fun_prop)
    (by unfold GoldbachWindow.poly GoldbachFourthMoment.phase; fun_prop) δ hδ

theorem totalBandError_le (L D Q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    totalBandError L D Q δ ≤
      2*BeaumontSmallModuliPolylog.totalError (L+D+1) Q δ +
      2*BeaumontSmallModuliPolylog.totalError L Q δ := by
  unfold totalBandError BeaumontSmallModuliPolylog.totalError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_le_sum fun q _ => denominatorBandError_le q L D δ hδ

theorem additiveModel_eq_unitMean (q a : ℕ) [NeZero q] :
    GoldbachGRHWindow.additiveModel q (a : ZMod q) = GoldbachMajorArc.unitMean q a := by
  rw [GoldbachGRHWindow.additiveModel_eq_reduced_sum]
  unfold GoldbachMajorArc.unitMean
  congr 1
  apply sum_congr rfl
  intro r _
  unfold GoldbachMajorArc.phase
  congr 2
  ring

theorem band_error_eq (q a L D : ℕ) [NeZero q] (β : ℝ) :
    GoldbachWindow.poly (L+D+2) (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β -
      GoldbachWindow.poly (L+1) (GoldbachGRHAnalytic.errorCoeff (a : ZMod q)) β =
        BulkCircle.S L D ((a : ℝ)/q+β) - GoldbachMajorArc.unitMean q a*BulkCircle.U L D β := by
  have hlen : L+D+2 = (L+D+1)+1 := by omega
  rw [hlen, GoldbachGRHAnalytic.shifted_error_eq,
    GoldbachGRHAnalytic.shifted_error_eq, additiveModel_eq_unitMean]
  have hk (n : ℕ) : GoldbachGRHKernel.kernel n β = GoldbachMajorArc.kernel n β := by
    unfold GoldbachGRHKernel.kernel GoldbachWindow.poly GoldbachMajorArc.kernel
    simp only [one_mul]
    rfl
  rw [hk, hk]
  change (GoldbachMajorArc.primeSum (L+D+1) ((a : ℝ)/q+β) -
      GoldbachMajorArc.unitMean q a*GoldbachMajorArc.kernel (L+D+1) β) -
    (GoldbachMajorArc.primeSum L ((a : ℝ)/q+β) -
      GoldbachMajorArc.unitMean q a*GoldbachMajorArc.kernel L β) = _
  unfold BulkCircle.S BulkCircle.U
  ring

end
end BeaumontSmallModuliBand

/- Source section: BeaumontLowModel.lean -/

open Finset Filter MeasureTheory
open scoped Topology Interval Classical
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace BeaumontLowModel
noncomputable section

def mass (L D q a : ℕ) (s : Set ℝ) : ℝ :=
  ∫ β in s, ‖GoldbachMajorArc.unitMean q a * BulkCircle.U L D β‖^2

theorem kernel_eq_old (D : ℕ) (β : ℝ) :
    GoldbachMajorArc.kernel D β = GoldbachGRHKernel.kernel D β := by
  unfold GoldbachGRHKernel.kernel GoldbachWindow.poly GoldbachMajorArc.kernel
  simp only [one_mul]
  rfl

theorem mass_eq (L D q a : ℕ) (s : Set ℝ) :
    mass L D q a s = ‖GoldbachMajorArc.unitMean q a‖^2 *
      ∫ β in s, ‖GoldbachGRHKernel.kernel D β‖^2 := by
  have he (β : ℝ) : ‖GoldbachMajorArc.unitMean q a * BulkCircle.U L D β‖^2 =
      ‖GoldbachMajorArc.unitMean q a‖^2 * ‖GoldbachGRHKernel.kernel D β‖^2 := by
    rw [BulkCircle.shifted_kernel, norm_mul, norm_mul, BulkCircle.norm_phase,
      one_mul, mul_pow, kernel_eq_old]
  unfold mass
  simp_rw [he]
  exact MeasureTheory.integral_const_mul _ _

theorem centered_kernel_mass (D : ℕ) :
    (∫ β in Set.Icc (-(1/2) : ℝ) (1/2), ‖GoldbachGRHKernel.kernel D β‖^2) = (D : ℝ)+1 := by
  let F : ℝ → ℝ := fun β => ‖GoldbachGRHKernel.kernel D β‖^2
  have hp : Function.Periodic F 1 := by
    intro β
    simp only [F, GoldbachGRHKernel.kernel_periodic D β]
  have hi := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ)+1 = 1/2 by norm_num, zero_add] at hi
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
  exact hi.trans (GoldbachGRHKernel.full_parseval D)

theorem kernel_mass_le (D : ℕ) (s : Set ℝ)
    (hs : s ⊆ Set.Icc (-(1/2) : ℝ) (1/2)) :
    (∫ β in s, ‖GoldbachGRHKernel.kernel D β‖^2) ≤ (D : ℝ)+1 := by
  rw [← centered_kernel_mass D]
  apply setIntegral_mono_set
    (((GoldbachGRHKernel.kernel_continuous D).norm.pow 2).integrableOn_Icc)
    (Eventually.of_forall fun _ => sq_nonneg _)
  exact Eventually.of_forall hs

theorem kernel_tail_le (D : ℕ) (s : Set ℝ) (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (hs : s ⊆ Set.Icc (-(1/2) : ℝ) (1/2))
    (hcut : ∀ β ∈ s, r < |β|) :
    (∫ β in s, ‖GoldbachGRHKernel.kernel D β‖^2) ≤ 1/(2*r) := by
  let F : ℝ → ℝ := fun β => ‖GoldbachGRHKernel.kernel D β‖^2
  let A : Set ℝ := Set.Icc (-(1/2) : ℝ) (1/2)
  let B : Set ℝ := Set.Icc (-r) r
  have hF : Continuous F := (GoldbachGRHKernel.kernel_continuous D).norm.pow 2
  have hBA : B ⊆ A := Set.Icc_subset_Icc (neg_le_neg hrhalf) hrhalf
  have hsub : s ⊆ A \ B := by
    intro β hβ
    refine ⟨hs hβ, ?_⟩
    intro hb
    have hb' : |β| ≤ r := abs_le.mpr hb
    exact (not_lt_of_ge hb') (hcut β hβ)
  have hinner : (∫ β in B, F β) = GoldbachGRHKernel.mass D r := by
    rw [GoldbachGRHKernel.mass, intervalIntegral.integral_of_le (by linarith),
      ← integral_Icc_eq_integral_Ioc]
  have hfull : (∫ β in A, F β) = (D : ℝ)+1 := centered_kernel_mass D
  have ht : (∫ β in A \ B, F β) ≤ 1/(2*r) := by
    rw [setIntegral_sdiff measurableSet_Icc hF.integrableOn_Icc hBA, hinner, hfull]
    exact (GoldbachGRHKernel.mass_loss D hr hrhalf).2
  apply le_trans _ ht
  apply setIntegral_mono_set (hF.integrableOn_Icc.mono_set Set.sdiff_subset)
    (Eventually.of_forall fun _ => sq_nonneg _)
  exact Eventually.of_forall hsub

theorem mean_sq_le (q a : ℕ) (hq : 0 < q) (hc : a.Coprime q) :
    ‖GoldbachMajorArc.unitMean q a‖^2 ≤ 4/(q : ℝ) := by
  have he := pow_le_pow_left₀ (norm_nonneg _)
    (ThinRamanujan.unitMean_sqrt q a hq hc) 2
  apply he.trans_eq
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  norm_num

/-- On one low-denominator packet, its principal model contributes at most
O(D/R) outside the major arcs of cutoff R, including packets with q > R. -/
theorem model_minor_mass_le (L D q a R : ℕ) (hq : 0 < q) (hc : a.Coprime q)
    (hR : 0 < R) (hDR : 2*R ≤ D) (s : Set ℝ)
    (hs : s ⊆ Set.Icc (-(1/2) : ℝ) (1/2))
    (hcut : q ≤ R → ∀ β ∈ s, (R : ℝ)/((q : ℝ)*(D : ℝ)) < |β|) :
    mass L D q a s ≤ 4*((D : ℝ)+1)/(R : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hnon : 0 ≤ ∫ β in s, ‖GoldbachGRHKernel.kernel D β‖^2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [mass_eq]
  by_cases hqR : q ≤ R
  · let r : ℝ := (R : ℝ)/((q : ℝ)*(D : ℝ))
    have hr : 0 < r := by dsimp [r]; positivity
    have hrhalf : r ≤ 1/2 := by
      dsimp [r]
      apply (div_le_iff₀ (mul_pos hq0 hD0)).2
      have hDR' : 2*(R : ℝ) ≤ D := by exact_mod_cast hDR
      nlinarith only [hDR', mul_le_mul_of_nonneg_right hq1 hD0.le]
    have ht := kernel_tail_le D s r hr hrhalf hs (hcut hqR)
    have hm := mul_le_mul (mean_sq_le q a hq hc) ht hnon (by positivity : 0 ≤ 4/(q : ℝ))
    apply hm.trans
    have he : (4/(q : ℝ))*(1/(2*r)) = 2*(D : ℝ)/(R : ℝ) := by
      dsimp [r]
      field_simp
      ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hR0.le
    nlinarith only [Nat.cast_nonneg (α := ℝ) D]
  · have hRq : (R : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hqR))
    have hm := mul_le_mul (mean_sq_le q a hq hc) (kernel_mass_le D s hs)
      hnon (by positivity : 0 ≤ 4/(q : ℝ))
    apply hm.trans
    calc
      _ ≤ (4/(R : ℝ))*((D : ℝ)+1) := by gcongr
      _ = _ := by ring

end
end BeaumontLowModel

/- Source section: BeaumontLowPacket.lean -/

open Finset Filter MeasureTheory
open scoped Topology Interval BigOperators Classical
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace BeaumontLowPacket
noncomputable section

theorem band_denominator_nonneg (q L D : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ BeaumontSmallModuliBand.denominatorBandError q L D δ := by
  unfold BeaumontSmallModuliBand.denominatorBandError
  split_ifs
  · exact le_rfl
  · apply sum_nonneg
    intro a _
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => sq_nonneg _

theorem one_band_error_le (q a L D P : ℕ) (hq : 0 < q) (hqP : q ≤ P)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ β in (-δ)..δ, ‖BulkCircle.S L D ((a : ℝ)/q+β) -
      GoldbachMajorArc.unitMean q a*BulkCircle.U L D β‖^2) ≤
      BeaumontSmallModuliBand.totalBandError L D P δ := by
  letI : NeZero q := ⟨by omega⟩
  have hqmem : q ∈ Icc 1 P := mem_Icc.mpr ⟨hq, hqP⟩
  have hrow : BeaumontSmallModuliBand.denominatorBandError q L D δ ≤
      BeaumontSmallModuliBand.totalBandError L D P δ := by
    exact single_le_sum (fun r _ => band_denominator_nonneg r L D δ hδ) hqmem
  apply le_trans _ hrow
  rw [BeaumontSmallModuliBand.denominatorBandError, dif_neg (NeZero.ne q)]
  have hsingle := Finset.single_le_sum
    (fun b (_ : b ∈ (univ : Finset (ZMod q))) =>
      intervalIntegral.integral_nonneg_of_forall (μ := volume) (by linarith : -δ ≤ δ)
        (fun β => sq_nonneg
          (‖GoldbachWindow.poly (L+D+2) (GoldbachGRHAnalytic.errorCoeff b) β -
            GoldbachWindow.poly (L+1) (GoldbachGRHAnalytic.errorCoeff b) β‖)))
    (mem_univ (a : ZMod q))
  convert hsingle using 1
  apply intervalIntegral.integral_congr
  intro β _
  dsimp only
  rw [BeaumontSmallModuliBand.band_error_eq]

private theorem normsq_le_error (z w : ℂ) : ‖z‖^2 ≤ 2*‖z-w‖^2+2*‖w‖^2 := by
  have h := norm_add_le (z-w) w
  rw [sub_add_cancel] at h
  have hp := pow_le_pow_left₀ (norm_nonneg z) h 2
  nlinarith only [hp, sq_nonneg (‖z-w‖-‖w‖)]

/-- A complete local prime-energy bound on one rational packet.  The mask is
the complement of the actual major arcs, and the prime spectrum is the actual
central band, with no prime-power replacement. -/
theorem packet_minor_energy (L D q a R P : ℕ)
    (hq : 0 < q) (hqP : q ≤ P) (ha : a ≤ q) (hc : a.Coprime q)
    (hR : 0 < R) (hDR : 2*R ≤ D) (δ : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (B : Set ℝ) (hB : B ⊆ Set.Icc (-δ) δ)
    (hminor : ∀ β ∈ B, (a : ℝ)/q+β ∉ GoldbachBlockGeometry.arcs R D) :
    (∫ β in B, ‖BulkCircle.S L D ((a : ℝ)/q+β)‖^2) ≤
      2*BeaumontSmallModuliBand.totalBandError L D P δ + 8*((D : ℝ)+1)/(R : ℝ) := by
  let F : ℝ → ℂ := fun β => BulkCircle.S L D ((a : ℝ)/q+β)
  let M : ℝ → ℂ := fun β => GoldbachMajorArc.unitMean q a*BulkCircle.U L D β
  have hF : Continuous F := by
    unfold F BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hM : Continuous M := by
    unfold M BulkCircle.U GoldbachMajorArc.kernel GoldbachMajorArc.phase
    fun_prop
  have hiF : IntegrableOn (fun β => ‖F β‖^2) B volume :=
    ((hF.norm.pow 2).integrableOn_Icc).mono_set hB
  have hiM : IntegrableOn (fun β => ‖M β‖^2) B volume :=
    ((hM.norm.pow 2).integrableOn_Icc).mono_set hB
  have hiE : IntegrableOn (fun β => ‖F β-M β‖^2) B volume :=
    (((hF.sub hM).norm.pow 2).integrableOn_Icc).mono_set hB
  have hpoint : ∀ β : ℝ, ‖F β‖^2 ≤ 2*‖F β-M β‖^2+2*‖M β‖^2 :=
    fun β => normsq_le_error _ _
  have hcharge := MeasureTheory.integral_mono hiF ((hiE.const_mul 2).add (hiM.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hcharge
  rw [MeasureTheory.integral_add (hiE.const_mul 2) (hiM.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hcharge
  have herror : (∫ β in B, ‖F β-M β‖^2) ≤
      BeaumontSmallModuliBand.totalBandError L D P δ := by
    apply le_trans _ (one_band_error_le q a L D P hq hqP δ hδ)
    rw [intervalIntegral.integral_of_le (by linarith : -δ ≤ δ),
      ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set ((hF.sub hM).norm.pow 2 |>.integrableOn_Icc)
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hB)
  have hhalf : B ⊆ Set.Icc (-(1/2) : ℝ) (1/2) :=
    hB.trans (Set.Icc_subset_Icc (neg_le_neg hδhalf) hδhalf)
  have hmodel := BeaumontLowModel.model_minor_mass_le L D q a R hq hc hR hDR B hhalf (by
    intro hqR β hβ
    by_contra hfail
    have hbound : |β| ≤ (R : ℝ)/((q : ℝ)*(D : ℝ)) := le_of_not_gt hfail
    apply hminor β hβ
    refine ⟨q, a, hq, hqR, ha, hc, ?_⟩
    change |(a : ℝ)/q+β-(a : ℝ)/q| ≤ (R : ℝ)/((q : ℝ)*(D : ℝ))
    simpa only [add_sub_cancel_left] using hbound)
  change (∫ β in B, ‖M β‖^2) ≤ 4*((D : ℝ)+1)/(R : ℝ) at hmodel
  change (∫ β in B, ‖F β‖^2) ≤ _
  calc
    _ ≤ 2*(∫ β in B, ‖F β-M β‖^2) + 2*(∫ β in B, ‖M β‖^2) := hcharge
    _ ≤ 2*BeaumontSmallModuliBand.totalBandError L D P δ + 2*(4*((D : ℝ)+1)/(R : ℝ)) :=
      id <| add_le_add (mul_le_mul_of_nonneg_left herror (by norm_num))
        (mul_le_mul_of_nonneg_left hmodel (by norm_num))
    _ = _ := by ring

/-- The preceding packet estimate in the original frequency variable, ready
to be used on a mesh cell. -/
theorem cell_minor_energy (L D q a R P : ℕ)
    (hq : 0 < q) (hqP : q ≤ P) (ha : a ≤ q) (hc : a.Coprime q)
    (hR : 0 < R) (hDR : 2*R ≤ D) (δ l u : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2) (hlu : l ≤ u)
    (hl : (a : ℝ)/q-δ ≤ l) (hu : u ≤ (a : ℝ)/q+δ) :
    (∫ t in l..u, (GoldbachBlockGeometry.arcs R D)ᶜ.indicator
      (fun t => ‖BulkCircle.S L D t‖^2) t) ≤
      4*(BeaumontSmallModuliPolylog.totalError (L+D+1) P δ +
        BeaumontSmallModuliPolylog.totalError L P δ) + 8*((D : ℝ)+1)/(R : ℝ) := by
  let c : ℝ := (a : ℝ)/q
  let W : Set ℝ := (GoldbachBlockGeometry.arcs R D)ᶜ
  let V : Set ℝ := (fun β : ℝ => c+β) ⁻¹' W
  let B : Set ℝ := Set.Ioc (l-c) (u-c) ∩ V
  have hW : MeasurableSet W :=
    (GoldbachEstermann.measurable_block_arcs R D).compl
  have hV : MeasurableSet V := hW.preimage (continuous_const.add continuous_id).measurable
  have hB : B ⊆ Set.Icc (-δ) δ := by
    intro β hβ
    have hb := hβ.1
    change l-c < β ∧ β ≤ u-c at hb
    change c-δ ≤ l at hl
    change u ≤ c+δ at hu
    constructor <;> linarith
  have hminor : ∀ β ∈ B, c+β ∉ GoldbachBlockGeometry.arcs R D := by
    intro β hβ
    exact hβ.2
  have he : (∫ t in l..u, W.indicator (fun t => ‖BulkCircle.S L D t‖^2) t) =
      ∫ β in B, ‖BulkCircle.S L D (c+β)‖^2 := by
    have hs := intervalIntegral.integral_comp_add_left
      (f := W.indicator (fun t => ‖BulkCircle.S L D t‖^2)) (a := l-c) (b := u-c) c
    have hs' : (∫ β in (l-c)..(u-c), W.indicator (fun t => ‖BulkCircle.S L D t‖^2) (c+β)) =
        ∫ t in l..u, W.indicator (fun t => ‖BulkCircle.S L D t‖^2) t := by
      simpa only [show c+(l-c) = l by ring, show c+(u-c) = u by ring] using hs
    rw [← hs', intervalIntegral.integral_of_le (sub_le_sub_right hlu c)]
    change (∫ β in Set.Ioc (l-c) (u-c), V.indicator (fun β => ‖BulkCircle.S L D (c+β)‖^2) β) = _
    rw [MeasureTheory.integral_indicator hV, Measure.restrict_restrict hV]
    simp only [B, Set.inter_comm]
  change (∫ t in l..u, W.indicator (fun t => ‖BulkCircle.S L D t‖^2) t) ≤ _
  rw [he]
  have hp := packet_minor_energy L D q a R P hq hqP ha hc hR hDR δ hδ hδhalf B hB hminor
  have hb := BeaumontSmallModuliBand.totalBandError_le L D P δ hδ
  apply hp.trans
  calc
    _ ≤ 2*(2*BeaumontSmallModuliPolylog.totalError (L+D+1) P δ +
        2*BeaumontSmallModuliPolylog.totalError L P δ) + 8*((D : ℝ)+1)/(R : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) le_rfl
    _ = _ := by ring

end
end BeaumontLowPacket




end

/- Source: BeaumontParameters.lean -/
section

/-! Common parameters and their elementary eventual growth properties. -/

open Filter
open scoped Topology

namespace GoldbachBeaumontParameters

def scale (X : ℕ) : ℕ := 3*X
def logScale (X : ℕ) : ℕ := Nat.log 2 (3*X+2)
def window (X : ℕ) : ℕ := Nat.sqrt X
def denominatorCutoff (X : ℕ) : ℕ := logScale X ^ 1000
def approximationBound (X : ℕ) : ℕ := window X / logScale X ^ 2000
def physicalWindow (X : ℕ) : ℕ := window X / 24
def progressionWindow (X : ℕ) : ℕ := approximationBound X / 24
def lowerFactor (X : ℕ) : ℕ := logScale X ^ 101
def upperFactor (X : ℕ) : ℕ := physicalWindow X / logScale X ^ 100

theorem logScale_pos (X : ℕ) : 0 < logScale X :=
  Nat.log_pos (by decide) (by omega)

theorem logScale_tendsto : Tendsto logScale atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2^b:ℕ)] with X hX
  exact Nat.le_log_of_pow_le (by decide) (by omega)

theorem logScale_le_four_log {X : ℕ} (hX : 4 ≤ X) :
    (logScale X : ℝ) ≤ 4*Real.log X := by
  have hXp : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0<X)
  have harg : 0 < ((3*X+2:ℕ):ℝ) := by positivity
  have hlog := Real.natLog_le_logb (3*X+2) 2
  simp only [Nat.cast_ofNat,Real.logb] at hlog
  have hL : 0 ≤ Real.log ((3*X+2:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1≤3*X+2))
  have htwo := Real.log_two_gt_d9
  have hhalf : Real.log ((3*X+2:ℕ):ℝ)/Real.log 2 ≤
      2*Real.log ((3*X+2:ℕ):ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith [mul_nonneg hL (show 0 ≤ 2*Real.log 2-1 by linarith)]
  have hargle : ((3*X+2:ℕ):ℝ) ≤ (X:ℝ)^2 := by
    have hXr : (4:ℝ) ≤ X := by exact_mod_cast hX
    push_cast
    nlinarith
  have hsq := Real.log_le_log harg hargle
  rw [Real.log_pow] at hsq
  norm_num1 at hsq
  exact (hlog.trans hhalf).trans (by linarith)

theorem eventually_mul_logScale_power_le_rpow (C : ℝ) (hC : 0 ≤ C)
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ X : ℕ in atTop, C*(logScale X : ℝ)^k ≤ (X:ℝ)^s := by
  have ht : Tendsto (fun X : ℕ => (Real.log (X:ℝ))^k/(X:ℝ)^s) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (k:ℝ) hs).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hm := ht.const_mul (C*4^k)
  simp only [mul_zero] at hm
  filter_upwards [hm.eventually_lt_const zero_lt_one, eventually_ge_atTop (4:ℕ)]
    with X hsmall hX
  have hXp : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0<X)
  have hxsp : 0 < (X:ℝ)^s := Real.rpow_pos_of_pos hXp _
  have hcap := pow_le_pow_left₀ (Nat.cast_nonneg (logScale X))
    (logScale_le_four_log hX) k
  rw [mul_pow] at hcap
  have hsmall' : C*4^k*(Real.log (X:ℝ))^k < (X:ℝ)^s := by
    apply (div_lt_one hxsp).mp
    simpa only [mul_div_assoc] using hsmall
  exact (mul_le_mul_of_nonneg_left hcap hC).trans
    (by nlinarith only [hsmall'])

theorem eventually_logScale_power_le (k : ℕ) :
    ∀ᶠ X : ℕ in atTop, logScale X ^ k ≤ X := by
  filter_upwards [eventually_mul_logScale_power_le_rpow 1 (by norm_num) k 1 (by norm_num)]
    with X hX
  norm_num only [one_mul, Real.rpow_one] at hX
  exact_mod_cast hX

theorem eventually_large_grid :
    ∀ᶠ X : ℕ in atTop, 1000000 ≤ logScale X ∧ logScale X ^ 100000 ≤ X :=
  (logScale_tendsto.eventually_ge_atTop 1000000).and (eventually_logScale_power_le 100000)

theorem natural_log_margin {X : ℕ} (hX : 0 < X) (hg : 32 ≤ logScale X) :
    1 + Real.log (64*(scale X:ℝ)) ≤ (logScale X:ℝ) := by
  have hN : 0 < (scale X:ℝ) := by dsimp [scale]; positivity
  have hp : scale X < 2^(logScale X+1) := by
    have ht := Nat.lt_pow_succ_log_self (by decide : 1<2) (3*X+2)
    dsimp [scale,logScale] at *
    omega
  have hlog := Real.log_le_log hN (by exact_mod_cast hp.le : (scale X:ℝ) ≤ (2:ℝ)^(logScale X+1))
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have h64 : Real.log (64:ℝ) = 6*Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (64:ℝ)≠0) hN.ne', h64]
  have htwo : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have hgr : (32:ℝ) ≤ logScale X := by exact_mod_cast hg
  have hm := mul_le_mul_of_nonneg_left htwo (show 0 ≤ (logScale X:ℝ)+7 by positivity)
  nlinarith


end GoldbachBeaumontParameters
end

/- Source: BeaumontLowGrowth.lean -/
section


open Filter
open scoped Topology

namespace BeaumontLowScales
open GoldbachBeaumontParameters

lemma real_le_nat_div (a b : ℕ) (t : ℝ) (hb : 0 < b) (ht : 1 ≤ t)
    (hab : 2*(b : ℝ)*t ≤ (a : ℝ)) : t ≤ ((a/b : ℕ) : ℝ) := by
  have hfloor : (a : ℝ) < (b : ℝ)*(((a/b : ℕ) : ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ a hb
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  have htwot : 2*t < ((a/b : ℕ) : ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hbr).mp (by nlinarith only [hab,hfloor])
  linarith

lemma window_root_bounds {X : ℕ} (hX : 1 ≤ X) :
    (window X : ℝ) ≤ (X : ℝ)^(1/2 : ℝ) ∧
    (X : ℝ)^(1/2 : ℝ) ≤ 2*(window X : ℝ) := by
  have hH : 1 ≤ window X := Nat.le_sqrt'.mpr (by simpa using hX)
  have hHr : (1 : ℝ) ≤ window X := by exact_mod_cast hH
  have hsq : (window X : ℝ)^2 ≤ (X : ℝ) := by
    exact_mod_cast Nat.sqrt_le' X
  have hsq' : (X : ℝ) < ((window X : ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' X
  have hroot := Real.sq_sqrt (Nat.cast_nonneg X)
  have hroot0 := Real.sqrt_nonneg (X : ℝ)
  rw [← Real.sqrt_eq_rpow]
  constructor <;> nlinarith

lemma progression_le_window (X : ℕ) : progressionWindow X ≤ window X :=
  (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)

theorem eventually_divided_window_power (k : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ)^(17/36 : ℝ) ≤ ((window X/(logScale X^k*24) : ℕ) : ℝ) := by
  filter_upwards [eventually_mul_logScale_power_le_rpow 96 (by norm_num)
      k (1/36) (by norm_num), eventually_ge_atTop (1 : ℕ)] with X hsmall hX
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have ht : 1 ≤ (X : ℝ)^(17/36 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  have hg : 0 < logScale X := logScale_pos X
  have hg0 : 0 ≤ (logScale X : ℝ) := by positivity
  have hcap := mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg hXp.le (17/36 : ℝ))
  rw [← Real.rpow_add hXp] at hcap
  norm_num only [show (1/36 : ℝ)+17/36 = 1/2 by norm_num] at hcap
  have hroot := (window_root_bounds hX).2
  apply real_le_nat_div (window X) (logScale X ^ k * 24)
    ((X : ℝ)^(17/36 : ℝ)) (by positivity) ht (by
      push_cast
      nlinarith only [hcap,hroot])

theorem eventually_progression_power :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ)^(17/36 : ℝ) ≤ (progressionWindow X : ℝ) := by
  simpa only [progressionWindow, approximationBound, Nat.div_div_eq_div_mul] using
    eventually_divided_window_power 2000


end BeaumontLowScales
end

/- Source: BeaumontLowScales.lean -/
section


/-! Specialization of the actual small-modulus error estimate to the common
square-root-window parameters. All estimates are uniform in the two endpoints
of the central prime band. -/

open Filter MeasureTheory
open scoped Topology Interval

namespace BeaumontLowScales

open GoldbachBeaumontParameters

noncomputable def packetRadius (X : ℕ) : ℝ :=
  1/(approximationBound X : ℝ) + 1/(window X : ℝ)

lemma prefix_log_bounds {X n : ℕ} (hX : 100 ≤ X)
    (hg : 32 ≤ logScale X) (hnlo : scale X ≤ 10*n) (hnhi : n ≤ scale X) :
    (logScale X : ℝ) ≤ 8*Real.log (n : ℝ) ∧
    Real.log (n : ℝ) ≤ (logScale X : ℝ) := by
  have hn : 10 ≤ n := by dsimp [scale] at hnlo; omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hnX : (X : ℝ) ≤ (n : ℝ)^2 := by
    have hnr : (10 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 3*(X : ℝ) ≤ 10*(n : ℝ) := by exact_mod_cast hnlo
    nlinarith
  have hl := Real.log_le_log hXr hnX
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hglog := logScale_le_four_log (by omega : 4 ≤ X)
  have hupper := natural_log_margin (by omega : 0 < X) hg
  have hn64 : (n : ℝ) ≤ 64*(scale X : ℝ) := by
    have hh : (n : ℝ) ≤ (scale X : ℝ) := by exact_mod_cast hnhi
    have : (0 : ℝ) ≤ scale X := by positivity
    linarith
  have hlogupper := Real.log_le_log hnp hn64
  exact ⟨by linarith, by linarith⟩

lemma packetRadius_bounds {X : ℕ} (hR : 4 ≤ approximationBound X) :
    0 ≤ packetRadius X ∧ packetRadius X ≤ 1/2 ∧
    6*(progressionWindow X : ℝ)*packetRadius X ≤ 1 := by
  have hRH : approximationBound X ≤ window X := Nat.div_le_self _ _
  have hRp : 0 < (approximationBound X : ℝ) := by exact_mod_cast (by omega : 0 < approximationBound X)
  have hHp : 0 < (window X : ℝ) := by exact_mod_cast (by omega : 0 < window X)
  have hRHr : (approximationBound X : ℝ) ≤ window X := by exact_mod_cast hRH
  have hR4 : (4 : ℝ) ≤ approximationBound X := by exact_mod_cast hR
  have hrec : 1/(window X : ℝ) ≤ 1/(approximationBound X : ℝ) :=
    one_div_le_one_div_of_le hRp hRHr
  have hδ : packetRadius X ≤ 2/(approximationBound X : ℝ) := by
    dsimp [packetRadius]
    calc
      1/(approximationBound X : ℝ)+1/(window X : ℝ) ≤
          1/(approximationBound X : ℝ)+1/(approximationBound X : ℝ) := add_le_add le_rfl hrec
      _ = _ := by ring
  have hhR : 24*(progressionWindow X : ℝ) ≤ (approximationBound X : ℝ) := by
    exact_mod_cast Nat.mul_div_le (approximationBound X) 24
  refine ⟨by unfold packetRadius; positivity, ?_, ?_⟩
  · exact hδ.trans ((div_le_iff₀ hRp).2 (by linarith))
  · calc
      _ ≤ 6*(progressionWindow X : ℝ)*(2/(approximationBound X : ℝ)) := by
        gcongr
      _ ≤ 1 := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hRp).2 (by nlinarith)

/-- The true progression error at either endpoint of a central band. The
threshold is independent of the endpoint, hence of the moving target window. -/
theorem eventually_prefix_error :
    ∀ᶠ X : ℕ in atTop, ∀ n : ℕ, scale X ≤ 10*n → n ≤ scale X →
      BeaumontSmallModuliPolylog.totalError n (denominatorCutoff X) (packetRadius X) ≤
        4096*(scale X : ℝ)/(logScale X : ℝ)^4 := by
  obtain ⟨C,hC,T,hT⟩ := BeaumontSmallModuliPolylog.totalError_small 2000 12000
  have hgC : ∀ᶠ X : ℕ in atTop,
      8*(96*(C*3^12000)) ≤ (logScale X : ℝ) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp logScale_tendsto).eventually_ge_atTop _
  filter_upwards [eventually_progression_power,
      logScale_tendsto.eventually_ge_atTop (max 1000000 T),
      eventually_ge_atTop (100 : ℕ), hgC,
      eventually_mul_logScale_power_le_rpow 3 (by norm_num) 2000 (1/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 1600 (by norm_num) 3006 (1/2) (by norm_num),
      eventually_mul_logScale_power_le_rpow 6 (by norm_num) 1003 (17/36) (by norm_num)]
    with X hpow hg hX hgC hAP hEP hDG
  intro n hnlo hnhi
  let g : ℝ := logScale X
  let h : ℝ := progressionWindow X
  let L : ℝ := Real.log (n : ℝ)
  have hgN : 1000000 ≤ logScale X := (le_max_left _ _).trans hg
  have hgT : T ≤ logScale X := (le_max_right _ _).trans hg
  have hgR : (1000000 : ℝ) ≤ g := by dsimp [g]; exact_mod_cast hgN
  have hg0 : 0 < g := by linarith only [hgR]
  have hg1 : 1 ≤ g := by linarith only [hgR]
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hn : 2 ≤ n := by dsimp [scale] at hnlo; omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlor : 3*(X : ℝ) ≤ 10*(n : ℝ) := by exact_mod_cast hnlo
  have hnhir : (n : ℝ) ≤ 3*(X : ℝ) := by exact_mod_cast hnhi
  obtain ⟨hgL,hLg⟩ := prefix_log_bounds hX (by omega : 32 ≤ logScale X) hnlo hnhi
  change g ≤ 8*L at hgL
  change L ≤ g at hLg
  have hL : 16 ≤ L := by linarith only [hgR,hgL]
  have hL0 : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hpow1 : 1 ≤ (X : ℝ)^(17/36 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hh1 : 1 ≤ h := hpow1.trans hpow
  have hh0 : 0 < h := by linarith only [hh1]
  have hh : 0 < progressionWindow X := by
    have he : (0 : ℝ) < progressionWindow X := hh0
    exact_mod_cast he
  have hH10 : 10 ≤ window X := Nat.le_sqrt'.mpr (by norm_num; exact hX)
  have hHsq := Nat.sqrt_le' X
  have hHn : window X ≤ n := by
    dsimp [window] at hH10 hHsq ⊢
    dsimp [scale] at hnlo
    nlinarith only [hH10,hHsq,hnlo]
  have hhn : progressionWindow X ≤ n := (progression_le_window X).trans hHn
  have hQc : (denominatorCutoff X : ℝ) = g^1000 := by
    simp only [denominatorCutoff,Nat.cast_pow,g]
  have hQh : (denominatorCutoff X : ℝ) ≤ h := by
    rw [hQc]
    have hmono := pow_le_pow_right₀ hg1 (by norm_num : 1000 ≤ 1003)
    have hcap : g^1003 ≤ (X : ℝ)^(17/36 : ℝ) := by
      change 6*g^1003 ≤ _ at hDG
      linarith only [hDG,pow_nonneg hg0.le 1003]
    exact hmono.trans (hcap.trans hpow)
  have hQhn : denominatorCutoff X ≤ progressionWindow X := by
    have he : (denominatorCutoff X : ℝ) ≤ (progressionWindow X : ℝ) := hQh
    exact_mod_cast he
  have hQn : denominatorCutoff X ≤ n := hQhn.trans hhn
  have hgQ : logScale X ≤ denominatorCutoff X := by
    dsimp [denominatorCutoff]
    exact Nat.le_self_pow (by norm_num : 1000 ≠ 0) _
  have hTh : T ≤ 2*progressionWindow X := by
    have := hgT.trans (hgQ.trans hQhn)
    omega
  have hroot := window_root_bounds (by omega : 1 ≤ X)
  have hhroot : h ≤ (X : ℝ)^(1/2 : ℝ) :=
    (by
      change (progressionWindow X : ℝ) ≤ (window X : ℝ)
      exact_mod_cast progression_le_window X : h ≤ (window X : ℝ)).trans hroot.1
  have hcubelow : (X : ℝ)^(1/3 : ℝ) ≤ h :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1/3 : ℝ) ≤ 17/36)).trans hpow
  have hcubeX : (X : ℝ) ≤ h^3 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le (1/3 : ℝ)) hcubelow 3
    have he : ((X : ℝ)^(1/3 : ℝ))^3 = (X : ℝ) := by
      simpa only [one_div,Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hXp.le (by norm_num : (3 : ℕ) ≠ 0)
    rwa [he] at hp
  have hcube : (n : ℝ) ≤ (2*h)^3 := by
    nlinarith only [hnhir,hcubeX,pow_nonneg hh0.le 3]
  have hnpow : (n : ℝ)^(4/9 : ℝ) ≤ 3*(X : ℝ)^(4/9 : ℝ) := by
    calc
      _ ≤ (3*(X : ℝ))^(4/9 : ℝ) := Real.rpow_le_rpow hnp.le hnhir (by norm_num)
      _ = (3 : ℝ)^(4/9 : ℝ)*(X : ℝ)^(4/9 : ℝ) := Real.mul_rpow (by norm_num) hXp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num))
        (Real.rpow_nonneg hXp.le _)
  have hAP' := mul_le_mul_of_nonneg_right hAP (Real.rpow_nonneg hXp.le (4/9 : ℝ))
  rw [← Real.rpow_add hXp] at hAP'
  norm_num only [show (1/36 : ℝ)+4/9 = 17/36 by norm_num] at hAP'
  have hscale : (denominatorCutoff X : ℝ)^2*(n : ℝ)^(4/9 : ℝ) ≤ h := by
    rw [hQc]
    calc
      _ ≤ (g^1000)^2*(3*(X : ℝ)^(4/9 : ℝ)) := by gcongr
      _ = (3*g^2000)*(X : ℝ)^(4/9 : ℝ) := by ring
      _ ≤ (X : ℝ)^(17/36 : ℝ) := hAP'
      _ ≤ h := hpow
  have hloghx := Real.log_le_log (Real.rpow_pos_of_pos hXp _) hcubelow
  rw [Real.log_rpow hXp] at hloghx
  have hglog := logScale_le_four_log (by omega : 4 ≤ X)
  change g ≤ _ at hglog
  have hghlog : g ≤ 12*Real.log h := by linarith only [hloghx,hglog]
  have hlogh : 12 ≤ Real.log h := by linarith only [hghlog,hgR]
  have hlog2h := Real.log_le_log hh0 (show h ≤ 2*h by linarith only [hh0])
  have hglog2sq : g ≤ (Real.log (2*h))^2 := by
    nlinarith only [hghlog,hlogh,hlog2h,sq_nonneg (Real.log (2*h)-12)]
  have hQlog : (denominatorCutoff X : ℝ) ≤ (Real.log (2*h))^2000 := by
    rw [hQc]
    have he := pow_le_pow_left₀ hg0.le hglog2sq 1000
    simpa only [← pow_mul, show 2*1000 = 2000 by norm_num] using he
  have hR : 4 ≤ approximationBound X := by
    have hd : 24*progressionWindow X ≤ approximationBound X :=
      Nat.mul_div_le (approximationBound X) 24
    omega
  obtain ⟨hδ,hδhalf,hw⟩ := packetRadius_bounds hR
  have hsmall : 480*(denominatorCutoff X : ℝ)^3*h*L^6 ≤ (n : ℝ) := by
    have hcap := mul_le_mul_of_nonneg_right hEP (Real.rpow_nonneg hXp.le (1/2 : ℝ))
    have hroot_sq : ((X : ℝ)^(1/2 : ℝ))^2 = (X : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hXp.le
    have hcap' : 1600*g^3006*(X : ℝ)^(1/2 : ℝ) ≤ (X : ℝ) := by
      simpa only [g, ← pow_two, hroot_sq] using hcap
    calc
      _ ≤ 480*(g^1000)^3*((X : ℝ)^(1/2 : ℝ))*g^6 := by rw [hQc]; gcongr
      _ = 480*g^3006*(X : ℝ)^(1/2 : ℝ) := by ring
      _ ≤ (n : ℝ) := by nlinarith only [hcap',hnlor]
  have hbulk : 96*(C*3^12000)*(denominatorCutoff X : ℝ)^3*L^5 ≤ L^12000 := by
    have hgLsq : g ≤ L^2 := by nlinarith only [hgL,hL,sq_nonneg (L-8)]
    have hPcube : (denominatorCutoff X : ℝ)^3 ≤ L^6000 := by
      rw [hQc]
      have hp := pow_le_pow_left₀ hg0.le hgLsq 3000
      simpa only [← pow_mul] using hp
    have hK : 96*(C*3^12000) ≤ L := by
      change 8*(96*(C*3^12000)) ≤ g at hgC
      exact le_of_mul_le_mul_left (hgC.trans hgL) (by norm_num : (0 : ℝ) < 8)
    calc
      _ ≤ L*L^6000*L^5 := by gcongr
      _ = L^6006 := by ring
      _ ≤ _ := pow_le_pow_right₀ hL1 (by norm_num : 6006 ≤ 12000)
  have hdiag : 36*(denominatorCutoff X : ℝ)^2*L^6 ≤ h^2 := by
    have hbase : 6*g^1003 ≤ h := hDG.trans hpow
    calc
      _ ≤ 36*(g^1000)^2*g^6 := by rw [hQc]; gcongr
      _ = (6*g^1003)^2 := by ring
      _ ≤ h^2 := pow_le_pow_left₀ (by positivity) hbase 2
  have herr := hT n (denominatorCutoff X) (progressionWindow X) (packetRadius X)
    hn hh hhn hQn hTh hcube hscale hQlog hδ hw hL hsmall hbulk hdiag
  apply herr.trans
  have hgpow := pow_le_pow_left₀ hg0.le hgL 4
  have hgp : 0 < g^4 := by positivity
  have hLp : 0 < L^4 := by positivity
  apply (div_le_div_iff₀ hLp hgp).2
  have hNn : (n : ℝ) ≤ (scale X : ℝ) := by exact_mod_cast hnhi
  change (n : ℝ)*g^4 ≤ 4096*(scale X : ℝ)*L^4
  calc
    _ ≤ (n : ℝ)*(8*L)^4 := mul_le_mul_of_nonneg_left hgpow hnp.le
    _ ≤ (scale X : ℝ)*(8*L)^4 := mul_le_mul_of_nonneg_right hNn (by positivity)
    _ = _ := by ring

/-- Uniform low-denominator branch on a whole frequency mesh cell. The
Dirichlet approximation is required only at its left endpoint. -/
theorem eventually_low_denominator_cell :
    ∀ᶠ X : ℕ in atTop, ∀ L D q a j : ℕ,
      scale X ≤ 10*L → L+D+1 ≤ scale X → 2*logScale X^18 ≤ D →
      0 < q → q ≤ denominatorCutoff X → a ≤ q → a.Coprime q →
      |(j : ℝ)/(window X : ℝ)-(a : ℝ)/(q : ℝ)| ≤
        1/((q : ℝ)*(approximationBound X : ℝ)) →
      (∫ t in ((j : ℝ)/(window X : ℝ))..(((j : ℝ)+1)/(window X : ℝ)),
        (Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachBlockGeometry.arcs (logScale X^18) D)ᶜ.indicator
          (fun t => ‖Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.BulkCircle.S L D t‖^2) t) ≤
        (scale X : ℝ)/(logScale X : ℝ)^3 := by
  filter_upwards [eventually_prefix_error, eventually_progression_power,
      logScale_tendsto.eventually_ge_atTop 1000000, eventually_ge_atTop (1 : ℕ)]
    with X herror hprog hg hX
  intro L D q a j hL hD hmajor hq hqP ha hc happrox
  let g : ℝ := logScale X
  let N : ℝ := scale X
  let H : ℝ := window X
  let R : ℝ := approximationBound X
  let c : ℝ := (a : ℝ)/(q : ℝ)
  let l : ℝ := (j : ℝ)/H
  let u : ℝ := ((j : ℝ)+1)/H
  have hgR : (1000000 : ℝ) ≤ g := by dsimp [g]; exact_mod_cast hg
  have hg0 : 0 < g := by linarith only [hgR]
  have hg1 : 1 ≤ g := by linarith only [hgR]
  have hN0 : 0 ≤ N := by positivity
  have hh1 : 1 ≤ progressionWindow X := by
    have ht : 1 ≤ (X : ℝ)^(17/36 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
    exact_mod_cast ht.trans hprog
  have hR4 : 4 ≤ approximationBound X := by
    have hd : 24*progressionWindow X ≤ approximationBound X :=
      Nat.mul_div_le (approximationBound X) 24
    omega
  have hRp : 0 < R := by dsimp [R]; exact_mod_cast (by omega : 0 < approximationBound X)
  have hRH : approximationBound X ≤ window X := Nat.div_le_self _ _
  have hHp : 0 < H := by dsimp [H]; exact_mod_cast (by omega : 0 < window X)
  have hqp : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hδ,hδhalf,hw⟩ := packetRadius_bounds hR4
  have hinv : 1/((q : ℝ)*R) ≤ 1/R := by
    apply one_div_le_one_div_of_le hRp
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) hRp.le]
  have hnear : |l-c| ≤ 1/R := happrox.trans hinv
  have habs := abs_le.mp hnear
  have hlu : l ≤ u := by
    dsimp [l,u]
    exact div_le_div_of_nonneg_right (by linarith) hHp.le
  have hu_eq : u = l+1/H := by dsimp [u,l]; ring
  have hl : c-packetRadius X ≤ l := by
    have hinvH : 0 ≤ 1/H := by positivity
    change 0 ≤ 1/(window X : ℝ) at hinvH
    dsimp [packetRadius] at *
    change -(1/R) ≤ l-c ∧ l-c ≤ 1/R at habs
    change c-(1/R+1/H) ≤ l
    linarith
  have hu : u ≤ c+packetRadius X := by
    change u ≤ c+(1/R+1/H)
    rw [hu_eq]
    linarith only [habs.2]
  have hmainpos : 0 < logScale X^18 := pow_pos (logScale_pos X) _
  have he := BeaumontLowPacket.cell_minor_energy L D q a (logScale X^18)
    (denominatorCutoff X) hq hqP ha hc hmainpos hmajor (packetRadius X) l u
    hδ hδhalf hlu hl hu
  have hLhi : L ≤ scale X := by omega
  have hLupper : scale X ≤ 10*(L+D+1) := by omega
  have heL := herror L hL hLhi
  have heU := herror (L+D+1) hLupper hD
  have hDp : (D : ℝ)+1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show D+1 ≤ scale X by omega)
  have hmaincast : ((logScale X^18 : ℕ) : ℝ) = g^18 := by simp only [Nat.cast_pow,g]
  change (∫ t in l..u, _) ≤ N/g^3
  apply he.trans
  rw [hmaincast]
  change BeaumontSmallModuliPolylog.totalError L (denominatorCutoff X) (packetRadius X) ≤
    4096*N/g^4 at heL
  change BeaumontSmallModuliPolylog.totalError (L+D+1) (denominatorCutoff X) (packetRadius X) ≤
    4096*N/g^4 at heU
  have hmodel : 8*((D : ℝ)+1)/g^18 ≤ 8*N/g^4 := by
    calc
      _ ≤ 8*N/g^18 := div_le_div_of_nonneg_right (by linarith only [hDp]) (by positivity)
      _ ≤ 8*N/g^4 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hg1 (by norm_num : 4 ≤ 18))
  calc
    _ ≤ 4*(4096*N/g^4+4096*N/g^4)+8*N/g^4 := by gcongr
    _ = 32776*N/g^4 := by ring
    _ ≤ N/g^3 := by
      apply (div_le_div_iff₀ (by positivity : 0 < g^4) (by positivity : 0 < g^3)).2
      calc
        _ = 32776*(N*g^3) := by ring
        _ ≤ g*(N*g^3) := mul_le_mul_of_nonneg_right (by linarith only [hgR]) (by positivity)
        _ = _ := by ring

end BeaumontLowScales


end

/- Source: BeaumontBilinearWindow.lean -/
section


/-!
Finite geometric and bilinear estimates adapted from the accepted
Conjectures.Goldbach.TypeIiSpacingBound module, main revision 272d7a3.
The short moving-window correlation estimates below are new.
-/

open scoped BigOperators ComplexConjugate

namespace GoldbachBeaumontBilinear

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def cap (H : ℕ) (x : ℝ) : ℝ :=
  if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [Complex.norm_exp]
  simp

lemma E_pow (x : ℝ) (m : ℕ) : E x ^ m = E ((m : ℝ) * x) := by
  induction m with
  | zero => simp [E]
  | succ m ih =>
    rw [pow_succ, ih, ← E_add]
    congr 1
    push_cast
    ring

lemma E_sub_conj (x y : ℝ) : E (x - y) = E x * conj (E y) := by
  simp only [E, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma E_mul_star (x y : ℝ) : E x * (starRingEnd ℂ) (E y) = E (x - y) :=
  (E_sub_conj x y).symm

lemma cap_nonneg (H : ℕ) (x : ℝ) : 0 ≤ cap H x := by
  unfold cap
  split_ifs
  · positivity
  · exact le_min (Nat.cast_nonneg _) (div_nonneg (by norm_num) (norm_nonneg _))

lemma sum_Ico_pow_eq_shift (M L : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.Ico M (M + L), z ^ j = z ^ M * ∑ j ∈ Finset.range L, z ^ j := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => j - M) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    rw [Finset.mem_Ico] at hj₁ hj₂
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    refine ⟨M + r, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, by omega⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [← pow_add, Nat.add_sub_of_le hj.1]

lemma norm_sum_range_pow_le (L : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ j ∈ Finset.range L, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

lemma sum_Ico_E_le_cap (M L H : ℕ) (x : ℝ) (hLH : L ≤ H) :
    ‖∑ m ∈ Finset.Ico M (M + L), E ((m : ℝ) * x)‖ ≤ cap H x := by
  have hrw : ∑ m ∈ Finset.Ico M (M + L), E ((m : ℝ) * x)
      = ∑ m ∈ Finset.Ico M (M + L), (E x) ^ m := by
    apply Finset.sum_congr rfl
    intro m _
    rw [E_pow]
  have htriv : ‖∑ m ∈ Finset.Ico M (M + L), (E x) ^ m‖ ≤ (L : ℝ) := by
    rw [sum_Ico_pow_eq_shift, norm_mul, norm_pow, norm_E, one_pow, one_mul]
    calc ‖∑ j ∈ Finset.range L, (E x) ^ j‖
        ≤ ∑ j ∈ Finset.range L, ‖(E x) ^ j‖ := norm_sum_le _ _
      _ = (L : ℝ) := by simp [norm_pow, norm_E]
  rw [hrw]
  by_cases hx : E x = 1
  · rw [cap, ite_eq_left hx]
    exact htriv.trans (by exact_mod_cast hLH)
  · rw [cap, ite_eq_right hx]
    refine le_min (htriv.trans (by exact_mod_cast hLH)) ?_
    rw [sum_Ico_pow_eq_shift, norm_mul, norm_pow, norm_E, one_pow, one_mul]
    have h := norm_sum_range_pow_le L (norm_E x) hx
    rwa [norm_sub_rev] at h

lemma sum_ite_cutoff (M H c : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.Ico M (M + H), (if m ≤ c then f m else 0)
      = ∑ m ∈ Finset.Ico M (min (M + H) (c + 1)), f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, lt_min h2 (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩, ?_⟩
    have h4 := lt_of_lt_of_le h2 (min_le_right _ _)
    omega

lemma sum_ite_mul_le (N M H q c : ℕ) (f : ℕ → ℂ)
    (hc : ∀ m, M ≤ m → m < M + H → (m * q ≤ N ↔ m ≤ c)) :
    ∑ m ∈ Finset.Ico M (M + H), (if m * q ≤ N then f m else 0)
      = ∑ m ∈ Finset.Ico M (min (M + H) (c + 1)), f m := by
  have hcong : ∀ m ∈ Finset.Ico M (M + H),
      (if m * q ≤ N then f m else 0) = (if m ≤ c then f m else 0) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    by_cases h : m * q ≤ N
    · rw [ite_eq_left h, ite_eq_left ((hc m hm.1 hm.2).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h2 => h ((hc m hm.1 hm.2).mpr h2))]
  rw [Finset.sum_congr rfl hcong, sum_ite_cutoff]

lemma mul_max_iff (N k l m : ℕ) : (m * k ≤ N ∧ m * l ≤ N) ↔ (m * max k l ≤ N) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total k l with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  · intro h
    exact ⟨le_trans (Nat.mul_le_mul_left m (le_max_left k l)) h,
      le_trans (Nat.mul_le_mul_left m (le_max_right k l)) h⟩

lemma pair_bound (N M H : ℕ) (t : ℝ) (k l : ℕ) :
    ‖∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)‖
      ≤ cap H (((k : ℝ) - (l : ℝ)) * t) := by
  have hmlt : ∀ m : ℕ, (m : ℝ) * (k : ℝ) * t - (m : ℝ) * (l : ℝ) * t
      = (m : ℝ) * (((k : ℝ) - (l : ℝ)) * t) := by
    intro m
    ring
  have hterm : ∀ m : ℕ,
      (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)
      = (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) := by
    intro m
    by_cases hk : m * k ≤ N
    · by_cases hl : m * l ≤ N
      · rw [ite_eq_left hk, ite_eq_left hl, ite_eq_left ⟨hk, hl⟩, E_mul_star, hmlt m]
      · rw [ite_eq_left hk, ite_eq_right hl, ite_eq_right (fun h : m * k ≤ N ∧ m * l ≤ N => hl h.2)]
        simp
    · rw [ite_eq_right hk, ite_eq_right (fun h : m * k ≤ N ∧ m * l ≤ N => hk h.1)]
      simp
  have hsum : ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) *
          (starRingEnd ℂ) (if m * l ≤ N then E ((m : ℝ) * (l : ℝ) * t) else 0)
      = ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) :=
    Finset.sum_congr rfl (fun m _ => hterm m)
  have hmaxsum : ∑ m ∈ Finset.Ico M (M + H),
        (if m * k ≤ N ∧ m * l ≤ N then
          E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0)
      = ∑ m ∈ Finset.Ico M (M + H),
        (if m * max k l ≤ N then E ((m : ℝ) * (((k : ℝ) - (l : ℝ)) * t)) else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : m * max k l ≤ N
    · rw [ite_eq_left h, ite_eq_left ((mul_max_iff N k l m).mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h ((mul_max_iff N k l m).mp hc))]
  have hcond : ∀ m : ℕ, M ≤ m → m < M + H →
      (m * max k l ≤ N ↔ m ≤ if max k l = 0 then M + H else N / max k l) := by
    intro m hm1 hm2
    by_cases hq : max k l = 0
    · rw [ite_eq_left hq]
      constructor
      · intro _
        omega
      · intro _
        rw [hq, Nat.mul_zero]
        omega
    · rw [ite_eq_right hq]
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).symm
  rw [hsum, hmaxsum,
    sum_ite_mul_le N M H (max k l) (if max k l = 0 then M + H else N / max k l) _ hcond]
  by_cases hB : M ≤ min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)
  · have hLB : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)
        = M + (min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) - M) :=
      (Nat.add_sub_of_le hB).symm
    have hLH : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) - M ≤ H := by
      have h1 : min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1) ≤ M + H :=
        min_le_left _ _
      omega
    rw [hLB]
    exact sum_Ico_E_le_cap M _ H _ hLH
  · have hempty : Finset.Ico M
        (min (M + H) ((if max k l = 0 then M + H else N / max k l) + 1)) = ∅ := by
      rw [Finset.Ico_eq_empty]
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    exact cap_nonneg H _

lemma energy_identity {α β : Type*} (s : Finset α) (u : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ u, ∑ k ∈ u, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ u, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ u, ∑ k ∈ u,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

lemma energy_le_correlations {α β : Type*} (s : Finset α) (u : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ u, ∑ k ∈ u, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s u b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

lemma norm_bilinear_sq_le {α β : Type*} (s : Finset α) (u : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) :
    ‖∑ m ∈ s, a m * ∑ n ∈ u, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        (∑ n ∈ u, ∑ k ∈ u, ‖b n‖ * ‖b k‖ *
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  calc
    _ ≤ (∑ m ∈ s, ‖a m‖ * ‖∑ n ∈ u, b n * z m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le s (fun m => a m * ∑ n ∈ u, b n * z m n)
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ m ∈ s, ‖∑ n ∈ u, b n * z m n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_le_correlations s u b z)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem main_aux (N M H : ℕ) (K : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)‖ ^ 2
      ≤ (∑ m ∈ Finset.Ico M (M + H), ‖a m‖ ^ 2) *
        (∑ k ∈ K, ∑ l ∈ K, ‖b k‖ * ‖b l‖ * cap H (((k : ℝ) - (l : ℝ)) * t)) := by
  have hb : ∀ m k : ℕ, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)
      = b k * (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) := by
    intro m k
    by_cases h : m * k ≤ N
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  have hL : ∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, (if m * k ≤ N then b k * E ((m : ℝ) * (k : ℝ) * t) else 0)
      = ∑ m ∈ Finset.Ico M (M + H), a m *
        ∑ k ∈ K, b k * (if m * k ≤ N then E ((m : ℝ) * (k : ℝ) * t) else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_congr rfl (fun k _ => hb m k)]
  rw [hL]
  have h := norm_bilinear_sq_le (Finset.Ico M (M + H)) K a b
    (fun m n => if m * n ≤ N then E ((m : ℝ) * (n : ℝ) * t) else 0)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun m _ => sq_nonneg _))
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left (pair_bound N M H t k l)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end GoldbachBeaumontBilinear

namespace GoldbachBeaumontBilinear
noncomputable section
open Finset

lemma cap_mono {H K : ℕ} (hHK : H ≤ K) (x : ℝ) : cap H x ≤ cap K x := by
  unfold cap
  split_ifs
  · exact_mod_cast hHK
  · exact min_le_min_right _ (by exact_mod_cast hHK)

/-- A further hyperbolic cutoff still leaves one integer interval. -/
lemma two_cutoffs_cap (M H c d j : ℕ) (x : ℝ) :
    ‖∑ m ∈ Ico M (M+H),
      (if m ≤ c ∧ m*d ≤ j then E ((m:ℝ)*x) else 0)‖ ≤ cap H x := by
  have hsame :
      (∑ m ∈ Ico M (M+H), (if m ≤ c ∧ m*d ≤ j then E ((m:ℝ)*x) else 0)) =
      ∑ m ∈ Ico M (M+H),
        (if m ≤ min c (if d=0 then M+H else j/d) then E ((m:ℝ)*x) else 0) := by
    apply sum_congr rfl
    intro m hm
    have hmH : m ≤ M+H := (mem_Ico.mp hm).2.le
    have he : (m ≤ c ∧ m*d ≤ j) ↔ m ≤ min c (if d=0 then M+H else j/d) := by
      by_cases hd : d=0
      · simp [hd, hmH]
      · simp only [hd, ↓reduceIte, le_min_iff]
        rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd)]
    simp only [he]
  rw [hsame, sum_ite_cutoff]
  let U := min (M+H) (min c (if d=0 then M+H else j/d)+1)
  by_cases hMU : M ≤ U
  · have he : U = M+(U-M) := (Nat.add_sub_of_le hMU).symm
    change ‖∑ m ∈ Ico M U, E ((m:ℝ)*x)‖ ≤ cap H x
    rw [he]
    exact sum_Ico_E_le_cap _ _ _ _ (by dsimp [U]; omega)
  · have he : Ico M U = ∅ := by rw [Ico_eq_empty]; omega
    change ‖∑ m ∈ Ico M U, E ((m:ℝ)*x)‖ ≤ cap H x
    rw [he, sum_empty, norm_zero]
    exact cap_nonneg _ _

lemma triangle_layer_count (h v : ℕ) :
    ((range h).filter (fun j => v ≤ j)).card = h-v := by
  have he : (range h).filter (fun j => v ≤ j) = Ico v h := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [he, Nat.card_Ico]

lemma triangle_layers (h v : ℕ) (z : ℂ) :
    ((h-v : ℕ):ℂ)*z = ∑ j ∈ range h, (if v ≤ j then z else 0) := by
  rw [← sum_filter, sum_const, triangle_layer_count, nsmul_eq_mul]

/-- The triangular overlap weight is a sum of interval cutoffs. -/
theorem triangular_geometric_bound (M H c h d : ℕ) (x : ℝ) :
    ‖∑ m ∈ Ico M (M+H),
      (if m ≤ c then ((h-m*d : ℕ):ℂ)*E ((m:ℝ)*x) else 0)‖ ≤
      (h:ℝ)*cap H x := by
  have he (m : ℕ) :
      (if m ≤ c then ((h-m*d : ℕ):ℂ)*E ((m:ℝ)*x) else 0) =
      ∑ j ∈ range h, (if m ≤ c ∧ m*d ≤ j then E ((m:ℝ)*x) else 0) := by
    by_cases hm : m ≤ c
    · simp only [hm, ↓reduceIte, true_and]
      exact triangle_layers h (m*d) _
    · simp [hm]
  simp_rw [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ j ∈ range h,
        ‖∑ m ∈ Ico M (M+H),
          (if m ≤ c ∧ m*d ≤ j then E ((m:ℝ)*x) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range h, cap H x :=
      sum_le_sum (fun j _ => two_cutoffs_cap M H c d j x)
    _ = _ := by simp

lemma overlap_count (N h a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    ((range (N+h)).filter (fun u => a ≤ u ∧ u < a+h ∧ b ≤ u ∧ u < b+h)).card
      = h-Nat.dist a b := by
  have he : (range (N+h)).filter
      (fun u => a ≤ u ∧ u < a+h ∧ b ≤ u ∧ u < b+h) =
      Ico (max a b) (min (a+h) (b+h)) := by
    ext u
    simp only [mem_filter, mem_range, mem_Ico, max_le_iff, lt_min_iff]
    omega
  rw [he, Nat.card_Ico]
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left (by omega), Nat.dist_eq_sub_of_le hab]
    omega
  · rw [max_eq_left hba, min_eq_right (by omega), Nat.dist_eq_sub_of_le_right hba]
    omega

/-- Column indexed by a product, restricted to an actual moving box. -/
def windowColumn (N h : ℕ) (α : ℝ) (u m k : ℕ) : ℂ :=
  if m*k ≤ N ∧ m*k ≤ u ∧ u < m*k+h then E (α*(m:ℝ)*(k:ℝ)) else 0

theorem window_column_correlation (N h m k l : ℕ) (α : ℝ) :
    (∑ u ∈ range (N+h),
      windowColumn N h α u m k * conj (windowColumn N h α u m l)) =
      if m*k ≤ N ∧ m*l ≤ N then
        ((h-m*Nat.dist k l : ℕ):ℂ)*E ((m:ℝ)*(α*((k:ℝ)-(l:ℝ))))
      else 0 := by
  by_cases hk : m*k ≤ N
  · by_cases hl : m*l ≤ N
    · rw [ite_eq_left ⟨hk,hl⟩]
      have hp (u : ℕ) :
          windowColumn N h α u m k * conj (windowColumn N h α u m l) =
          if m*k ≤ u ∧ u < m*k+h ∧ m*l ≤ u ∧ u < m*l+h then
            E ((m:ℝ)*(α*((k:ℝ)-(l:ℝ)))) else 0 := by
        dsimp [windowColumn]
        by_cases hkU : m*k ≤ u ∧ u < m*k+h
        · by_cases hlU : m*l ≤ u ∧ u < m*l+h
          · simp only [hk,hl,hkU.1,hkU.2,hlU.1,hlU.2, true_and, ↓reduceIte]
            rw [← E_sub_conj]
            congr 1
            ring
          · have hnot : ¬(m*k ≤ u ∧ u < m*k+h ∧ m*l ≤ u ∧ u < m*l+h) := by
              intro h
              exact hlU ⟨h.2.2.1,h.2.2.2⟩
            simp only [hk,hl,hkU.1,hkU.2,true_and,hlU,↓reduceIte,hnot]
            simp
        · have hnot : ¬(m*k ≤ u ∧ u < m*k+h ∧ m*l ≤ u ∧ u < m*l+h) := by
            intro h
            exact hkU ⟨h.1,h.2.1⟩
          simp [hk,hl,hkU,hnot]
      simp_rw [hp]
      rw [←sum_filter, sum_const, overlap_count N h (m*k) (m*l) hk hl,
        Nat.dist_mul_left, nsmul_eq_mul]
    · rw [ite_eq_right (by tauto)]
      apply sum_eq_zero
      intro u hu
      simp [windowColumn, hl]
  · rw [ite_eq_right (by tauto)]
    apply sum_eq_zero
    intro u hu
    simp [windowColumn, hk]

theorem window_gram_bound (N M H h k l : ℕ) (α : ℝ) :
    ‖∑ m ∈ Ico M (M+H), ∑ u ∈ range (N+h),
      windowColumn N h α u m k * conj (windowColumn N h α u m l)‖ ≤
      (h:ℝ)*cap H (α*((k:ℝ)-(l:ℝ))) := by
  simp_rw [window_column_correlation]
  have he (m : ℕ) (hm : m ∈ Ico M (M+H)) :
      (m*k ≤ N ∧ m*l ≤ N) ↔
      m ≤ if max k l = 0 then M+H else N / max k l := by
    rw [mul_max_iff]
    by_cases hz : max k l = 0
    · simp only [hz, ↓reduceIte, mul_zero, zero_le]
      exact iff_of_true trivial (mem_Ico.mp hm).2.le
    · simp only [hz, ↓reduceIte]
      exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hz)).symm
  have hs : (∑ m ∈ Ico M (M+H),
      if m*k ≤ N ∧ m*l ≤ N then
        ((h-m*Nat.dist k l : ℕ):ℂ)*E ((m:ℝ)*(α*((k:ℝ)-(l:ℝ)))) else 0) =
      ∑ m ∈ Ico M (M+H),
        if m ≤ (if max k l = 0 then M+H else N / max k l) then
          ((h-m*Nat.dist k l : ℕ):ℂ)*E ((m:ℝ)*(α*((k:ℝ)-(l:ℝ)))) else 0 :=
    sum_congr rfl (fun m hm => if_congr (he m hm) rfl rfl)
  rw [hs]
  exact triangular_geometric_bound M H _ h (Nat.dist k l) _

theorem window_gram_zero_of_far (N M H h k l : ℕ) (α : ℝ)
    (hfar : h ≤ M*Nat.dist k l) :
    (∑ m ∈ Ico M (M+H), ∑ u ∈ range (N+h),
      windowColumn N h α u m k * conj (windowColumn N h α u m l)) = 0 := by
  simp_rw [window_column_correlation]
  apply sum_eq_zero
  intro m hm
  have hhm : h ≤ m*Nat.dist k l :=
    hfar.trans (Nat.mul_le_mul_right _ (mem_Ico.mp hm).1)
  simp [Nat.sub_eq_zero_of_le hhm]

end
end GoldbachBeaumontBilinear

namespace GoldbachBeaumontBilinear

/-- Scalar saving from a short-side factor and a denominator both lying
between W and h/W. This is the numerical form of the local Type II bound. -/
theorem rational_scale_saving (d ℓ m q h W L : ℝ)
    (hd : 0 ≤ d) (hℓ : 0 ≤ ℓ) (hW : 0 < W) (hW1 : 1 ≤ W)
    (hL : 1 ≤ L) (hWm : W ≤ m) (hWq : W ≤ q)
    (hdm : d*m ≤ h) (hℓm : ℓ ≤ 64*m)
    (hmh : m*W ≤ h) (hqh : q*W ≤ h) :
    (2*(2*d+1)/q+1)*(2*ℓ+4*q*L) ≤ 1024*h*L/W := by
  have hm : 0 < m := hW.trans_le hWm
  have hq : 0 < q := hW.trans_le hWq
  have hh : 0 ≤ h := (mul_nonneg hm.le hW.le).trans hmh
  have hq1 : 1 ≤ q := hW1.trans hWq
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hdW : d*W ≤ h := (mul_le_mul_of_nonneg_left hWm hd).trans hdm
  have hpoly : (4*d+2+q)*(2*ℓ+4*q*L)*W ≤ 1024*h*L*q := by
    calc
      _ ≤ (4*d+3*q)*(128*m+4*q*L)*W := by
        apply mul_le_mul_of_nonneg_right _ hW.le
        exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 512*(d*m)*W + 16*(d*W)*q*L + 384*(m*W)*q + 12*(q*W)*q*L := by ring
      _ ≤ 512*h*q*L + 16*h*q*L + 384*h*q*L + 12*h*q*L := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · calc
                _ ≤ 512*h*q := by gcongr
                _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
            · gcongr
          · calc
              _ ≤ 384*h*q := by gcongr
              _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
        · gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hh hL0) hq.le]
  apply (le_div_iff₀ hW).mpr
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    _ = (4*d+2+q)*(2*ℓ+4*q*L)*W := by field_simp; ring
    _ ≤ _ := by nlinarith only [hpoly]

theorem local_energy_log_budget (d ℓ m q h L N U V E : ℝ)
    (hd : 0 ≤ d) (hℓ : 0 ≤ ℓ) (hh : 0 < h) (hL : 16 ≤ L)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hWm : L^100 ≤ m) (hWq : L^100 ≤ q)
    (hdm : d*m ≤ h) (hℓm : ℓ ≤ 64*m)
    (hmh : m*L^100 ≤ h) (hqh : q*L^100 ≤ h)
    (hUV : U*V ≤ N*L^50)
    (hE : h^2/4*E ≤ U*(h*(2*(2*d+1)/q+1)*(2*ℓ+4*q*L))*V) :
    E ≤ N/L^40 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hsave := rational_scale_saving d ℓ m q h (L^100) L hd hℓ
    (by positivity) (one_le_pow₀ hL1) hL1 hWm hWq hdm hℓm hmh hqh
  have hcoef : 4096*L^51 ≤ L^60 := by
    have hc : (4096:ℝ) ≤ L^9 := by
      exact (show (4096:ℝ) = 16^3 by norm_num).le.trans
        ((pow_le_pow_left₀ (by norm_num) hL 3).trans
          (pow_le_pow_right₀ hL1 (by norm_num)))
    calc
      _ ≤ L^9*L^51 := by gcongr
      _ = _ := by ring
  have hnum : N*L^50*h*(1024*h*L/L^100) ≤ (h^2/4)*(N/L^40) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4*L^100 by positivity)).mp
    have hpow : L^100 = L^40*L^60 := by ring
    calc
      _ = N*h^2*(4096*L^51) := by field_simp; ring
      _ ≤ N*h^2*L^60 := mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = _ := by rw [hpow]; field_simp
  have hb : h^2/4*E ≤ (h^2/4)*(N/L^40) := by
    calc
      _ ≤ U*(h*(2*(2*d+1)/q+1)*(2*ℓ+4*q*L))*V := hE
      _ = (U*V)*h*((2*(2*d+1)/q+1)*(2*ℓ+4*q*L)) := by ring
      _ ≤ (U*V)*h*(1024*h*L/L^100) :=
        mul_le_mul_of_nonneg_left hsave (by positivity)
      _ ≤ N*L^50*h*(1024*h*L/L^100) := by gcongr
      _ ≤ _ := hnum
  exact (mul_le_mul_iff_right₀ (show 0 < h^2/4 by positivity)).mp hb

end GoldbachBeaumontBilinear

namespace GoldbachBeaumontBilinear
noncomputable section
open Finset

theorem symmetric_weighted_sum_le {β : Type*} (t : Finset β)
    (f : β → ℝ) (K : β → β → ℝ)
    (hK : ∀ n ∈ t, ∀ k ∈ t, 0 ≤ K n k)
    (hsym : ∀ n ∈ t, ∀ k ∈ t, K n k = K k n) :
    (∑ n ∈ t, ∑ k ∈ t, f n * f k * K n k) ≤
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
  have hfirst : (∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    simp only [Finset.mul_sum]
  have hsecond : (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k hk n hn]
  calc
    _ ≤ ∑ n ∈ t, ∑ k ∈ t,
        (f n ^ 2 * K n k + f k ^ 2 * K n k) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [mul_nonneg (sq_nonneg (f n - f k)) (hK n hn k hk)]
    _ = ((∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) +
        (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k)) / 2 := by
      simp only [add_div, Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by rw [hfirst, hsecond]; ring

/-- Reversing a correlation conjugates it, hence preserves its norm. -/
theorem correlation_norm_symm {α β : Type*} (s : Finset α)
    (z : α → β → ℂ) (n k : β) :
    ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ =
      ‖∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)‖ := by
  have hc : (∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)) =
      (starRingEnd ℂ) (∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)) := by
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hc, Complex.norm_conj]

/-- Cauchy in the shorter multiplicative variable, before summing the
physical window locations. The correlation retains both indices. -/
theorem windows_energy_of_row {ι κ υ : Type*}
    (I : Finset ι) (K : Finset κ) (R : Finset υ)
    (a : ι → ℂ) (b : κ → ℂ) (z : υ → ι → κ → ℂ) (C : ℝ)
    (hrow : ∀ k ∈ K, (∑ l ∈ K,
      ‖∑ m ∈ I, ∑ u ∈ R, z u m k * conj (z u m l)‖) ≤ C) :
    (∑ u ∈ R, ‖∑ m ∈ I, a m * ∑ k ∈ K, b k*z u m k‖^2) ≤
      (∑ m ∈ I, ‖a m‖^2)*C*(∑ k ∈ K, ‖b k‖^2) := by
  classical
  let J := I ×ˢ R
  let Z (v : ι × υ) (k : κ) := z v.2 v.1 k
  let F (k l : κ) := ‖∑ v ∈ J, Z v k * conj (Z v l)‖
  have hrow' (k : κ) (hk : k ∈ K) : (∑ l ∈ K, F k l) ≤ C := by
    simpa only [F, J, Z, sum_product] using hrow k hk
  have hSchur := symmetric_weighted_sum_le K (fun k => ‖b k‖) F
    (fun _ _ _ _ => norm_nonneg _)
    (fun k _ l _ => correlation_norm_symm J Z k l)
  have hE : (∑ v ∈ J, ‖∑ k ∈ K, b k*Z v k‖^2) ≤
      C*(∑ k ∈ K, ‖b k‖^2) := by
    apply (energy_le_correlations J K b Z).trans
    apply hSchur.trans
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hrow' k hk) (sq_nonneg ‖b k‖)
  have hA : 0 ≤ ∑ m ∈ I, ‖a m‖^2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ ∑ u ∈ R, (∑ m ∈ I, ‖a m‖^2)*
        (∑ m ∈ I, ‖∑ k ∈ K, b k*z u m k‖^2) := by
      apply sum_le_sum
      intro u hu
      calc
        _ ≤ (∑ m ∈ I, ‖a m‖*‖∑ k ∈ K, b k*z u m k‖)^2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          simpa only [norm_mul] using
            norm_sum_le I (fun m => a m*∑ k ∈ K, b k*z u m k)
        _ ≤ _ := sum_mul_sq_le_sq_mul_sq I _ _
    _ = (∑ m ∈ I, ‖a m‖^2)*(∑ v ∈ J, ‖∑ k ∈ K, b k*Z v k‖^2) := by
      rw [←mul_sum]
      congr 1
      dsimp only [J, Z]
      rw [sum_product, sum_comm]
    _ ≤ (∑ m ∈ I, ‖a m‖^2)*(C*(∑ k ∈ K, ‖b k‖^2)) :=
      mul_le_mul_of_nonneg_left hE hA
    _ = _ := by ring

def bilinearCoefficient (I K : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ I, ∑ k ∈ K, if m*k=n then a m*b k else 0

def movingCoefficient (N h : ℕ) (c : ℕ → ℂ) (u : ℕ) : ℂ :=
  ∑ n ∈ (range (N+1)).filter (fun n => u+1-h ≤ n ∧ n ≤ u), c n

lemma bilinearCoefficient_sum (I K F : Finset ℕ) (a b w : ℕ → ℂ) :
    (∑ n ∈ F, bilinearCoefficient I K a b n * w n) =
      ∑ m ∈ I, ∑ k ∈ K, if m*k ∈ F then a m*b k*w (m*k) else 0 := by
  classical
  calc
    _ = ∑ n ∈ F, ∑ m ∈ I, ∑ k ∈ K,
        if m*k=n then a m*b k*w n else 0 := by
      simp only [bilinearCoefficient, sum_mul, ite_mul, zero_mul]
    _ = ∑ m ∈ I, ∑ k ∈ K, ∑ n ∈ F,
        if m*k=n then a m*b k*w n else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro k hk
      simp only [sum_ite_eq]

theorem moving_bilinearCoefficient (N h u : ℕ) (I K : Finset ℕ)
    (a b : ℕ → ℂ) (α : ℝ) :
    movingCoefficient N h
      (fun n => bilinearCoefficient I K a b n * E (α*(n:ℝ))) u =
      ∑ m ∈ I, a m*∑ k ∈ K, b k*windowColumn N h α u m k := by
  unfold movingCoefficient
  rw [bilinearCoefficient_sum]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have he : (m*k ∈ (range (N+1)).filter (fun n => u+1-h ≤ n ∧ n ≤ u)) ↔
      m*k ≤ N ∧ m*k ≤ u ∧ u < m*k+h := by
    simp only [mem_filter, mem_range]
    omega
  rw [windowColumn]
  simp only [he]
  split_ifs
  · simp only [Nat.cast_mul, mul_assoc]
  · simp

/-- The exact finite moving mean of a hyperbolic bilinear polynomial. -/
theorem moving_bilinear_energy_of_row (N M H h : ℕ) (K : Finset ℕ)
    (a b : ℕ → ℂ) (α C : ℝ)
    (hrow : ∀ k ∈ K, (∑ l ∈ K,
      ‖∑ m ∈ Ico M (M+H), ∑ u ∈ range (N+h),
        windowColumn N h α u m k * conj (windowColumn N h α u m l)‖) ≤ C) :
    (∑ u ∈ range (N+h),
      ‖movingCoefficient N h
        (fun n => bilinearCoefficient (Ico M (M+H)) K a b n * E (α*(n:ℝ))) u‖^2) ≤
      (∑ m ∈ Ico M (M+H), ‖a m‖^2)*C*(∑ k ∈ K, ‖b k‖^2) := by
  simp_rw [moving_bilinearCoefficient]
  exact windows_energy_of_row (Ico M (M+H)) K (range (N+h)) a b
    (windowColumn N h α) C hrow


end
end GoldbachBeaumontBilinear

end

/- Source: BeaumontBilinearRationalBase.lean -/
section

/-! Local Fourier energy of an actual bilinear convolution. The two inputs
are the proved finite moving-window Gram calculation and the accepted
rational reciprocal-distance estimate. -/

open Finset MeasureTheory
open scoped BigOperators Interval ComplexConjugate
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open OAI.Problem337

namespace GoldbachBeaumontBilinear
noncomputable section

lemma E_eq_vaughan (x : ℝ) : E x = VaughanBilinear.phase x := rfl

lemma cap_eq_geometricBound (M : ℕ) (x : ℝ) :
    cap M x = VaughanBilinear.geometricBound M x := rfl

def rationalWindowScale (h M H q : ℕ) : ℝ :=
  (h:ℝ)*(2*((2*(h/M)+1:ℕ):ℝ)/q+1)*
    (2*(H:ℝ)+4*(q:ℝ)*(1+Real.log (2*(q:ℝ))))

theorem window_gram_rational_row (N M H h : ℕ) (hM : 0 < M)
    (K : Finset ℕ) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q:ℤ))
    (happrox : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2) (k : ℕ) :
    (∑ l ∈ K, ‖∑ m ∈ Ico M (M+H), ∑ u ∈ range (N+h),
      windowColumn N h α u m k * conj (windowColumn N h α u m l)‖) ≤
      rationalWindowScale h M H q := by
  classical
  let S := K.filter (fun l => Nat.dist k l ≤ h/M)
  let F (l : ℕ) := ‖∑ m ∈ Ico M (M+H), ∑ u ∈ range (N+h),
    windowColumn N h α u m k * conj (windowColumn N h α u m l)‖
  have hsum : (∑ l ∈ S, F l) = ∑ l ∈ K, F l := by
    apply sum_subset (filter_subset _ _)
    intro l hl hls
    have hd : h/M < Nat.dist k l := by
      by_contra! h
      exact hls (mem_filter.mpr ⟨hl,h⟩)
    have hd' : h/M+1 ≤ Nat.dist k l := hd
    have hfar : h ≤ M*Nat.dist k l :=
      (Nat.lt_mul_div_succ h hM).le.trans (Nat.mul_le_mul_left M hd')
    dsimp only [F]
    rw [window_gram_zero_of_far N M H h k l α hfar, norm_zero]
  have hspan (l : ℕ) (hl : l ∈ S) :
      (l:ℤ) ∈ Ico ((k:ℤ)-(h/M:ℕ))
        (((k:ℤ)-(h/M:ℕ))+((2*(h/M)+1:ℕ):ℤ)) := by
    have hd := (mem_filter.mp hl).2
    have hlo := Nat.dist_tri_left k l
    have hhi := Nat.dist_tri_left' k l
    apply mem_Ico.mpr
    constructor <;> omega
  have hcap := VaughanBilinear.sum_geometricBound_difference_le
    α a q hq hcop happrox H S (fun l : ℕ => (l:ℤ))
    ((k:ℤ)-(h/M:ℕ)) (2*(h/M)+1) hspan
    (by intro l hl j hj he; dsimp only at he; exact_mod_cast he) (k:ℤ)
  simp only [Int.cast_sub, Int.cast_natCast, ←cap_eq_geometricBound] at hcap
  change (∑ l ∈ K, F l) ≤ _
  rw [←hsum]
  calc
    _ ≤ ∑ l ∈ S, (h:ℝ)*cap H (α*((k:ℝ)-(l:ℝ))) :=
      sum_le_sum (fun l _ => window_gram_bound N M H h k l α)
    _ = (h:ℝ)*(∑ l ∈ S, cap H (α*((k:ℝ)-(l:ℝ)))) := (mul_sum ..).symm
    _ ≤ (h:ℝ)*((2*((2*(h/M)+1:ℕ):ℝ)/q+1)*
        (2*(H:ℝ)+4*(q:ℝ)*(1+Real.log (2*(q:ℝ))))) :=
      mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg h)
    _ = _ := by unfold rationalWindowScale; ring

theorem moving_bilinear_rational_energy (N M H h : ℕ) (hM : 0 < M)
    (K : Finset ℕ) (c b : ℕ → ℂ) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q:ℤ))
    (happrox : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2) :
    (∑ u ∈ range (N+h),
      ‖movingCoefficient N h
        (fun n => bilinearCoefficient (Ico M (M+H)) K c b n * E (α*(n:ℝ))) u‖^2) ≤
      (∑ m ∈ Ico M (M+H), ‖c m‖^2)*rationalWindowScale h M H q*
        (∑ k ∈ K, ‖b k‖^2) :=
  moving_bilinear_energy_of_row N M H h K c b α _
    (fun k _ => window_gram_rational_row N M H h hM K α a q hq hcop happrox k)

lemma moving_eq_gallagher (N h u : ℕ) (b : ℕ → ℂ) :
    GoldbachWindow.moving (N+1) h b u = movingCoefficient N h b u :=
  GoldbachWindow.moving_eq_sum _ _ _ _

lemma moving_at_last_zero (N h : ℕ) (b : ℕ → ℂ) :
    movingCoefficient N h b (N+h) = 0 := by
  unfold movingCoefficient
  have he : (range (N+1)).filter (fun n => N+h+1-h ≤ n ∧ n ≤ N+h) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn
    have hnN := mem_range.mp hn
    omega
  rw [he,sum_empty]

theorem local_bilinear_rational_energy (N M H h : ℕ) (hM : 0 < M) (hh : 0 < h)
    (K : Finset ℕ) (c b : ℕ → ℂ) (α δ : ℝ) (hδ : 0 ≤ δ)
    (hwidth : 6*(h:ℝ)*δ ≤ 1)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime a (q:ℤ))
    (happrox : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2) :
    (h:ℝ)^2/4 *
      (∫ t in (-δ)..δ, ‖GoldbachWindow.poly (N+1)
        (fun n => bilinearCoefficient (Ico M (M+H)) K c b n * E (α*(n:ℝ))) t‖^2) ≤
      (∑ m ∈ Ico M (M+H), ‖c m‖^2)*rationalWindowScale h M H q*
        (∑ k ∈ K, ‖b k‖^2) := by
  have hg := GoldbachWindow.low_frequency_le (N+1) h
    (fun n => bilinearCoefficient (Ico M (M+H)) K c b n * E (α*(n:ℝ))) δ hh hδ hwidth
  simp_rw [moving_eq_gallagher] at hg
  have he : N+1+h = (N+h)+1 := by omega
  rw [he,sum_range_succ,moving_at_last_zero,norm_zero,zero_pow (by decide),add_zero] at hg
  exact hg.trans (moving_bilinear_rational_energy N M H h hM K c b α a q hq hcop happrox)



end
end GoldbachBeaumontBilinear
end

/- Source: BeaumontHighTypeII.lean -/
section


open Finset MeasureTheory
open scoped BigOperators Interval
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace GoldbachBeaumontHigh
noncomputable section
open GoldbachBeaumontBilinear

def prefixPoly (N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ range (N+1), c n * E (t*(n:ℝ))

lemma prefixPoly_cont (N : ℕ) (c : ℕ → ℂ) : Continuous (prefixPoly N c) := by
  unfold prefixPoly E
  fun_prop

lemma prefixPoly_shift (N : ℕ) (c : ℕ → ℂ) (α t : ℝ) :
    prefixPoly N c (α+t) =
      GoldbachWindow.poly (N+1) (fun n => c n*E (α*(n:ℝ))) t := by
  unfold prefixPoly GoldbachWindow.poly
  apply sum_congr rfl
  intro n hn
  change c n*E ((α+t)*(n:ℝ)) = c n*E (α*(n:ℝ))*E ((n:ℝ)*t)
  rw [show (α+t)*(n:ℝ) = α*(n:ℝ)+(n:ℝ)*t by ring, E_add]
  ring

/-- Passing from the centered Gallagher integral to one entire mesh cell. -/
lemma prefix_cell_le_centered (N : ℕ) (c : ℕ → ℂ) (α δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ t in α..(α+δ), ‖prefixPoly N c t‖^2) ≤
      ∫ t in (-δ)..δ,
        ‖GoldbachWindow.poly (N+1) (fun n => c n*E (α*(n:ℝ))) t‖^2 := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => ‖prefixPoly N c t‖^2) (a:=0) (b:=δ) α
  simp only [add_zero] at ht
  rw [←ht]
  simp_rw [prefixPoly_shift]
  apply intervalIntegral.integral_mono_interval (by linarith) hδ le_rfl
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hc : Continuous (fun t =>
      ‖GoldbachWindow.poly (N+1) (fun n => c n*E (α*(n:ℝ))) t‖^2) := by
    unfold GoldbachWindow.poly GoldbachFourthMoment.phase
    fun_prop
  exact hc.intervalIntegrable _ _

/-- Uniform local Type II saving with the actual finite convolution coefficients.
The cutoffs in the polynomial may be smaller than the master energy budget N. -/
theorem bilinear_cell_log_saving (K : Finset ℕ) (c b : ℕ → ℂ)
    (Ncut M J h q : ℕ) (α δ g Z : ℝ)
    (hM : 0<M) (hh : 0<h) (hq : 0<q)
    (hδ : 0≤δ) (hwidth : 6*(h:ℝ)*δ≤1)
    (a : ℤ) (hcop : IsCoprime a (q:ℤ))
    (happrox : |α-(a:ℝ)/q|≤1/(q:ℝ)^2)
    (hg : 16≤g) (hZ : 0≤Z)
    (hgm : g^100≤(M:ℝ)) (hgq : g^100≤(q:ℝ))
    (hJ : (J:ℝ)≤64*(M:ℝ))
    (hmg : (M:ℝ)*g^100≤h) (hqg : (q:ℝ)*g^100≤h)
    (hlog : 1+Real.log (2*(q:ℝ))≤g)
    (hcoeff : (∑ m ∈ Ico M (M+J), ‖c m‖^2)*
      (∑ k ∈ K, ‖b k‖^2) ≤ Z*g^50) :
    (∫ t in α..(α+δ), ‖prefixPoly Ncut
      (bilinearCoefficient (Ico M (M+J)) K c b) t‖^2) ≤ Z/g^40 := by
  let U : ℝ := ∑ m ∈ Ico M (M+J), ‖c m‖^2
  let V : ℝ := ∑ k ∈ K, ‖b k‖^2
  let ec : ℝ := ∫ t in (-δ)..δ, ‖GoldbachWindow.poly (Ncut+1)
    (fun n => bilinearCoefficient (Ico M (M+J)) K c b n * E (α*(n:ℝ))) t‖^2
  have hU : 0≤U := sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0≤V := sum_nonneg (fun _ _ => sq_nonneg _)
  have he := local_bilinear_rational_energy Ncut M J h hM hh K c b α δ hδ
    hwidth a q hq hcop happrox
  have he' : (h:ℝ)^2/4*ec ≤
      U*((h:ℝ)*(2*(2*(h/M:ℕ)+1)/(q:ℝ)+1)*(2*(J:ℝ)+4*(q:ℝ)*g))*V := by
    apply he.trans
    dsimp only [rationalWindowScale,U,V]
    push_cast
    gcongr
  have hdm : ((h/M:ℕ):ℝ)*(M:ℝ)≤h := by
    exact_mod_cast Nat.div_mul_le_self h M
  have hs := local_energy_log_budget ((h/M:ℕ):ℝ) J M q h g Z U V ec
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hh) hg hZ hU hV
    hgm hgq hdm hJ hmg hqg hcoeff he'
  exact (prefix_cell_le_centered Ncut _ α δ hδ).trans hs

lemma norm_sub_sq_le (z w : ℂ) : ‖z-w‖^2≤2*‖z‖^2+2*‖w‖^2 := by
  have hn := norm_sub_le z w
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma prefix_prime_eq (n : ℕ) (t : ℝ) :
    prefixPoly n (fun k => (GoldbachMajorArc.primeWeight k:ℂ)) t =
      GoldbachMajorArc.primeSum n t := by
  unfold prefixPoly GoldbachMajorArc.primeSum
  apply sum_congr rfl
  intro k hk
  change _ * E (t*(k:ℝ)) = _ * E ((k:ℝ)*t)
  rw [mul_comm t (k:ℝ)]

/-- The elementary prime-power correction, uniform in every shorter initial segment. -/
theorem mangoldt_prime_error (N n : ℕ) (hN : 1≤N) (hnN : n≤N) (t : ℝ) :
    ‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t -
      GoldbachMajorArc.primeSum n t‖ ≤ 2*Real.sqrt N*Real.log N := by
  by_cases hn0 : n=0
  · subst n
    simp [prefixPoly,GoldbachMajorArc.primeSum,GoldbachMajorArc.primeWeight]
    positivity
  have hn : 1≤n := by omega
  have hnon (k : ℕ) : 0≤ArithmeticFunction.vonMangoldt k-GoldbachMajorArc.primeWeight k := by
    by_cases hk : k.Prime <;>
      simp [GoldbachMajorArc.primeWeight,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  have he : prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t -
      GoldbachMajorArc.primeSum n t =
      ∑ k ∈ range (n+1), ((ArithmeticFunction.vonMangoldt k-
        GoldbachMajorArc.primeWeight k:ℝ):ℂ)*E (t*(k:ℝ)) := by
    rw [←prefix_prime_eq]
    simp only [prefixPoly,←sum_sub_distrib,Complex.ofReal_sub,sub_mul]
  rw [he]
  calc
    _ ≤ ∑ k ∈ range (n+1),
        ‖((ArithmeticFunction.vonMangoldt k-GoldbachMajorArc.primeWeight k:ℝ):ℂ)*E (t*(k:ℝ))‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ range (n+1),
        (ArithmeticFunction.vonMangoldt k-GoldbachMajorArc.primeWeight k) := by
      simp only [norm_mul,E,Complex.norm_exp_ofReal_mul_I,mul_one,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n-Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero,←Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,GoldbachMajorArc.primeWeight,
        sum_filter,sum_sub_distrib]
    _ ≤ 2*Real.sqrt n*Real.log n := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)
    _ ≤ 2*Real.sqrt N*Real.log N := by
      have hl := Real.log_le_log (show (0:ℝ)<n by exact_mod_cast (by omega : 0<n))
        (show (n:ℝ)≤N by exact_mod_cast hnN)
      have hs := Real.sqrt_le_sqrt (show (n:ℝ)≤N by exact_mod_cast hnN)
      gcongr

/-- Turning the actual Mangoldt initial segment estimate into a prime initial segment estimate. -/
theorem prime_cell_of_mangoldt (N n H : ℕ) (α g : ℝ)
    (hN : 1≤N) (hnN : n≤N) (hH : 0<H) (hg : 16≤g)
    (hlog : Real.log N≤g) (hlarge : 4*g^12≤H)
    (henergy : (∫ t in α..(α+1/(H:ℝ)),
      ‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2)≤(N:ℝ)/g^10) :
    (∫ t in α..(α+1/(H:ℝ)), ‖GoldbachMajorArc.primeSum n t‖^2)≤4*(N:ℝ)/g^10 := by
  have hgr : 0<g := by linarith
  have hHr : 0<(H:ℝ) := by exact_mod_cast hH
  have hNr : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hln : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcorr : (1/(H:ℝ))*(4*(N:ℝ)*(Real.log N)^2) ≤ (N:ℝ)/g^10 := by
    have hlog2 := pow_le_pow_left₀ hln hlog 2
    apply (le_div_iff₀ (show 0<g^10 by positivity)).mpr
    rw [show (1/(H:ℝ))*(4*(N:ℝ)*(Real.log N)^2)*g^10 =
      (4*(N:ℝ)*(Real.log N)^2*g^10)/(H:ℝ) by ring]
    apply (div_le_iff₀ hHr).mpr
    have hm := mul_le_mul_of_nonneg_left hlarge hNr
    calc
      _ = 4*(N:ℝ)*(Real.log N)^2*g^10 := by ring
      _ ≤ 4*(N:ℝ)*g^2*g^10 := by gcongr
      _ = (N:ℝ)*(4*g^12) := by ring
      _ ≤ _ := hm
  have hcont : Continuous (fun t => ‖prefixPoly n
      (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2) := (prefixPoly_cont ..).norm.pow 2
  have hpc : Continuous (fun t => ‖GoldbachMajorArc.primeSum n t‖^2) := by
    unfold GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hpoint (t : ℝ) : ‖GoldbachMajorArc.primeSum n t‖^2≤
      2*‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2+
        2*(4*(N:ℝ)*(Real.log N)^2) := by
    let z := prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t
    have he := mangoldt_prime_error N n hN hnN t
    have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    have hs := Real.sq_sqrt hNr
    have hp := norm_sub_sq_le z (z-GoldbachMajorArc.primeSum n t)
    simp only [sub_sub_cancel] at hp
    dsimp only [z] at hp
    nlinarith
  calc
    _ ≤ ∫ t in α..(α+1/(H:ℝ)),
        2*‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2+
          2*(4*(N:ℝ)*(Real.log N)^2) := by
      apply intervalIntegral.integral_mono_on (by linarith [one_div_pos.mpr hHr]) (hpc.intervalIntegrable _ _)
        ((continuous_const.mul hcont |>.add continuous_const).intervalIntegrable _ _)
      exact fun t _ => hpoint t
    _ = 2*(∫ t in α..(α+1/(H:ℝ)),
        ‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2)+
          2*((1/(H:ℝ))*(4*(N:ℝ)*(Real.log N)^2)) := by
      have hc2 : IntervalIntegrable (fun t => 2*‖prefixPoly n
          (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2) volume α (α+1/(H:ℝ)) :=
        (hcont.const_mul 2).intervalIntegrable _ _
      have hcc : IntervalIntegrable (fun _ : ℝ => 2*(4*(N:ℝ)*(Real.log N)^2)) volume
          α (α+1/(H:ℝ)) := intervalIntegrable_const
      rw [intervalIntegral.integral_add hc2 hcc,intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring
    _ ≤ 2*((N:ℝ)/g^10)+2*((N:ℝ)/g^10) := by gcongr
    _ = _ := by ring


/-- The actual central prime band inherits the high-denominator cell saving. -/
theorem band_cell_of_mangoldt (N L D H : ℕ) (α g : ℝ)
    (hN : 1≤N) (hupper : L+D+1≤N) (hH : 0<H) (hg : 16≤g)
    (hlog : Real.log N≤g) (hlarge : 4*g^12≤H)
    (henergy : ∀ n≤N, (∫ t in α..(α+1/(H:ℝ)),
      ‖prefixPoly n (fun k => (ArithmeticFunction.vonMangoldt k:ℂ)) t‖^2)≤(N:ℝ)/g^10) :
    (∫ t in α..(α+1/(H:ℝ)), ‖BulkCircle.S L D t‖^2)≤(N:ℝ)/g^3 := by
  have hg0 : 0<g := by linarith
  have hg1 : 1≤g := by linarith
  have hHr : 0<(H:ℝ) := by exact_mod_cast hH
  have hL : L≤N := by omega
  have htop := prime_cell_of_mangoldt N (L+D+1) H α g hN hupper hH hg hlog hlarge
    (henergy (L+D+1) hupper)
  have hbottom := prime_cell_of_mangoldt N L H α g hN hL hH hg hlog hlarge
    (henergy L hL)
  have hp (n : ℕ) : Continuous (fun t => ‖GoldbachMajorArc.primeSum n t‖^2) := by
    unfold GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hs : Continuous (fun t => ‖BulkCircle.S L D t‖^2) := by
    unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have he : (∫ t in α..(α+1/(H:ℝ)), ‖BulkCircle.S L D t‖^2)≤16*(N:ℝ)/g^10 := by
    calc
      _ ≤ ∫ t in α..(α+1/(H:ℝ)),
          2*‖GoldbachMajorArc.primeSum (L+D+1) t‖^2+
            2*‖GoldbachMajorArc.primeSum L t‖^2 := by
        apply intervalIntegral.integral_mono_on (by linarith [one_div_pos.mpr hHr])
          (hs.intervalIntegrable _ _) (((hp _).const_mul 2 |>.add ((hp _).const_mul 2)).intervalIntegrable _ _)
        intro t ht
        exact norm_sub_sq_le _ _
      _ = 2*(∫ t in α..(α+1/(H:ℝ)), ‖GoldbachMajorArc.primeSum (L+D+1) t‖^2)+
          2*(∫ t in α..(α+1/(H:ℝ)), ‖GoldbachMajorArc.primeSum L t‖^2) := by
        rw [intervalIntegral.integral_add
          (((hp (L+D+1)).const_mul 2).intervalIntegrable _ _)
          (((hp L).const_mul 2).intervalIntegrable _ _)]
        simp only [intervalIntegral.integral_const_mul]
      _ ≤ 2*(4*(N:ℝ)/g^10)+2*(4*(N:ℝ)/g^10) := by gcongr
      _ = _ := by ring
  have hbig : (16:ℝ)≤g^7 :=
    hg.trans (le_self_pow₀ hg1 (by decide : 7≠0))
  apply he.trans
  have hr : (16:ℝ)/g^7≤1 := (div_le_one (by positivity)).2 hbig
  calc
    _ = ((16:ℝ)/g^7)*((N:ℝ)/g^3) := by field_simp <;> ring
    _ ≤ 1*((N:ℝ)/g^3) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := one_mul _

lemma masked_cell_le (W : Set ℝ) (hW : MeasurableSet W) (S : ℝ → ℂ)
    (hS : Continuous S) (a b : ℝ) (hab : a≤b) :
    (∫ t in a..b, W.indicator (fun u => ‖S u‖^2) t)≤
      ∫ t in a..b, ‖S t‖^2 := by
  have hi := (hS.norm.pow 2).intervalIntegrable (μ:=volume) a b
  apply intervalIntegral.integral_mono_on hab
    (show IntervalIntegrable (W.indicator (fun u => ‖S u‖^2)) volume a b from
      ⟨hi.1.indicator hW,hi.2.indicator hW⟩) hi
  intro t ht
  by_cases hw : t∈W <;> simp [hw]

/-- Dirichlet approximation of an arbitrary mesh endpoint in the unit interval. -/
theorem endpoint_approximant (R : ℕ) (hR : 0<R) (α : ℝ)
    (hα : α∈Set.Icc (0:ℝ) 1) :
    ∃ q a : ℕ, 0<q ∧ q≤R ∧ a≤q ∧ a.Coprime q ∧
      |α-(a:ℝ)/q|≤1/((q:ℝ)*(R:ℝ)) := by
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le α hR
  have hdpos : (0:ℝ)<s.den := Nat.cast_pos.mpr s.pos
  have hRp : (0:ℝ)<R := Nat.cast_pos.mpr hR
  rw [Rat.cast_def,mul_comm ((R:ℝ)+1) (s.den:ℝ)] at hs
  have hclose : |α*s.den-s.num|<1 := by
    have h := mul_le_mul_of_nonneg_right hs hdpos.le
    rw [←abs_of_pos hdpos,←abs_mul,abs_of_pos hdpos] at h
    rw [sub_mul,div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div,one_mul,div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have hα0 : 0≤α*s.den := mul_nonneg hα.1 hdpos.le
  have hα1 : α*(s.den:ℝ)≤(s.den:ℝ) := by simpa using mul_le_mul_of_nonneg_right hα.2 hdpos.le
  have hnlo : (-1:ℤ)<s.num := by exact_mod_cast (show (-1:ℝ)<s.num by linarith)
  have hnhi : s.num<(s.den:ℤ)+1 := by exact_mod_cast (show (s.num:ℝ)<s.den+1 by linarith)
  have hcast : (s.num.natAbs:ℤ)=s.num := by
    rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs:ℝ)=s.num := by
    calc (s.num.natAbs:ℝ) = ((s.num.natAbs:ℤ):ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z:ℝ)) hcast
  have hle : s.num.natAbs≤ s.den := by
    exact_mod_cast (show (s.num.natAbs:ℤ)≤ s.den by omega)
  rw [←hcast'] at hs
  refine ⟨s.den,s.num.natAbs,s.pos,hd,hle,s.reduced,hs.trans ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  gcongr
  linarith

end
end GoldbachBeaumontHigh




end

/- Source: BeaumontExceptionTransfer.lean -/
section

/-!
Finite outer reduction for L-goldbach-beaumont-one-sided-hole-cluster.
The counting function and window below are literal copies of the frozen task.
The finite squared-error argument is the argument of the accepted
Conjectures.Goldbach.DynExceptionEnergy, specialized to the actual bad set.
-/

namespace GoldbachBeaumont

open Finset

def centralPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n)

def centralCount (n : ℕ) : ℕ := (centralPrimes n).card

def evenWindow (X y : ℕ) : Finset ℕ :=
  (Finset.Icc y (y + Nat.sqrt X)).filter Even

def centralHoles (X y : ℕ) : Finset ℕ :=
  (Finset.Icc y (y + Nat.sqrt X)).filter (fun n => Even n ∧ centralCount n = 0)

noncomputable def centralPrimeLogRep (n : ℕ) : ℝ :=
  ∑ p ∈ centralPrimes n, Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ)

theorem mem_centralPrimes {n p : ℕ} :
    p ∈ centralPrimes n ↔
      p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n := by
  simp only [centralPrimes, mem_filter, mem_range, Nat.lt_succ_iff]
  tauto

theorem centralPrimeLogRep_nonneg (n : ℕ) : 0 ≤ centralPrimeLogRep n := by
  exact Finset.sum_nonneg (fun p _ =>
    mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg (n - p)))

theorem centralPrimeLogRep_eq_zero_of_count_zero {n : ℕ}
    (hn : centralCount n = 0) : centralPrimeLogRep n = 0 := by
  have he : centralPrimes n = ∅ := Finset.card_eq_zero.mp hn
  simp only [centralPrimeLogRep, he, Finset.sum_empty]

theorem centralPrimeLogRep_pos_of_count_pos {n : ℕ}
    (hn : 0 < centralCount n) : 0 < centralPrimeLogRep n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hn
  have hmem := mem_centralPrimes.mp hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hmem.1.one_lt
  have hq1 : (1 : ℝ) < (n - p : ℕ) := by exact_mod_cast hmem.2.2.1.one_lt
  have hpos := mul_pos (Real.log_pos hp1) (Real.log_pos hq1)
  exact hpos.trans_le (Finset.single_le_sum
    (fun r _ => mul_nonneg (Real.log_natCast_nonneg r)
      (Real.log_natCast_nonneg (n-r))) hp)

theorem centralPrimeLogRep_eq_zero_iff {n : ℕ} :
    centralPrimeLogRep n = 0 ↔ centralCount n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hp := centralPrimeLogRep_pos_of_count_pos (Nat.pos_of_ne_zero hn)
    simpa only [h, lt_self_iff_false] using hp
  · exact centralPrimeLogRep_eq_zero_of_count_zero

theorem centralHoles_subset (X y : ℕ) : centralHoles X y ⊆ evenWindow X y := by
  intro n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
    (Finset.mem_filter.mp hn).2.1⟩

theorem centralHoles_eq_filter (X y : ℕ) :
    centralHoles X y = (evenWindow X y).filter (fun n => centralCount n = 0) := by
  ext n
  simp only [centralHoles, evenWindow, mem_filter, and_assoc]

/-- Every actual central hole consumes at least the squared positive main-term floor. -/
theorem centralHoles_energy (X y : ℕ) (r b : ℕ → ℝ) (L : ℝ)
    (hL : 0 < L)
    (hr : ∀ n ∈ centralHoles X y, r n = 0)
    (hb : ∀ n ∈ evenWindow X y, L ≤ b n) :
    ((centralHoles X y).card : ℝ) * L ^ 2 ≤
      ∑ n ∈ evenWindow X y, (r n - b n) ^ 2 := by
  calc
    ((centralHoles X y).card : ℝ) * L ^ 2
        = ∑ n ∈ centralHoles X y, L ^ 2 := by simp
    _ ≤ ∑ n ∈ centralHoles X y, (r n - b n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [hr n hn, zero_sub, neg_sq]
      exact pow_le_pow_left₀ hL.le (hb n (centralHoles_subset X y hn)) 2
    _ ≤ ∑ n ∈ evenWindow X y, (r n - b n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (centralHoles_subset X y)
        (fun _ _ _ => sq_nonneg _)

theorem centralHoles_card_le (X y : ℕ) (r b : ℕ → ℝ) (L B : ℝ)
    (hL : 0 < L)
    (hr : ∀ n ∈ centralHoles X y, r n = 0)
    (hb : ∀ n ∈ evenWindow X y, L ≤ b n)
    (hE : (∑ n ∈ evenWindow X y, (r n - b n) ^ 2) ≤ B * L ^ 2) :
    ((centralHoles X y).card : ℝ) ≤ B := by
  have h := (centralHoles_energy X y r b L hL hr hb).trans hE
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp h

theorem centralCount_zero_forbids_prime_pair {n i j : ℕ}
    (hn : centralCount n = 0) (hij : i + j = n)
    (hi : i.Prime) (hj : j.Prime) (hlo : n ≤ 3 * i) (hup : 3 * i ≤ 2 * n) : False := by
  have himem : i ∈ centralPrimes n := mem_centralPrimes.mpr
    ⟨hi, by omega, by simpa only [← hij, Nat.add_sub_cancel_left] using hj, hlo, hup⟩
  have : centralPrimes n = ∅ := Finset.card_eq_zero.mp hn
  simpa only [this, Finset.notMem_empty] using himem

/-- Complex Fourier form: on a genuine hole the full coefficient vanishes, so
the minor-arc coefficient cancels the positive real main-arc coefficient. -/
theorem centralHoles_complex_energy (X y : ℕ) (major minor : ℕ → ℂ) (L : ℝ)
    (hL : 0 ≤ L)
    (hsplit : ∀ n ∈ centralHoles X y, major n + minor n = 0)
    (hmajor : ∀ n ∈ centralHoles X y, L ≤ (major n).re) :
    ((centralHoles X y).card : ℝ) * L ^ 2 ≤
      ∑ n ∈ evenWindow X y, ‖minor n‖ ^ 2 := by
  have hpoint (n : ℕ) (hn : n ∈ centralHoles X y) : L ^ 2 ≤ ‖minor n‖ ^ 2 := by
    have hRe := congrArg Complex.re (hsplit n hn)
    rw [Complex.add_re, Complex.zero_re] at hRe
    apply pow_le_pow_left₀ hL
    have hnorm := (abs_le.mp (Complex.abs_re_le_norm (minor n))).1
    linarith only [hmajor n hn, hRe, hnorm]
  calc
    ((centralHoles X y).card : ℝ) * L ^ 2
        = ∑ _n ∈ centralHoles X y, L ^ 2 := by simp
    _ ≤ ∑ n ∈ centralHoles X y, ‖minor n‖ ^ 2 := Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ evenWindow X y, ‖minor n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (centralHoles_subset X y)
        (fun _ _ _ => sq_nonneg _)

theorem centralHoles_card_le_of_complex_energy (X y : ℕ)
    (major minor : ℕ → ℂ) (L B : ℝ) (hL : 0 < L)
    (hsplit : ∀ n ∈ centralHoles X y, major n + minor n = 0)
    (hmajor : ∀ n ∈ centralHoles X y, L ≤ (major n).re)
    (hE : (∑ n ∈ evenWindow X y, ‖minor n‖ ^ 2) ≤ B * L ^ 2) :
    ((centralHoles X y).card : ℝ) ≤ B := by
  have h := (centralHoles_complex_energy X y major minor L hL.le hsplit hmajor).trans hE
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp h

/-- Interface for a short-window analytic proof. The representation can have any
fixed prime support, provided an empty central count forces its coefficient to vanish. -/
def UniformCentralEnergy : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
    X ≤ y → y ≤ 2 * X →
    ∃ (r b : ℕ → ℝ) (L : ℝ), 0 < L ∧
      (∀ n ∈ centralHoles X y, r n = 0) ∧
      (∀ n ∈ evenWindow X y, L ≤ b n) ∧
      (∑ n ∈ evenWindow X y, (r n - b n) ^ 2) ≤
        (ε * (Nat.sqrt X : ℝ)) * L ^ 2

theorem frozen_target_of_uniform_energy (hEnergy : UniformCentralEnergy) :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p =>
      p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y ≤ 2*X →
      ((((Finset.Icc y (y+Nat.sqrt X)).filter
        (fun n => Even n ∧ H n=0)).card):ℝ) ≤ ε*(Nat.sqrt X:ℝ) := by
  intro H ε hε
  obtain ⟨X₀, hX₀⟩ := hEnergy ε hε
  refine ⟨X₀, ?_⟩
  intro X hX y hXy hyX
  obtain ⟨r, b, L, hL, hr, hb, hE⟩ := hX₀ X hX y hXy hyX
  exact centralHoles_card_le X y r b L (ε * (Nat.sqrt X : ℝ)) hL hr hb hE

end GoldbachBeaumont




end

/- Source: BeaumontCentralPackage.lean -/
section

/- BEGIN BeaumontMainArc.lean -/

open Finset Filter MeasureTheory
open scoped Topology
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace GoldbachBeaumontMainArc
noncomputable section

def centralWidth (X : ℕ) : ℕ := BulkCircle.length (3 * X)
def centralStart (X y : ℕ) : ℕ :=
  BulkCircle.start (3 * X) (y + Nat.sqrt X + 1)

theorem fixed_window_geometry {X y H : ℕ} (hX : 1024 ≤ X)
    (hH : 100 * (H + 1) ≤ X) (hy : X ≤ y) (hy2 : y ≤ 2 * X) :
    let D := BulkCircle.length (3 * X)
    let L := BulkCircle.start (3 * X) (y + H + 1)
    0 < L ∧ L + D + 1 ≤ 3 * X ∧ 3 * X ≤ 64 * D ∧
      (∀ n ∈ Icc y (y + H), ∀ k : ℕ, L < k → k ≤ L + D + 1 →
        k ≤ n ∧ n ≤ 3 * k ∧ 3 * k ≤ 2 * n) ∧
      (∀ n ∈ Icc y (y + H), ∃ m : ℕ,
        n = m + 2 * (L + 1) ∧ m ≤ D ∧ D - m ≤ H + 2) := by
  dsimp [BulkCircle.length, BulkCircle.start]
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro n hn k hk1 hk2
    have hn' := mem_Icc.mp hn
    omega
  · intro n hn
    have hn' := mem_Icc.mp hn
    refine ⟨n - 2 * (((y + H + 1 - 3 * X / 32 + 1) / 2 - 1) + 1), ?_, ?_, ?_⟩ <;>
      omega

theorem eventually_sqrt_small :
    ∀ᶠ X : ℕ in atTop, 1024 ≤ X ∧ 100 * (Nat.sqrt X + 1) ≤ X := by
  filter_upwards [eventually_ge_atTop (1000000 : ℕ)] with X hX
  have hroot : 1000 ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hsq := Nat.sqrt_le' X
  constructor
  · omega
  · nlinarith

theorem eventually_window_in_block (e : ℕ) :
    ∀ᶠ X : ℕ in atTop, Nat.sqrt X + 1 ≤ BulkCircle.block e (3 * X) := by
  have ht : Tendsto (fun X : ℕ => 3 * X) atTop atTop :=
    tendsto_atTop_mono (fun X => by change X ≤ 3 * X; omega) tendsto_id
  filter_upwards [ht.eventually (BulkCircle.eventually_grid e),
    eventually_ge_atTop (1000000000000000000000000 : ℕ)] with X hgrid hX
  let H := Nat.sqrt X
  let r := BulkCircle.root e (3 * X)
  have hr : 1 ≤ r := BulkCircle.rpos e (3 * X)
  have hr4 : r ^ 4 ≤ X := by dsimp [r] at *; omega
  have hr2 : r ^ 2 ≤ H := by
    apply Nat.le_sqrt'.mpr
    simpa only [← pow_mul] using hr4
  have hH : 1000000000000 ≤ H := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hrH : 1000000 * r ≤ H := by
    have h1 := Nat.mul_le_mul_left 1000000000000 hr2
    have h2 := Nat.mul_le_mul_right H hH
    nlinarith
  have hh := Nat.mul_le_mul_right (H + 1) hrH
  have hs : H ^ 2 ≤ X := Nat.sqrt_le' X
  have hm : (H + 1) * (1000000 * r) ≤ 3 * X := by nlinarith
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < 1000000 * r)).mpr hm

theorem eventually_major_floor (e : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ Icc y (y + Nat.sqrt X), Even n →
      (centralWidth X : ℝ) / 288 ≤
        (GoldbachBlockGeometry.majorContribution (BulkCircle.cut e (3 * X))
          (centralWidth X) (BulkCircle.integrand (centralStart X y) (centralWidth X) n)).re := by
  have ht : Tendsto (fun X : ℕ => 3 * X) atTop atTop :=
    tendsto_atTop_mono (fun X => by change X ≤ 3 * X; omega) tendsto_id
  filter_upwards [eventually_sqrt_small, eventually_window_in_block e,
    ht.eventually (BulkCircle.eventually_grid e),
    ht.eventually (BulkCircle.eventually_major (2 * e + 36) (by omega))]
    with X hsmall hwindow hgrid hmajor
  intro y hy hy2 n hn heven
  obtain ⟨hL, hux, hxD, hcentral, hfreq⟩ :=
    fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  obtain ⟨m, hnm, hmD, hDm⟩ := hfreq n hn
  obtain ⟨_, _, _, _, _, hsep, hshort⟩ := BulkCircle.grid_bounds e (3 * X) hgrid
  apply hmajor (centralStart X y) (centralWidth X) n m hxD hL hux hnm heven hmD hsep
  have hbound : centralWidth X ≤ BulkCircle.block e (3 * X) + 1 + m := by
    dsimp [centralWidth]
    omega
  have hboundR : (centralWidth X : ℝ) - m ≤ (BulkCircle.block e (3 * X) : ℝ) + 1 := by
    have hr : (centralWidth X : ℝ) ≤ (BulkCircle.block e (3 * X) : ℝ) + 1 + m := by exact_mod_cast hbound
    linarith
  exact (mul_le_mul_of_nonneg_left hboundR (by positivity)).trans hshort

theorem central_support_eventually :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ Icc y (y + Nat.sqrt X), ∀ k : ℕ,
        centralStart X y < k → k ≤ centralStart X y + centralWidth X + 1 →
        k ≤ n ∧ n ≤ 3 * k ∧ 3 * k ≤ 2 * n := by
  filter_upwards [eventually_sqrt_small] with X hX
  intro y hy hy2
  exact (fixed_window_geometry hX.1 hX.2 hy hy2).2.2.2.1

theorem centralWidth_floor {X : ℕ} (hX : 1024 ≤ X) :
    (X : ℝ) / 4096 ≤ (centralWidth X : ℝ) / 288 := by
  have h : 9 * X ≤ 128 * centralWidth X := by dsimp [centralWidth, BulkCircle.length]; omega
  have hr : (9 : ℝ) * X ≤ 128 * centralWidth X := by exact_mod_cast h
  nlinarith

theorem eventually_major_floor_root (e : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ Icc y (y + Nat.sqrt X), Even n →
      (centralWidth X : ℝ) / 288 ≤
        (GoldbachBlockGeometry.majorContribution (BulkCircle.root e (3 * X))
          (centralWidth X) (BulkCircle.integrand (centralStart X y) (centralWidth X) n)).re := by
  have ht : Tendsto (fun X : ℕ => 3 * X) atTop atTop :=
    tendsto_atTop_mono (fun X => by change X ≤ 3 * X; omega) tendsto_id
  filter_upwards [eventually_sqrt_small, eventually_window_in_block e,
    ht.eventually (BulkCircle.eventually_grid e),
    ht.eventually (BulkCircle.eventually_major (e + 18) (by omega))]
    with X hsmall hwindow hgrid hmajor
  intro y hy hy2 n hn heven
  obtain ⟨hL, hux, hxD, hcentral, hfreq⟩ :=
    fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  obtain ⟨m, hnm, hmD, hDm⟩ := hfreq n hn
  obtain ⟨_, _, _, _, _, hsep, hshort⟩ := BulkCircle.grid_bounds e (3 * X) hgrid
  have hroot : 1 ≤ BulkCircle.root e (3 * X) := BulkCircle.rpos e (3 * X)
  have hrcut : BulkCircle.root e (3 * X) ≤ BulkCircle.cut e (3 * X) := by
    rw [BulkCircle.cut_sq]
    exact Nat.le_self_pow (by decide) _
  have hsep' : 2 * (BulkCircle.root e (3 * X)) ^ 2 < centralWidth X := by
    have hp : (BulkCircle.root e (3 * X)) ^ 2 ≤ (BulkCircle.cut e (3 * X)) ^ 2 := by gcongr
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hp) hsep
  apply hmajor (centralStart X y) (centralWidth X) n m hxD hL hux hnm heven hmD hsep'
  have hbound : centralWidth X ≤ BulkCircle.block e (3 * X) + 1 + m := by
    dsimp [centralWidth]
    omega
  have hboundR : (centralWidth X : ℝ) - m ≤ (BulkCircle.block e (3 * X) : ℝ) + 1 := by
    have hr : (centralWidth X : ℝ) ≤ (BulkCircle.block e (3 * X) : ℝ) + 1 + m := by exact_mod_cast hbound
    linarith
  have hrootR : 1 ≤ (BulkCircle.root e (3 * X) : ℝ) := by exact_mod_cast hroot
  have hsqrt := Real.sqrt_le_self_iff.mpr (Or.inr hrootR)
  rw [BulkCircle.cut_sq, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)] at hshort
  have hDmR : 0 ≤ (centralWidth X : ℝ) - m := by
    have hm : (m : ℝ) ≤ centralWidth X := by exact_mod_cast hmD
    linarith
  calc
    4 * Real.sqrt (BulkCircle.root e (3 * X)) * ((centralWidth X : ℝ) - m)
      ≤ 4 * (BulkCircle.root e (3 * X) : ℝ) * ((BulkCircle.block e (3 * X) : ℝ) + 1) := by
        gcongr
    _ ≤ _ := hshort







end
end GoldbachBeaumontMainArc

/- BEGIN BeaumontMajorMinor.lean -/

open Finset Filter MeasureTheory
open scoped Topology
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc GoldbachBeaumont GoldbachBeaumontMainArc

namespace GoldbachBeaumontFourier
noncomputable section

def majorArcs (X : ℕ) : Set ℝ :=
  GoldbachBlockGeometry.arcs (BulkCircle.root 0 (3 * X)) (centralWidth X)

def majorCoefficient (X y n : ℕ) : ℂ :=
  GoldbachBlockGeometry.majorContribution (BulkCircle.root 0 (3 * X))
    (centralWidth X) (BulkCircle.integrand (centralStart X y) (centralWidth X) n)

def minorCoefficient (X y n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (majorArcs X)ᶜ.indicator
    (BulkCircle.integrand (centralStart X y) (centralWidth X) n) t

theorem majorArcs_measurable (X : ℕ) : MeasurableSet (majorArcs X) :=
  GoldbachEstermann.measurable_block_arcs _ _

theorem zero_pairs {L D n : ℕ}
    (hcentral : ∀ k : ℕ, L < k → k ≤ L + D + 1 → n ≤ 3 * k ∧ 3 * k ≤ 2 * n)
    (hcount : centralCount n = 0) (i j : ℕ) (hij : i + j = n) :
    BulkCircle.ww L D i * BulkCircle.ww L D j = 0 := by
  by_cases hi : L < i ∧ i ≤ L + D + 1
  · by_cases hj : L < j ∧ j ≤ L + D + 1
    · rw [BulkCircle.ww, if_pos hi, BulkCircle.ww, if_pos hj]
      by_cases hpi : i.Prime
      · by_cases hpj : j.Prime
        · exact (centralCount_zero_forbids_prime_pair hcount hij hpi hpj
            (hcentral i hi.1 hi.2).1 (hcentral i hi.1 hi.2).2).elim
        · simp [primeWeight, hpj]
      · simp [primeWeight, hpi]
    · simp [BulkCircle.ww, hj]
  · simp [BulkCircle.ww, hi]

theorem full_coefficient_zero {L D N n : ℕ} (hupper : L + D + 1 ≤ N)
    (hcentral : ∀ k : ℕ, L < k → k ≤ L + D + 1 → n ≤ 3 * k ∧ 3 * k ≤ 2 * n)
    (hcount : centralCount n = 0) :
    (∫ t in (0 : ℝ)..1, BulkCircle.integrand L D n t) = 0 := by
  have hfull := WindowBessel.ExceptionalCoefficients.zero_from_pairs
    (BulkCircle.ww L D) n N (zero_pairs hcentral hcount)
  unfold BulkCircle.integrand
  simp_rw [BulkCircle.as_mask N L D hupper]
  exact hfull

theorem major_add_minor (X y n : ℕ) :
    majorCoefficient X y n + minorCoefficient X y n =
      ∫ t in (0 : ℝ)..1, BulkCircle.integrand (centralStart X y) (centralWidth X) n t := by
  have hc : Continuous (BulkCircle.integrand (centralStart X y) (centralWidth X) n) := by
    unfold BulkCircle.integrand BulkCircle.S primeSum phase
    fun_prop
  exact WindowBessel.ExceptionalCoefficients.indicator_integral_split
    (majorArcs_measurable X) (hc.intervalIntegrable 0 1)

theorem eventually_major_minor_package :
    ∀ᶠ X : ℕ in atTop, 1024 ≤ X ∧ ∀ y : ℕ, X ≤ y → y ≤ 2 * X →
      ∀ n ∈ centralHoles X y,
        majorCoefficient X y n + minorCoefficient X y n = 0 ∧
          (X : ℝ) / 4096 ≤ (majorCoefficient X y n).re := by
  filter_upwards [eventually_sqrt_small, eventually_major_floor_root 0] with X hsmall hmajor
  refine ⟨hsmall.1, ?_⟩
  intro y hy hy2 n hn
  have hnwin := (mem_filter.mp hn).1
  have heven := (mem_filter.mp hn).2.1
  have hcount := (mem_filter.mp hn).2.2
  obtain ⟨hL, hupper, hxD, hcentral, hfreq⟩ :=
    fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  constructor
  · rw [major_add_minor]
    exact full_coefficient_zero hupper (fun k hk1 hk2 => (hcentral n hnwin k hk1 hk2).2) hcount
  · exact (centralWidth_floor hsmall.1).trans (hmajor y hy hy2 n hnwin heven)




end
end GoldbachBeaumontFourier
end

/- Source: BeaumontSampling.lean -/
section

/-!
Sampling proof adapted, without its unrelated rational-window counting portion, from
CGandGameEngineLearner/goldbach-proofs, ThreeQuartersExceptionalDirichletWindows.lean
SHA256 62fd39f29df66b19ea3a98261ba8cd116652d68f13dc8488699abd2008fb55bb.
The original retains the source notice for Clrs17's accepted Parseval proof:
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/138
commit 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64. Apache-2.0.
-/

section
open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace GoldbachBeaumontSampling

private theorem continuous_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

end GoldbachBeaumontSampling
end

section
open Set Finset MeasureTheory Filter intervalIntegral
noncomputable section
namespace GoldbachBeaumontSampling

private theorem variation_on_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    F x ≤ F y + ∫ u in l..r, |D u| := by
  have step {a b : ℝ} (ha : l≤a) (hab : a≤b) (hb : b≤r) :
      |F b-F a| ≤ ∫ u in l..r, |D u| := by
    rw [← integral_eq_sub_of_hasDerivAt (fun t _ => dF t) (cD.intervalIntegrable ..)]
    exact (abs_integral_le_integral_abs hab).trans (integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (cD.abs.intervalIntegrable ..))
  rcases le_total y x with h|h
  · linarith [(le_abs_self (F x-F y)).trans (step hy.1 h hx.2)]
  · linarith [(neg_le_abs (F y-F x)).trans (step hx.1 h hy.2)]

private theorem scaled_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x : ℝ} (hx : x ∈ Icc l r) :
    (r-l)*F x ≤ (∫ u in l..r, F u) + (r-l)*(∫ u in l..r, |D u|) := by
  let V := ∫ u in l..r, |D u|
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have h := integral_mono_on (μ:=volume) (hx.1.trans hx.2) (f:=fun _ : ℝ => F x) (g:=fun y => F y+V)
    (continuous_const.intervalIntegrable ..) ((hF.add continuous_const).intervalIntegrable ..)
    (fun _ hy => variation_on_cell dF cD hx hy)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add (hF.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),intervalIntegral.integral_const] at h
  exact h

/-- Sample anywhere in each of the n equal closed cells; the variation budget
is charged just once across the whole interval. -/
theorem sample_mesh {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {n : ℕ} (hn : 0<n) (t : ℕ→ℝ)
    (h : ∀ j<n, t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n,F (t j)) ≤ (n:ℝ)*(∫ x in (0:ℝ)..1,F x) + ∫ x in (0:ℝ)..1, |D x| := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let b := fun j : ℕ => (j:ℝ)/n
  have width (j : ℕ) : b (j+1)-b j = 1/(n:ℝ) := by dsimp [b];push_cast;ring
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have cell (j : ℕ) (hj : j∈range n) :
      F (t j) ≤ (n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x| := by
    have mem : t j ∈ Icc (b j) (b (j+1)) := by simpa [b] using h j (mem_range.mp hj)
    have z := scaled_cell dF cD mem
    rw [width] at z
    have zz := mul_le_mul_of_nonneg_left z hn0.le
    field_simp at zz
    linarith
  calc
    _ ≤ ∑ j ∈ range n, ((n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x|) :=
      sum_le_sum cell
    _ = _ := by
      rw [sum_add_distrib,←mul_sum,sum_integral_adjacent_intervals (fun _ _ => hF.intervalIntegrable ..),
        sum_integral_adjacent_intervals (fun _ _ => cD.abs.intervalIntegrable ..)]
      simp [b,hn0.ne']

end GoldbachBeaumontSampling
end
end

section
open Set Finset MeasureTheory intervalIntegral Complex
noncomputable section
namespace GoldbachBeaumontSampling

private def c : ℂ := (2*Real.pi:ℝ)*I
def wave (k : ℕ) (t : ℝ) : ℂ := Complex.exp (c * k * (t : ℂ))
def series (n : ℕ) (w : ℕ→ℝ) (t : ℝ) : ℂ := ∑ k ∈ range (n+1), (w k : ℂ)*wave k t

theorem wave_eq (k : ℕ) (t : ℝ) :
    wave k t = Complex.exp ((((2*Real.pi*((k:ℝ)*t):ℝ):ℂ))*I) := by
  unfold wave c
  apply congrArg Complex.exp
  push_cast
  ring

theorem energy (n : ℕ) (w : ℕ→ℝ) :
    (∫ t in (0:ℝ)..1, ‖series n w t‖^2) = ∑ k ∈ range (n+1), (w k)^2 := by
  simpa only [series,wave_eq] using continuous_parseval n w

private theorem wave_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (wave k) (wave k t * (c*k)) t := by
  let C := c*(k:ℂ)
  have hd := (Complex.hasDerivAt_exp (C*(t:ℂ))).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).const_mul C)
  change HasDerivAt (fun x : ℝ => Complex.exp (C*(x:ℂ))) (Complex.exp (C*(t:ℂ))*C) t
  simpa [C] using! hd.comp_ofReal

theorem series_deriv (n : ℕ) (w : ℕ→ℝ) (t : ℝ) :
    HasDerivAt (series n w) (c * series n (fun k => k*w k) t) t := by
  have h := HasDerivAt.fun_sum (u:=range (n+1)) (fun k _ => (wave_deriv k t).const_mul (w k:ℂ))
  apply h.congr_deriv
  unfold series
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem series_cont (n : ℕ) (w : ℕ→ℝ) : Continuous (series n w) :=
  continuous_iff_continuousAt.mpr (fun t => (series_deriv n w t).continuousAt)

private theorem energy_deriv_abs (n : ℕ) (w : ℕ→ℝ) (hn : 0<n) :
    (∫ t in (0:ℝ)..1, |2 * inner ℝ (series n w t) (c*series n (fun k => k*w k) t)|) ≤
      (4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  let F := series n w
  let G := series n (fun k => k*w k)
  have cF : Continuous F := series_cont ..
  have cG : Continuous G := series_cont ..
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hc : ‖c‖ = 2*Real.pi := by simp [c]
  have major (t : ℝ) : |2 * inner ℝ (F t) (c*G t)| ≤
      (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hv := abs_real_inner_le_norm (F t) (c*G t)
    rw [norm_mul,hc] at hv
    have key : 2*‖F t‖*‖G t‖ ≤ (n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2 := by
      apply (mul_le_mul_iff_right₀ hn0).mp
      field_simp
      nlinarith [sq_nonneg ((n:ℝ)*‖F t‖-‖G t‖)]
    nlinarith only [hv,mul_le_mul_of_nonneg_left key (show (0:ℝ)≤Real.pi by positivity)]
  have ci : Continuous (fun t => |2 * inner ℝ (F t) (c*G t)|) := by fun_prop
  have cj : Continuous (fun t => (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2)) := by fun_prop
  have ii := intervalIntegral.integral_mono (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (ci.intervalIntegrable ..) (cj.intervalIntegrable ..) major
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (by exact (continuous_const.mul (cF.norm.pow 2)).intervalIntegrable ..)
    (by exact (continuous_const.mul (cG.norm.pow 2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at ii
  dsimp only [F,G] at ii
  rw [energy,energy] at ii
  have edge : (∑ k ∈ range (n+1), ((k:ℝ)*w k)^2) ≤ (n:ℝ)^2 * ∑ k ∈ range (n+1),(w k)^2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (show k≤n by have := mem_range.mp hk;omega)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hk' 2) (sq_nonneg _)
  apply ii.trans
  have e := mul_le_mul_of_nonneg_left edge (show 0≤1/(n:ℝ) by positivity)
  have simpN : 1/(n:ℝ)*((n:ℝ)^2*(∑ k ∈ range (n+1),(w k)^2)) = n*(∑ k ∈ range (n+1),(w k)^2) := by field_simp
  rw [simpN] at e
  nlinarith only [mul_le_mul_of_nonneg_left e Real.pi_pos.le]

/-- A frequency polynomial may be sampled at an arbitrary point in every mesh
cell. The sample locations may depend on the coefficients. -/
theorem sample_series {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (t : ℕ→ℝ)
    (h : ∀ j<n,t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n, ‖series n w (t j)‖^2) ≤
      (1+4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  have cF := series_cont n w
  have cG := series_cont n (fun k => k*w k)
  have ht := sample_mesh (fun x => (series_deriv n w x).norm_sq)
    (by fun_prop) hn t h
  rw [energy] at ht
  linarith only [ht,energy_deriv_abs n w hn]

end GoldbachBeaumontSampling
end
end

end

/- Source: BeaumontLocalBessel.lean -/
section

/-!
Local Fourier energy by weighted duality.  The mesh sampling estimate is the
accepted Sobolev argument in ThreeQuartersExceptionalDirichletWindows.  It is
applied to the *short frequency interval*, so its scale is the target window
length, rather than the length of the prime polynomial.
-/

open Finset MeasureTheory Set Complex
open scoped BigOperators

namespace GoldbachBeaumontLocalBessel

noncomputable section

def poly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (N+1), a k * GoldbachBeaumontSampling.wave k t

theorem poly_cont (N : ℕ) (a : ℕ → ℂ) : Continuous (poly N a) := by
  unfold poly GoldbachBeaumontSampling.wave
  fun_prop

theorem poly_decompose (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    poly N a t = GoldbachBeaumontSampling.series N (fun k => (a k).re) t +
      Complex.I * GoldbachBeaumontSampling.series N (fun k => (a k).im) t := by
  unfold poly GoldbachBeaumontSampling.series
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.re_add_im (a k)]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, mul_one]
  ring

theorem poly_norm_sq_le (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖poly N a t‖ ^ 2 ≤
      2 * (‖GoldbachBeaumontSampling.series N (fun k => (a k).re) t‖ ^ 2 +
        ‖GoldbachBeaumontSampling.series N (fun k => (a k).im) t‖ ^ 2) := by
  rw [poly_decompose]
  have h := norm_add_le (GoldbachBeaumontSampling.series N (fun k => (a k).re) t)
    (Complex.I * GoldbachBeaumontSampling.series N (fun k => (a k).im) t)
  rw [norm_mul, Complex.norm_I, one_mul] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖GoldbachBeaumontSampling.series N (fun k => (a k).re) t‖ -
    ‖GoldbachBeaumontSampling.series N (fun k => (a k).im) t‖)]

theorem sample_poly {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (t : ℕ → ℝ)
    (ht : ∀ j < N, t j ∈ Icc ((j : ℝ)/N) (((j : ℝ)+1)/N)) :
    (∑ j ∈ range N, ‖poly N a (t j)‖ ^ 2) ≤
      2 * (1+4*Real.pi) * (N : ℝ) * ∑ k ∈ range (N+1), ‖a k‖ ^ 2 := by
  have hr := GoldbachBeaumontSampling.sample_series hN (fun k => (a k).re) t ht
  have hi := GoldbachBeaumontSampling.sample_series hN (fun k => (a k).im) t ht
  have hsum := Finset.sum_le_sum (s := range N) (fun j _ => poly_norm_sq_le N a (t j))
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hnorm : (∑ k ∈ range (N+1), (a k).re ^ 2) +
      (∑ k ∈ range (N+1), (a k).im ^ 2) =
      ∑ k ∈ range (N+1), ‖a k‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm (a k)).symm
  calc
    _ ≤ 2 * ((∑ j ∈ range N,
        ‖GoldbachBeaumontSampling.series N (fun k => (a k).re) (t j)‖ ^ 2) +
      (∑ j ∈ range N,
        ‖GoldbachBeaumontSampling.series N (fun k => (a k).im) (t j)‖ ^ 2)) := hsum
    _ ≤ 2 * ((1+4*Real.pi) * (N : ℝ) *
      (∑ k ∈ range (N+1), (a k).re ^ 2) +
      (1+4*Real.pi) * (N : ℝ) *
      (∑ k ∈ range (N+1), (a k).im ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hr hi) (by norm_num)
    _ = _ := by rw [← mul_add, hnorm]; ring

/-- A nonnegative weight with mass at most E in every mesh cell acts on a
degree-N polynomial with norm at most an explicit constant times N E. -/
theorem weighted_poly_energy {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ)
    (w : ℝ → ℝ) (E : ℝ) (hw : ∀ t, 0 ≤ w t) (hE : 0 ≤ E)
    (hwi : ∀ l r : ℝ, IntervalIntegrable w volume l r)
    (hloc : ∀ j < N, (∫ t in ((j : ℝ)/N)..(((j : ℝ)+1)/N), w t) ≤ E) :
    (∫ t in (0 : ℝ)..1, w t * ‖poly N a t‖ ^ 2) ≤
      E * (2 * (1+4*Real.pi) * (N : ℝ) * ∑ k ∈ range (N+1), ‖a k‖ ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := (poly_cont N a).norm.pow 2
  have hmax (j : ℕ) : ∃ t ∈ Icc ((j : ℝ)/N) (((j : ℝ)+1)/N),
      ∀ u ∈ Icc ((j : ℝ)/N) (((j : ℝ)+1)/N),
        ‖poly N a u‖ ^ 2 ≤ ‖poly N a t‖ ^ 2 := by
    have hab : (j : ℝ)/N ≤ ((j : ℝ)+1)/N :=
      div_le_div_of_nonneg_right (by linarith) hNr.le
    obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hab) hp.continuousOn
    exact ⟨t, ht, isMaxOn_iff.mp hm⟩
  choose t ht hbest using hmax
  have hi (l r : ℝ) : IntervalIntegrable (fun u => w u * ‖poly N a u‖ ^ 2)
      volume l r := (hwi l r).mul_continuousOn hp.continuousOn
  have hcell (j : ℕ) (hj : j ∈ range N) :
      (∫ u in ((j : ℝ)/N)..(((j : ℝ)+1)/N), w u * ‖poly N a u‖ ^ 2) ≤
      E * ‖poly N a (t j)‖ ^ 2 := by
    calc
      _ ≤ ∫ u in ((j : ℝ)/N)..(((j : ℝ)+1)/N), w u * ‖poly N a (t j)‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on
          (div_le_div_of_nonneg_right (by linarith) hNr.le)
          (hi _ _) ((hwi _ _).mul_const _)
        intro u hu
        exact mul_le_mul_of_nonneg_left (hbest j u hu) (hw u)
      _ = (∫ u in ((j : ℝ)/N)..(((j : ℝ)+1)/N), w u) *
          ‖poly N a (t j)‖ ^ 2 := intervalIntegral.integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hloc j (mem_range.mp hj)) (sq_nonneg _)
  have hsplit : (∫ u in (0 : ℝ)..1, w u * ‖poly N a u‖ ^ 2) =
      ∑ j ∈ range N, ∫ u in ((j : ℝ)/N)..(((j : ℝ)+1)/N),
        w u * ‖poly N a u‖ ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ => (j : ℝ)/N) (n := N) (fun _ _ => hi _ _)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div,
      div_self hNr.ne'] using h.symm
  rw [hsplit]
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sample_poly hN a t (fun j _ => ht j)) hE

def coeff (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f t * (starRingEnd ℂ) (GoldbachBeaumontSampling.wave k t)

theorem coefficient_duality (N : ℕ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t * (starRingEnd ℂ) (poly N (coeff f) t)) =
      ((∑ k ∈ range (N+1), ‖coeff f k‖ ^ 2 : ℝ) : ℂ) := by
  have hw (k : ℕ) : Continuous (GoldbachBeaumontSampling.wave k) := by
    unfold GoldbachBeaumontSampling.wave
    fun_prop
  have hint (k : ℕ) : IntervalIntegrable
      (fun t => f t * (starRingEnd ℂ) (GoldbachBeaumontSampling.wave k t)) volume 0 1 :=
    hf.mul_continuousOn (Complex.continuous_conj.comp (hw k)).continuousOn
  have hpoint (t : ℝ) : f t * (starRingEnd ℂ) (poly N (coeff f) t) =
      ∑ k ∈ range (N+1), (starRingEnd ℂ) (coeff f k) *
        (f t * (starRingEnd ℂ) (GoldbachBeaumontSampling.wave k t)) := by
    simp only [poly, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => (hint k).const_mul ((starRingEnd ℂ) (coeff f k))), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul]
  change (starRingEnd ℂ) (coeff f k) * coeff f k = _
  rw [mul_comm, Complex.mul_conj']
  norm_cast

/-- The short-window Bessel estimate. It is valid for any integrable complex
function.  Only its absolute mass in cells of width 1/N is needed. -/
theorem local_bessel {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ)
    (hf : ∀ l r : ℝ, IntervalIntegrable f volume l r)
    (E : ℝ) (hE : 0 < E)
    (hloc : ∀ j < N,
      (∫ t in ((j : ℝ)/N)..(((j : ℝ)+1)/N), ‖f t‖) ≤ E) :
    (∑ k ∈ range (N+1), ‖coeff f k‖ ^ 2) ≤
      (2 * (1+4*Real.pi) * (N : ℝ) * E) * (∫ t in (0 : ℝ)..1, ‖f t‖) := by
  let A : ℝ := ∑ k ∈ range (N+1), ‖coeff f k‖ ^ 2
  let D : ℝ := 2 * (1+4*Real.pi) * (N : ℝ) * E
  let T := poly N (coeff f)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hTc : Continuous T := poly_cont ..
  have hw (l r : ℝ) : IntervalIntegrable (fun t => ‖f t‖) volume l r := (hf l r).norm
  have hwT : IntervalIntegrable (fun t => ‖f t‖ * ‖T t‖) volume 0 1 :=
    (hw 0 1).mul_continuousOn hTc.norm.continuousOn
  have hwT2 : IntervalIntegrable (fun t => ‖f t‖ * ‖T t‖ ^ 2) volume 0 1 :=
    (hw 0 1).mul_continuousOn (hTc.norm.pow 2).continuousOn
  have hfirst : A ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖T t‖ := by
    have hd := coefficient_duality N f (hf 0 1)
    have he : ‖((A : ℝ) : ℂ)‖ = A := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    calc
      A = ‖((A : ℝ) : ℂ)‖ := he.symm
      _ = ‖∫ t in (0 : ℝ)..1, f t * (starRingEnd ℂ) (T t)‖ := by rw [hd]
      _ ≤ ∫ t in (0 : ℝ)..1, ‖f t * (starRingEnd ℂ) (T t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = _ := by simp only [norm_mul, Complex.norm_conj]
  have hweighted : (∫ t in (0 : ℝ)..1, ‖f t‖ * ‖T t‖ ^ 2) ≤ D * A := by
    have h := weighted_poly_energy hN (coeff f) (fun t => ‖f t‖) E
      (fun _ => norm_nonneg _) hE.le hw hloc
    exact h.trans_eq (by dsimp [D,A]; ring)
  have hpoint (t : ℝ) : 2*D*(‖f t‖*‖T t‖) ≤
      D^2*‖f t‖ + ‖f t‖*‖T t‖^2 := by
    have h := mul_nonneg (norm_nonneg (f t)) (sq_nonneg (D-‖T t‖))
    nlinarith only [h]
  have hyoung := intervalIntegral.integral_mono (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hwT.const_mul (2*D))
    (((hw 0 1).const_mul (D^2)).add hwT2) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hw 0 1).const_mul (D^2)) hwT2,
    intervalIntegral.integral_const_mul] at hyoung
  have h2 := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2*D)
  have hfinal : D * A ≤ D * (D * (∫ t in (0 : ℝ)..1, ‖f t‖)) := by
    nlinarith only [h2, hyoung, hweighted]
  exact (mul_le_mul_iff_right₀ hD).mp hfinal

end
end GoldbachBeaumontLocalBessel


end

/- Source: BeaumontMaskedBessel.lean -/
section

open Finset MeasureTheory Set Complex
open scoped BigOperators

namespace GoldbachBeaumontLocalBessel
noncomputable section

theorem wave_norm (n : ℕ) (t : ℝ) : ‖GoldbachBeaumontSampling.wave n t‖ = 1 := by
  rw [GoldbachBeaumontSampling.wave_eq, Complex.norm_exp]
  simp

theorem wave_add (m n : ℕ) (t : ℝ) :
    GoldbachBeaumontSampling.wave (m+n) t =
      GoldbachBeaumontSampling.wave m t * GoldbachBeaumontSampling.wave n t := by
  unfold GoldbachBeaumontSampling.wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_wave (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (GoldbachBeaumontSampling.wave n t) =
      Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I) := by
  rw [GoldbachBeaumontSampling.wave_eq, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

def maskedCoeff (W : Set ℝ) (P : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, W.indicator
    (fun u => P u * (starRingEnd ℂ) (GoldbachBeaumontSampling.wave n u)) t

def shiftedMask (W : Set ℝ) (P : ℝ → ℂ) (y : ℕ) (t : ℝ) : ℂ :=
  W.indicator P t * (starRingEnd ℂ) (GoldbachBeaumontSampling.wave y t)

theorem shiftedMask_norm (W : Set ℝ) (P : ℝ → ℂ) (y : ℕ) (t : ℝ) :
    ‖shiftedMask W P y t‖ = W.indicator (fun u => ‖P u‖) t := by
  simp only [shiftedMask, norm_mul, Complex.norm_conj, wave_norm, mul_one]
  by_cases ht : t ∈ W <;> simp [ht]

theorem coeff_shiftedMask (W : Set ℝ) (P : ℝ → ℂ) (y k : ℕ) :
    coeff (shiftedMask W P y) k = maskedCoeff W P (y+k) := by
  unfold coeff maskedCoeff
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ W
  · simp only [shiftedMask, Set.indicator_of_mem ht, wave_add, map_mul]
    ring
  · simp [shiftedMask, ht]

theorem shiftedMask_integrable (W : Set ℝ) (hW : MeasurableSet W)
    (P : ℝ → ℂ) (hP : Continuous P) (y : ℕ) (a b : ℝ) :
    IntervalIntegrable (shiftedMask W P y) volume a b := by
  have hi := hP.intervalIntegrable (μ := volume) a b
  have hm : IntervalIntegrable (W.indicator P) volume a b :=
    ⟨hi.1.indicator hW, hi.2.indicator hW⟩
  apply hm.mul_continuousOn
  apply Continuous.continuousOn
  unfold GoldbachBeaumontSampling.wave
  fun_prop

/-- A frequency window of length N is controlled by minor-arc energy on mesh
cells of length 1/N. The carrier phase y does not affect either norm. -/
theorem masked_window_bessel (N y : ℕ) (hN : 0 < N) (W : Set ℝ)
    (hW : MeasurableSet W) (P : ℝ → ℂ) (hP : Continuous P) (E : ℝ) (hE : 0 < E)
    (hloc : ∀ j < N,
      (∫ t in ((j : ℝ)/N)..(((j : ℝ)+1)/N), W.indicator (fun u => ‖P u‖) t) ≤ E) :
    (∑ n ∈ Finset.Icc y (y+N), ‖maskedCoeff W P n‖ ^ 2) ≤
      (2 * (1+4*Real.pi) * (N : ℝ) * E) *
        (∫ t in (0 : ℝ)..1, W.indicator (fun u => ‖P u‖) t) := by
  have h := local_bessel hN (shiftedMask W P y)
    (shiftedMask_integrable W hW P hP y) E hE (by
      simpa only [shiftedMask_norm] using hloc)
  simp only [shiftedMask_norm, coeff_shiftedMask] at h
  have hsum : (∑ n ∈ Finset.Icc y (y+N), ‖maskedCoeff W P n‖ ^ 2) =
      ∑ k ∈ Finset.range (N+1), ‖maskedCoeff W P (y+k)‖ ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [show y + N + 1 - y = N + 1 by omega]
  rw [hsum]
  exact h

theorem masked_square_window_bessel (N y : ℕ) (hN : 0 < N) (W : Set ℝ)
    (hW : MeasurableSet W) (S : ℝ → ℂ) (hS : Continuous S) (E : ℝ) (hE : 0 < E)
    (hloc : ∀ j < N,
      (∫ t in ((j : ℝ)/N)..(((j : ℝ)+1)/N), W.indicator (fun u => ‖S u‖ ^ 2) t) ≤ E) :
    (∑ n ∈ Finset.Icc y (y+N), ‖maskedCoeff W (fun t => (S t)^2) n‖ ^ 2) ≤
      (2 * (1+4*Real.pi) * (N : ℝ) * E) *
        (∫ t in (0 : ℝ)..1, W.indicator (fun u => ‖S u‖ ^ 2) t) := by
  let P : ℝ → ℂ := fun t => (S t)^2
  have hnorm : (fun u => ‖P u‖) = (fun u => ‖S u‖^2) := by
    funext u
    exact norm_pow (S u) 2
  have hlocal : ∀ j < N,
      (∫ t in ((j : ℝ)/N)..(((j : ℝ)+1)/N), W.indicator (fun u => ‖P u‖) t) ≤ E := by
    rw [hnorm]
    exact hloc
  have h := masked_window_bessel N y hN W hW P (hS.pow 2) E hE hlocal
  rw [hnorm] at h
  exact h

end
end GoldbachBeaumontLocalBessel


end

/- Source: BeaumontFinish.lean -/
section

open Finset Filter MeasureTheory
open scoped Topology BigOperators
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachBeaumont GoldbachBeaumontMainArc GoldbachBeaumontFourier
open GoldbachBeaumontParameters GoldbachBeaumontLocalBessel

namespace GoldbachBeaumontFinish
noncomputable section

def localMinorBound : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2*X → ∀ j < Nat.sqrt X,
    (∫ t in ((j:ℝ)/(Nat.sqrt X:ℝ))..(((j:ℝ)+1)/(Nat.sqrt X:ℝ)),
      (majorArcs X)ᶜ.indicator
        (fun u => ‖BulkCircle.S (centralStart X y) (centralWidth X) u‖^2) t) ≤
      (3*X:ℝ)/(logScale X:ℝ)^3

theorem minorCoefficient_eq_masked (X y n : ℕ) :
    minorCoefficient X y n = maskedCoeff (majorArcs X)ᶜ
      (fun t => (BulkCircle.S (centralStart X y) (centralWidth X) t)^2) n := by
  unfold minorCoefficient maskedCoeff BulkCircle.integrand
  simp_rw [conj_wave]
  rfl

theorem global_band_energy (N L D : ℕ) (hupper : L+D+1 ≤ N)
    (W : Set ℝ) (hW : MeasurableSet W) :
    (∫ t in (0:ℝ)..1, W.indicator (fun u => ‖BulkCircle.S L D u‖^2) t) ≤
      ((N:ℝ)+1)*(Real.log N)^2 := by
  have hS : Continuous (BulkCircle.S L D) := by
    unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hi := (hS.norm.pow 2).intervalIntegrable (μ:=volume) (0:ℝ) 1
  have him : IntervalIntegrable (W.indicator (fun t => ‖BulkCircle.S L D t‖^2))
      volume (0:ℝ) 1 := ⟨hi.1.indicator hW,hi.2.indicator hW⟩
  have hpoly (t : ℝ) : BulkCircle.S L D t =
      GoldbachWindow.poly (N+1) (fun k => (BulkCircle.ww L D k:ℂ)) t :=
    BulkCircle.as_mask N L D hupper t
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖BulkCircle.S L D t‖^2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) him hi
      intro t ht
      by_cases hw : t∈W <;> simp [hw,sq_nonneg]
    _ = ∑ k ∈ range (N+1), (BulkCircle.ww L D k)^2 := by
      simp_rw [hpoly]
      rw [GoldbachWindow.parseval]
      simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    _ ≤ _ := BulkCircle.mask_energy N L D

theorem eventual_global_band_energy :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2*X →
      (∫ t in (0:ℝ)..1, (majorArcs X)ᶜ.indicator
        (fun u => ‖BulkCircle.S (centralStart X y) (centralWidth X) u‖^2) t) ≤
        (4*(X:ℝ))*(logScale X:ℝ)^2 := by
  filter_upwards [eventually_sqrt_small, logScale_tendsto.eventually_ge_atTop 32]
    with X hsmall hg
  intro y hy hy2
  obtain ⟨hL,hupper,hsize,hcentral,hfreq⟩ :=
    fixed_window_geometry hsmall.1 hsmall.2 hy hy2
  have hX : 0<X := by omega
  have hmargin := natural_log_margin hX hg
  have hN : 0 < (scale X:ℝ) := by dsimp [scale]; positivity
  have hlog : Real.log (3*X:ℕ) ≤ (logScale X:ℝ) := by
    have hh := Real.log_le_log hN
      (show (scale X:ℝ) ≤ 64*(scale X:ℝ) by nlinarith)
    change Real.log (3*X:ℕ) ≤ _
    dsimp [scale] at hh hmargin
    linarith
  have hNN : ((3*X:ℕ):ℝ)+1 ≤ 4*(X:ℝ) := by
    have : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1≤X)
    push_cast
    linarith
  exact (global_band_energy (3*X) (centralStart X y) (centralWidth X)
    hupper (majorArcs X)ᶜ (majorArcs_measurable X).compl).trans
    (mul_le_mul hNN (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlog 2)
      (sq_nonneg _) (by positivity))

/-- Final counting step, stated against the actual local minor-arc estimate. -/
theorem frozen_target_of_local_minor (hlocal : localMinorBound) :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p =>
      p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y ≤ 2*X →
      ((((Finset.Icc y (y+Nat.sqrt X)).filter
        (fun n => Even n ∧ H n=0)).card):ℝ) ≤ ε*(Nat.sqrt X:ℝ) := by
  intro H ε hε
  let C : ℝ := 24*(1+4*Real.pi)*4096^2
  have hgrowth : ∀ᶠ X : ℕ in atTop, C ≤ ε*(logScale X:ℝ) := by
    have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp logScale_tendsto
    filter_upwards [ht.eventually_ge_atTop (C/ε)] with X hX
    simpa only [Function.comp_apply,mul_comm] using (div_le_iff₀ hε).mp hX
  have he : ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2*X →
      ((centralHoles X y).card:ℝ) ≤ ε*(Nat.sqrt X:ℝ) := by
    filter_upwards [hlocal, eventually_major_minor_package,
      eventual_global_band_energy, hgrowth] with X hlocal hmain hglobal hgrowth
    intro y hy hy2
    have hX : 0<X := by omega
    have hXr : 0<(X:ℝ) := by exact_mod_cast hX
    have hroot : 0<Nat.sqrt X := Nat.sqrt_pos.2 hX
    have hrootR : 0<(Nat.sqrt X:ℝ) := by exact_mod_cast hroot
    have hgr : 0<(logScale X:ℝ) := by exact_mod_cast logScale_pos X
    have hS : Continuous (BulkCircle.S (centralStart X y) (centralWidth X)) := by
      unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
      fun_prop
    have hb := masked_square_window_bessel (Nat.sqrt X) y hroot (majorArcs X)ᶜ
      (majorArcs_measurable X).compl _ hS ((3*X:ℝ)/(logScale X:ℝ)^3)
      (by positivity) (hlocal y hy hy2)
    simp_rw [←minorCoefficient_eq_masked] at hb
    have hsmall : (∑ n ∈ evenWindow X y, ‖minorCoefficient X y n‖^2) ≤
        (ε*(Nat.sqrt X:ℝ))*((X:ℝ)/4096)^2 := by
      calc
        _ ≤ ∑ n ∈ Icc y (y+Nat.sqrt X), ‖minorCoefficient X y n‖^2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
        _ ≤ _ := hb
        _ ≤ (2*(1+4*Real.pi)*(Nat.sqrt X:ℝ)*((3*X:ℝ)/(logScale X:ℝ)^3))*
            ((4*(X:ℝ))*(logScale X:ℝ)^2) := by
          exact mul_le_mul_of_nonneg_left (hglobal y hy hy2) (by positivity)
        _ = (24*(1+4*Real.pi)*(Nat.sqrt X:ℝ)*(X:ℝ)^2)/(logScale X:ℝ) := by
          field_simp
          ring
        _ ≤ _ := by
          apply (div_le_iff₀ hgr).mpr
          have hm := mul_le_mul_of_nonneg_right hgrowth
            (show 0 ≤ (Nat.sqrt X:ℝ)*((X:ℝ)/4096)^2 by positivity)
          dsimp [C] at hm
          convert hm using 1 <;> ring
    exact centralHoles_card_le_of_complex_energy X y
      (majorCoefficient X y) (minorCoefficient X y) ((X:ℝ)/4096)
      (ε*(Nat.sqrt X:ℝ)) (by positivity)
      (fun n hn => (hmain.2 y hy hy2 n hn).1)
      (fun n hn => (hmain.2 y hy hy2 n hn).2) hsmall
  exact eventually_atTop.mp he

end
end GoldbachBeaumontFinish

end

/- Source: BeaumontHeathBrown.lean -/
section

/-!
Finite Heath--Brown identity and coefficient bounds adapted from
CGandGameEngineLearner/goldbach-proofs, ShortProgressionsMeanTheta.lean,
SHA256 15330d5abe787aaf6554ebf45c92afb4b1754d44e171332573907a7ea24013e7. The original proof attributes the finite identity to
D. Koukoulopoulos, Primes in short arithmetic progressions, arXiv:1405.6592.
The harmonic convolution proof retains its upstream Apache-2.0 notices below.
-/
section

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace GoldbachBeaumontDivisor
private abbrev tau (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.zeta ^ k

/-- Every divisor of ab has a factorization into a divisor of a times one of b.
Counting all pairs only increases the sum. -/
private theorem divisor_product_cover (f : ℕ → ℕ) (a b : ℕ) :
    (∑ d ∈ (a*b).divisors, f d) ≤ ∑ u ∈ a.divisors, ∑ v ∈ b.divisors, f (u*v) := by
  classical
  let S := a.divisors ×ˢ b.divisors
  have hcov : (a*b).divisors ⊆ S.image (fun p : ℕ × ℕ => p.1*p.2) := by
    intro d hd
    obtain ⟨hd,hab⟩ := Nat.mem_divisors.mp hd
    obtain ⟨u,v,hu,hv,he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    apply mem_image.mpr
    exact ⟨(u,v), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hu,left_ne_zero_of_mul hab⟩,
      Nat.mem_divisors.mpr ⟨hv,right_ne_zero_of_mul hab⟩⟩, he.symm⟩
  calc _ ≤ ∑ d ∈ S.image (fun p : ℕ × ℕ => p.1*p.2), f d := sum_le_sum_of_subset hcov
       _ ≤ ∑ p ∈ S, f (p.1*p.2) := sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
       _ = _ := Finset.sum_product ..

private theorem tau_submul (k a b : ℕ) : tau k (a*b) ≤ tau k a * tau k b := by
  induction k generalizing a b with
  | zero =>
    by_cases ha : a = 1 <;> by_cases hb : b = 1 <;>
      simp [tau, ha, hb]
  | succ k ih =>
    simp only [tau, pow_succ, ArithmeticFunction.mul_zeta_apply]
    refine (divisor_product_cover _ a b).trans ?_
    rw [sum_mul_sum]
    exact sum_le_sum fun u _ => sum_le_sum fun v _ => ih u v

/-- The usual pointwise coefficient majorant τ_k(n)τ_m(n) ≤ τ_{km}(n),
including repeated prime factors. -/
theorem divisor_tuple_mul_le (k m n : ℕ) : tau k n * tau m n ≤ tau (k*m) n := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 1
    · subst n
      have h : (tau m).IsMultiplicative := isMultiplicative_zeta.pow
      simp [h.map_one, tau]
    · simp [tau, hn]
  | succ k ih =>
    rw [Nat.succ_mul, tau, pow_succ, ArithmeticFunction.mul_apply, Finset.sum_mul]
    change _ ≤ (ArithmeticFunction.zeta^(k*m+m)) n
    rw [pow_add, ArithmeticFunction.mul_apply]
    refine sum_le_sum fun d hd => ?_
    obtain ⟨hprod,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hd
    have hpos : d.2 ≠ 0 := by rintro h; simp [h] at hprod; omega
    simp only [ArithmeticFunction.zeta_apply_ne hpos, mul_one]
    calc
      _ ≤ tau k d.1 * (tau m d.1 * tau m d.2) := by
        apply Nat.mul_le_mul_left
        simpa only [hprod] using tau_submul m d.1 d.2
      _ = (tau k d.1 * tau m d.1) * tau m d.2 := (Nat.mul_assoc ..).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (ih d.1)

/-- Finite convolution and harmonic-sum bounds adapted from OpenAI's
openai/math, OAI.NumberTheory.EgyptianFractions.DivisorTupleBounds (Apache-2.0),
revision 3344da59991ed94f9ba711217b29c1d760badfa6, via BinaryShiftShortMixedEnergy
in goldbach-proofs, 78cbbee038c13a0f164cbbd96639a17feccb3d87. -/
private lemma sum_divisorsAntidiagonal_le_rectangle (N : ℕ)
    (F : ℕ × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x) ≤
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, F x := by
  have hdisj : Set.PairwiseDisjoint (Icc 1 N : Finset ℕ)
      Nat.divisorsAntidiagonal := by
    intro n hn m hm hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact hnm ((Nat.mem_divisorsAntidiagonal.mp hxn).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hxm).1)
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_biUnion.mp hx
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxn
    have ha : 0 < x.1 := by
      by_contra h
      have : x.1 = 0 := by omega
      simp [this] at hprod
      omega
    have hb : 0 < x.2 := by
      by_contra h
      have : x.2 = 0 := by omega
      simp [this] at hprod
      omega
    have haN : x.1 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.2, hprod.symm⟩).trans (mem_Icc.mp hn).2
    have hbN : x.2 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.1, by simpa [Nat.mul_comm] using hprod.symm⟩).trans (mem_Icc.mp hn).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩
  · intro x hx hxnot
    exact hF x

/-- The harmonic norm on an initial interval is submultiplicative for
Dirichlet convolution of nonnegative arithmetic functions. -/
theorem harmonic_convolution_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((f * g) n : ℝ) / n) ≤
      (∑ a ∈ Icc 1 N, (f a : ℝ) / a) *
      (∑ b ∈ Icc 1 N, (g b : ℝ) / b) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [Nat.cast_mul, ← hp, Nat.cast_mul]
      ring
    _ ≤ ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) :=
      sum_divisorsAntidiagonal_le_rectangle N _ (by intro x; positivity)
    _ = _ := by rw [sum_product, sum_mul_sum]

lemma zeta_harmonic_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.zeta n : ℝ) / n) =
      (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.zeta_apply_ne hn0]

/-- The harmonic sum over ordered `k`-factor tuples has at most the expected
`k` logarithmic factors. -/
theorem divisorTuple_harmonic_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (tau k n : ℝ) / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [tau, pow_zero, ArithmeticFunction.one_apply]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div]
    by_cases hN : 1 ≤ N
    · simp [hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have h := harmonic_convolution_le (ArithmeticFunction.zeta ^ k)
      ArithmeticFunction.zeta N
    rw [zeta_harmonic_sum] at h
    calc
      _ ≤ (∑ n ∈ Icc 1 N, (tau k n : ℝ) / n) *
          (harmonic N : ℝ) := by simpa [tau, pow_succ] using h
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by rw [harmonic, Rat.cast_sum]; positivity)
      _ = _ := (pow_succ _ _).symm

/-- Weighted coefficient energy for the critical-line normalization in
Koukoulopoulos Lemma 3.2, for the entire range of real r ≥ 0. -/
theorem critical_divisor_energy (N m : ℕ) (r : ℝ) (hr : 0 ≤ r) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Icc 1 N, ‖a n‖ ≤ ((ArithmeticFunction.zeta ^ m) n : ℝ) * (Real.log n)^r) :
    (∑ n ∈ Icc 1 N, ‖a n‖^2/(n:ℝ)) ≤
      ((Real.log N)^r)^2 * (1+Real.log N)^(m*m) := by
  have hn (n : ℕ) (h : n ∈ Icc 1 N) : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp h).1
  have hlog (n : ℕ) (h : n ∈ Icc 1 N) : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (mem_Icc.mp h).1)
  have hH : (0:ℝ) ≤ (harmonic N : ℝ) := by rw [harmonic, Rat.cast_sum]; positivity
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ((Real.log N)^r)^2 * (((tau (m*m)) n : ℝ) / n) := by
      apply sum_le_sum
      intro n h
      have hh := pow_le_pow_left₀ (norm_nonneg _) (ha n h) 2
      rw [mul_pow] at hh
      have ht : ((tau m n : ℝ))^2 ≤ (tau (m*m) n : ℝ) := by
        exact_mod_cast (by simpa only [pow_two] using divisor_tuple_mul_le m m n :
          (tau m n)^2 ≤ tau (m*m) n)
      have hl := Real.rpow_le_rpow (hlog n h)
        (Real.log_le_log (hn n h) (by exact_mod_cast (mem_Icc.mp h).2 : (n:ℝ) ≤ N)) hr
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (hn n h).le
      refine hh.trans ?_
      rw [mul_comm (((Real.log N)^r)^2) _]
      exact mul_le_mul ht (pow_le_pow_left₀ (Real.rpow_nonneg (hlog n h) _) hl 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ((divisorTuple_harmonic_le (m*m) N).trans
      (pow_le_pow_left₀ hH (harmonic_le_one_add_log N) _)) (sq_nonneg _)

end GoldbachBeaumontDivisor

end
section

/-!
# Finite Heath--Brown identity

The coefficient identity at the start of §4 of D. Koukoulopoulos,
*Primes in short arithmetic progressions* (arXiv:1405.6592), before any dyadic
or smooth splitting. A term indexed by `j` below has `2 * (j + 1)` factors.

The truncation convention agrees with `truncateArithmetic` in the local
`goldbach-short-progressions/lean/Conjectures/Goldbach/B13BilateralVaughanReduction.lean`.
-/

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace GoldbachBeaumontHeathBrown

noncomputable section


/-- Truncate the coefficients of an arithmetic function to `n ≤ H`. -/
def truncate (f : (ArithmeticFunction ℝ)) (H : ℕ) : (ArithmeticFunction ℝ) := ⟨fun n => if n ≤ H then f n else 0, by simp⟩

@[simp]
theorem truncate_apply (f : (ArithmeticFunction ℝ)) (H n : ℕ) : truncate f H n = if n ≤ H then f n else 0 :=
  rfl

private theorem convolution_vanishes_below {f g : (ArithmeticFunction ℝ)} {a b : ℕ}
    (hf : ∀ n < a, f n = 0) (hg : ∀ n < b, g n = 0) :
    ∀ n < a * b, (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases ha : p.1 < a
  · rw [hf _ ha, zero_mul]
  · have hb : p.2 < b := by
      by_contra! h
      exact (not_le_of_gt hn) (hp' ▸ Nat.mul_le_mul (Nat.le_of_not_gt ha) h)
    rw [hg _ hb, mul_zero]

private theorem power_vanishes_below {f : (ArithmeticFunction ℝ)} {a : ℕ} (hf : ∀ n < a, f n = 0) (k : ℕ) :
    ∀ n < a ^ k, (f ^ k) n = 0 := by
  induction k with
  | zero =>
      intro n hn
      have hn' : n = 0 := by simpa using hn
      simp [hn']
  | succ k ih => simpa only [pow_succ] using convolution_vanishes_below ih hf

/-- The truncated (μ : ArithmeticFunction ℝ)öbius series inverts zeta below the first discarded index.
After taking `k` convolution powers the cutoff becomes `(H + 1)^k`. -/
theorem heathBrown_remainder_vanishes (H k n : ℕ) (hn : n < (H + 1) ^ k) :
    (Λ * (1 - truncate (μ : ArithmeticFunction ℝ) H * (ζ : ArithmeticFunction ℝ)) ^ k) n = 0 := by
  have hinv : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have heq : 1 - truncate (μ : ArithmeticFunction ℝ) H * (ζ : ArithmeticFunction ℝ) = ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) H) * (ζ : ArithmeticFunction ℝ) := by
    rw [sub_mul, hinv]
  have hcut : ∀ m < H + 1, ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) H) m = 0 := by
    intro m hm
    change (μ : ArithmeticFunction ℝ) m - truncate (μ : ArithmeticFunction ℝ) H m = 0
    simp [Nat.le_of_lt_succ hm]
  have hbase (f : (ArithmeticFunction ℝ)) : ∀ m < 1, f m = 0 := by
    intro m hm
    have hm' : m = 0 := by omega
    simp [hm']
  have herror : ∀ m < H + 1, (1 - truncate (μ : ArithmeticFunction ℝ) H * (ζ : ArithmeticFunction ℝ) : (ArithmeticFunction ℝ)) m = 0 := by
    rw [heq]
    simpa only [mul_one] using convolution_vanishes_below hcut (hbase (ζ : ArithmeticFunction ℝ))
  exact convolution_vanishes_below (hbase Λ) (power_vanishes_below herror k)
    n (by simpa using hn)

/-- The convolution product for the `(j+1)`-st term. -/
def block (H j : ℕ) : (ArithmeticFunction ℝ) := ArithmeticFunction.log * (ζ : ArithmeticFunction ℝ) ^ j * (truncate (μ : ArithmeticFunction ℝ) H) ^ (j + 1)

private theorem alternating_expansion (F : (ArithmeticFunction ℝ)) (k : ℕ) :
    1 - (1 - F) ^ k =
      ∑ j ∈ Finset.range k, ((-1 : (ArithmeticFunction ℝ)) ^ j * (k.choose (j + 1) : (ArithmeticFunction ℝ))) * F ^ (j + 1) := by
  rw [sub_eq_add_neg 1 F, add_comm 1 (-F), add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  rw [show 1 - ((∑ j ∈ Finset.range k, (-F) ^ (j + 1) * (k.choose (j + 1) : (ArithmeticFunction ℝ))) + 1) =
      -(∑ j ∈ Finset.range k, (-F) ^ (j + 1) * (k.choose (j + 1) : (ArithmeticFunction ℝ))) by abel,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_pow F (j + 1), pow_succ (-1 : (ArithmeticFunction ℝ)) j]
  ring

private theorem eval_sum {ι : Type*} (S : Finset ι) (f : ι → (ArithmeticFunction ℝ)) (n : ℕ) :
    (∑ i ∈ S, f i) n = ∑ i ∈ S, f i n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [Finset.sum_insert hi, ih]

private theorem coefficient_apply (k j : ℕ) (f : (ArithmeticFunction ℝ)) (n : ℕ) :
    (((-1 : (ArithmeticFunction ℝ)) ^ j * (k.choose (j + 1) : (ArithmeticFunction ℝ))) * f) n =
      ((-1 : ℝ) ^ j * (k.choose (j + 1) : ℝ)) * f n := by
  have hcast (z : ℤ) (f : (ArithmeticFunction ℝ)) : ((z : (ArithmeticFunction ℝ)) * f) n = (z : ℝ) * f n := by
    rw [← zsmul_eq_mul, ← zsmul_eq_mul]
    rfl
  calc
    _ = (((( (-1 : ℤ) ^ j * (k.choose (j + 1) : ℤ)) : ℤ) : (ArithmeticFunction ℝ)) * f) n := by
      push_cast
      rfl
    _ = _ := by
      rw [hcast]
      push_cast
      rfl

/-- Heath--Brown's finite identity, valid at every `n < (H + 1)^k`, including
`n ≤ H^k` for `k > 0`. The untruncated factors are `log` and `j` copies of zeta. -/
theorem heathBrown_apply (H k n : ℕ) (hn : n < (H + 1) ^ k) :
    Λ n = ∑ j ∈ Finset.range k,
      ((-1 : ℝ) ^ j * (k.choose (j + 1) : ℝ)) * block H j n := by
  let F : (ArithmeticFunction ℝ) := truncate (μ : ArithmeticFunction ℝ) H * (ζ : ArithmeticFunction ℝ)
  have hzero : (Λ * (1 - F) ^ k) n = 0 := heathBrown_remainder_vanishes H k n hn
  have hfinite : Λ n = (Λ * (1 - (1 - F) ^ k)) n := by
    rw [mul_sub, mul_one]
    change Λ n = Λ n - (Λ * (1 - F) ^ k) n
    rw [hzero, sub_zero]
  rw [hfinite, alternating_expansion, Finset.mul_sum, eval_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Λ * (((-1 : (ArithmeticFunction ℝ)) ^ j * (k.choose (j + 1) : (ArithmeticFunction ℝ))) * F ^ (j + 1)) =
      ((-1 : (ArithmeticFunction ℝ)) ^ j * (k.choose (j + 1) : (ArithmeticFunction ℝ))) * (Λ * F ^ (j + 1)) by ring,
    coefficient_apply]
  have hblock : Λ * F ^ (j + 1) = block H j := by
    calc
      _ = (Λ * (ζ : ArithmeticFunction ℝ)) * (ζ : ArithmeticFunction ℝ) ^ j * (truncate (μ : ArithmeticFunction ℝ) H) ^ (j + 1) := by
        dsimp only [F]
        rw [mul_pow, pow_succ' (ζ : ArithmeticFunction ℝ)]
        ring
      _ = _ := by rw [ArithmeticFunction.vonMangoldt_mul_zeta]; rfl
  rw [hblock]

/-- The zero-based factor list before inserting smooth or dyadic cutoffs. -/
def factor (H j i : ℕ) : (ArithmeticFunction ℝ) := if i = 0 then ArithmeticFunction.log else if i < j + 1 then (ζ : ArithmeticFunction ℝ) else truncate (μ : ArithmeticFunction ℝ) H

/-- Exactly `j+1` non-(μ : ArithmeticFunction ℝ)öbius factors followed by `j+1` truncated (μ : ArithmeticFunction ℝ)öbius factors. -/
theorem block_eq_prod (H j : ℕ) :
    block H j = ∏ i ∈ Finset.range (2 * (j + 1)), factor H j i := by
  rw [two_mul, Finset.prod_range_add, Finset.prod_range_succ' (factor H j)]
  have hfirst : (∏ i ∈ Finset.range j, factor H j (i + 1)) = (ζ : ArithmeticFunction ℝ) ^ j := by
    calc
      _ = ∏ _i ∈ Finset.range j, (ζ : ArithmeticFunction ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hil : i + 1 < j + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hi)
        simp [factor, hil]
      _ = _ := by simp
  have hsecond : (∏ i ∈ Finset.range (j + 1), factor H j (j + 1 + i)) =
      (truncate (μ : ArithmeticFunction ℝ) H) ^ (j + 1) := by
    calc
      _ = ∏ _i ∈ Finset.range (j + 1), truncate (μ : ArithmeticFunction ℝ) H := by
        apply Finset.prod_congr rfl
        intro i _
        simp [factor, show ¬ (j + 1 + i < j + 1) by omega]
      _ = _ := by simp
  rw [hfirst, hsecond]
  simp [block, factor, mul_comm]

/-- Apply the coefficient formula to any finite collection of terms with a complex
weight. In particular the weight may be a Dirichlet character. -/
theorem heathBrown_weighted_sum (H k : ℕ) (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ n ∈ S, n < (H + 1) ^ k) :
    (∑ n ∈ S, (Λ n : ℂ) * w n) =
      ∑ j ∈ Finset.range k, ((-1 : ℂ) ^ j * (k.choose (j + 1) : ℂ)) *
        ∑ n ∈ S, (block H j n : ℂ) * w n := by
  calc
    _ = ∑ n ∈ S, ∑ j ∈ Finset.range k,
        ((-1 : ℂ) ^ j * (k.choose (j + 1) : ℂ)) * (block H j n : ℂ) * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [heathBrown_apply H k n (hS n hn)]
      push_cast
      rw [Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- The cutoff in the paper is the floor of the real `k`-th root of the
coefficient range. -/
def rangeCutoff (X : ℝ) (k : ℕ) : ℕ := ⌊X ^ (1 / (k : ℝ))⌋₊

theorem lt_rangeCutoff_power {X : ℝ} (hX : 0 ≤ X) {k n : ℕ} (hk : 0 < k) (hn : (n : ℝ) ≤ X) :
    n < (rangeCutoff X k + 1) ^ k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hroot : (X ^ (1 / (k : ℝ))) ^ k = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX, one_div_mul_cancel hk', Real.rpow_one]
  have hf : X ^ (1 / (k : ℝ)) < (rangeCutoff X k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt := pow_lt_pow_left₀ hf (Real.rpow_nonneg hX _) hk.ne'
  rw [hroot] at hlt
  exact_mod_cast hn.trans_lt hlt

/-- Coefficient form with the precise real root cutoff on the window `n ≤ X`. -/
theorem heathBrown_on_real_range {X : ℝ} (hX : 0 ≤ X) {k n : ℕ} (hk : 0 < k) (hn : (n : ℝ) ≤ X) :
    Λ n = ∑ j ∈ Finset.range k,
      ((-1 : ℝ) ^ j * (k.choose (j + 1) : ℝ)) *
        (∏ i ∈ Finset.range (2 * (j + 1)), factor (rangeCutoff X k) j i) n := by
  simp_rw [← block_eq_prod]
  exact heathBrown_apply _ _ _ (lt_rangeCutoff_power hX hk hn)

/-- A real interval `(y, z]` as a finite set of nonnegative integers. -/
def shortWindow (y z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun n => y < (n : ℝ) ∧ (n : ℝ) ≤ z)

@[simp]
theorem mem_shortWindow {y z : ℝ} {n : ℕ} :
    n ∈ shortWindow y z ↔ y < (n : ℝ) ∧ (n : ℝ) ≤ z := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hz : 0 ≤ z := (Nat.cast_nonneg n).trans h.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).2 h.2)), h⟩

/-- The character-twisted finite short-interval identity, with `X = 4*x`
in the application. The upper interval endpoint `z` must satisfy `z ≤ X`. -/
theorem heathBrown_short_window {X y z : ℝ} (hX : 0 ≤ X) (hz : z ≤ X)
    {k q : ℕ} (hk : 0 < k) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ shortWindow y z, (Λ n : ℂ) * χ (n : ZMod q)) =
      ∑ j ∈ Finset.range k, ((-1 : ℂ) ^ j * (k.choose (j + 1) : ℂ)) *
        ∑ n ∈ shortWindow y z,
          ((∏ i ∈ Finset.range (2 * (j + 1)), factor (rangeCutoff X k) j i) n : ℂ) *
            χ (n : ZMod q) := by
  simp_rw [← block_eq_prod]
  apply heathBrown_weighted_sum
  intro n hn
  exact lt_rangeCutoff_power hX hk ((mem_shortWindow.mp hn).2.trans hz)

private theorem convolution_pointwise_congr {X n : ℕ} {a b c d : (ArithmeticFunction ℝ)}
    (ha : ∀ m ≤ X, a m = c m) (hb : ∀ m ≤ X, b m = d m) (hn : n ≤ X) :
    (a * b) n = (c * d) n := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp', hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have h1 : p.1 ∣ n := ⟨p.2, hp'.symm⟩
  have h2 : p.2 ∣ n := ⟨p.1, by simpa only [mul_comm] using hp'.symm⟩
  rw [ha _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h1).trans hn),
    hb _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h2).trans hn)]

private theorem product_pointwise_congr {ι : Type*} (S : Finset ι) {X : ℕ} {a b : ι → (ArithmeticFunction ℝ)}
    (h : ∀ i ∈ S, ∀ n ≤ X, a i n = b i n) :
    ∀ n ≤ X, (∏ i ∈ S, a i) n = (∏ i ∈ S, b i) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
      intro n hn
      simp only [Finset.prod_insert hi]
      exact convolution_pointwise_congr (h i (Finset.mem_insert_self i S))
        (ih fun t ht => h t (Finset.mem_insert_of_mem ht)) hn

/-- Finite localization of a convolution block. Only a partition on coefficients
up to `X` is required. This identity does not assert that a smooth dyadic
partition exists or bound the number of resulting boxes. -/
theorem block_apply_eq_sum_boxes {ι : Type*} (H j X n : ℕ) (hn : n ≤ X)
    (boxes : ℕ → Finset ι) (piece : ℕ → ι → (ArithmeticFunction ℝ))
    (hpiece : ∀ i ∈ Finset.range (2 * (j + 1)), ∀ m ≤ X,
      factor H j i m = (∑ b ∈ boxes i, piece i b) m) :
    let S := Finset.range (2 * (j + 1))
    block H j n = ∑ b ∈ S.pi boxes, (∏ i ∈ S.attach, piece i.1 (b i.1 i.2)) n := by
  dsimp only
  rw [block_eq_prod, product_pointwise_congr _ hpiece n hn, Finset.prod_sum, eval_sum]

end
end GoldbachBeaumontHeathBrown

end
section

namespace GoldbachBeaumontCoefficient

open scoped BigOperators

abbrev AF := ArithmeticFunction ℂ

private theorem convolution_support {f g : AF} {A B : ℕ}
    (hf : ∀ n > A, f n = 0) (hg : ∀ n > B, g n = 0) :
    ∀ n > A*B, (f*g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases ha : A < p.1
  · rw [hf _ ha, zero_mul]
  by_cases hb : B < p.2
  · rw [hg _ hb, mul_zero]
  exact (not_lt_of_ge ((Nat.mem_divisorsAntidiagonal.mp hp).1 ▸
    Nat.mul_le_mul (le_of_not_gt ha) (le_of_not_gt hb))) hn |>.elim

theorem convolution_product_support {ι : Type*} (s : Finset ι) (N : ι → ℕ) (f : ι → AF)
    (hN : ∀ i ∈ s, ∀ n > N i, f i n = 0) :
    ∀ n > ∏ i ∈ s, N i, (∏ i ∈ s, f i) n = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n hn
    rw [Finset.prod_empty] at hn ⊢
    exact ArithmeticFunction.one_apply_ne (Nat.ne_of_gt hn)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact convolution_support (hN i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hN j (Finset.mem_insert_of_mem hj)))

private theorem convolution_coeff {f g : AF} {a b d e : ℕ}
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ ((ArithmeticFunction.zeta^a) n : ℝ) * (Real.log n)^d)
    (hg : ∀ n : ℕ, 1 ≤ n → ‖g n‖ ≤ ((ArithmeticFunction.zeta^b) n : ℝ) * (Real.log n)^e)
    (n : ℕ) : ‖(f*g) n‖ ≤ ((ArithmeticFunction.zeta^(a+b)) n : ℝ) * (Real.log n)^(d+e) := by
  simp only [pow_add ArithmeticFunction.zeta, ArithmeticFunction.mul_apply, Nat.cast_sum, Nat.cast_mul]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2‖ ≤
        ∑ p ∈ n.divisorsAntidiagonal, ‖f p.1 * g p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, (((ArithmeticFunction.zeta^a) p.1 : ℝ) *
        ((ArithmeticFunction.zeta^b) p.2 : ℝ)) * (Real.log n)^(d+e) := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hm, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hp₁ : 0 < p.1 := Nat.pos_of_ne_zero (fun hp' => hn (by rw [← hm, hp', zero_mul]))
      have hp₂ : 0 < p.2 := Nat.pos_of_ne_zero (fun hp' => hn (by rw [← hm, hp', mul_zero]))
      have h₁ : 1 ≤ (p.1 : ℝ) := by exact_mod_cast hp₁
      have h₂ : 1 ≤ (p.2 : ℝ) := by exact_mod_cast hp₂
      have hm₁ : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨p.2, hm.symm⟩
      have hm₂ : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨p.1, by rw [← hm, mul_comm]⟩
      have hl₁ : Real.log (p.1 : ℝ) ≤ Real.log n := Real.log_le_log (by linarith) (by exact_mod_cast hm₁)
      have hl₂ : Real.log (p.2 : ℝ) ≤ Real.log n := Real.log_le_log (by linarith) (by exact_mod_cast hm₂)
      have hleft := (hf p.1 hp₁).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.log_nonneg h₁) hl₁ d) (Nat.cast_nonneg _))
      have hright := (hg p.2 hp₂).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.log_nonneg h₂) hl₂ e) (Nat.cast_nonneg _))
      rw [norm_mul, pow_add]
      exact (mul_le_mul hleft hright (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ = _ := by rw [Finset.sum_mul]

/-- The product of finitely many bounded/logarithmic coefficient sequences has
the expected divisor budget and the sum of their logarithmic exponents. -/
theorem convolution_product_coeff {ι : Type*} (s : Finset ι) (f : ι → AF) (d : ι → ℕ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, 1 ≤ n → ‖f i n‖ ≤ (Real.log n)^d i) (n : ℕ) :
    ‖(∏ i ∈ s, f i) n‖ ≤ ((ArithmeticFunction.zeta^s.card) n : ℝ) *
      (Real.log n)^(∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    by_cases hn : n = 1 <;> simp [hn]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Finset.sum_insert hi, add_comm s.card]
    apply convolution_coeff _ (fun n _ => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) n)
    intro m hm
    simpa [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt hm)] using
      hf i (Finset.mem_insert_self _ _) m hm

end GoldbachBeaumontCoefficient
end

namespace GoldbachBeaumontDivisor
open Finset
open scoped BigOperators

/-- Unweighted coefficient energy for an arbitrary bounded/logarithmic
Dirichlet-convolution block. -/
theorem divisor_energy (N m : ℕ) (r : ℝ) (hr : 0 ≤ r) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Icc 1 N, ‖a n‖ ≤ ((ArithmeticFunction.zeta ^ m) n : ℝ) * (Real.log n)^r) :
    (∑ n ∈ Icc 1 N, ‖a n‖^2) ≤
      (N : ℝ) * (((Real.log N)^r)^2 * (1+Real.log N)^(m*m)) := by
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      ‖a n‖^2 ≤ (N : ℝ) * (‖a n‖^2/(n:ℝ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    calc
      _ = (n : ℝ) * (‖a n‖^2/(n:ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N) (by positivity)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * (‖a n‖^2/(n:ℝ)) := sum_le_sum hpoint
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, ‖a n‖^2/(n:ℝ) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (critical_divisor_energy N m r hr a ha) (Nat.cast_nonneg _)
end GoldbachBeaumontDivisor






namespace GoldbachBeaumontGrouping
open Finset
open scoped BigOperators

/-- Greedy crossing of a product threshold. This is the finite combinatorial
step that creates a Type II block from factors each at most A. -/
theorem exists_subset_prod_between {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    {A : ℝ} (hA : 1 ≤ A) (hv : ∀ i ∈ s, 0 ≤ v i ∧ v i ≤ A)
    (hprod : A ≤ ∏ i ∈ s, v i) :
    ∃ t ⊆ s, A ≤ ∏ i ∈ t, v i ∧ (∏ i ∈ t, v i) ≤ A^2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hAeq : A = 1 := le_antisymm (by simpa using hprod) hA
      exact ⟨∅, by simp, by simp [hAeq], by simp [hAeq]⟩
  | insert i s hi ih =>
      by_cases hs : A ≤ ∏ j ∈ s, v j
      · obtain ⟨t, hts, htlo, hthi⟩ := ih
          (fun j hj => hv j (mem_insert_of_mem hj)) hs
        exact ⟨t, hts.trans (subset_insert _ _), htlo, hthi⟩
      · refine ⟨insert i s, subset_rfl, hprod, ?_⟩
        rw [prod_insert hi, pow_two]
        exact mul_le_mul (hv i (mem_insert_self _ _)).2 (le_of_not_ge hs)
          (prod_nonneg (fun j hj => (hv j (mem_insert_of_mem hj)).1))
          (zero_le_one.trans hA)

/-- Either there is a factor grouping in [A,B], or the entire small-factor
product is below A and at most two factors remain. The parameters are abstract;
for the application A is a power of log X and B is sqrt X divided by that power. -/
theorem typeII_or_two_large {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    {A B X : ℝ} (hA : 1 ≤ A) (hAB : A^2 ≤ B)
    (hv : ∀ i ∈ s, 1 ≤ v i) (hprod : (∏ i ∈ s, v i) ≤ X)
    (hcube : X < B^3) :
    (∃ t ⊆ s, A ≤ ∏ i ∈ t, v i ∧ (∏ i ∈ t, v i) ≤ B) ∨
      ((∏ i ∈ s.filter (fun i => v i < A), v i) < A ∧
        (s.filter (fun i => B < v i)).card ≤ 2 ∧
        ∀ i ∈ s, v i < A ∨ B < v i) := by
  classical
  by_cases hmid : ∃ t ⊆ s, A ≤ ∏ i ∈ t, v i ∧ (∏ i ∈ t, v i) ≤ B
  · exact Or.inl hmid
  right
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := (sq_nonneg A).trans hAB
  have hgap (i : ι) (hi : i ∈ s) : v i < A ∨ B < v i := by
    by_cases hlo : v i < A
    · exact Or.inl hlo
    · right
      by_contra! hhi
      apply hmid
      exact ⟨{i}, singleton_subset_iff.mpr hi, by simpa using (le_of_not_gt hlo),
        by simpa using hhi⟩
  have hsmall : (∏ i ∈ s.filter (fun i => v i < A), v i) < A := by
    by_contra! h
    obtain ⟨t, hts, htlo, hthi⟩ := exists_subset_prod_between
      (s.filter (fun i => v i < A)) v hA (fun i hi =>
        ⟨zero_le_one.trans (hv i (mem_filter.mp hi).1), (mem_filter.mp hi).2.le⟩) h
    exact hmid ⟨t, hts.trans (filter_subset _ _), htlo, hthi.trans hAB⟩
  have hlarge : (s.filter (fun i => B < v i)).card ≤ 2 := by
    by_contra! h
    obtain ⟨t, hts, htcard⟩ := exists_subset_card_eq (by omega :
      3 ≤ (s.filter (fun i => B < v i)).card)
    have hts' : t ⊆ s := hts.trans (filter_subset _ _)
    have hp : B^3 ≤ ∏ i ∈ t, v i := by
      have h := prod_le_prod₀ (s := t) (f := fun _ => B) (g := v)
        (fun _ _ => hB0) (fun i hi => (mem_filter.mp (hts hi)).2.le)
      simpa [htcard] using h
    have hup : (∏ i ∈ t, v i) ≤ ∏ i ∈ s, v i :=
      prod_le_prod_of_subset_of_one_le₀ hts'
        (fun i hi => zero_le_one.trans (hv i (hts' hi))) (fun i hi _ => hv i hi)
    exact (not_le_of_gt hcube) (hp.trans (hup.trans hprod))
  exact ⟨hsmall, hlarge, hgap⟩

/-- A factor constrained by the short Möbius cutoff cannot be one of the
remaining large factors. -/
theorem large_factor_is_smooth {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (smooth : ι → Prop) {B : ℝ}
    (hcut : ∀ i ∈ s, ¬ smooth i → v i ≤ B) {i : ι}
    (hi : i ∈ s.filter (fun i => B < v i)) : smooth i := by
  classical
  by_contra h
  exact (not_le_of_gt (mem_filter.mp hi).2) (hcut i (mem_filter.mp hi).1 h)

end GoldbachBeaumontGrouping

end

/- Source: BeaumontSharpBoxes.lean -/
section

/-! Sharp dyadic boxes for the finite Heath--Brown identity. Every factor uses
[2^b,2^(b+1)); the Möbius factors retain their exact truncation cutoff. -/

namespace GoldbachBeaumontSharpBoxes
open Finset ArithmeticFunction GoldbachBeaumontHeathBrown
open scoped BigOperators Classical ArithmeticFunction.Moebius
noncomputable section

abbrev AF := ArithmeticFunction ℝ

def indices (X : ℕ) : Finset ℕ := range (Nat.log 2 X + 1)

def piece (f : AF) (b : ℕ) : AF :=
  ⟨fun n => if 2^b ≤ n ∧ n < 2^(b+1) then f n else 0, by
    have hp : 0 < (2 : ℕ)^b := pow_pos (by decide) _
    simp [show ¬ (2 : ℕ)^b ≤ 0 by omega]⟩

@[simp] theorem piece_apply (f : AF) (b n : ℕ) :
    piece f b n = if 2^b ≤ n ∧ n < 2^(b+1) then f n else 0 := rfl

private theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → AF) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [sum_insert hi, ih]

/-- Exact sharp partition including n=1 and all dyadic endpoints. -/
theorem piece_partition (X : ℕ) (f : AF) {n : ℕ} (hn : n ≤ X) :
    f n = (∑ b ∈ indices X, piece f b) n := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hj : Nat.log 2 n ∈ indices X := mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right hn))
  rw [eval_sum, sum_eq_single (Nat.log 2 n)]
  · simp [Nat.pow_log_le_self 2 hn0, Nat.lt_pow_succ_log_self (by decide : 1 < 2) n]
  · intro b hb hbj
    have hnot : ¬ (2^b ≤ n ∧ n < 2^(b+1)) := by
      intro hh
      exact hbj (Nat.log_eq_of_pow_le_of_lt_pow hh.1 hh.2).symm
    simp [hnot]
  · exact fun h => (h hj).elim

theorem piece_partition_supported (X : ℕ) (f : AF)
    (hf : ∀ n > X, f n = 0) : f = ∑ b ∈ indices X, piece f b := by
  ext n
  by_cases hn : n ≤ X
  · exact piece_partition X f hn
  · rw [eval_sum]
    simp [hf n (lt_of_not_ge hn)]

theorem piece_support {f : AF} {b n : ℕ} (h : piece f b n ≠ 0) :
    2^b ≤ n ∧ n < 2^(b+1) := by
  by_contra hh
  simp [hh] at h

def isMobius (j i : ℕ) : Bool := decide (j+1 ≤ i)
def slots (j : ℕ) : Finset ℕ := range (2*(j+1))
abbrev Choice (j : ℕ) := ∀ i ∈ slots j, ℕ

def choices (X H j : ℕ) : Finset (Choice j) :=
  (slots j).pi (fun i => indices (if isMobius j i then H else X))
def boxFactor (H j i b : ℕ) : AF := piece (factor H j i) b
def boxProduct (H j : ℕ) (b : Choice j) : AF :=
  ∏ i ∈ (slots j).attach, boxFactor H j i.1 (b i.1 i.2)

theorem factor_partition (X H j i : ℕ) {n : ℕ} (hn : n ≤ X) :
    factor H j i n =
      (∑ b ∈ indices (if isMobius j i then H else X), boxFactor H j i b) n := by
  by_cases hi : j+1 ≤ i
  · have hi0 : i ≠ 0 := by omega
    have hs : ∀ m > H, factor H j i m = 0 := by
      intro m hm
      simp [factor, hi0, not_lt.mpr hi, not_le.mpr hm]
    simpa [isMobius, hi, boxFactor] using
      congrArg (fun f : AF => f n) (piece_partition_supported H (factor H j i) hs)
  · simpa [isMobius, hi, boxFactor] using piece_partition X (factor H j i) hn

theorem block_partition (X H j : ℕ) {n : ℕ} (hn : n ≤ X) :
    block H j n = ∑ b ∈ choices X H j, boxProduct H j b n := by
  exact block_apply_eq_sum_boxes H j X n hn
    (fun i => indices (if isMobius j i then H else X)) (boxFactor H j)
    (fun i _ m hm => factor_partition X H j i hm)

theorem card_choices_le (X H j : ℕ) (hH : H ≤ X) :
    (choices X H j).card ≤ (Nat.log 2 X+1)^(2*(j+1)) := by
  unfold choices
  rw [card_pi]
  have hcap (i : ℕ) : (if isMobius j i then H else X) ≤ X := by
    split
    · exact hH
    · exact le_rfl
  calc
    _ ≤ ∏ i ∈ slots j, (Nat.log 2 X+1) := prod_le_prod fun i _ => by
      simp only [indices, card_range]
      exact Nat.add_le_add_right (Nat.log_mono_right (hcap i)) 1
    _ = _ := by simp [slots]

/-- The exact finite identity after sharp boxing; the complex weight is
arbitrary, so it includes additive characters and moving-window masks. -/
theorem heathBrown_weighted_sum_boxed (X H k : ℕ) (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ n ∈ S, n ≤ X) (hX : X < (H+1)^k) :
    (∑ n ∈ S, (vonMangoldt n : ℂ)*w n) =
      ∑ j ∈ range k, ((-1 : ℂ)^j * (k.choose (j+1) : ℂ)) *
        ∑ b ∈ choices X H j, ∑ n ∈ S, (boxProduct H j b n : ℂ)*w n := by
  rw [heathBrown_weighted_sum H k S w (fun n hn => (hS n hn).trans_lt hX)]
  apply sum_congr rfl
  intro j hj
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [block_partition X H j (hS n hn)]
  push_cast
  rw [sum_mul]

/-- Each sharp box scale is at most its own coefficient cutoff. -/
theorem choice_lower_le {X H j : ℕ} {b : Choice j}
    (hb : b ∈ choices X H j) {i : ℕ} (hi : i ∈ slots j)
    (hcap : (if isMobius j i then H else X) ≠ 0) :
    2^(b i hi) ≤ (if isMobius j i then H else X) := by
  have hbi := mem_pi.mp hb i hi
  have hlo : b i hi ≤ Nat.log 2 (if isMobius j i then H else X) :=
    Nat.le_of_lt_succ (mem_range.mp hbi)
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hlo).trans
    (Nat.pow_log_le_self 2 hcap)

private theorem convolution_coefficient_support {f g : ArithmeticFunction ℝ}
    {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hf : ∀ k : ℕ, f k ≠ 0 → a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (hg : ∀ k : ℕ, g k ≠ 0 → c ≤ (k : ℝ) ∧ (k : ℝ) ≤ d)
    {n : ℕ} (hn : (f * g) n ≠ 0) : a * c ≤ n ∧ (n : ℝ) ≤ b * d := by
  obtain ⟨p, hp, hv⟩ : ∃ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 ≠ 0 := by
    by_contra! h
    exact hn (by rw [ArithmeticFunction.mul_apply]; exact Finset.sum_eq_zero h)
  have hf' := hf p.1 (left_ne_zero_of_mul hv)
  have hg' := hg p.2 (right_ne_zero_of_mul hv)
  have heq : (p.1 : ℝ) * (p.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← heq]
  exact ⟨mul_le_mul hf'.1 hg'.1 hc (Nat.cast_nonneg p.1),
    mul_le_mul hf'.2 hg'.2 (Nat.cast_nonneg p.2) (ha.trans (hf'.1.trans hf'.2))⟩

/-- A nonzero coefficient of a box is supported between the products of the
individual lower and upper endpoints. -/
theorem product_coefficient_support {ι : Type*} (I : Finset ι)
    (f : ι → ArithmeticFunction ℝ) (a b : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ a i)
    (hf : ∀ i ∈ I, ∀ k : ℕ, f i k ≠ 0 → a i ≤ (k : ℝ) ∧ (k : ℝ) ≤ b i)
    {n : ℕ} (hn : (∏ i ∈ I, f i) n ≠ 0) :
    (∏ i ∈ I, a i) ≤ n ∧ (n : ℝ) ≤ ∏ i ∈ I, b i := by
  classical
  induction I using Finset.induction_on generalizing n with
  | empty =>
      have hn' : n = 1 := by
        by_contra h
        exact hn (by simp [h])
      simp [hn']
  | insert i I hi ih =>
      have he : ∀ t ∈ I, t ∈ insert i I := fun _ => Finset.mem_insert_of_mem
      simp only [Finset.prod_insert hi] at hn ⊢
      exact convolution_coefficient_support (hpos i (Finset.mem_insert_self i I))
        (Finset.prod_nonneg (fun t ht => hpos t (he t ht))) (hf i (Finset.mem_insert_self i I))
        (fun k hk => ih (fun t ht => hpos t (he t ht)) (fun t ht => hf t (he t ht)) hk) hn


/-- Exact support bounds for any subproduct of the sharp dyadic factors. -/
theorem subproduct_support {j H : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    {n : ℕ} (hn : (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n ≠ 0) :
    (∏ i ∈ t, ((2 : ℝ)^(b i.1 i.2))) ≤ n ∧
      (n : ℝ) ≤ ∏ i ∈ t, ((2 : ℝ)^(b i.1 i.2 + 1)) := by
  apply product_coefficient_support t _ _ _ (fun _ _ => by positivity) _ hn
  intro i hi k hk
  have h := piece_support (f := factor H j i.1) hk
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2.le

/-- A contributing box has product of upper dyadic lengths at most 2^(number of slots)
times the coefficient cap. This is the constant lost by grouping upper lengths. -/
theorem contributing_upper_product {j H : ℕ} (b : Choice j) {n : ℕ}
    (hn : boxProduct H j b n ≠ 0) :
    (∏ i ∈ (slots j).attach, ((2 : ℝ)^(b i.1 i.2 + 1))) ≤
      (2 : ℝ)^(2*(j+1)) * n := by
  have hs := subproduct_support b (slots j).attach hn
  simp_rw [pow_succ]
  rw [prod_mul_distrib, prod_const]
  rw [mul_comm]
  have hcard : ((slots j).attach).card = 2*(j+1) := by simp [slots]
  rw [hcard]
  exact mul_le_mul_of_nonneg_left hs.1 (by positivity)

/-- The sharp/logarithmic factors use exactly the indicated interval, with
no smooth weight. -/
theorem boxFactor_log (H j b n : ℕ) :
    boxFactor H j 0 b n =
      if 2^b ≤ n ∧ n < 2^(b+1) then Real.log n else 0 := by
  simp [boxFactor, factor, ArithmeticFunction.log_apply]

theorem boxFactor_zeta (H j i b n : ℕ) (hi : i ≠ 0) (hij : i < j+1)
    (hn : n ≠ 0) :
    boxFactor H j i b n = if 2^b ≤ n ∧ n < 2^(b+1) then 1 else 0 := by
  simp [boxFactor, factor, hi, hij, ArithmeticFunction.zeta_apply_ne hn]


/-- Real arithmetic coefficients as a complex arithmetic function. -/
def complexCoeffs (f : AF) : ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ), by simp⟩
@[simp] theorem complexCoeffs_apply (f : AF) (n : ℕ) :
    complexCoeffs f n = (f n : ℂ) := rfl

theorem complexCoeffs_prod {ι : Type*} (s : Finset ι) (f : ι → AF) :
    complexCoeffs (∏ i ∈ s, f i) = ∏ i ∈ s, complexCoeffs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext n
      by_cases h : n = 1 <;> simp [h]
  | insert i s hi ih =>
      simp only [prod_insert hi, ← ih]
      ext n
      simp [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

def logDegree (i : ℕ) : ℕ := if i = 0 then 1 else 0

theorem factor_coeff_bound (H j i b n : ℕ) (hn : 1 ≤ n) :
    ‖complexCoeffs (boxFactor H j i b) n‖ ≤ (Real.log n)^logDegree i := by
  rw [complexCoeffs_apply, Complex.norm_real, Real.norm_eq_abs, boxFactor, piece_apply]
  have hL := Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  split
  · unfold factor logDegree
    split_ifs
    · simp [ArithmeticFunction.log_apply, abs_of_nonneg hL]
    · simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt hn)]
    · rw [truncate_apply]
      split
      · simpa using (show |((μ n : ℤ) : ℝ)| ≤ 1 by exact_mod_cast (@abs_moebius_le_one n))
      · simp
  · simp only [abs_zero]
    exact pow_nonneg hL _

theorem subproduct_coeff_bound {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (n : ℕ) :
    ‖((∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n : ℂ)‖ ≤
      ((ArithmeticFunction.zeta^t.card) n : ℝ) *
        (Real.log n)^(∑ i ∈ t, logDegree i.1) := by
  change ‖complexCoeffs (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n‖ ≤ _
  rw [complexCoeffs_prod]
  exact GoldbachBeaumontCoefficient.convolution_product_coeff t _ _
    (fun i _ n hn => factor_coeff_bound H j i.1 (b i.1 i.2) n hn) n

theorem subproduct_log_degree {j : ℕ} (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) : (∑ i ∈ t, logDegree i.1) ≤ 1 := by
  have h := sum_le_sum_of_subset ht (f := fun i => logDegree i.1)
  have hwhole : (∑ i ∈ (slots j).attach, logDegree i.1) ≤ 1 := by
    rw [sum_attach]
    simp [logDegree, sum_ite_eq', slots]
  exact h.trans hwhole

/-- Exact L2 coefficient budget for any of the two grouped HB factors. -/
theorem subproduct_energy {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (M : ℕ) :
    (∑ n ∈ Icc 1 M, ‖((∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n : ℂ)‖^2) ≤
      (M : ℝ) * (((Real.log M)^(∑ i ∈ t, logDegree i.1))^2 *
        (1+Real.log M)^(t.card*t.card)) := by
  have h := GoldbachBeaumontDivisor.divisor_energy M t.card
    ((∑ i ∈ t, logDegree i.1 : ℕ) : ℝ) (Nat.cast_nonneg _)
    (fun n => ((∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n : ℂ)) (by
      intro n hn
      rw [Real.rpow_natCast]
      exact subproduct_coeff_bound b t n)
  simpa only [Real.rpow_natCast] using h

/-- A convenient uniform HB3 budget. It deliberately allows the full six-factor
moment exponent for either grouped coefficient sequence. -/
theorem subproduct_energy_log38 {j H : ℕ} (hj : j < 3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Icc 1 M, ‖((∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n : ℂ)‖^2) ≤
      (M : ℝ) * (1+Real.log M)^38 := by
  have he := subproduct_energy (H := H) b t M
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hL : 1 ≤ 1+Real.log (M : ℝ) := by linarith
  have hr := subproduct_log_degree t ht
  have hc : t.card ≤ 6 := by
    apply (card_le_card ht).trans
    rw [card_attach, slots, card_range]
    omega
  have hp : (Real.log (M : ℝ))^(∑ i ∈ t, logDegree i.1) ≤ 1+Real.log M := by
    calc
      _ ≤ (1+Real.log (M : ℝ))^(∑ i ∈ t, logDegree i.1) :=
        pow_le_pow_left₀ hlog (by linarith) _
      _ ≤ (1+Real.log (M : ℝ))^1 := pow_le_pow_right₀ hL hr
      _ = _ := pow_one _
  have hpow : (1+Real.log (M : ℝ))^(t.card*t.card) ≤ (1+Real.log M)^36 :=
    pow_le_pow_right₀ hL (by nlinarith)
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
  calc
    _ ≤ (1+Real.log (M : ℝ))^2 * (1+Real.log M)^36 :=
      mul_le_mul (pow_le_pow_left₀ (pow_nonneg hlog _) hp 2) hpow
        (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]

/-- The two coefficient sequences multiply by genuine Dirichlet convolution. -/
theorem split_box_product {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    boxProduct H j b =
      (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) *
      (∏ i ∈ (slots j).attach \ t, boxFactor H j i.1 (b i.1 i.2)) := by
  symm
  rw [mul_comm]
  exact prod_sdiff ht


def upper (j : ℕ) (b : Choice j) (i : {i // i ∈ slots j}) : ℝ :=
  2^(b i.1 i.2 + 1)

/-- The grouping dichotomy for an actual nonzero HB3 box, with its actual sharp
upper lengths. All analytic choices of A and B occur outside this finite result. -/
theorem box_grouping {j H : ℕ} (hj : j < 3) (b : Choice j) {n : ℕ}
    (hn : boxProduct H j b n ≠ 0) {A B X : ℝ}
    (hA : 1 ≤ A) (hAB : A^2 ≤ B) (hnX : (n : ℝ) ≤ X) (hXB : 64*X < B^3) :
    (∃ t ⊆ (slots j).attach,
      A ≤ ∏ i ∈ t, upper j b i ∧ (∏ i ∈ t, upper j b i) ≤ B) ∨
      ((∏ i ∈ (slots j).attach.filter (fun i => upper j b i < A), upper j b i) < A ∧
        ((slots j).attach.filter (fun i => B < upper j b i)).card ≤ 2 ∧
        ∀ i ∈ (slots j).attach, upper j b i < A ∨ B < upper j b i) := by
  have hprod : (∏ i ∈ (slots j).attach, upper j b i) ≤ 64*X := by
    have hs := contributing_upper_product b hn
    have hp : (2 : ℝ)^(2*(j+1)) ≤ 64 := by
      have he : 2*(j+1) ≤ 6 := by omega
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
      norm_num at h ⊢
      exact h
    exact hs.trans (mul_le_mul hp hnX (Nat.cast_nonneg _) (by norm_num))
  exact GoldbachBeaumontGrouping.typeII_or_two_large (slots j).attach (upper j b)
    hA hAB (fun i _ => one_le_pow₀ (by norm_num)) hprod hXB

/-- Under the Möbius cutoff, every large factor of the residual branch is
one of the log/zeta factors. -/
theorem large_box_factor_is_smooth {X H j : ℕ} {b : Choice j}
    (hb : b ∈ choices X H j) (hH : H ≠ 0) {B : ℝ} (hB : 2*(H : ℝ) ≤ B)
    {i : {i // i ∈ slots j}} (hi : B < upper j b i) : i.1 < j+1 := by
  by_contra! hmu
  have hlow := choice_lower_le hb i.2 (by simpa [isMobius, hmu] using hH)
  have hlow' : ((2 : ℝ)^(b i.1 i.2)) ≤ H := by
    exact_mod_cast (by simpa [isMobius, hmu] using hlow : (2 : ℕ)^(b i.1 i.2) ≤ H)
  have hup : upper j b i ≤ 2*(H : ℝ) := by
    dsimp only [upper]
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hlow' (by norm_num)
  exact (not_le_of_gt hi) (hup.trans hB)


end
end GoldbachBeaumontSharpBoxes







end

/- Source: BeaumontBoxBilinear.lean -/
section

open Finset ArithmeticFunction
open scoped BigOperators

namespace GoldbachBeaumontSharpBoxes
noncomputable section

/-- Dirichlet convolution agrees exactly with the finite bilinear coefficient
when its two factors have the indicated finite supports. -/
theorem convolution_eq_bilinear (f g : ArithmeticFunction ℂ) (I K : Finset ℕ)
    (hf : ∀ n ∉ I, f n = 0) (hg : ∀ n ∉ K, g n = 0) (n : ℕ) :
    (f*g) n = GoldbachBeaumontBilinear.bilinearCoefficient I K f g n := by
  classical
  unfold GoldbachBeaumontBilinear.bilinearCoefficient
  by_cases hn : n = 0
  · subst n
    rw [ArithmeticFunction.map_zero]
    symm
    apply sum_eq_zero
    intro m hm
    apply sum_eq_zero
    intro k hk
    by_cases hmk : m*k = 0
    · rcases Nat.mul_eq_zero.mp hmk with hm0 | hk0
      · simp [hm0]
      · simp [hk0]
    · simp [hmk]
  rw [ArithmeticFunction.mul_apply,
    ← sum_product' I K (fun m k => if m*k=n then f m*g k else 0)]
  have heq : n.divisorsAntidiagonal ∩ (I ×ˢ K) =
      (I ×ˢ K).filter (fun p => p.1*p.2 = n) := by
    ext p
    simp only [mem_inter, Nat.mem_divisorsAntidiagonal, mem_filter]
    simp [hn, and_comm]
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal ∩ (I ×ˢ K), f p.1*g p.2 := by
      symm
      apply sum_subset inter_subset_left
      intro p hp hnot
      have hpair : p ∉ I ×ˢ K := fun h => hnot (mem_inter.mpr ⟨hp,h⟩)
      by_cases hm : p.1 ∈ I
      · have hk : p.2 ∉ K := fun h => hpair (mem_product.mpr ⟨hm,h⟩)
        rw [hg p.2 hk, mul_zero]
      · rw [hf p.1 hm, zero_mul]
    _ = _ := by rw [heq, sum_filter]

def lowerNat {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) : ℕ :=
  ∏ i ∈ t, 2^(b i.1 i.2)
def upperNat {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) : ℕ :=
  ∏ i ∈ t, 2^(b i.1 i.2+1)
def rowLength {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) : ℕ :=
  upperNat b t + 1 - lowerNat b t

def groupedCoeff (H j : ℕ) (b : Choice j) (t : Finset {i // i ∈ slots j}) (n : ℕ) : ℂ :=
  ((∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n : ℂ)

theorem lowerNat_pos {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) :
    0 < lowerNat b t := prod_pos (fun _ _ => pow_pos (by decide) _)

theorem upperNat_eq {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) :
    upperNat b t = 2^t.card * lowerNat b t := by
  unfold lowerNat upperNat
  simp_rw [pow_succ]
  rw [prod_mul_distrib, prod_const, mul_comm]

theorem lowerNat_le_upperNat {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) :
    lowerNat b t ≤ upperNat b t := by
  rw [upperNat_eq]
  exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)

theorem row_endpoint {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) :
    lowerNat b t + rowLength b t = upperNat b t + 1 := by
  have h := lowerNat_le_upperNat b t
  unfold rowLength
  omega

theorem row_width_le {j : ℕ} (hj : j < 3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    rowLength b t ≤ 64*lowerNat b t := by
  have hp := lowerNat_pos b t
  have hc : t.card ≤ 6 := by
    apply (card_le_card ht).trans
    rw [card_attach, slots, card_range]
    omega
  have hpow : 2^t.card ≤ (64 : ℕ) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hc
    norm_num at h ⊢
    exact h
  have hu : upperNat b t ≤ 64*lowerNat b t := by
    rw [upperNat_eq]
    exact Nat.mul_le_mul_right _ hpow
  unfold rowLength
  omega

theorem groupedCoeff_support {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) {n : ℕ}
    (hn : groupedCoeff H j b t n ≠ 0) :
    n ∈ Ico (lowerNat b t) (lowerNat b t + rowLength b t) := by
  have hn' : (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2)) n ≠ 0 := by
    intro h
    exact hn (by simp [groupedCoeff,h])
  have hs := subproduct_support b t hn'
  have hL : lowerNat b t ≤ n := by
    unfold lowerNat
    exact_mod_cast hs.1
  have hU : n ≤ upperNat b t := by
    unfold upperNat
    exact_mod_cast hs.2
  rw [row_endpoint]
  exact mem_Ico.mpr ⟨hL, Nat.lt_succ_of_le hU⟩

/-- The exact coefficient identity needed by the actual short-window Type II
estimate. The first row interval has length at most 64 times its start. -/
theorem boxProduct_eq_bilinear {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) (n : ℕ) :
    (boxProduct H j b n : ℂ) =
      GoldbachBeaumontBilinear.bilinearCoefficient
        (Ico (lowerNat b t) (lowerNat b t + rowLength b t))
        (Ico (lowerNat b ((slots j).attach \ t))
          (lowerNat b ((slots j).attach \ t) + rowLength b ((slots j).attach \ t)))
        (groupedCoeff H j b t) (groupedCoeff H j b ((slots j).attach \ t)) n := by
  let f : ArithmeticFunction ℂ := complexCoeffs (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2))
  let g : ArithmeticFunction ℂ := complexCoeffs
    (∏ i ∈ (slots j).attach \ t, boxFactor H j i.1 (b i.1 i.2))
  have hf : ∀ m ∉ Ico (lowerNat b t) (lowerNat b t + rowLength b t), f m = 0 := by
    intro m hm
    by_contra h
    exact hm (groupedCoeff_support b t h)
  have hg : ∀ m ∉ Ico (lowerNat b ((slots j).attach \ t))
      (lowerNat b ((slots j).attach \ t) + rowLength b ((slots j).attach \ t)), g m = 0 := by
    intro m hm
    by_contra h
    exact hm (groupedCoeff_support b ((slots j).attach \ t) h)
  have he : (boxProduct H j b n : ℂ) = (f*g) n := by
    rw [split_box_product b t ht]
    simp [f,g,ArithmeticFunction.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [he]
  exact convolution_eq_bilinear f g _ _ hf hg n

/-- The coefficient L2 on the exact row is bounded by the already verified
full initial-interval coefficient energy. -/
theorem row_energy_le {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) :
    (∑ n ∈ Ico (lowerNat b t) (lowerNat b t + rowLength b t),
      ‖groupedCoeff H j b t n‖^2) ≤
      (upperNat b t : ℝ) *
        (((Real.log (upperNat b t))^(∑ i ∈ t, logDegree i.1))^2 *
          (1+Real.log (upperNat b t))^(t.card*t.card)) := by
  have hsub : Ico (lowerNat b t) (lowerNat b t + rowLength b t) ⊆
      Icc 1 (upperNat b t) := by
    intro n hn
    rw [row_endpoint] at hn
    have hp := lowerNat_pos b t
    have h := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
    (subproduct_energy (H := H) b t (upperNat b t))

/-- The logarithmic coefficient degree is charged once across both grouped
factors, since only the original slot zero contains a logarithm. -/
theorem complementary_degrees {j : ℕ}
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    (∑ i ∈ t, logDegree i.1) + (∑ i ∈ (slots j).attach \ t, logDegree i.1) ≤ 1 := by
  have he := sum_sdiff ht (f := fun i => logDegree i.1)
  have hh : (∑ i ∈ (slots j).attach, logDegree i.1) ≤ 1 := by
    rw [sum_attach]
    simp [logDegree, sum_ite_eq', slots]
  omega

theorem complementary_card_le_six {j : ℕ} (hj : j < 3)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    t.card + ((slots j).attach \ t).card ≤ 6 := by
  have he := card_sdiff_add_card_eq_card ht
  have hh : ((slots j).attach).card ≤ 6 := by
    rw [card_attach, slots, card_range]
    omega
  omega

/-- Even permitting an empty grouped side, the combined divisor/logarithm
moment exponent of the two coefficients is at most 38. -/
theorem paired_coefficient_exponent_le38 {j : ℕ} (hj : j < 3)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    2*(∑ i ∈ t, logDegree i.1) + t.card*t.card +
      2*(∑ i ∈ (slots j).attach \ t, logDegree i.1) +
      ((slots j).attach \ t).card*((slots j).attach \ t).card ≤ 38 := by
  have hd := complementary_degrees t ht
  have hc := complementary_card_le_six hj t ht
  have hsq := Nat.mul_le_mul hc hc
  nlinarith


end
end GoldbachBeaumontSharpBoxes





end

/- Source: BeaumontBoxAssembly.lean -/
section

open Finset ArithmeticFunction
open scoped BigOperators

namespace GoldbachBeaumontSharpBoxes
noncomputable section

/-- A common logarithmic cap for one actual grouped row. -/
theorem row_energy_common {j H : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) {W : ℕ} (hW : upperNat b t ≤ W) :
    (∑ n ∈ Ico (lowerNat b t) (lowerNat b t+rowLength b t),
      ‖groupedCoeff H j b t n‖^2) ≤
      (upperNat b t : ℝ) * (1+Real.log W)^(
        2*(∑ i ∈ t, logDegree i.1) + t.card*t.card) := by
  have hU : 0 < upperNat b t := (lowerNat_pos b t).trans_le (lowerNat_le_upperNat b t)
  have hUr : (0 : ℝ) < upperNat b t := by exact_mod_cast hU
  have hlogU : 0 ≤ Real.log (upperNat b t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hU)
  have hlog : Real.log (upperNat b t : ℝ) ≤ Real.log (W : ℝ) :=
    Real.log_le_log hUr (by exact_mod_cast hW)
  have hlogW : 0 ≤ Real.log (W : ℝ) := hlogU.trans hlog
  have hp := pow_le_pow_left₀ hlogU (show Real.log (upperNat b t : ℝ) ≤ 1+Real.log W by linarith)
    (∑ i ∈ t, logDegree i.1)
  have hp2 := pow_le_pow_left₀ (pow_nonneg hlogU _) hp 2
  have hq := pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log (upperNat b t : ℝ))
    (show 1+Real.log (upperNat b t : ℝ) ≤ 1+Real.log (W : ℝ) by linarith) (t.card*t.card)
  apply (row_energy_le (H := H) b t).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ((1+Real.log W)^(∑ i ∈ t, logDegree i.1))^2 *
        (1+Real.log W)^(t.card*t.card) :=
      mul_le_mul hp2 hq (by positivity) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- The paired L2 bound needed by the actual Type II theorem. -/
theorem paired_row_energy {j H : ℕ} (hj : j < 3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) {W : ℕ}
    (htW : upperNat b t ≤ W) (hcW : upperNat b ((slots j).attach \ t) ≤ W) :
    (∑ n ∈ Ico (lowerNat b t) (lowerNat b t+rowLength b t),
      ‖groupedCoeff H j b t n‖^2) *
      (∑ n ∈ Ico (lowerNat b ((slots j).attach \ t))
        (lowerNat b ((slots j).attach \ t)+rowLength b ((slots j).attach \ t)),
        ‖groupedCoeff H j b ((slots j).attach \ t) n‖^2) ≤
      (upperNat b t : ℝ) * upperNat b ((slots j).attach \ t) * (1+Real.log W)^38 := by
  have htE := row_energy_common (H := H) b t htW
  have hcE := row_energy_common (H := H) b ((slots j).attach \ t) hcW
  have hW : 1 ≤ W := (lowerNat_pos b t).trans_le
    ((lowerNat_le_upperNat b t).trans htW)
  have hL : 1 ≤ 1+Real.log (W : ℝ) := by
    have := Real.log_nonneg (show 1 ≤ (W : ℝ) by exact_mod_cast hW)
    linarith
  have hbase : 0 ≤ (upperNat b t : ℝ) * upperNat b ((slots j).attach \ t) := by positivity
  calc
    _ ≤ ((upperNat b t : ℝ) * (1+Real.log W)^(
        2*(∑ i ∈ t, logDegree i.1) + t.card*t.card)) *
      ((upperNat b ((slots j).attach \ t) : ℝ) * (1+Real.log W)^(
        2*(∑ i ∈ (slots j).attach \ t, logDegree i.1) +
          ((slots j).attach \ t).card*((slots j).attach \ t).card)) :=
        mul_le_mul htE hcE (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = ((upperNat b t : ℝ) * upperNat b ((slots j).attach \ t)) *
      (1+Real.log W)^((2*(∑ i ∈ t, logDegree i.1) + t.card*t.card) +
        (2*(∑ i ∈ (slots j).attach \ t, logDegree i.1) +
          ((slots j).attach \ t).card*((slots j).attach \ t).card)) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by
        have h := paired_coefficient_exponent_le38 hj t ht
        omega)) hbase

/-- Weighted convolution expansion on arbitrary finite supports. -/
theorem weighted_convolution_sum (f g : ArithmeticFunction ℂ) (I K F : Finset ℕ)
    (w : ℕ → ℂ) (hf : ∀ n ∉ I, f n = 0) (hg : ∀ n ∉ K, g n = 0) :
    (∑ n ∈ F, (f*g) n*w n) =
      ∑ m ∈ I, ∑ k ∈ K, if m*k ∈ F then f m*g k*w (m*k) else 0 := by
  simp_rw [convolution_eq_bilinear f g I K hf hg]
  exact GoldbachBeaumontBilinear.bilinearCoefficient_sum I K F f g w

/-- Expanding the remaining two smooth factors after fixing the small product. -/
theorem triple_convolution_sum (f g h : ArithmeticFunction ℂ) (I J K F : Finset ℕ)
    (w : ℕ → ℂ) (hf : ∀ n ∉ I, f n = 0) (hg : ∀ n ∉ J, g n = 0)
    (hh : ∀ n ∉ K, h n = 0) :
    (∑ n ∈ F, (f*(g*h)) n*w n) =
      ∑ s ∈ I, ∑ m ∈ J, ∑ k ∈ K,
        if s*(m*k) ∈ F then f s*g m*h k*w (s*(m*k)) else 0 := by
  classical
  let B := (J ×ˢ K).image (fun p : ℕ × ℕ => p.1*p.2)
  have hmem (m : ℕ) (hm : m ∈ J) (k : ℕ) (hk : k ∈ K) : m*k ∈ B :=
    mem_image.mpr ⟨(m,k), mem_product.mpr ⟨hm,hk⟩, rfl⟩
  have hgh : ∀ n ∉ B, (g*h) n = 0 := by
    intro n hn
    rw [convolution_eq_bilinear g h J K hg hh]
    unfold GoldbachBeaumontBilinear.bilinearCoefficient
    apply sum_eq_zero
    intro m hm
    apply sum_eq_zero
    intro k hk
    have hne : m*k ≠ n := by
      intro he
      exact hn (he ▸ hmem m hm k hk)
    simp [hne]
  rw [weighted_convolution_sum f (g*h) I B F w hf hgh]
  apply sum_congr rfl
  intro s hs
  calc
    _ = f s * ∑ v ∈ B, (g*h) v*(if s*v ∈ F then w (s*v) else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      split_ifs <;> ring
    _ = f s * ∑ m ∈ J, ∑ k ∈ K,
        if m*k ∈ B then g m*h k*(if s*(m*k) ∈ F then w (s*(m*k)) else 0) else 0 := by
      rw [weighted_convolution_sum g h J K B _ hg hh]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [if_pos (hmem m hm k hk)]
      split_ifs <;> ring

/-- Fixing a positive small product scales the exact integer cutoff endpoints. -/
theorem scaled_product_window (s L N v : ℕ) (hs : 0 < s) :
    s*v ∈ Ioc L N ↔ v ∈ Ioc (L/s) (N/s) := by
  simp only [mem_Ioc]
  rw [Nat.div_lt_iff_lt_mul hs, Nat.le_div_iff_mul_le hs]
  simp only [mul_comm]

/-- The phase has the same frequency after fixing the small product. -/
theorem scaled_phase (s v : ℕ) (α : ℝ) :
    GoldbachBeaumontBilinear.E (α*(s*v : ℕ)) =
      GoldbachBeaumontBilinear.E (((s : ℝ)*α)*(v : ℝ)) := by
  congr 1
  push_cast
  ring

def activeChoices (X H j : ℕ) (F : Finset ℕ) : Finset (Choice j) :=
  (choices X H j).filter (fun b => ∃ n ∈ F, boxProduct H j b n ≠ 0)

theorem card_activeChoices_le (X H j : ℕ) (F : Finset ℕ) (hH : H ≤ X) :
    (activeChoices X H j F).card ≤ (Nat.log 2 X+1)^(2*(j+1)) :=
  (card_le_card (filter_subset _ _)).trans (card_choices_le X H j hH)

/-- The exact boxed HB identity with all identically-zero boxes discarded in
one fixed coefficient band F. The retained family is independent of frequency. -/
theorem heathBrown_weighted_sum_active (X H k : ℕ) (F : Finset ℕ) (w : ℕ → ℂ)
    (hF : ∀ n ∈ F, n ≤ X) (hX : X < (H+1)^k) :
    (∑ n ∈ F, (vonMangoldt n : ℂ)*w n) =
      ∑ j ∈ range k, ((-1 : ℂ)^j * (k.choose (j+1) : ℂ)) *
        ∑ b ∈ activeChoices X H j F, ∑ n ∈ F, (boxProduct H j b n : ℂ)*w n := by
  rw [heathBrown_weighted_sum_boxed X H k F w hF hX]
  apply sum_congr rfl
  intro j hj
  congr 1
  symm
  apply sum_subset (filter_subset _ _)
  intro b hb hba
  apply sum_eq_zero
  intro n hn
  have hz : boxProduct H j b n = 0 := by
    by_contra h
    exact hba (mem_filter.mpr ⟨hb,n,hn,h⟩)
  simp [hz]

theorem paired_upper_eq {j : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach) :
    upperNat b t * upperNat b ((slots j).attach \ t) = upperNat b (slots j).attach := by
  unfold upperNat
  rw [mul_comm]
  exact prod_sdiff ht

theorem paired_upper_le {j H : ℕ} (hj : j < 3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    {n X : ℕ} (hn : boxProduct H j b n ≠ 0) (hnX : n ≤ X) :
    upperNat b t * upperNat b ((slots j).attach \ t) ≤ 64*X := by
  rw [paired_upper_eq b t ht]
  have hs := contributing_upper_product b hn
  have hp : (2 : ℝ)^(2*(j+1)) ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2*(j+1) ≤ 6)
    norm_num at h ⊢
    exact h
  have hnX' : (n : ℝ) ≤ X := by exact_mod_cast hnX
  have hbound := hs.trans (mul_le_mul hp hnX' (Nat.cast_nonneg _) (by norm_num))
  unfold upperNat
  exact_mod_cast hbound

/-- A complete finite coefficient-energy budget for an actual contributing HB3
box. This is uniform in the selected Type II grouping. -/
theorem contributing_paired_energy {j H : ℕ} (hj : j < 3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    {n X : ℕ} (hn : boxProduct H j b n ≠ 0) (hnX : n ≤ X) :
    (∑ m ∈ Ico (lowerNat b t) (lowerNat b t+rowLength b t),
      ‖groupedCoeff H j b t m‖^2) *
      (∑ m ∈ Ico (lowerNat b ((slots j).attach \ t))
        (lowerNat b ((slots j).attach \ t)+rowLength b ((slots j).attach \ t)),
        ‖groupedCoeff H j b ((slots j).attach \ t) m‖^2) ≤
      64*(X : ℝ) * (1+Real.log (64*(X : ℝ)))^38 := by
  have hp := paired_upper_le hj b t ht hn hnX
  have htpos : 0 < upperNat b t := (lowerNat_pos b t).trans_le (lowerNat_le_upperNat b t)
  have hcpos : 0 < upperNat b ((slots j).attach \ t) :=
    (lowerNat_pos b _).trans_le (lowerNat_le_upperNat b _)
  have htW : upperNat b t ≤ 64*X := (Nat.le_mul_of_pos_right _ hcpos).trans hp
  have hcW : upperNat b ((slots j).attach \ t) ≤ 64*X :=
    (Nat.le_mul_of_pos_left _ htpos).trans hp
  have he := paired_row_energy (H := H) hj b t ht htW hcW
  have hp' : (upperNat b t : ℝ) * upperNat b ((slots j).attach \ t) ≤ 64*(X : ℝ) := by
    exact_mod_cast hp
  apply he.trans
  push_cast
  exact mul_le_mul_of_nonneg_right hp' (by positivity)


end
end GoldbachBeaumontSharpBoxes





end

/- Source: BeaumontResidualBoxes.lean -/
section

open Finset ArithmeticFunction
open scoped BigOperators

namespace GoldbachBeaumontSharpBoxes
noncomputable section

def groupAF (H j : ℕ) (b : Choice j) (t : Finset {i // i ∈ slots j}) : ArithmeticFunction ℂ :=
  complexCoeffs (∏ i ∈ t, boxFactor H j i.1 (b i.1 i.2))
def groupInterval {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) : Finset ℕ :=
  Ico (lowerNat b t) (lowerNat b t+rowLength b t)
def slotAF (H j : ℕ) (b : Choice j) (i : {i // i ∈ slots j}) : ArithmeticFunction ℂ :=
  complexCoeffs (boxFactor H j i.1 (b i.1 i.2))
def slotInterval {j : ℕ} (b : Choice j) (i : {i // i ∈ slots j}) : Finset ℕ :=
  Ico (2^(b i.1 i.2)) (2^(b i.1 i.2+1))

theorem groupAF_support {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j}) :
    ∀ n ∉ groupInterval b t, groupAF H j b t n = 0 := by
  intro n hn
  by_contra h
  exact hn (groupedCoeff_support b t h)

theorem slotAF_support {H j : ℕ} (b : Choice j) (i : {i // i ∈ slots j}) :
    ∀ n ∉ slotInterval b i, slotAF H j b i n = 0 := by
  intro n hn
  have hz : boxFactor H j i.1 (b i.1 i.2) n = 0 := by
    by_contra h
    exact hn (mem_Ico.mpr (piece_support h))
  simp [slotAF,hz]

theorem mem_groupInterval_pos {j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    {n : ℕ} (hn : n ∈ groupInterval b t) : 0 < n :=
  (lowerNat_pos b t).trans_le (mem_Ico.mp hn).1

theorem complexCoeffs_mul (f g : AF) :
    complexCoeffs (f*g) = complexCoeffs f * complexCoeffs g := by
  ext n
  simp [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

theorem complex_box_split {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) :
    complexCoeffs (boxProduct H j b) =
      groupAF H j b t * groupAF H j b ((slots j).attach \ t) := by
  rw [split_box_product b t ht, complexCoeffs_mul]
  rfl

/-- If no large factor remains, the entire contribution is already supported
on the grouped small-product interval. -/
theorem residual_zero_sum {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) (hlarge : (slots j).attach \ t = ∅)
    (F : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ F, (boxProduct H j b n : ℂ)*w n) =
      ∑ s ∈ groupInterval b t, if s ∈ F then groupedCoeff H j b t s*w s else 0 := by
  have he : groupAF H j b ((slots j).attach \ t) = 1 := by
    ext n
    by_cases hn : n = 1 <;> simp [groupAF,hlarge,hn]
  change (∑ n ∈ F, complexCoeffs (boxProduct H j b) n*w n) = _
  rw [complex_box_split b t ht, he]
  have h := weighted_convolution_sum (groupAF H j b t) (1 : ArithmeticFunction ℂ)
    (groupInterval b t) {1} F w (groupAF_support b t) (by
      intro n hn
      exact ArithmeticFunction.one_apply_ne (by simpa using hn))
  simpa [groupAF,groupedCoeff] using h

/-- Actual one-large-factor residual identity. -/
theorem residual_one_sum {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) (i : {i // i ∈ slots j})
    (hlarge : (slots j).attach \ t = {i}) (F : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ F, (boxProduct H j b n : ℂ)*w n) =
      ∑ s ∈ groupInterval b t, ∑ m ∈ slotInterval b i,
        if s*m ∈ F then groupedCoeff H j b t s * slotAF H j b i m * w (s*m) else 0 := by
  have he : groupAF H j b ((slots j).attach \ t) = slotAF H j b i := by
    simp [groupAF,hlarge,slotAF]
  change (∑ n ∈ F, complexCoeffs (boxProduct H j b) n*w n) = _
  rw [complex_box_split b t ht, he]
  exact weighted_convolution_sum _ _ _ _ F w (groupAF_support b t) (slotAF_support b i)

/-- Actual two-large-factor residual identity. The remaining small factors have
already been grouped into their exact product coefficient at s. -/
theorem residual_two_sum {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) (i k : {i // i ∈ slots j}) (hik : i ≠ k)
    (hlarge : (slots j).attach \ t = {i,k}) (F : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ F, (boxProduct H j b n : ℂ)*w n) =
      ∑ s ∈ groupInterval b t, ∑ m ∈ slotInterval b i, ∑ r ∈ slotInterval b k,
        if s*(m*r) ∈ F then
          groupedCoeff H j b t s * slotAF H j b i m * slotAF H j b k r * w (s*(m*r))
        else 0 := by
  have he : groupAF H j b ((slots j).attach \ t) = slotAF H j b i * slotAF H j b k := by
    have hnot : i ∉ ({k} : Finset {i // i ∈ slots j}) := by simpa using hik
    simp only [groupAF, hlarge, prod_insert hnot, prod_singleton]
    rw [complexCoeffs_mul]
    rfl
  change (∑ n ∈ F, complexCoeffs (boxProduct H j b) n*w n) = _
  rw [complex_box_split b t ht, he]
  exact triple_convolution_sum _ _ _ _ _ _ F w
    (groupAF_support b t) (slotAF_support b i) (slotAF_support b k)

def slotLinear (H j : ℕ) (b : Choice j) (i : {i // i ∈ slots j})
    (L N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ slotInterval b i, if m ∈ Ioc L N then
    slotAF H j b i m * GoldbachBeaumontBilinear.E (α*(m : ℝ)) else 0

def slotRectangle (H j : ℕ) (b : Choice j) (i k : {i // i ∈ slots j})
    (L N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ slotInterval b i, ∑ r ∈ slotInterval b k,
    if m*r ∈ Ioc L N then slotAF H j b i m * slotAF H j b k r *
      GoldbachBeaumontBilinear.E (α*(m*r : ℕ)) else 0

/-- The residual branch with one smooth factor, exact integer scaled endpoints
and the actual scaled additive frequency. -/
theorem residual_one_phase {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) (i : {i // i ∈ slots j})
    (hlarge : (slots j).attach \ t = {i}) (L N : ℕ) (α : ℝ) :
    (∑ n ∈ Ioc L N, (boxProduct H j b n : ℂ)*GoldbachBeaumontBilinear.E (α*(n : ℝ))) =
      ∑ s ∈ groupInterval b t, groupedCoeff H j b t s *
        slotLinear H j b i (L/s) (N/s) ((s : ℝ)*α) := by
  rw [residual_one_sum b t ht i hlarge]
  apply sum_congr rfl
  intro s hs
  have hs0 := mem_groupInterval_pos b t hs
  unfold slotLinear
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  simp only [scaled_product_window s L N m hs0, scaled_phase s m α]
  split_ifs <;> ring

/-- The residual branch with two smooth factors is an outer sum over positive
small products s of exact rectangles at cutoffs floor(L/s), floor(N/s). -/
theorem residual_two_phase {H j : ℕ} (b : Choice j) (t : Finset {i // i ∈ slots j})
    (ht : t ⊆ (slots j).attach) (i k : {i // i ∈ slots j}) (hik : i ≠ k)
    (hlarge : (slots j).attach \ t = {i,k}) (L N : ℕ) (α : ℝ) :
    (∑ n ∈ Ioc L N, (boxProduct H j b n : ℂ)*GoldbachBeaumontBilinear.E (α*(n : ℝ))) =
      ∑ s ∈ groupInterval b t, groupedCoeff H j b t s *
        slotRectangle H j b i k (L/s) (N/s) ((s : ℝ)*α) := by
  rw [residual_two_sum b t ht i k hik hlarge]
  apply sum_congr rfl
  intro s hs
  have hs0 := mem_groupInterval_pos b t hs
  unfold slotRectangle
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro r hr
  simp only [scaled_product_window s L N (m*r) hs0, scaled_phase s (m*r) α]
  split_ifs <;> ring

/-- On a smooth slot the sharp box coefficient is exactly 1 or log, without
any additional cutoff weight. -/
theorem smooth_slot_value {H j : ℕ} (b : Choice j) (i : {i // i ∈ slots j})
    (hi : i.1 < j+1) {n : ℕ} (hn : n ∈ slotInterval b i) :
    slotAF H j b i n = if i.1=0 then (Real.log n : ℂ) else 1 := by
  have hpow : 0 < (2 : ℕ)^(b i.1 i.2) := pow_pos (by decide) _
  have hn0 : n ≠ 0 := Nat.ne_of_gt (hpow.trans_le (mem_Ico.mp hn).1)
  have hn' := mem_Ico.mp hn
  unfold slotAF
  rw [complexCoeffs_apply, boxFactor, piece_apply, if_pos hn']
  by_cases hi0 : i.1=0
  · simp only [GoldbachBeaumontHeathBrown.factor, hi0, if_pos rfl, ite_true, ArithmeticFunction.log_apply]
  · simp [GoldbachBeaumontHeathBrown.factor, hi0, hi, ArithmeticFunction.zeta_apply_ne hn0]

end
end GoldbachBeaumontSharpBoxes



end

/- Source: BeaumontHBEnergy.lean -/
section

open Finset MeasureTheory ArithmeticFunction
open scoped BigOperators

namespace GoldbachBeaumontSharpBoxes
noncomputable section

def coefficientPolynomial (F : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ F, c n * GoldbachBeaumontBilinear.E (θ*(n : ℝ))

theorem coefficientPolynomial_cont (F : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (coefficientPolynomial F c) := by
  unfold coefficientPolynomial GoldbachBeaumontBilinear.E
  fun_prop

def boxPrefix (H j : ℕ) (b : Choice j) (C : ℕ) (θ : ℝ) : ℂ :=
  coefficientPolynomial (Ioc 0 C) (fun n => (boxProduct H j b n : ℂ)) θ

def mangoldtPrefix (C : ℕ) (θ : ℝ) : ℂ :=
  coefficientPolynomial (Ioc 0 C) (fun n => (vonMangoldt n : ℂ)) θ

theorem norm_finset_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  have hc := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
  exact h.trans hc

theorem integral_finset_sum_sq {ι : Type*} (s : Finset ι) (P : ι → ℝ → ℂ)
    (hP : ∀ i, Continuous (P i)) (a b : ℝ) (hab : a ≤ b) :
    (∫ θ in a..b, ‖∑ i ∈ s, P i θ‖^2) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ θ in a..b, ‖P i θ‖^2 := by
  have hsum : Continuous (fun θ => ∑ i ∈ s, P i θ) :=
    continuous_finsetSum _ (fun i _ => hP i)
  have hsq : Continuous (fun θ => ∑ i ∈ s, ‖P i θ‖^2) :=
    continuous_finsetSum _ (fun i _ => (hP i).norm.pow 2)
  have h := intervalIntegral.integral_mono (μ := volume) hab
    ((hsum.norm.pow 2).intervalIntegrable a b)
    ((continuous_const.mul hsq).intervalIntegrable a b)
    (fun θ => norm_finset_sum_sq s (fun i => P i θ))
  change (∫ θ in a..b, ‖∑ i ∈ s, P i θ‖^2) ≤
    ∫ θ in a..b, (s.card : ℝ)*(∑ i ∈ s, ‖P i θ‖^2) at h
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (s := s) (f := fun i θ => ‖P i θ‖^2)
      (fun i _ => ((hP i).norm.pow 2).intervalIntegrable a b)] at h
  exact h

/-- Exact HB3 cell-energy assembly. All analytic input is the actual cell
energy of each active fixed-band box; there is no proxy coefficient sequence. -/
theorem mangoldt_prefix_energy (N H C : ℕ) (hCN : C ≤ N) (hHN : H ≤ N)
    (hcut : N < (H+1)^3) (g a b : ℝ) (hg : 16 ≤ g) (hab : a ≤ b)
    (hlog : ((Nat.log 2 N+1 : ℕ) : ℝ) ≤ 2*g)
    (hbox : ∀ j < 3, ∀ z ∈ activeChoices N H j (Ioc 0 C),
      (∫ θ in a..b, ‖boxPrefix H j z C θ‖^2) ≤ (N : ℝ)/g^30) :
    (∫ θ in a..b, ‖mangoldtPrefix C θ‖^2) ≤ (N : ℝ)/g^10 := by
  let B : ℝ := (2*g)^6
  let E : ℝ := (N : ℝ)/g^30
  let J := fun j => activeChoices N H j (Ioc 0 C)
  let S := fun (j : ℕ) (θ : ℝ) => ∑ z ∈ J j, boxPrefix H j z C θ
  let c := fun j : ℕ => (-1 : ℂ)^j * ((3 : ℕ).choose (j+1) : ℂ)
  have hg0 : 0 < g := by linarith
  have hB : 0 ≤ B := by positivity
  have hE : 0 ≤ E := by positivity
  have hP (j : ℕ) (z : Choice j) : Continuous (boxPrefix H j z C) :=
    coefficientPolynomial_cont _ _
  have hS (j : ℕ) : Continuous (S j) :=
    continuous_finsetSum _ (fun z _ => hP j z)
  have hcard (j : ℕ) (hj : j < 3) : ((J j).card : ℝ) ≤ B := by
    have hn := card_activeChoices_le N H j (Ioc 0 C) hHN
    have hr : ((J j).card : ℝ) ≤ (((Nat.log 2 N+1 : ℕ) : ℝ))^(2*(j+1)) := by
      exact_mod_cast hn
    have hbase : 1 ≤ ((Nat.log 2 N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (Nat.log 2 N)
    exact hr.trans ((pow_le_pow_right₀ hbase (by omega : 2*(j+1) ≤ 6)).trans
      (pow_le_pow_left₀ (by positivity) hlog 6))
  have hSE (j : ℕ) (hj : j < 3) :
      (∫ θ in a..b, ‖S j θ‖^2) ≤ B^2*E := by
    have hs := integral_finset_sum_sq (J j) (fun z => boxPrefix H j z C) (hP j) a b hab
    have hsums : (∑ z ∈ J j, ∫ θ in a..b, ‖boxPrefix H j z C θ‖^2) ≤ ((J j).card : ℝ)*E := by
      calc
        _ ≤ ∑ _z ∈ J j, E := sum_le_sum (fun z hz => hbox j hj z hz)
        _ = _ := by simp
    calc
      _ ≤ ((J j).card : ℝ) * ∑ z ∈ J j, ∫ θ in a..b, ‖boxPrefix H j z C θ‖^2 := hs
      _ ≤ ((J j).card : ℝ) * (((J j).card : ℝ)*E) :=
        mul_le_mul_of_nonneg_left hsums (Nat.cast_nonneg _)
      _ = ((J j).card : ℝ)^2*E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard j hj) 2) hE
  have hc (j : ℕ) (hj : j ∈ range 3) : ‖c j‖^2 ≤ 9 := by
    have hj' := mem_range.mp hj
    interval_cases j <;> norm_num [c]
  have hsum (θ : ℝ) : mangoldtPrefix C θ = ∑ j ∈ range 3, c j*S j θ := by
    exact heathBrown_weighted_sum_active N H 3 (Ioc 0 C)
      (fun n => GoldbachBeaumontBilinear.E (θ*(n : ℝ)))
      (fun n hn => (mem_Ioc.mp hn).2.trans hCN) hcut
  have hweighted (j : ℕ) (hj : j ∈ range 3) :
      (∫ θ in a..b, ‖c j*S j θ‖^2) ≤ 9*(B^2*E) := by
    have he : (fun θ => ‖c j*S j θ‖^2) = (fun θ => ‖c j‖^2 * ‖S j θ‖^2) := by
      funext θ
      rw [norm_mul, mul_pow]
    rw [he, intervalIntegral.integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hSE j (mem_range.mp hj)) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hc j hj) (by positivity))
  have htotal : (∫ θ in a..b, ‖mangoldtPrefix C θ‖^2) ≤ 81*B^2*E := by
    simp_rw [hsum]
    have h := integral_finset_sum_sq (range 3) (fun j θ => c j*S j θ)
      (fun j => continuous_const.mul (hS j)) a b hab
    have hs := sum_le_sum hweighted
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)
    simp only [card_range, Nat.cast_ofNat] at h
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat] at hm
    exact h.trans (hm.trans_eq (by ring))
  have hbig : (331776 : ℝ) ≤ g^8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hg 8
    norm_num at h
    linarith
  have hratio : (331776 : ℝ)/g^8 ≤ 1 := (div_le_one (pow_pos hg0 _)).2 hbig
  apply htotal.trans
  calc
    _ = ((331776 : ℝ)/g^8)*((N : ℝ)/g^10) := by
      dsimp only [B,E]
      field_simp [hg0.ne']
      ring
    _ ≤ 1*((N : ℝ)/g^10) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := one_mul _

end
end GoldbachBeaumontSharpBoxes

end

/- Source: BeaumontTypeIIBoxes.lean -/
section

open Finset MeasureTheory ArithmeticFunction
open scoped BigOperators

namespace GoldbachBeaumontHigh
noncomputable section
open GoldbachBeaumontBilinear GoldbachBeaumontSharpBoxes

lemma prefixPoly_eq_coefficientPolynomial (C : ℕ) (c : ℕ → ℂ) (hc : c 0=0) (t : ℝ) :
    prefixPoly C c t = coefficientPolynomial (Ioc 0 C) c t := by
  unfold prefixPoly coefficientPolynomial
  rw [Nat.range_succ_eq_Icc_zero,←Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le C)]
  simp [hc]

lemma boxPrefix_eq_prefixPoly {HC j : ℕ} (b : Choice j) (C : ℕ) (t : ℝ) :
    boxPrefix HC j b C t = prefixPoly C (fun n => (boxProduct HC j b n:ℂ)) t := by
  symm
  exact prefixPoly_eq_coefficientPolynomial C _ (by simp) t

lemma mangoldtPrefix_eq_prefixPoly (C : ℕ) (t : ℝ) :
    mangoldtPrefix C t = prefixPoly C (fun n => (vonMangoldt n:ℂ)) t := by
  symm
  exact prefixPoly_eq_coefficientPolynomial C _ (by simp) t

lemma cast_upperNat {j : ℕ} (b : Choice j) (t : Finset {i // i∈slots j}) :
    (upperNat b t:ℝ)=∏ i∈t, upper j b i := by
  simp [upperNat,upper]

/-- A selected actual HB3 grouping gives the required local saving. -/
theorem typeII_box_cell {N HC j C h q : ℕ} (hj : j<3) (b : Choice j)
    (hb : b∈activeChoices N HC j (Ioc 0 C)) (hCN : C≤N)
    (t : Finset {i // i∈slots j}) (ht : t⊆(slots j).attach)
    (α δ g : ℝ) (hg : 128≤g) (hh : 0<h) (hq : 0<q)
    (hδ : 0≤δ) (hwidth : 6*(h:ℝ)*δ≤1)
    (a : ℤ) (hcop : IsCoprime a (q:ℤ))
    (happrox : |α-(a:ℝ)/q|≤1/(q:ℝ)^2)
    (hlo : g^101≤∏ i∈t, upper j b i)
    (hhi : (∏ i∈t, upper j b i)*g^100≤(h:ℝ))
    (hqlo : g^100≤(q:ℝ)) (hqhi : (q:ℝ)*g^100≤(h:ℝ))
    (hlogq : 1+Real.log (2*(q:ℝ))≤g)
    (hlogN : 1+Real.log (64*(N:ℝ))≤g) :
    (∫ θ in α..(α+δ), ‖boxPrefix HC j b C θ‖^2)≤(N:ℝ)/g^30 := by
  have hg0 : 0<g := by linarith
  have hg1 : 1≤g := by linarith
  obtain ⟨n,hn,hnz⟩ := (mem_filter.mp hb).2
  have hnN := (mem_Ioc.mp hn).2.trans hCN
  have hpair := contributing_paired_energy hj b t ht hnz hnN
  let M := lowerNat b t
  let J := rowLength b t
  let K := Ico (lowerNat b ((slots j).attach \ t))
    (lowerNat b ((slots j).attach \ t)+rowLength b ((slots j).attach \ t))
  have hM : 0<M := lowerNat_pos b t
  have hJ : (J:ℝ)≤64*(M:ℝ) := by exact_mod_cast row_width_le hj b t ht
  have hU : (upperNat b t:ℝ)≤65*(M:ℝ) := by
    have he := row_endpoint b t
    have hlen := row_width_le hj b t ht
    have : upperNat b t≤65*M := by dsimp [M]; omega
    exact_mod_cast this
  have hlow : g^101≤(upperNat b t:ℝ) := by simpa only [cast_upperNat] using hlo
  have hMlow : g^100≤(M:ℝ) := by
    have h65 : (65:ℝ)*g^100≤g^101 := by
      calc
        _ ≤ g*g^100 := mul_le_mul_of_nonneg_right (by linarith : (65:ℝ)≤g) (by positivity)
        _ = _ := by ring
    nlinarith [h65.trans (hlow.trans hU)]
  have hMhi : (M:ℝ)*g^100≤(h:ℝ) := by
    have hu : (M:ℝ)≤(upperNat b t:ℝ) := by exact_mod_cast lowerNat_le_upperNat b t
    have hu' : (upperNat b t:ℝ)*g^100≤(h:ℝ) := by
      simpa only [cast_upperNat] using hhi
    exact (mul_le_mul_of_nonneg_right hu (by positivity)).trans hu'
  have hcoeff :
      (∑ m∈Ico M (M+J), ‖groupedCoeff HC j b t m‖^2)*
      (∑ k∈K, ‖groupedCoeff HC j b ((slots j).attach \ t) k‖^2)≤(N:ℝ)*g^50 := by
    have hlog0 : 0≤1+Real.log (64*(N:ℝ)) := by
      have hN : 1≤N := (mem_Ioc.mp hn).1.trans_le hnN
      have hl := Real.log_nonneg (show (1:ℝ)≤64*(N:ℝ) by exact_mod_cast (by omega : 1≤64*N))
      linarith
    have hc : (64:ℝ)≤g^12 :=
      (show (64:ℝ)≤g by linarith).trans (le_self_pow₀ hg1 (by decide : 12≠0))
    calc
      _ ≤ 64*(N:ℝ)*(1+Real.log (64*(N:ℝ)))^38 := hpair
      _ ≤ 64*(N:ℝ)*g^38 := by gcongr
      _ ≤ g^12*(N:ℝ)*g^38 := by gcongr
      _ = _ := by ring
  have he := bilinear_cell_log_saving K (groupedCoeff HC j b t)
    (groupedCoeff HC j b ((slots j).attach \ t)) C M J h q α δ g N
    hM hh hq hδ hwidth a hcop happrox (by linarith) (Nat.cast_nonneg _)
    hMlow hqlo hJ hMhi hqhi hlogq hcoeff
  have hid (θ : ℝ) : boxPrefix HC j b C θ =
      prefixPoly C (bilinearCoefficient (Ico M (M+J)) K
        (groupedCoeff HC j b t) (groupedCoeff HC j b ((slots j).attach \ t))) θ := by
    rw [boxPrefix_eq_prefixPoly]
    congr 1
    funext n
    exact boxProduct_eq_bilinear b t ht n
  simp_rw [hid]
  exact he.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (pow_le_pow_right₀ hg1 (by decide : 30≤40)))

end
end GoldbachBeaumontHigh

end

/- Source: SmoothTransference.lean -/
section

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace GoldbachBeaumontSmooth
noncomputable section

/-- Distinct reduced rational centres have the usual reciprocal-product separation. -/
theorem rational_gap_mul (a b : ℚ) (hne : a ≠ b) :
    1 ≤ (a.den : ℝ) * b.den * |(a : ℝ) - b| := by
  have hcross : a.num * (b.den : ℤ) - b.num * a.den ≠ 0 := by
    intro h
    apply hne
    exact Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp h)
  have hi := Int.one_le_abs hcross
  have hr : (1 : ℝ) ≤ |(a.num : ℝ) * b.den - b.num * a.den| := by exact_mod_cast hi
  have ha : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hb : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  have heq : (a.num : ℝ) * b.den - b.num * a.den =
      (a.den : ℝ) * b.den * ((a : ℝ) - b) := by
    rw [Rat.cast_def a, Rat.cast_def b]
    field_simp
    <;> ring
  rw [heq, abs_mul, abs_of_pos (mul_pos ha hb)] at hr
  exact hr

/-- Changing the approximant resolves an off-centre rational resonance. -/
theorem exists_transferred_approx (α : ℝ) (a : ℚ)
    (hβ : 0 < |α - (a : ℝ)|)
    (hclose : (a.den : ℝ) ^ 2 * |α - (a : ℝ)| ≤ 1) :
    ∃ b : ℚ,
      |α - (b : ℝ)| ≤ 1 / (b.den : ℝ) ^ 2 ∧
      3 / (4 * ((a.den : ℝ) * |α - (a : ℝ)|)) ≤ b.den ∧
      (b.den : ℝ) ≤ 5 / ((a.den : ℝ) * |α - (a : ℝ)|) := by
  let δ : ℝ := (a.den : ℝ) * |α - (a : ℝ)|
  have hq : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hq1 : (1 : ℝ) ≤ a.den := by exact_mod_cast a.pos
  have hδ : 0 < δ := mul_pos hq hβ
  have hqδ : (a.den : ℝ) * δ ≤ 1 := by dsimp [δ]; nlinarith only [hclose]
  have hδ1 : δ ≤ 1 := by nlinarith only [hqδ, hq1, hδ]
  let K : ℕ := ⌈4 / δ⌉₊
  have hKlo : 4 / δ ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) < 4 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKpos : 0 < K := by
    have h := (div_pos (by norm_num : (0 : ℝ) < 4) hδ).trans_le hKlo
    exact_mod_cast h
  have hδK : 4 ≤ δ * K := by
    have h := (div_le_iff₀ hδ).mp hKlo
    nlinarith only [h]
  have hqK : 4 * (a.den : ℝ) ≤ K := by
    have h1 := mul_le_mul_of_nonneg_left hqδ (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith only [hδK, h1, hδ]
  obtain ⟨b, hb, hbK⟩ := Real.exists_rat_abs_sub_le_and_den_le α hKpos
  have hr : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  have hKnon : (0 : ℝ) ≤ K := by positivity
  have hbscaled : ((K : ℝ) + 1) * b.den * |α - (b : ℝ)| ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < ((K : ℝ) + 1) * b.den)).mp hb
    nlinarith only [h]
  have hne : a ≠ b := by
    intro hab
    subst b
    dsimp [δ] at hδK
    nlinarith only [hδK, hbscaled, mul_nonneg hq.le (abs_nonneg (α - (a : ℝ)))]
  have hgap := rational_gap_mul a b hne
  have htri : |(a : ℝ) - b| ≤ |α - (a : ℝ)| + |α - (b : ℝ)| := by
    have h := abs_sub_le (a : ℝ) α (b : ℝ)
    simpa only [abs_sub_comm (a : ℝ) α] using h
  have htriscale := mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ (a.den : ℝ) * b.den)
  have herror : 4 * (a.den : ℝ) * b.den * |α - (b : ℝ)| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (show 4 * (a.den : ℝ) ≤ (K : ℝ) + 1 by linarith)
      (mul_nonneg hr.le (abs_nonneg (α - (b : ℝ))))
    nlinarith only [h, hbscaled]
  have hδr : 3 ≤ 4 * δ * b.den := by
    dsimp [δ]
    nlinarith only [hgap, htriscale, herror]
  refine ⟨b, ?_, ?_, ?_⟩
  · apply hb.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hr)
    have hbr : (b.den : ℝ) ≤ K := by exact_mod_cast hbK
    nlinarith
  · exact (div_le_iff₀ (by positivity : 0 < 4 * δ)).mpr (by nlinarith only [hδr])
  · have hbr : (b.den : ℝ) ≤ K := by exact_mod_cast hbK
    apply (le_div_iff₀ hδ).mpr
    have hKhi' : (K : ℝ) * δ < 4 + δ := by
      have h := mul_lt_mul_of_pos_right hKhi hδ
      have heq : (4 / δ + 1) * δ = 4 + δ := by field_simp <;> ring
      rw [heq] at h
      exact h
    nlinarith [mul_le_mul_of_nonneg_right hbr hδ.le]


open OAI.Problem337

/-- The cap sum supplied by the accepted Vaughan development, with a common log. -/
theorem hyperbolic_caps_common (α : ℝ) (a : ℚ) (N : ℝ) (M : ℕ)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ N) (haN : (a.den : ℝ) ≤ 5 * N)
    (ha : |α - (a : ℝ)| ≤ 1 / (a.den : ℝ) ^ 2) :
    (∑ m ∈ Finset.Icc 1 (M : ℤ),
      RationalPhaseSpacing.truncatedInv (N / (m : ℝ))
        (RationalPhaseSpacing.intDistance (α * m))) ≤
      8 * ((M : ℝ) + a.den + N / a.den) * (1 + Real.log (10 * N)) := by
  have hq : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hq1 : (1 : ℝ) ≤ a.den := by exact_mod_cast a.pos
  have hap : |α - (a.num : ℝ) / a.den| ≤ 1 / (a.den : ℝ) ^ 2 := by
    simpa only [Rat.cast_def] using ha
  have h := RationalPhaseSpacing.sum_truncatedInv_hyperbolic_le
    α a.num a.den a.pos (Rat.isCoprime_num_den a) hap N (by linarith) M
  have hlq : 1 + Real.log (2 * (a.den : ℝ)) ≤ 1 + Real.log (10 * N) := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (a.den : ℝ)) (by linarith : 2 * (a.den : ℝ) ≤ 10 * N)
    linarith
  have hlm : 1 + Real.log ((M : ℝ) + 1) ≤ 1 + Real.log (10 * N) := by
    gcongr
    linarith
  have hl0 : 0 ≤ 1 + Real.log (10 * N) := by
    have := Real.log_nonneg (show 1 ≤ 10 * N by linarith)
    linarith
  calc
    _ ≤ 8 * ((M : ℝ) + a.den) * (1 + Real.log (2 * (a.den : ℝ))) +
        (4 * N / (a.den : ℝ)) * (1 + Real.log ((M : ℝ) + 1)) := h
    _ ≤ 8 * ((M : ℝ) + a.den) * (1 + Real.log (10 * N)) +
        (4 * N / (a.den : ℝ)) * (1 + Real.log (10 * N)) := by gcongr
    _ ≤ _ := by
      have hnq := div_nonneg (show 0 ≤ N by linarith) hq.le
      simp only [mul_div_assoc]
      nlinarith [mul_nonneg hnq hl0]

/-- Scalar peak after Dirichlet transference, including the exact rational centre. -/
def rationalPeak (N q β : ℝ) : ℝ :=
  N / (q * (1 + N * |β|))



theorem rationalPeak_nonneg {N q β : ℝ} (hN : 0 ≤ N) (hq : 0 ≤ q) :
    0 ≤ rationalPeak N q β := by
  unfold rationalPeak
  positivity

/-- Diophantine transference gives a decaying peak, rather than a flat N/q bound. -/
theorem hyperbolic_caps_decay (α : ℝ) (a : ℚ) (N R : ℝ) (M : ℕ)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ N) (hR : 1 ≤ R) (hRN : R ≤ N)
    (hqR : (a.den : ℝ) ≤ R)
    (happrox : |α - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R)) :
    (∑ m ∈ Finset.Icc 1 (M : ℤ),
      RationalPhaseSpacing.truncatedInv (N / (m : ℝ))
        (RationalPhaseSpacing.intDistance (α * m))) ≤
      80 * (1 + Real.log (10 * N)) *
        ((M : ℝ) + R + N / R + rationalPeak N a.den (α - (a : ℝ))) := by
  let q : ℝ := a.den
  let β : ℝ := |α - (a : ℝ)|
  let p : ℝ := rationalPeak N q (α - (a : ℝ))
  let L : ℝ := 1 + Real.log (10 * N)
  have hN0 : 0 < N := by linarith
  have hR0 : 0 < R := by linarith
  have hq : 0 < q := by dsimp [q]; exact_mod_cast a.pos
  have hq1 : 1 ≤ q := by dsimp [q]; exact_mod_cast a.pos
  have hβ : 0 ≤ β := abs_nonneg _
  have hp : 0 ≤ p := rationalPeak_nonneg hN0.le hq.le
  have hL : 0 ≤ L := by
    have := Real.log_nonneg (show 1 ≤ 10 * N by linarith)
    dsimp [L]; linarith
  have hδ : q * β ≤ 1 / R := by
    have hh := mul_le_mul_of_nonneg_left happrox hq.le
    have heq : q * (1 / (q * R)) = 1 / R := by field_simp <;> ring
    change q * β ≤ q * (1 / (q * R)) at hh
    rw [heq] at hh
    exact hh
  have hclose : q ^ 2 * β ≤ 1 := by
    have hqr : q / R ≤ 1 := (div_le_one hR0).mpr hqR
    have hh := mul_le_mul_of_nonneg_left hδ hq.le
    simp only [div_eq_mul_inv, one_mul] at hqr hh
    nlinarith only [hqr, hh]
  have ha : |α - (a : ℝ)| ≤ 1 / (a.den : ℝ) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by nlinarith only [hclose])
  have hpdef : p * (q * (1 + N * β)) = N := by
    dsimp [p, rationalPeak, β]
    exact div_mul_cancel₀ _ (by positivity)
  have hNR : 0 ≤ N / R := div_nonneg hN0.le hR0.le
  by_cases hnear : N * β ≤ 1
  · have hNq : N / q ≤ 2 * p := by
      apply (div_le_iff₀ hq).mpr
      have hh := mul_le_mul_of_nonneg_left hnear (mul_nonneg hp hq.le)
      nlinarith only [hpdef, hh]
    have hh := hyperbolic_caps_common α a N M hN hM (by linarith) ha
    have hcost : (M : ℝ) + q + N / q ≤
        10 * ((M : ℝ) + R + N / R + p) := by
      have hM0 : (0 : ℝ) ≤ M := by positivity
      nlinarith only [hqR, hNq, hM0, hR0, hNR, hp]
    have hmult := mul_le_mul_of_nonneg_right hcost hL
    dsimp [q, L, p] at *
    nlinarith only [hh, hmult]
  · have hfar : 1 < N * β := lt_of_not_ge hnear
    have hβpos : 0 < β := by nlinarith only [hfar, hN0]
    obtain ⟨b, hb, hbmin, hbmax⟩ := exists_transferred_approx α a hβpos hclose
    have hb0 : (0 : ℝ) < b.den := by exact_mod_cast b.pos
    have hqb : 0 < q * β := mul_pos hq hβpos
    have hNδ : 1 ≤ N * (q * β) := by
      have hh := mul_le_mul_of_nonneg_right hq1 (mul_nonneg hN0.le hβ)
      nlinarith only [hfar, hh]
    have hbinN : (b.den : ℝ) ≤ 5 * N := by
      apply hbmax.trans
      exact (div_le_iff₀ hqb).mpr (by nlinarith only [hNδ])
    have hbpeak : (b.den : ℝ) ≤ 10 * p := by
      apply hbmax.trans
      apply (div_le_iff₀ hqb).mpr
      have hh := mul_le_mul_of_nonneg_left (le_of_lt hfar) (mul_nonneg hp hq.le)
      have hn : N * 1 ≤ N * (2 * p * q * β) := by nlinarith only [hpdef, hh]
      have hh' := (mul_le_mul_iff_right₀ hN0).mp hn
      nlinarith only [hh']
    have hbprod : 3 ≤ 4 * (q * β) * b.den := by
      have hh := (div_le_iff₀ (by positivity : 0 < 4 * (q * β))).mp hbmin
      nlinarith only [hh]
    have hNb : N / (b.den : ℝ) ≤ 2 * N / R := by
      have hrδ : R * (q * β) ≤ 1 := by
        simpa only [mul_comm R] using (le_div_iff₀ hR0).mp hδ
      have hh := mul_le_mul_of_nonneg_left hbprod hR0.le
      have hh' := mul_le_mul_of_nonneg_right hrδ hb0.le
      have hRb : R ≤ 2 * (b.den : ℝ) := by nlinarith only [hh, hh']
      apply (div_le_div_iff₀ hb0 hR0).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hRb hN0.le]
    have hh := hyperbolic_caps_common α b N M hN hM hbinN hb
    have hcost : (M : ℝ) + b.den + N / b.den ≤
        10 * ((M : ℝ) + R + N / R + p) := by
      have hM0 : (0 : ℝ) ≤ M := by positivity
      rw [mul_div_assoc] at hNb
      nlinarith only [hbpeak, hNb, hM0, hR0, hNR, hp]
    have hmult := mul_le_mul_of_nonneg_right hcost hL
    dsimp [q, L, p] at *
    nlinarith only [hh, hmult]



end
end GoldbachBeaumontSmooth
end

/- Source: SmoothPeakIntegral.lean -/
section

open MeasureTheory

namespace GoldbachBeaumontSmooth
noncomputable section

/-- The translated Cauchy kernel has uniformly bounded mass on every finite interval. -/
theorem cauchy_kernel_integral {A : ℝ} (hA : 0 < A) (c u v : ℝ) :
    (∫ x in u..v, A ^ 2 / (1 + (A * (x - c)) ^ 2)) ≤ Real.pi * A := by
  have hden (x : ℝ) : (1 + (A * (x - c)) ^ 2) ≠ 0 := by positivity
  have hc : Continuous (fun x : ℝ => A ^ 2 / (1 + (A * (x - c)) ^ 2)) := by
    fun_prop
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => A * Real.arctan (A * (x - c)))
      (A ^ 2 / (1 + (A * (x - c)) ^ 2)) x := by
    convert ((((hasDerivAt_id x).sub_const c).const_mul A).arctan.const_mul A) using 1 <;>
      simp only [id_eq, mul_one, sub_zero] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable u v)]
  have hu := Real.neg_pi_div_two_lt_arctan (A * (u - c))
  have hv := Real.arctan_lt_pi_div_two (A * (v - c))
  nlinarith [mul_lt_mul_of_pos_left hu hA, mul_lt_mul_of_pos_left hv hA]

/-- A rational resonance has mass proportional to N/q². -/
theorem rational_peak_integral {N q : ℝ} (hN : 0 < N) (hq : 0 < q)
    (c u v : ℝ) (huv : u ≤ v) :
    (∫ x in u..v, (N / (q * (1 + N * |x - c|))) ^ 2) ≤ Real.pi * N / q ^ 2 := by
  have hden (x : ℝ) : q * (1 + N * |x - c|) ≠ 0 := by positivity
  have hc : Continuous (fun x : ℝ => (N / (q * (1 + N * |x - c|))) ^ 2) := by fun_prop
  have hd (x : ℝ) : (1 + (N * (x - c)) ^ 2) ≠ 0 := by positivity
  have hc' : Continuous (fun x : ℝ => (q ^ 2)⁻¹ * (N ^ 2 / (1 + (N * (x - c)) ^ 2))) := by fun_prop
  have hp (x : ℝ) : (N / (q * (1 + N * |x - c|))) ^ 2 ≤
      (q ^ 2)⁻¹ * (N ^ 2 / (1 + (N * (x - c)) ^ 2)) := by
    have habs := sq_abs (x - c)
    have hdenle : 1 + (N * (x - c)) ^ 2 ≤ (1 + N * |x - c|) ^ 2 := by
      rw [mul_pow, ← habs]
      nlinarith [mul_nonneg hN.le (abs_nonneg (x - c))]
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg N)
      (show 0 < 1 + (N * (x - c)) ^ 2 by positivity) hdenle
    have hm := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (q ^ 2)⁻¹)
    convert hm using 1 <;> field_simp <;> ring
  calc
    _ ≤ ∫ x in u..v, (q ^ 2)⁻¹ * (N ^ 2 / (1 + (N * (x - c)) ^ 2)) :=
      intervalIntegral.integral_mono_on huv (hc.intervalIntegrable u v)
        (hc'.intervalIntegrable u v) (fun x _ => hp x)
    _ = (q ^ 2)⁻¹ * (∫ x in u..v, N ^ 2 / (1 + (N * (x - c)) ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (q ^ 2)⁻¹ * (Real.pi * N) :=
      mul_le_mul_of_nonneg_left (cauchy_kernel_integral hN c u v) (by positivity)
    _ = _ := by ring


theorem center_scaled_bounds {q R u v t : ℝ} (hq : 0 < q) (hR : 0 < R)
    {a : ℤ} (ht : t ∈ Set.Icc u v) (he : |t - (a : ℝ) / q| ≤ 1 / (q * R)) :
    q * u - 1 / R ≤ a ∧ (a : ℝ) ≤ q * v + 1 / R := by
  have habs : |q * t - (a : ℝ)| ≤ 1 / R := by
    calc
      _ = q * |t - (a : ℝ) / q| := by
        have heq : q * t - (a : ℝ) = q * (t - (a : ℝ) / q) := by field_simp <;> ring
        rw [heq, abs_mul, abs_of_pos hq]
      _ ≤ q * (1 / (q * R)) := mul_le_mul_of_nonneg_left he hq.le
      _ = 1 / R := by field_simp <;> ring
  have htlo := mul_le_mul_of_nonneg_left ht.1 hq.le
  have hthi := mul_le_mul_of_nonneg_left ht.2 hq.le
  have ha := abs_le.mp habs
  constructor <;> linarith

/-- A cell of width v-u meets at most q(v-u)+3 denominator-q rational neighborhoods. -/
theorem active_centers_card {q R u v : ℝ} (hq : 0 < q) (hR : 1 ≤ R)
    (S : Finset ℤ)
    (hS : ∀ a ∈ S, ∃ t ∈ Set.Icc u v, |t - (a : ℝ) / q| ≤ 1 / (q * R))
    (huv : u ≤ v) : (S.card : ℝ) ≤ q * (v - u) + 3 := by
  classical
  by_cases hne : S.Nonempty
  · let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := S.min'_mem hne
    have hhi : hi ∈ S := S.max'_mem hne
    have hle : lo ≤ hi := Finset.min'_le S hi hhi
    have hsub : S ⊆ Finset.Icc lo hi := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S a ha, Finset.le_max' S a ha⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hc
    have hc' : (S.card : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by exact_mod_cast hc
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi + 1 - lo)] at hc'
    have hnat : (S.card : ℤ) + lo ≤ hi + 1 := by omega
    have hreal : (S.card : ℝ) + lo ≤ hi + 1 := by exact_mod_cast hnat
    obtain ⟨t, ht, he⟩ := hS lo hlo
    obtain ⟨s, hs, hf⟩ := hS hi hhi
    have hl := (center_scaled_bounds hq (by linarith : 0 < R) ht he).1
    have hh := (center_scaled_bounds hq (by linarith : 0 < R) hs hf).2
    have hRinv : 1 / R ≤ 1 := (div_le_one (by linarith : 0 < R)).mpr hR
    linarith
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have := mul_nonneg hq.le (sub_nonneg.mpr huv)
    linarith



theorem reciprocal_denominator_sums {P R : ℕ} (hP : 0 < P) (hPR : P ≤ R) :
    (∑ q ∈ Finset.Ioc P R, (q : ℝ)⁻¹) ≤ 1 + Real.log R ∧
      (∑ q ∈ Finset.Ioc P R, ((q : ℝ) ^ 2)⁻¹) ≤ (P : ℝ)⁻¹ := by
  constructor
  · calc
      _ ≤ ∑ q ∈ Finset.Icc 1 R, (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          have hq' := Finset.mem_Ioc.mp hq
          exact Finset.mem_Icc.mpr ⟨by omega, hq'.2⟩
        · intro q _ _; positivity
      _ ≤ _ := by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log R
  · exact (sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt hP) hPR).trans
      (sub_le_self _ (by positivity))

/-- The total resonance mass meeting a cell gains either its width or 1/P. -/
theorem active_peaks_integral {N u v : ℝ} (hN : 0 < N) (huv : u ≤ v)
    {P R : ℕ} (hP : 0 < P) (hPR : P ≤ R)
    (S : ℕ → Finset ℤ)
    (hS : ∀ q ∈ Finset.Ioc P R, ∀ a ∈ S q,
      ∃ t ∈ Set.Icc u v, |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * R)) :
    (∫ t in u..v, ∑ q ∈ Finset.Ioc P R, ∑ a ∈ S q,
      (N / ((q : ℝ) * (1 + N * |t - (a : ℝ) / q|))) ^ 2) ≤
      Real.pi * N * ((v - u) * (1 + Real.log R) + 3 / (P : ℝ)) := by
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hq (q : ℕ) (hq' : q ∈ Finset.Ioc P R) : (0 : ℝ) < q := by
    have := (Finset.mem_Ioc.mp hq').1
    exact_mod_cast (show 0 < q by omega)
  have hc (q : ℕ) (hq' : q ∈ Finset.Ioc P R) (a : ℤ) :
      Continuous (fun t : ℝ => (N / ((q : ℝ) * (1 + N * |t - (a : ℝ) / q|))) ^ 2) := by
    have hden (t : ℝ) : (q : ℝ) * (1 + N * |t - (a : ℝ) / q|) ≠ 0 := by
      have := hq q hq'; positivity
    fun_prop
  rw [intervalIntegral.integral_finsetSum
    (fun q hq' => (continuous_finsetSum (S q) (fun a _ => hc q hq' a)).intervalIntegrable u v)]
  have hmass (q : ℕ) (hq' : q ∈ Finset.Ioc P R) :
      (∫ t in u..v, ∑ a ∈ S q,
        (N / ((q : ℝ) * (1 + N * |t - (a : ℝ) / q|))) ^ 2) ≤
      Real.pi * N * ((v - u) / q + 3 / (q : ℝ) ^ 2) := by
    rw [intervalIntegral.integral_finsetSum (fun a _ => (hc q hq' a).intervalIntegrable u v)]
    have hcard := active_centers_card (hq q hq') hR (S q) (hS q hq') huv
    calc
      _ ≤ ∑ a ∈ S q, Real.pi * N / (q : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun a _ => rational_peak_integral hN (hq q hq') ((a : ℝ) / q) u v huv)
      _ = (S q).card * (Real.pi * N / (q : ℝ) ^ 2) := by simp
      _ ≤ ((q : ℝ) * (v - u) + 3) * (Real.pi * N / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ ∑ q ∈ Finset.Ioc P R, Real.pi * N * ((v - u) / q + 3 / (q : ℝ) ^ 2) :=
      Finset.sum_le_sum hmass
    _ = Real.pi * N * ((v - u) * (∑ q ∈ Finset.Ioc P R, (q : ℝ)⁻¹) +
        3 * (∑ q ∈ Finset.Ioc P R, ((q : ℝ) ^ 2)⁻¹)) := by
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ _ := by
      obtain ⟨h1, h2⟩ := reciprocal_denominator_sums hP hPR
      have hh1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr huv)
      have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [div_eq_mul_inv] using add_le_add hh1 hh2



end
end GoldbachBeaumontSmooth
end

/- Source: SmoothBilinear.lean -/
section

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open OAI.Problem337

namespace GoldbachBeaumontSmooth
noncomputable section

def hyperbolicCaps (N : ℝ) (M : ℕ) (α : ℝ) : ℝ :=
  ∑ m ∈ Ioc 0 M, RationalPhaseSpacing.truncatedInv (N / m)
    (RationalPhaseSpacing.intDistance (α * m))

theorem hyperbolicCaps_eq_int (N : ℝ) (M : ℕ) (α : ℝ) :
    hyperbolicCaps N M α = ∑ m ∈ Icc 1 (M : ℤ),
      RationalPhaseSpacing.truncatedInv (N / (m : ℝ))
        (RationalPhaseSpacing.intDistance (α * m)) := by
  unfold hyperbolicCaps
  apply Finset.sum_nbij' (fun d : ℕ => (d : ℤ)) Int.toNat
  · intro d hd
    obtain ⟨hd0, hdA⟩ := Finset.mem_Ioc.mp hd
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd0, by exact_mod_cast hdA⟩
  · intro d hd
    obtain ⟨hd1, hdA⟩ := Finset.mem_Icc.mp hd
    apply Finset.mem_Ioc.mpr
    omega
  · intro d _; exact Int.toNat_natCast d
  · intro d hd
    exact Int.toNat_of_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega)
  · intro d _; simp

theorem hyperbolicCaps_nonneg {N : ℝ} (hN : 0 ≤ N) (M : ℕ) (α : ℝ) :
    0 ≤ hyperbolicCaps N M α := by
  apply Finset.sum_nonneg
  intro m _
  exact RationalPhaseSpacing.truncatedInv_nonneg (by positivity)
    (RationalPhaseSpacing.intDistance_nonneg _)

theorem norm_phase_Ioc_mul_le_caps (α : ℝ) (N d A B : ℕ)
    (hAB : A ≤ B) (hB : B ≤ N / d) :
    ‖∑ k ∈ Ioc A B, RealPhase.phase (α * (d * k : ℕ))‖ ≤
      2 * RationalPhaseSpacing.truncatedInv ((N : ℝ) / d)
        (RationalPhaseSpacing.intDistance (α * d)) := by
  have heq : (∑ k ∈ Ioc A B, RealPhase.phase (α * (d * k : ℕ))) =
      (∑ k ∈ Ioc 0 B, RealPhase.phase (α * (d * k : ℕ))) -
      ∑ k ∈ Ioc 0 A, RealPhase.phase (α * (d * k : ℕ)) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using sum_Ioc_consecutive
      (fun k => RealPhase.phase (α * (d * k : ℕ))) (Nat.zero_le A) hAB
  rw [heq]
  have h1 := VaughanHyperbolic.norm_phase_Ioc_mul_le_variable α N d B hB
  have h2 := VaughanHyperbolic.norm_phase_Ioc_mul_le_variable α N d A (hAB.trans hB)
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_log_phase_Ioc_mul_le_caps (α : ℝ) (N d A B : ℕ)
    (hN : 1 ≤ N) (hAB : A ≤ B) (hB : B ≤ N / d) :
    ‖∑ k ∈ Ioc A B, (Real.log k : ℂ) * RealPhase.phase (α * (d * k : ℕ))‖ ≤
      4 * Real.log N * RationalPhaseSpacing.truncatedInv ((N : ℝ) / d)
        (RationalPhaseSpacing.intDistance (α * d)) := by
  let C := RationalPhaseSpacing.truncatedInv ((N : ℝ) / d)
    (RationalPhaseSpacing.intDistance (α * d))
  have hC : 0 ≤ C := RationalPhaseSpacing.truncatedInv_nonneg (by positivity)
    (RationalPhaseSpacing.intDistance_nonneg _)
  have hprefix (k : ℕ) (hk : k ≤ N / d) :
      ‖∑ j ∈ Ioc 0 k, (Real.log j : ℂ) * RealPhase.phase (α * (d * j : ℕ))‖ ≤
      2 * Real.log N * C := by
    by_cases hk0 : k = 0
    · simp only [hk0, Ioc_self, sum_empty, norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hN))) hC
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
    have hlog : Real.log k ≤ Real.log N := Real.log_le_log hkpos
      (by exact_mod_cast hk.trans (Nat.div_le_self N d))
    have hh := Vaughan.log_weighted_sum_norm_le
      (fun j => RealPhase.phase (α * (d * j : ℕ))) k C
      (fun j hj => VaughanHyperbolic.norm_phase_Ioc_mul_le_variable α N d j (hj.trans hk))
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog hC])
  have heq : (∑ k ∈ Ioc A B, (Real.log k : ℂ) * RealPhase.phase (α * (d * k : ℕ))) =
      (∑ k ∈ Ioc 0 B, (Real.log k : ℂ) * RealPhase.phase (α * (d * k : ℕ))) -
      ∑ k ∈ Ioc 0 A, (Real.log k : ℂ) * RealPhase.phase (α * (d * k : ℕ)) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using sum_Ioc_consecutive
      (fun k => (Real.log k : ℂ) * RealPhase.phase (α * (d * k : ℕ))) (Nat.zero_le A) hAB
  rw [heq]
  exact (norm_sub_le _ _).trans (by have h1 := hprefix B hB; have h2 := hprefix A (hAB.trans hB); linarith)

/-- Uniformly bounded outer coefficients and two arbitrary hyperbolic endpoints. -/
theorem norm_smooth_bilinear_le_caps (α : ℝ) (N M : ℕ) (c : ℕ → ℂ)
    (A B : ℕ → ℕ) {W : ℝ} (hW : 0 ≤ W)
    (hc : ∀ m ∈ Ioc 0 M, ‖c m‖ ≤ W)
    (hAB : ∀ m ∈ Ioc 0 M, A m ≤ B m)
    (hB : ∀ m ∈ Ioc 0 M, B m ≤ N / m) :
    ‖∑ m ∈ Ioc 0 M, c m * ∑ k ∈ Ioc (A m) (B m),
      RealPhase.phase (α * (m * k : ℕ))‖ ≤ 2 * W * hyperbolicCaps N M α := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 M, ‖c m * ∑ k ∈ Ioc (A m) (B m),
        RealPhase.phase (α * (m * k : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 M, 2 * W * RationalPhaseSpacing.truncatedInv ((N : ℝ) / m)
        (RationalPhaseSpacing.intDistance (α * m)) := by
      apply sum_le_sum
      intro m hm
      rw [norm_mul]
      have hh := mul_le_mul (hc m hm) (norm_phase_Ioc_mul_le_caps α N m (A m) (B m)
        (hAB m hm) (hB m hm)) (norm_nonneg _) hW
      nlinarith only [hh]
    _ = _ := by rw [hyperbolicCaps, mul_sum]

/-- The same smooth factor can carry the logarithm occurring in Heath-Brown's identity. -/
theorem norm_log_smooth_bilinear_le_caps (α : ℝ) (N M : ℕ) (c : ℕ → ℂ)
    (A B : ℕ → ℕ) {W : ℝ} (hW : 0 ≤ W) (hN : 1 ≤ N)
    (hc : ∀ m ∈ Ioc 0 M, ‖c m‖ ≤ W)
    (hAB : ∀ m ∈ Ioc 0 M, A m ≤ B m)
    (hB : ∀ m ∈ Ioc 0 M, B m ≤ N / m) :
    ‖∑ m ∈ Ioc 0 M, c m * ∑ k ∈ Ioc (A m) (B m),
      (Real.log k : ℂ) * RealPhase.phase (α * (m * k : ℕ))‖ ≤
      4 * W * Real.log N * hyperbolicCaps N M α := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 M, ‖c m * ∑ k ∈ Ioc (A m) (B m),
        (Real.log k : ℂ) * RealPhase.phase (α * (m * k : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 M, 4 * W * Real.log N * RationalPhaseSpacing.truncatedInv ((N : ℝ) / m)
        (RationalPhaseSpacing.intDistance (α * m)) := by
      apply sum_le_sum
      intro m hm
      rw [norm_mul]
      have hh := mul_le_mul (hc m hm) (norm_log_phase_Ioc_mul_le_caps α N m (A m) (B m)
        hN (hAB m hm) (hB m hm)) (norm_nonneg _) hW
      nlinarith only [hh]
    _ = _ := by rw [hyperbolicCaps, mul_sum]

end
end GoldbachBeaumontSmooth
end

/- Source: SmoothLocalEnergy.lean -/
section

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace GoldbachBeaumontSmooth
noncomputable section

/-- Only the finitely many rational neighborhoods meeting the cell are retained. -/
def activeCenters (q R : ℕ) (u v : ℝ) : Finset ℤ := by
  classical
  exact (Icc ⌊(q : ℝ) * u - 1 / (R : ℝ)⌋ ⌈(q : ℝ) * v + 1 / (R : ℝ)⌉).filter
    (fun a => ∃ t ∈ Set.Icc u v, |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * R))

theorem mem_activeCenters {q R : ℕ} (hq : 0 < q) (hR : 0 < R)
    {u v t : ℝ} {a : ℤ} (ht : t ∈ Set.Icc u v)
    (ha : |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * R)) :
    a ∈ activeCenters q R u v := by
  classical
  have hh := center_scaled_bounds (by exact_mod_cast hq : (0 : ℝ) < q)
    (by exact_mod_cast hR : (0 : ℝ) < R) ht ha
  rw [activeCenters, mem_filter]
  refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, t, ht, ha⟩
  · have h := (Int.floor_le ((q : ℝ) * u - 1 / (R : ℝ))).trans hh.1
    exact_mod_cast h
  · have h := hh.2.trans (Int.le_ceil ((q : ℝ) * v + 1 / (R : ℝ)))
    exact_mod_cast h

theorem activeCenters_spec (q R : ℕ) (u v : ℝ) (a : ℤ)
    (ha : a ∈ activeCenters q R u v) :
    ∃ t ∈ Set.Icc u v, |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * R) := by
  classical
  exact (mem_filter.mp ha).2

set_option maxHeartbeats 400000 in
/-- A smooth bilinear sum has small local energy away from low-denominator wide arcs. -/
theorem masked_smooth_local_energy (F : ℝ → ℂ) (hFcont : Continuous F)
    (T : Set ℝ) (hT : MeasurableSet T) {u v : ℝ} (huv : u ≤ v)
    (N : ℝ) (M P R : ℕ) {W : ℝ} (hW : 0 ≤ W)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ N) (hP : 0 < P) (hPR : P ≤ R)
    (hRN : (R : ℝ) ≤ N)
    (hF : ∀ t ∈ Set.Icc u v, ‖F t‖ ≤ W * hyperbolicCaps N M t)
    (hcover : ∀ t ∈ Set.Icc u v, t ∈ T → ∃ a : ℚ,
      a.den ≤ R ∧ |t - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R) ∧
        (P < a.den ∨ rationalPeak N a.den (t - (a : ℝ)) ≤ 4 * R)) :
    let K := 80 * W * (1 + Real.log (10 * N))
    let E := (M : ℝ) + 5 * R + N / R
    (∫ t in u..v, T.indicator (fun t => ‖F t‖ ^ 2) t) ≤
      2 * K ^ 2 * (E ^ 2 * (v - u) +
        Real.pi * N * ((v - u) * (1 + Real.log R) + 3 / (P : ℝ))) := by
  classical
  let K := 80 * W * (1 + Real.log (10 * N))
  let E := (M : ℝ) + 5 * R + N / R
  let G (t : ℝ) := ∑ q ∈ Ioc P R, ∑ a ∈ activeCenters q R u v,
    (N / ((q : ℝ) * (1 + N * |t - (a : ℝ) / q|))) ^ 2
  have hN0 : 0 < N := by linarith
  have hRpos : 0 < R := hP.trans_le hPR
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hRpos
  have hL : 0 ≤ 1 + Real.log (10 * N) := by
    have := Real.log_nonneg (show 1 ≤ 10 * N by linarith)
    linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hG0 (t : ℝ) : 0 ≤ G t := by
    apply sum_nonneg; intro q _
    apply sum_nonneg; intro a _
    exact sq_nonneg _
  have hGc : Continuous G := by
    apply continuous_finsetSum
    intro q hq
    have hq0 : (0 : ℝ) < q := by
      have := (mem_Ioc.mp hq).1
      exact_mod_cast (show 0 < q by omega)
    apply continuous_finsetSum
    intro a _
    have hden (t : ℝ) : (q : ℝ) * (1 + N * |t - (a : ℝ) / q|) ≠ 0 := by positivity
    fun_prop
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc u v) :
      T.indicator (fun t => ‖F t‖ ^ 2) t ≤ 2 * K ^ 2 * (E ^ 2 + G t) := by
    by_cases htT : t ∈ T
    · rw [Set.indicator_of_mem htT]
      obtain ⟨a, haR, ha, halow⟩ := hcover t ht htT
      have hanum : a.num ∈ activeCenters a.den R u v :=
        mem_activeCenters a.pos hRpos ht (by simpa only [Rat.cast_def] using ha)
      let p := if P < a.den then rationalPeak N a.den (t - (a : ℝ)) else 0
      have hp : 0 ≤ p := by
        dsimp [p]; split_ifs
        · exact rationalPeak_nonneg hN0.le (by positivity)
        · exact le_rfl
      have hpG : p ^ 2 ≤ G t := by
        by_cases haP : P < a.den
        · have hq : a.den ∈ Ioc P R := mem_Ioc.mpr ⟨haP, haR⟩
          have h1 := single_le_sum
            (fun b (_ : b ∈ activeCenters a.den R u v) => sq_nonneg
              (N / ((a.den : ℝ) * (1 + N * |t - (b : ℝ) / a.den|)))) hanum
          have h2 := single_le_sum (fun q (_ : q ∈ Ioc P R) =>
            sum_nonneg (fun b (_ : b ∈ activeCenters q R u v) => sq_nonneg
              (N / ((q : ℝ) * (1 + N * |t - (b : ℝ) / q|))))) hq
          dsimp [p, rationalPeak]
          simp only [if_pos haP]
          simpa only [Rat.cast_def] using h1.trans h2
        · simp only [p, if_neg haP, zero_pow (by decide : 2 ≠ 0)]
          exact hG0 t
      have hcap := hyperbolic_caps_decay t a N R M hN hM hR1 hRN
        (by exact_mod_cast haR) ha
      rw [← hyperbolicCaps_eq_int] at hcap
      have hbound : ‖F t‖ ≤ K * (E + p) := by
        have hh := (hF t ht).trans (mul_le_mul_of_nonneg_left hcap hW)
        have he : rationalPeak N a.den (t - (a : ℝ)) ≤ 4 * R + p := by
          by_cases haP : P < a.den
          · simp only [p, if_pos haP]
            linarith
          · have hh := halow.resolve_left haP
            simpa only [p, if_neg haP, add_zero] using hh
        have heK := mul_le_mul_of_nonneg_left he hK
        dsimp [K, E] at *
        nlinarith only [hh, heK]
      have hs : ‖F t‖ ^ 2 ≤ (K * (E + p)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (add_nonneg hE hp))).mpr hbound
      have hsum : (E + p) ^ 2 ≤ 2 * (E ^ 2 + p ^ 2) := by nlinarith [sq_nonneg (E - p)]
      have hsumK := mul_le_mul_of_nonneg_left hsum (sq_nonneg K)
      have hpGK := mul_le_mul_of_nonneg_left hpG (sq_nonneg K)
      nlinarith only [hs, hsumK, hpGK]
    · rw [Set.indicator_of_notMem htT]
      positivity
  have hFI : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume u v :=
    (hFcont.norm.pow 2).intervalIntegrable u v
  have hTI : IntervalIntegrable (T.indicator (fun t => ‖F t‖ ^ 2)) volume u v :=
    ⟨hFI.1.indicator hT, hFI.2.indicator hT⟩
  have hBI : IntervalIntegrable (fun t => 2 * K ^ 2 * (E ^ 2 + G t)) volume u v :=
    (continuous_const.mul (continuous_const.add hGc)).intervalIntegrable u v
  have hmass := active_peaks_integral hN0 huv hP hPR
    (fun q => activeCenters q R u v) (fun q _ a ha => activeCenters_spec q R u v a ha)
  calc
    _ ≤ ∫ t in u..v, 2 * K ^ 2 * (E ^ 2 + G t) :=
      intervalIntegral.integral_mono_on huv hTI hBI hpoint
    _ = 2 * K ^ 2 * (E ^ 2 * (v - u) + ∫ t in u..v, G t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const (hGc.intervalIntegrable u v),
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change E ^ 2 * (v - u) + (∫ t in u..v, G t) ≤ E ^ 2 * (v - u) +
        Real.pi * N * ((v - u) * (1 + Real.log R) + 3 / (P : ℝ))
      have hm : (∫ t in u..v, G t) ≤
          Real.pi * N * ((v - u) * (1 + Real.log R) + 3 / (P : ℝ)) := hmass
      linarith only [hm]


/-- A rational centre outside its wide neighborhood contributes only to the error scale. -/
theorem rationalPeak_le_of_separation {N R : ℝ} (hN : 0 ≤ N) (hR : 0 < R)
    (a : ℚ) (t : ℝ) (hsep : 1 / (4 * (a.den : ℝ) * R) ≤ |t - (a : ℝ)|) :
    rationalPeak N a.den (t - (a : ℝ)) ≤ 4 * R := by
  have hq : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  unfold rationalPeak
  apply (div_le_iff₀ (by positivity : 0 < (a.den : ℝ) * (1 + N * |t - (a : ℝ)|))).mpr
  have hh := (div_le_iff₀ (by positivity : 0 < 4 * (a.den : ℝ) * R)).mp hsep
  have hn := mul_le_mul_of_nonneg_left hh hN
  nlinarith only [hn, mul_pos hq hR]

/-- Pointwise Dirichlet approximation plus low-centre separation supplies the local cover. -/
theorem dirichlet_cover_of_separation {N : ℝ} (hN : 0 ≤ N) {P R : ℕ}
    (hR : 0 < R) (t : ℝ)
    (hsep : ∀ a : ℚ, a.den ≤ P → 1 / (4 * (a.den : ℝ) * R) ≤ |t - (a : ℝ)|) :
    ∃ a : ℚ, a.den ≤ R ∧ |t - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R) ∧
      (P < a.den ∨ rationalPeak N a.den (t - (a : ℝ)) ≤ 4 * R) := by
  obtain ⟨a, ha, haR⟩ := Real.exists_rat_abs_sub_le_and_den_le t hR
  have hq : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  refine ⟨a, haR, ha.trans ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by positivity : 0 < (a.den : ℝ) * R)
    nlinarith only [hq]
  · by_cases hp : P < a.den
    · exact Or.inl hp
    · exact Or.inr (rationalPeak_le_of_separation hN hR0 a t
        (hsep a (le_of_not_gt hp)))

/-- The cell form used after a single rational approximation at the mesh endpoint. -/
theorem smooth_cell_energy_of_separation (F : ℝ → ℂ) (hFcont : Continuous F)
    {u v : ℝ} (huv : u ≤ v) (N : ℝ) (M P R : ℕ) {W : ℝ} (hW : 0 ≤ W)
    (hN : 1 ≤ N) (hM : (M : ℝ) ≤ N) (hP : 0 < P) (hPR : P ≤ R)
    (hRN : (R : ℝ) ≤ N)
    (hF : ∀ t ∈ Set.Icc u v, ‖F t‖ ≤ W * hyperbolicCaps N M t)
    (hsep : ∀ t ∈ Set.Icc u v, ∀ a : ℚ, a.den ≤ P →
      1 / (4 * (a.den : ℝ) * R) ≤ |t - (a : ℝ)|) :
    let K := 80 * W * (1 + Real.log (10 * N))
    let E := (M : ℝ) + 5 * R + N / R
    (∫ t in u..v, ‖F t‖ ^ 2) ≤
      2 * K ^ 2 * (E ^ 2 * (v - u) +
        Real.pi * N * ((v - u) * (1 + Real.log R) + 3 / (P : ℝ))) := by
  have hh := masked_smooth_local_energy F hFcont Set.univ MeasurableSet.univ huv
    N M P R hW hN hM hP hPR hRN hF
    (fun t ht _ => dirichlet_cover_of_separation (by linarith) (hP.trans_le hPR) t (hsep t ht))
  simpa only [Set.indicator_univ] using hh



end
end GoldbachBeaumontSmooth
end

/- Source: SmoothEndpointSeparation.lean -/
section

open Finset

namespace GoldbachBeaumontSmooth
noncomputable section

/-- Multiplication by a small integer cannot turn a high-denominator centre into
one with denominator r when s*r is smaller than the original denominator. -/
theorem scaled_rational_gap (s : ℕ) (hs : 0 < s) (a b : ℚ)
    (hden : s * b.den < a.den) :
    1 ≤ (a.den : ℝ) * b.den * |(s : ℝ) * (a : ℝ) - (b : ℝ)| := by
  have hcross : (s : ℤ) * a.num * b.den - b.num * a.den ≠ 0 := by
    intro hz
    have hd : (a.den : ℤ) ∣ a.num * ((s * b.den : ℕ) : ℤ) := by
      refine ⟨b.num, ?_⟩
      push_cast
      nlinarith only [hz]
    have hd' := (Rat.isCoprime_num_den a).symm.dvd_of_dvd_mul_left hd
    have hdn : a.den ∣ s * b.den := by exact_mod_cast hd'
    have hle := Nat.le_of_dvd (Nat.mul_pos hs b.pos) hdn
    omega
  have hi := Int.one_le_abs hcross
  have hr : (1 : ℝ) ≤ |(s : ℝ) * a.num * b.den - b.num * a.den| := by exact_mod_cast hi
  have ha0 : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hb0 : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  have he : (s : ℝ) * a.num * b.den - b.num * a.den =
      (a.den : ℝ) * b.den * ((s : ℝ) * (a : ℝ) - (b : ℝ)) := by
    rw [Rat.cast_def a, Rat.cast_def b]
    field_simp <;> ring
  rw [he, abs_mul, abs_of_pos (mul_pos ha0 hb0)] at hr
  exact hr

/-- A high-denominator endpoint approximation keeps an entire scaled mesh cell
away from every sufficiently small denominator. -/
theorem scaled_cell_separation (s : ℕ) (hs : 0 < s) (a b : ℚ)
    {α θ R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    (hqR : (a.den : ℝ) ≤ R) (hden : s * b.den < a.den)
    (hrR : 2 * (s : ℝ) * b.den ≤ R)
    (hrH : 4 * (s : ℝ) * b.den * R ≤ H)
    (happrox : |α - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R))
    (hcell : |θ - (s : ℝ) * α| ≤ (s : ℝ) / H) :
    1 / (4 * (b.den : ℝ) * R) ≤ |θ - (b : ℝ)| := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hr : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  have hg := scaled_rational_gap s hs a b hden
  have happ : (a.den : ℝ) * R * |α - (a : ℝ)| ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos hq hR)).mp happrox
    nlinarith only [h]
  have hperr : 4 * (a.den : ℝ) * b.den * s * |α - (a : ℝ)| ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hrR
      (mul_nonneg (show (0 : ℝ) ≤ 2 * a.den by positivity) (abs_nonneg (α - (a : ℝ))))
    nlinarith only [h, happ]
  have hcoeff : 4 * (s : ℝ) * b.den * a.den ≤ H := by
    exact (mul_le_mul_of_nonneg_left hqR (by positivity)).trans hrH
  have hshift : 4 * (a.den : ℝ) * b.den * |θ - (s : ℝ) * α| ≤ 1 := by
    have h := (le_div_iff₀ hH).mp hcell
    have hh := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (θ - (s : ℝ) * α))
    have hmul : (s : ℝ) * (4 * (a.den : ℝ) * b.den * |θ - (s : ℝ) * α|) ≤ (s : ℝ) * 1 := by
      nlinarith only [h, hh]
    exact (mul_le_mul_iff_right₀ hsR).mp hmul
  have htri : |(s : ℝ) * (a : ℝ) - (b : ℝ)| ≤
      (s : ℝ) * |α - (a : ℝ)| + |θ - (s : ℝ) * α| + |θ - (b : ℝ)| := by
    have h1 := abs_sub_le ((s : ℝ) * (a : ℝ)) ((s : ℝ) * α) (b : ℝ)
    have h2 := abs_sub_le ((s : ℝ) * α) θ (b : ℝ)
    have he : |(s : ℝ) * (a : ℝ) - (s : ℝ) * α| = (s : ℝ) * |α - (a : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hsR, abs_sub_comm]
    rw [he] at h1
    rw [abs_sub_comm ((s : ℝ) * α) θ] at h2
    linarith only [h1, h2]
  have ht := mul_le_mul_of_nonneg_left htri (mul_nonneg hq.le hr.le)
  have hlast : 1 ≤ 4 * (a.den : ℝ) * b.den * |θ - (b : ℝ)| := by
    nlinarith only [hg, ht, hperr, hshift]
  have hlastR := mul_le_mul_of_nonneg_right hqR
    (show 0 ≤ 4 * (b.den : ℝ) * |θ - (b : ℝ)| by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 4 * (b.den : ℝ) * R)).mpr
  nlinarith only [hlast, hlastR]

/-- The public form uses a single cutoff P and works for every scaled low centre. -/
theorem scaled_mesh_low_centres (s P : ℕ) (hs : 0 < s) (a : ℚ)
    {α θ R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    (hPq : P < a.den) (hqR : (a.den : ℝ) ≤ R)
    (hPR : 2 * (P : ℝ) ≤ R) (hPH : 4 * (P : ℝ) * R ≤ H)
    (happrox : |α - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R))
    (hcell : |θ - (s : ℝ) * α| ≤ (s : ℝ) / H)
    (b : ℚ) (hb : s * b.den ≤ P) :
    1 / (4 * (b.den : ℝ) * R) ≤ |θ - (b : ℝ)| := by
  have hbR : (s : ℝ) * b.den ≤ P := by exact_mod_cast hb
  apply scaled_cell_separation s hs a b hR hH hqR (hb.trans_lt hPq) ?_ ?_ happrox hcell
  · linarith
  · have h := mul_le_mul_of_nonneg_right hbR hR.le
    nlinarith only [h, hPH]


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothRectangle.lean -/
section

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open OAI.Problem337

namespace GoldbachBeaumontSmooth
noncomputable section

def smoothWeight (b : Bool) (n : ℕ) : ℂ := if b then (Real.log n : ℂ) else 1

def boxWeight (b : Bool) (A B n : ℕ) : ℂ :=
  if A < n ∧ n ≤ B then smoothWeight b n else 0

def rectangleKernel (N L A B C D : ℕ) (e f : Bool) (α : ℝ) (m k : ℕ) : ℂ :=
  boxWeight e A B m * boxWeight f C D k *
    (if L < m*k ∧ m*k ≤ N then RealPhase.phase (α * (m*k : ℕ)) else 0)

def smoothRectangle (N L A B C D : ℕ) (e f : Bool) (α : ℝ) : ℂ :=
  ∑ m ∈ Ioc 0 N, ∑ k ∈ Ioc 0 N, rectangleKernel N L A B C D e f α m k

theorem smoothWeight_bound {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (b : Bool) :
    ‖smoothWeight b n‖ ≤ 1 + Real.log N := by
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hn.trans hnN)
  cases b
  · simpa [smoothWeight] using (show (1 : ℝ) ≤ 1 + Real.log N by linarith)
  · have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hl := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnN : (n : ℝ) ≤ N)
    change ‖((Real.log (n : ℝ) : ℝ) : ℂ)‖ ≤ 1 + Real.log N
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hln]
    linarith

theorem boxWeight_bound {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (b : Bool) (A B : ℕ) : ‖boxWeight b A B n‖ ≤ 1 + Real.log N := by
  unfold boxWeight
  split_ifs
  · exact smoothWeight_bound hn hnN b
  · simp only [norm_zero]
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hn.trans hnN)
    linarith

theorem norm_smoothWeight_Ioc_le_caps (α : ℝ) (N d A B : ℕ)
    (hN : 1 ≤ N) (hAB : A ≤ B) (hB : B ≤ N / d) (b : Bool) :
    ‖∑ k ∈ Ioc A B, smoothWeight b k * RealPhase.phase (α * (d*k : ℕ))‖ ≤
      4 * (1 + Real.log N) * RationalPhaseSpacing.truncatedInv ((N : ℝ) / d)
        (RationalPhaseSpacing.intDistance (α * d)) := by
  have hcap : 0 ≤ RationalPhaseSpacing.truncatedInv ((N : ℝ) / d)
      (RationalPhaseSpacing.intDistance (α * d)) :=
    RationalPhaseSpacing.truncatedInv_nonneg (by positivity)
      (RationalPhaseSpacing.intDistance_nonneg _)
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  cases b
  · simp only [smoothWeight, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact (norm_phase_Ioc_mul_le_caps α N d A B hAB hB).trans
      (by nlinarith [mul_nonneg hl hcap])
  · simp only [smoothWeight, ↓reduceIte]
    exact (norm_log_phase_Ioc_mul_le_caps α N d A B hN hAB hB).trans
      (by nlinarith)

theorem Ioc_min_left_eq (a b : ℕ) : Ioc (min a b) b = Ioc a b := by
  ext k
  simp only [mem_Ioc]
  omega

/-- The product cutoff leaves exactly one finite interval in the smooth factor. -/
theorem smooth_inner_interval (N L C D m : ℕ) (hm : 0 < m) (w : ℕ → ℂ) :
    (∑ k ∈ Ioc 0 N, if C < k ∧ k ≤ D ∧ L < m*k ∧ m*k ≤ N then w k else 0) =
      ∑ k ∈ Ioc (min (max C (L / m)) (min D (N / m))) (min D (N / m)), w k := by
  rw [Ioc_min_left_eq, ← sum_filter]
  congr 1
  ext k
  have hlow : L / m < k ↔ L < m*k := by
    rw [Nat.div_lt_iff_lt_mul hm, Nat.mul_comm k m]
  have hupp : k ≤ N / m ↔ m*k ≤ N := by
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm k m]
  simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff, hlow, hupp]
  have hdiv := Nat.div_le_self N m
  constructor
  · intro h
    exact ⟨⟨h.2.1, h.2.2.2.1⟩, h.2.2.1, h.2.2.2.2⟩
  · rintro ⟨⟨hC,hL⟩,hD,hN⟩
    have hkN : k ≤ N := (hupp.mpr hN).trans hdiv
    exact ⟨⟨by omega,hkN⟩,hC,hD,hL,hN⟩

theorem rectangle_inner (N L A B C D : ℕ) (e f : Bool) (α : ℝ)
    {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ Ioc 0 N, rectangleKernel N L A B C D e f α m k) =
      boxWeight e A B m *
        ∑ k ∈ Ioc (min (max C (L/m)) (min D (N/m))) (min D (N/m)),
          smoothWeight f k * RealPhase.phase (α * (m*k : ℕ)) := by
  rw [← smooth_inner_interval N L C D m hm
    (fun k => smoothWeight f k * RealPhase.phase (α * (m*k : ℕ))), mul_sum]
  apply sum_congr rfl
  intro k _
  unfold rectangleKernel boxWeight
  by_cases h1 : A < m ∧ m ≤ B <;> by_cases h2 : C < k ∧ k ≤ D <;>
    by_cases h3 : L < m*k ∧ m*k ≤ N <;> simp [h1,h2,h3, and_assoc, mul_assoc]

/-- Hyperbolic splitting makes at least one variable at most sqrt N. -/
theorem hyperbola_split (N : ℕ) (F : ℕ → ℕ → ℂ)
    (hF : ∀ m k, N < m*k → F m k = 0) :
    (∑ m ∈ Ioc 0 N, ∑ k ∈ Ioc 0 N, F m k) =
      (∑ m ∈ Ioc 0 (Nat.sqrt N), ∑ k ∈ Ioc 0 N, F m k) +
      ∑ k ∈ Ioc 0 (Nat.sqrt N), ∑ m ∈ Ioc (Nat.sqrt N) N, F m k := by
  have hMN := Nat.sqrt_le_self N
  have hsplit := sum_Ioc_consecutive (fun m => ∑ k ∈ Ioc 0 N, F m k)
    (Nat.zero_le (Nat.sqrt N)) hMN
  rw [← hsplit]
  congr 1
  rw [sum_comm]
  symm
  apply sum_subset (Ioc_subset_Ioc_right hMN)
  intro k hk hnot
  apply sum_eq_zero
  intro m hm
  have hk' := mem_Ioc.mp hk
  have hm' := mem_Ioc.mp hm
  have hkl : Nat.sqrt N < k := by
    simp only [mem_Ioc, hk'.1, true_and, not_le] at hnot
    exact hnot
  have hprod := Nat.mul_le_mul (Nat.succ_le_of_lt hm'.1) (Nat.succ_le_of_lt hkl)
  exact hF m k ((Nat.lt_succ_sqrt N).trans_le hprod)

theorem rectangle_swap (N L A B C D : ℕ) (e f : Bool) (α : ℝ) (m k : ℕ) :
    rectangleKernel N L A B C D e f α m k =
      rectangleKernel N L C D A B f e α k m := by
  unfold rectangleKernel
  rw [Nat.mul_comm m k, mul_comm (boxWeight e A B m) (boxWeight f C D k)]

theorem rectangle_restrict_first (N L A B C D M k : ℕ) (e f : Bool) (α : ℝ)
    (hMN : M ≤ N) :
    (∑ m ∈ Ioc M N, rectangleKernel N L A B C D e f α m k) =
      ∑ m ∈ Ioc 0 N, rectangleKernel N L (max A M) B C D e f α m k := by
  have hsub : Ioc M N ⊆ Ioc 0 N := Ioc_subset_Ioc_left (Nat.zero_le M)
  calc
    _ = ∑ m ∈ Ioc M N, rectangleKernel N L (max A M) B C D e f α m k := by
      apply sum_congr rfl
      intro m hm
      have hmM := (mem_Ioc.mp hm).1
      simp only [rectangleKernel,boxWeight,max_lt_iff,hmM,and_true]
    _ = _ := by
      apply sum_subset hsub
      intro m hm hnot
      have hmM : m ≤ M := by
        have hmN := (mem_Ioc.mp hm).2
        simp only [mem_Ioc,hmN,and_true,not_lt] at hnot
        exact hnot
      have hbad : ¬ max A M < m := by omega
      simp [rectangleKernel,boxWeight,hbad]

theorem norm_short_rectangle_le (N L A B C D M : ℕ) (e f : Bool) (α : ℝ)
    (hN : 1 ≤ N) (hMN : M ≤ N) :
    ‖∑ m ∈ Ioc 0 M, ∑ k ∈ Ioc 0 N, rectangleKernel N L A B C D e f α m k‖ ≤
      4 * (1 + Real.log N) ^ 2 * hyperbolicCaps N M α := by
  have hlog : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    linarith
  calc
    _ ≤ ∑ m ∈ Ioc 0 M, ‖∑ k ∈ Ioc 0 N, rectangleKernel N L A B C D e f α m k‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 M, 4 * (1 + Real.log N)^2 *
        RationalPhaseSpacing.truncatedInv ((N : ℝ) / m)
          (RationalPhaseSpacing.intDistance (α * m)) := by
      apply sum_le_sum
      intro m hm
      have hm' := mem_Ioc.mp hm
      rw [rectangle_inner N L A B C D e f α hm'.1, norm_mul]
      have hc := boxWeight_bound (Nat.succ_le_of_lt hm'.1) (hm'.2.trans hMN) e A B
      have hh := norm_smoothWeight_Ioc_le_caps α N m
        (min (max C (L/m)) (min D (N/m))) (min D (N/m)) hN (min_le_right _ _)
        (min_le_right _ _) f
      have hp := mul_le_mul hc hh (norm_nonneg _) hlog
      nlinarith only [hp]
    _ = _ := by rw [hyperbolicCaps,mul_sum]

/-- Complete smooth d2 estimate, including either or both logarithmic factors. -/
theorem norm_smoothRectangle_le_caps (N L A B C D : ℕ) (e f : Bool) (α : ℝ)
    (hN : 1 ≤ N) :
    ‖smoothRectangle N L A B C D e f α‖ ≤
      8 * (1 + Real.log N) ^ 2 * hyperbolicCaps N (Nat.sqrt N) α := by
  unfold smoothRectangle
  rw [hyperbola_split N _ (by
    intro m k hmk
    have hh : ¬m*k ≤ N := not_le.mpr hmk
    simp [rectangleKernel,hh])]
  have hright : (∑ k ∈ Ioc 0 (Nat.sqrt N), ∑ m ∈ Ioc (Nat.sqrt N) N,
      rectangleKernel N L A B C D e f α m k) =
      ∑ k ∈ Ioc 0 (Nat.sqrt N), ∑ m ∈ Ioc 0 N,
        rectangleKernel N L C D (max A (Nat.sqrt N)) B f e α k m := by
    apply sum_congr rfl
    intro k _
    rw [rectangle_restrict_first N L A B C D (Nat.sqrt N) k e f α (Nat.sqrt_le_self N)]
    apply sum_congr rfl
    intro m _
    exact rectangle_swap N L (max A (Nat.sqrt N)) B C D e f α m k
  rw [hright]
  have h1 := norm_short_rectangle_le N L A B C D (Nat.sqrt N) e f α hN (Nat.sqrt_le_self N)
  have h2 := norm_short_rectangle_le N L C D (max A (Nat.sqrt N)) B (Nat.sqrt N) f e α hN (Nat.sqrt_le_self N)
  exact (norm_add_le _ _).trans (by linarith)

theorem continuous_smoothRectangle (N L A B C D : ℕ) (e f : Bool) :
    Continuous (smoothRectangle N L A B C D e f) := by
  unfold smoothRectangle
  apply continuous_finsetSum
  intro m _
  apply continuous_finsetSum
  intro k _
  unfold rectangleKernel
  split_ifs
  · unfold RealPhase.phase
    fun_prop
  · fun_prop


/-- The analytic rectangle agrees with the original finite sharp rectangle,
even when its displayed dyadic endpoints extend beyond the product cutoff. -/
theorem smoothRectangle_eq_Ioc (N L A B C D : ℕ) (e f : Bool) (α : ℝ) :
    smoothRectangle N L A B C D e f α =
      ∑ m ∈ Ioc A B, ∑ k ∈ Ioc C D, if L < m * k ∧ m * k ≤ N then
        smoothWeight e m * smoothWeight f k * RealPhase.phase (α*(m*k : ℕ)) else 0 := by
  classical
  unfold smoothRectangle
  rw [← sum_product', ← sum_product']
  let S := (Ioc 0 N) ×ˢ (Ioc 0 N)
  let T := (Ioc A B) ×ˢ (Ioc C D)
  calc
    _ = ∑ p ∈ S ∩ T, rectangleKernel N L A B C D e f α p.1 p.2 := by
      symm
      apply sum_subset inter_subset_left
      intro p hp hnot
      have hn : p ∉ T := fun ht => hnot (mem_inter.mpr ⟨hp,ht⟩)
      by_cases hm : A < p.1 ∧ p.1 ≤ B
      · have hk : ¬ (C < p.2 ∧ p.2 ≤ D) := by
          intro hk; exact hn (mem_product.mpr ⟨mem_Ioc.mpr hm,mem_Ioc.mpr hk⟩)
        simp [rectangleKernel,boxWeight,hk]
      · simp [rectangleKernel,boxWeight,hm]
    _ = ∑ p ∈ T, rectangleKernel N L A B C D e f α p.1 p.2 := by
      apply sum_subset inter_subset_right
      intro p hp hnot
      obtain ⟨hm,hk⟩ := mem_product.mp hp
      have hm0 : 0 < p.1 := by have := (mem_Ioc.mp hm).1; omega
      have hk0 : 0 < p.2 := by have := (mem_Ioc.mp hk).1; omega
      by_cases hprod : L < p.1 * p.2 ∧ p.1 * p.2 ≤ N
      · have hmN : p.1 ≤ N := (Nat.le_mul_of_pos_right p.1 hk0).trans hprod.2
        have hkN : p.2 ≤ N := (Nat.le_mul_of_pos_left p.2 hm0).trans hprod.2
        exact False.elim (hnot (mem_inter.mpr ⟨mem_product.mpr
          ⟨mem_Ioc.mpr ⟨hm0,hmN⟩,mem_Ioc.mpr ⟨hk0,hkN⟩⟩,hp⟩))
      · simp [rectangleKernel,hprod]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hm,hk⟩ := mem_product.mp hp
      have hm' := mem_Ioc.mp hm
      have hk' := mem_Ioc.mp hk
      simp only [rectangleKernel,boxWeight,if_pos hm',if_pos hk']
      split_ifs <;> simp

/-- A missing smooth factor is represented by the unit coefficient at one. -/
theorem smoothRectangle_one_factor (N L A B : ℕ) (e : Bool) (α : ℝ) :
    smoothRectangle N L A B 0 1 e false α =
      ∑ m ∈ Ioc A B, if m ∈ Ioc L N then
        smoothWeight e m * RealPhase.phase (α*(m : ℝ)) else 0 := by
  rw [smoothRectangle_eq_Ioc]
  simp [show Ioc (0:ℕ) 1 = {1} by decide, smoothWeight, mem_Ioc]

theorem smoothRectangle_zero_factors (N L : ℕ) (α : ℝ) :
    smoothRectangle N L 0 1 0 1 false false α =
      if 1 ∈ Ioc L N then RealPhase.phase α else 0 := by
  rw [smoothRectangle_one_factor]
  simp [show Ioc (0:ℕ) 1 = {1} by decide, smoothWeight]

theorem positive_Ico_eq_Ioc {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Ico a b = Ioc (a-1) (b-1) := by
  ext m
  simp only [mem_Ico,mem_Ioc]
  omega


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothRectangleEnergy.lean -/
section

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open OAI.Problem337

namespace GoldbachBeaumontSmooth
noncomputable section

theorem hyperbolicCaps_mono {N Z : ℝ} (hN : 0 ≤ N) (hNZ : N ≤ Z)
    {M K : ℕ} (hMK : M ≤ K) (α : ℝ) : hyperbolicCaps N M α ≤ hyperbolicCaps Z K α := by
  unfold hyperbolicCaps
  calc
    _ ≤ ∑ m ∈ Ioc 0 M, RationalPhaseSpacing.truncatedInv (Z / m)
        (RationalPhaseSpacing.intDistance (α * m)) := by
      apply sum_le_sum
      intro m _
      apply RationalPhaseSpacing.truncatedInv_mono_cap
      exact div_le_div_of_nonneg_right hNZ (Nat.cast_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hMK)
      (fun m _ _ => RationalPhaseSpacing.truncatedInv_nonneg
        (div_nonneg (hN.trans hNZ) (Nat.cast_nonneg _))
        (RationalPhaseSpacing.intDistance_nonneg _))

/-- Every shorter initial segment is estimated using the same master scale. -/
theorem norm_smoothRectangle_le_master (N Z L A B C D : ℕ) (e f : Bool) (α : ℝ)
    (hZ : 1 ≤ Z) (hNZ : N ≤ Z) :
    ‖smoothRectangle N L A B C D e f α‖ ≤
      8 * (1 + Real.log Z) ^ 2 * hyperbolicCaps Z (Nat.sqrt Z) α := by
  have hcapZ : 0 ≤ hyperbolicCaps Z (Nat.sqrt Z) α := hyperbolicCaps_nonneg (Nat.cast_nonneg _) _ _
  by_cases hN : N = 0
  · subst N
    simp only [smoothRectangle,Ioc_self,sum_empty,norm_zero]
    positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hlogN : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
    linarith
  have hlogZ : 0 ≤ 1 + Real.log Z := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Z by exact_mod_cast hZ)
    linarith
  have hlog : 1 + Real.log N ≤ 1 + Real.log Z := by
    have := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast Nat.pos_of_ne_zero hN)
      (show (N : ℝ) ≤ Z by exact_mod_cast hNZ)
    linarith
  have hpow : 8 * (1 + Real.log N)^2 ≤ 8 * (1 + Real.log Z)^2 := by gcongr
  have hcaps := hyperbolicCaps_mono (Nat.cast_nonneg N)
    (by exact_mod_cast hNZ : (N : ℝ) ≤ Z) (Nat.sqrt_le_sqrt hNZ) α
  exact (norm_smoothRectangle_le_caps N L A B C D e f α hN1).trans
    (mul_le_mul hpow hcaps (hyperbolicCaps_nonneg (Nat.cast_nonneg _) _ _) (by positivity))

/-- The actual d2 rectangle on a scaled cell, including uniform shorter prefixes. -/
theorem smoothRectangle_scaled_cell_energy (N Z L A B C D : ℕ) (e f : Bool)
    (s P Q R : ℕ) (hs : 0 < s) (hZ : 1 ≤ Z) (hNZ : N ≤ Z)
    (hP : 0 < P) (hPR : P ≤ R) (hRZ : R ≤ Z) (hsP : s * P ≤ Q)
    (a : ℚ) {α H : ℝ} (hH : 0 < H) (hQq : Q < a.den)
    (hqR : a.den ≤ R) (hQR : 2 * (Q : ℝ) ≤ R) (hQH : 4 * (Q : ℝ) * R ≤ H)
    (happrox : |α - (a : ℝ)| ≤ 1 / ((a.den : ℝ) * R)) :
    let K := 640 * (1 + Real.log Z)^2 * (1 + Real.log (10 * (Z : ℝ)))
    let E := (Nat.sqrt Z : ℝ) + 5 * R + (Z : ℝ) / R
    (∫ t in α..α + 1/H, ‖smoothRectangle N L A B C D e f ((s : ℝ)*t)‖^2) ≤
      (s : ℝ)⁻¹ * (2 * K^2 * (E^2 * ((s : ℝ)/H) +
        Real.pi * Z * (((s : ℝ)/H) * (1 + Real.log R) + 3/(P : ℝ)))) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hRpos : 0 < R := hP.trans_le hPR
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hRpos
  have huv : (s : ℝ)*α ≤ (s : ℝ)*(α+1/H) := by
    apply mul_le_mul_of_nonneg_left _ hsR.le
    have := one_div_pos.mpr hH
    linarith
  have hsep : ∀ θ ∈ Set.Icc ((s : ℝ)*α) ((s : ℝ)*(α+1/H)),
      ∀ b : ℚ, b.den ≤ P → 1/(4*(b.den : ℝ)*R) ≤ |θ-(b : ℝ)| := by
    intro θ hθ b hb
    have hcell : |θ-(s : ℝ)*α| ≤ (s : ℝ)/H := by
      rw [abs_of_nonneg (sub_nonneg.mpr hθ.1)]
      have hu := hθ.2
      simp only [mul_add, mul_one_div] at hu
      linarith
    apply scaled_mesh_low_centres s Q hs a hR0 hH hQq
      (by exact_mod_cast hqR) hQR hQH happrox hcell b
    exact (Nat.mul_le_mul_left s hb).trans hsP
  have hh := smooth_cell_energy_of_separation (smoothRectangle N L A B C D e f)
    (continuous_smoothRectangle N L A B C D e f) huv Z (Nat.sqrt Z) P R
    (by positivity : 0 ≤ 8 * (1 + Real.log Z)^2)
    (by exact_mod_cast hZ) (by exact_mod_cast Nat.sqrt_le_self Z) hP hPR
    (by exact_mod_cast hRZ)
    (fun θ _ => norm_smoothRectangle_le_master N Z L A B C D e f θ hZ hNZ) hsep
  have hw : (s : ℝ)*(α+1/H)-(s : ℝ)*α = (s : ℝ)/H := by ring
  dsimp only at hh ⊢
  rw [hw] at hh
  rw [intervalIntegral.integral_comp_mul_left
    (fun θ => ‖smoothRectangle N L A B C D e f θ‖^2) (ne_of_gt hsR),smul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hsR.le)
  convert hmul using 1 <;> ring


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothScalarBudget.lean -/
section

open Finset MeasureTheory

namespace GoldbachBeaumontSmooth
noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The deliberately generous logarithmic margins leave room for every small
HB3 coefficient and every sharp-box summation. -/
theorem scaled_rectangle_scalar_budget {g H N Z s P R M : ℝ}
    (hg : 1000000 ≤ g) (hH : g^5000 ≤ H) (hNlo : H^2 ≤ N) (hNhi : N ≤ 12*H^2)
    (hZ : 0 ≤ Z) (hZN : Z ≤ N) (hs : 1 ≤ s) (hsg : s ≤ g^101)
    (hP : g^899 ≤ P) (hRlo : H/(2*g^2000) ≤ R) (hRhi : R ≤ H)
    (hM : 0 ≤ M) (hMhi : M ≤ 4*H)
    (hlZ0 : 0 ≤ 1+Real.log Z) (hlZ : 1+Real.log Z ≤ g)
    (hl10Z0 : 0 ≤ 1+Real.log (10*Z)) (hl10Z : 1+Real.log (10*Z) ≤ g)
    (hlR0 : 0 ≤ 1+Real.log R) (hlR : 1+Real.log R ≤ g) :
    let K := 640*(1+Real.log Z)^2*(1+Real.log (10*Z))
    let E := M+5*R+Z/R
    s⁻¹*(2*K^2*(E^2*(s/H)+Real.pi*Z*((s/H)*(1+Real.log R)+3/P))) ≤ N/g^600 := by
  let K := 640*(1+Real.log Z)^2*(1+Real.log (10*Z))
  let E := M+5*R+Z/R
  have hg1 : 1 ≤ g := by linarith
  have hgp : 0 < g := by linarith
  have hHp : 0 < H := (pow_pos hgp 5000).trans_le hH
  have hNp : 0 < N := (sq_pos_of_pos hHp).trans_le hNlo
  have hsp : 0 < s := by linarith
  have hPp : 0 < P := (pow_pos hgp 899).trans_le hP
  have hRp : 0 < R := (div_pos hHp (by positivity : 0 < 2*g^2000)).trans_le hRlo
  have hg2000 : 1 ≤ g^2000 := one_le_pow₀ hg1
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hK : K ≤ 640*g^3 := by
    have hh : (1+Real.log Z)^2*(1+Real.log (10*Z)) ≤ g^2*g := by gcongr
    dsimp [K]
    nlinarith only [hh]
  have hZR : Z/R ≤ 24*H*g^2000 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*g^2000)).mp hRlo
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 12*H by positivity)
    apply (div_le_iff₀ hRp).mpr
    nlinarith only [hZN,hNhi,hh']
  have hE : E ≤ 33*H*g^2000 := by
    have hh := mul_le_mul_of_nonneg_left hg2000 hHp.le
    dsimp [E]
    nlinarith only [hMhi,hRhi,hZR,hh]
  have hHN : H*g^5000 ≤ N :=
    (by nlinarith only [mul_le_mul_of_nonneg_left hH hHp.le] : H*g^5000 ≤ H^2).trans hNlo
  have hmain : H*g^4101 ≤ N/g^899 := by
    apply (le_div_iff₀ (pow_pos hgp 899)).mpr
    convert hHN using 1 <;> ring
  have henergy : E^2*(s/H) ≤ 1089*N/g^899 := by
    have hh : E^2*s ≤ (33*H*g^2000)^2*g^101 :=
      mul_le_mul (pow_le_pow_left₀ hE0 hE 2) hsg (by linarith) (by positivity)
    have hdiv := div_le_div_of_nonneg_right hh hHp.le
    have heq : (33*H*g^2000)^2*g^101/H = 1089*H*g^4101 := by field_simp; ring
    have hh' := mul_le_mul_of_nonneg_left hmain (by norm_num : (0:ℝ)≤1089)
    rw [heq] at hdiv
    simpa only [mul_div_assoc] using hdiv.trans (by nlinarith only [hh'])
  have hshort : (s/H)*(1+Real.log R) ≤ 1/g^899 := by
    have hp : g^1001 ≤ H := (pow_le_pow_right₀ hg1 (by norm_num : 1001≤5000)).trans hH
    have hh : (s/H)*(1+Real.log R) ≤ (g^101/H)*g :=
      mul_le_mul (div_le_div_of_nonneg_right hsg hHp.le) hlR hlR0 (by positivity)
    apply hh.trans
    rw [show (g^101/H)*g = g^102/H by ring]
    apply (div_le_div_iff₀ hHp (pow_pos hgp 899)).mpr
    convert hp using 1 <;> ring
  have htail : 3/P ≤ 3/g^899 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hgp 899) hP
  have harc : Real.pi*Z*((s/H)*(1+Real.log R)+3/P) ≤ 16*N/g^899 := by
    have hb : (s/H)*(1+Real.log R)+3/P ≤ 4/g^899 := by
      convert add_le_add hshort htail using 1 <;> ring
    have hπN : Real.pi*Z ≤ 4*N := by
      have hh := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hZ
      nlinarith only [hh,hZN]
    have hh := mul_le_mul hπN hb (by positivity) (by positivity)
    convert hh using 1 <;> ring
  have hbracket : E^2*(s/H)+Real.pi*Z*((s/H)*(1+Real.log R)+3/P) ≤ 1105*N/g^899 := by
    convert add_le_add henergy harc using 1 <;> ring
  have hKsq : 2*K^2 ≤ 819200*g^6 := by
    have hh := pow_le_pow_left₀ hK0 hK 2
    nlinarith only [hh]
  have hinvs : s⁻¹ ≤ 1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs
  have hb0 : 0 ≤ E^2*(s/H)+Real.pi*Z*((s/H)*(1+Real.log R)+3/P) := by positivity
  have hprod := mul_le_mul hKsq hbracket hb0 (by positivity)
  have hsmall : (905216000:ℝ) ≤ g^293 := by
    have hh : (905216000:ℝ) ≤ g^2 := by nlinarith [sq_nonneg (g-1000000)]
    exact hh.trans (pow_le_pow_right₀ hg1 (by norm_num : 2≤293))
  have hfinal : (819200*g^6)*(1105*N/g^899) ≤ N/g^600 := by
    rw [show (819200*g^6)*(1105*N/g^899) = (905216000*N*g^6)/g^899 by ring]
    apply (div_le_div_iff₀ (pow_pos hgp 899) (pow_pos hgp 600)).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ N*g^606 by positivity)
    convert hh using 1 <;> ring
  calc
    _ ≤ 1*(2*K^2*(E^2*(s/H)+Real.pi*Z*((s/H)*(1+Real.log R)+3/P))) :=
      mul_le_mul_of_nonneg_right hinvs (by positivity)
    _ ≤ (819200*g^6)*(1105*N/g^899) := by simpa only [one_mul] using hprod
    _ ≤ _ := hfinal


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothFiniteCombination.lean -/
section

open Finset MeasureTheory

namespace GoldbachBeaumontSmooth
noncomputable section

/-- Finite coefficient Cauchy, followed by the actual cell integral. -/
theorem finite_combination_energy {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ S, Continuous (F i)) {u v B : ℝ}
    (huv : u ≤ v) (hB : 0 ≤ B)
    (hE : ∀ i ∈ S, (∫ t in u..v, ‖F i t‖^2) ≤ B) :
    (∫ t in u..v, ‖∑ i ∈ S, c i*F i t‖^2) ≤
      (S.card : ℝ) * (∑ i ∈ S, ‖c i‖^2) * B := by
  have hp (t : ℝ) : ‖∑ i ∈ S, c i*F i t‖^2 ≤
      (S.card : ℝ) * (∑ i ∈ S, ‖c i‖^2 * ‖F i t‖^2) := by
    have hn := norm_sum_le S (fun i => c i*F i t)
    have hs := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun _ _ => norm_nonneg _))).mpr hn
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖c i*F i t‖)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,norm_mul,mul_pow] at hc
    simp only [norm_mul] at hs
    exact hs.trans hc
  have hleft : Continuous (fun t => ‖∑ i ∈ S, c i*F i t‖^2) :=
    (continuous_finsetSum S (fun i hi => continuous_const.mul (hF i hi))).norm.pow 2
  have hright : Continuous (fun t => (S.card : ℝ) * (∑ i ∈ S, ‖c i‖^2 * ‖F i t‖^2)) :=
    continuous_const.mul (continuous_finsetSum S (fun i hi => continuous_const.mul ((hF i hi).norm.pow 2)))
  have hEach (i : ι) (hi : i ∈ S) :
      IntervalIntegrable (fun t => ‖c i‖^2 * ‖F i t‖^2) volume u v :=
    (continuous_const.mul ((hF i hi).norm.pow 2)).intervalIntegrable u v
  calc
    _ ≤ ∫ t in u..v, (S.card : ℝ) * (∑ i ∈ S, ‖c i‖^2 * ‖F i t‖^2) :=
      intervalIntegral.integral_mono_on huv (hleft.intervalIntegrable u v)
        (hright.intervalIntegrable u v) (fun t _ => hp t)
    _ = (S.card : ℝ) * ∑ i ∈ S, ‖c i‖^2 * (∫ t in u..v, ‖F i t‖^2) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum hEach]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (S.card : ℝ) * ∑ i ∈ S, ‖c i‖^2 * B := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hE i hi) (sq_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

set_option maxRecDepth 100000 in
/-- The entire small-product coefficient sum still saves 360 logarithmic powers. -/
theorem small_product_combination_saving {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ S, Continuous (F i)) {u v N g : ℝ}
    (huv : u ≤ v) (hN : 0 ≤ N) (hg : 1 ≤ g)
    (hcard : (S.card : ℝ) ≤ g^101) (hc : (∑ i ∈ S, ‖c i‖^2) ≤ g^139)
    (hE : ∀ i ∈ S, (∫ t in u..v, ‖F i t‖^2) ≤ N/g^600) :
    (∫ t in u..v, ‖∑ i ∈ S, c i*F i t‖^2) ≤ N/g^360 := by
  have hgp : 0 < g := by linarith
  have hNZ : 0 ≤ N/g^600 := by positivity
  have hh := finite_combination_energy S c F hF huv hNZ hE
  have hprod : (S.card : ℝ)*(∑ i ∈ S,‖c i‖^2) ≤ g^240 := by
    have h := mul_le_mul hcard hc (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    convert h using 1 <;> ring
  calc
    _ ≤ (S.card : ℝ)*(∑ i ∈ S,‖c i‖^2)*(N/g^600) := hh
    _ ≤ g^240*(N/g^600) := mul_le_mul_of_nonneg_right hprod hNZ
    _ = _ := by field_simp <;> ring


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothResidualWarm.lean -/
section

/-! Concrete residual API aliases. The underlying identities are the actual
sharp-box convolution identities checked in the finite HB development. -/
namespace GoldbachBeaumontResidualSmooth
export GoldbachBeaumontSharpBoxes (groupAF groupInterval slotAF slotInterval
  groupAF_support slotAF_support mem_groupInterval_pos complexCoeffs_mul
  complex_box_split residual_zero_sum residual_one_sum residual_two_sum
  slotLinear slotRectangle residual_one_phase residual_two_phase smooth_slot_value
  scaled_product_window scaled_phase)
end GoldbachBeaumontResidualSmooth
end

/- Source: SmoothRectangleSaving.lean -/
section

open Finset MeasureTheory

namespace GoldbachBeaumontSmooth
noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Per-small-product energy with the concrete logarithmic cutoffs used by the proof. -/
theorem rectangle_scaled_saving (C N L A B D F g H R s : ℕ) (e f : Bool)
    (hg : 1000000 ≤ g) (hN : 1 ≤ N) (hCN : C ≤ N)
    (hH : (g : ℝ)^5000 ≤ H) (hNlo : (H : ℝ)^2 ≤ N) (hNhi : (N : ℝ) ≤ 12*(H : ℝ)^2)
    (hRlo : (H : ℝ)/(2*(g : ℝ)^2000) ≤ R) (hRhi : (R : ℝ) ≤ H) (hRN : R ≤ N)
    (hQR : 2*(g : ℝ)^1000 ≤ R) (hQH : 4*(g : ℝ)^1000*R ≤ H)
    (hlog : 1+Real.log (64*(N : ℝ)) ≤ g)
    (hs : 0 < s) (hsg : s ≤ g^101) (a : ℚ)
    (hQq : g^1000 < a.den) (hqR : a.den ≤ R)
    {α : ℝ} (happrox : |α - (a : ℝ)| ≤ 1/((a.den : ℝ)*R)) :
    (∫ t in α..α+1/(H : ℝ), ‖smoothRectangle C L A B D F e f ((s : ℝ)*t)‖^2) ≤
      (N : ℝ)/(g : ℝ)^600 := by
  have hgR : (1000000 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : 1 ≤ g := (by decide : 1 ≤ 1000000).trans hg
  have hg0 : 0 < g := (by decide : 0 < 1000000).trans_le hg
  have hgp : (0 : ℝ) < g := by exact_mod_cast hg0
  have hHp : (0 : ℝ) < H := (pow_pos hgp 5000).trans_le hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from hN)
  have hRp : (0 : ℝ) < R := by exact_mod_cast a.pos.trans_le hqR
  have hPR : g^899 ≤ R :=
    ((Nat.pow_le_pow_right hg1 (by norm_num : 899≤1000)).trans hQq.le).trans hqR
  have hsP : s*g^899 ≤ g^1000 := by
    calc
      _ ≤ g^101*g^899 := Nat.mul_le_mul_right _ hsg
      _ = _ := by rw [← pow_add]
  have hlogcap (z : ℝ) (hz : 1≤z) (hzN : z≤64*(N : ℝ)) :
      0≤1+Real.log z ∧ 1+Real.log z≤g := by
    have h0 := Real.log_nonneg hz
    have hh := Real.log_le_log (by linarith : 0<z) hzN
    constructor <;> linarith
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrnR : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hlogN := hlogcap N hnR (by linarith only [hnR])
  have hlog10N := hlogcap (10*(N : ℝ)) (by linarith only [hnR])
    (by linarith only [hnR])
  have hlogR := hlogcap R (by exact_mod_cast (show 1 ≤ R from a.pos.trans_le hqR))
    (by linarith only [hnR, hrnR])
  have hsqrt : (Nat.sqrt N : ℝ) ≤ 4*H := by
    have hh : (Nat.sqrt N : ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity : 0 ≤ 4*(H : ℝ))).mp
    nlinarith only [hh,hNhi,sq_nonneg (H : ℝ)]
  have hcell := smoothRectangle_scaled_cell_energy C N L A B D F e f s (g^899) (g^1000) R
    hs hN hCN (pow_pos hg0 _) hPR hRN hsP a hHp hQq hqR
    (by simpa only [Nat.cast_pow] using hQR) (by simpa only [Nat.cast_pow] using hQH) happrox
  have hbudget := scaled_rectangle_scalar_budget hgR hH hNlo hNhi (Nat.cast_nonneg N) le_rfl
    (show (1 : ℝ) ≤ s by exact_mod_cast (show 1 ≤ s from hs)) (show (s : ℝ) ≤ (g : ℝ)^101 by exact_mod_cast hsg)
    (show (g : ℝ)^899 ≤ (g^899 : ℕ) by norm_cast) hRlo hRhi (Nat.cast_nonneg (Nat.sqrt N)) hsqrt
    hlogN.1 hlogN.2 hlog10N.1 hlog10N.2 hlogR.1 hlogR.2
  exact hcell.trans hbudget


end
end GoldbachBeaumontSmooth
end

/- Source: SmoothResidualNormalization.lean -/
section

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open OAI.Problem337
open GoldbachBeaumontSharpBoxes GoldbachBeaumontSmooth

namespace GoldbachBeaumontResidualSmooth
noncomputable section

theorem E_eq_smooth_phase (x : ℝ) : GoldbachBeaumontBilinear.E x = RealPhase.phase x := by
  unfold GoldbachBeaumontBilinear.E RealPhase.phase
  congr 1
  ring

theorem slotInterval_eq {j : ℕ} (b : Choice j) (i : {i // i ∈ slots j}) :
    slotInterval b i = Ioc (2^(b i.1 i.2)-1) (2^(b i.1 i.2+1)-1) :=
  positive_Ico_eq_Ioc (pow_pos (by decide) _) (pow_pos (by decide) _)

theorem slotRectangle_eq_smooth {HC j : ℕ} (b : Choice j)
    (i k : {i // i ∈ slots j}) (hi : i.1 < j+1) (hk : k.1 < j+1)
    (L N : ℕ) (α : ℝ) :
    slotRectangle HC j b i k L N α =
      smoothRectangle N L (2^(b i.1 i.2)-1) (2^(b i.1 i.2+1)-1)
        (2^(b k.1 k.2)-1) (2^(b k.1 k.2+1)-1) (decide (i.1=0)) (decide (k.1=0)) α := by
  rw [smoothRectangle_eq_Ioc]
  unfold slotRectangle
  rw [slotInterval_eq b i,slotInterval_eq b k]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro r hr
  have hm' : m ∈ slotInterval b i := by rwa [slotInterval_eq]
  have hr' : r ∈ slotInterval b k := by rwa [slotInterval_eq]
  rw [smooth_slot_value b i hi hm',smooth_slot_value b k hk hr',E_eq_smooth_phase]
  simp only [mem_Ioc,smoothWeight,decide_eq_true_eq]

theorem slotLinear_eq_smooth {HC j : ℕ} (b : Choice j)
    (i : {i // i ∈ slots j}) (hi : i.1 < j+1) (L N : ℕ) (α : ℝ) :
    slotLinear HC j b i L N α =
      smoothRectangle N L (2^(b i.1 i.2)-1) (2^(b i.1 i.2+1)-1)
        0 1 (decide (i.1=0)) false α := by
  rw [smoothRectangle_one_factor]
  unfold slotLinear
  rw [slotInterval_eq b i]
  apply sum_congr rfl
  intro m hm
  have hm' : m ∈ slotInterval b i := by rwa [slotInterval_eq]
  rw [smooth_slot_value b i hi hm',E_eq_smooth_phase]
  simp only [smoothWeight,decide_eq_true_eq]

/-- Empty smooth remainder, padded by the unit coefficient at one twice. -/
theorem residual_zero_rectangle {HC j : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (hlarge : (slots j).attach \ t = ∅) (C : ℕ) (α : ℝ) :
    (∑ n ∈ Ioc 0 C, (boxProduct HC j b n : ℂ)*GoldbachBeaumontBilinear.E (α*(n : ℝ))) =
      ∑ s ∈ groupInterval b t, groupedCoeff HC j b t s *
        smoothRectangle (C/s) 0 0 1 0 1 false false ((s : ℝ)*α) := by
  rw [residual_zero_sum b t ht hlarge]
  apply sum_congr rfl
  intro s hs
  have hs0 := mem_groupInterval_pos b t hs
  have hdiv : 1 ≤ C/s ↔ s ≤ C := by
    constructor
    · intro h
      have hh := (Nat.le_div_iff_mul_le hs0).mp h
      simpa only [one_mul] using hh
    · intro h
      apply (Nat.le_div_iff_mul_le hs0).mpr
      simpa only [one_mul] using h
  rw [smoothRectangle_zero_factors,E_eq_smooth_phase]
  simp only [mem_Ioc,hs0,true_and,Nat.zero_lt_one,hdiv]
  split_ifs <;> simp [mul_comm α (s : ℝ)]

/-- Exact one-factor and two-factor normalizations use the same finite rectangle API. -/
theorem residual_one_rectangle {HC j : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (i : {i // i ∈ slots j}) (hi : i.1 < j+1)
    (hlarge : (slots j).attach \ t = {i}) (C : ℕ) (α : ℝ) :
    (∑ n ∈ Ioc 0 C, (boxProduct HC j b n : ℂ)*GoldbachBeaumontBilinear.E (α*(n : ℝ))) =
      ∑ s ∈ groupInterval b t, groupedCoeff HC j b t s *
        smoothRectangle (C/s) 0 (2^(b i.1 i.2)-1) (2^(b i.1 i.2+1)-1)
          0 1 (decide (i.1=0)) false ((s : ℝ)*α) := by
  rw [residual_one_phase b t ht i hlarge]
  apply sum_congr rfl
  intro s hs
  rw [slotLinear_eq_smooth b i hi,Nat.zero_div]

theorem residual_two_rectangle {HC j : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (i k : {i // i ∈ slots j}) (hik : i ≠ k) (hi : i.1 < j+1) (hk : k.1 < j+1)
    (hlarge : (slots j).attach \ t = {i,k}) (C : ℕ) (α : ℝ) :
    (∑ n ∈ Ioc 0 C, (boxProduct HC j b n : ℂ)*GoldbachBeaumontBilinear.E (α*(n : ℝ))) =
      ∑ s ∈ groupInterval b t, groupedCoeff HC j b t s *
        smoothRectangle (C/s) 0 (2^(b i.1 i.2)-1) (2^(b i.1 i.2+1)-1)
          (2^(b k.1 k.2)-1) (2^(b k.1 k.2+1)-1)
          (decide (i.1=0)) (decide (k.1=0)) ((s : ℝ)*α) := by
  rw [residual_two_phase b t ht i k hik hlarge]
  apply sum_congr rfl
  intro s hs
  rw [slotRectangle_eq_smooth b i k hi hk,Nat.zero_div]



end
end GoldbachBeaumontResidualSmooth
end

/- Source: SmoothResidualEnergy.lean -/
section

open Finset MeasureTheory
open GoldbachBeaumontSharpBoxes GoldbachBeaumontSmooth

namespace GoldbachBeaumontResidualSmooth
noncomputable section

/-- Zero, one and two remaining smooth slots all have one common exact form. -/
theorem residual_rectangle_shape {HC j : ℕ} (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (hcard : ((slots j).attach \ t).card ≤ 2)
    (hsmooth : ∀ i ∈ (slots j).attach \ t, i.1 < j+1) (C : ℕ) :
    ∃ A B D F : ℕ, ∃ e f : Bool, ∀ θ : ℝ,
      (∑ n ∈ Ioc 0 C, (boxProduct HC j b n : ℂ)*GoldbachBeaumontBilinear.E (θ*(n : ℝ))) =
        ∑ s ∈ groupInterval b t, groupedCoeff HC j b t s *
          smoothRectangle (C/s) 0 A B D F e f ((s : ℝ)*θ) := by
  classical
  let S := (slots j).attach \ t
  by_cases hzero : S = ∅
  · exact ⟨0,1,0,1,false,false,fun θ => residual_zero_rectangle b t ht hzero C θ⟩
  by_cases hone : S.card = 1
  · obtain ⟨i,hi⟩ := card_eq_one.mp hone
    have hs : i.1 < j+1 := hsmooth i (by change i∈S; rw [hi]; simp)
    exact ⟨2^(b i.1 i.2)-1,2^(b i.1 i.2+1)-1,0,1,decide (i.1=0),false,
      fun θ => residual_one_rectangle b t ht i hs hi C θ⟩
  · have htwo : S.card = 2 := by
      have hz : S.card ≠ 0 := fun h => hzero (card_eq_zero.mp h)
      change S.card ≤ 2 at hcard
      omega
    obtain ⟨i,k,hik,hikS⟩ := card_eq_two.mp htwo
    have hi : i.1 < j+1 := hsmooth i (by change i∈S; rw [hikS]; simp)
    have hk : k.1 < j+1 := hsmooth k (by change k∈S; rw [hikS]; simp)
    exact ⟨2^(b i.1 i.2)-1,2^(b i.1 i.2+1)-1,
      2^(b k.1 k.2)-1,2^(b k.1 k.2+1)-1,decide (i.1=0),decide (k.1=0),
      fun θ => residual_two_rectangle b t ht i k hik hi hk hikS C θ⟩

set_option maxRecDepth 100000 in
/-- The exact small-product interval has the required cardinality and divisor-moment budget. -/
theorem small_group_budget {HC j N g : ℕ} (hj : j<3) (b : Choice j)
    (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (hU : upperNat b t ≤ g^101) (hUN : upperNat b t ≤ N)
    (hlog : 1+Real.log (64*(N : ℝ)) ≤ g) :
    ((groupInterval b t).card : ℝ) ≤ (g : ℝ)^101 ∧
      (∀ s ∈ groupInterval b t, 0<s ∧ s≤g^101) ∧
      (∑ s ∈ groupInterval b t, ‖groupedCoeff HC j b t s‖^2) ≤ (g : ℝ)^139 := by
  have hlow := lowerNat_pos b t
  have hup : 0<upperNat b t := hlow.trans_le (lowerNat_le_upperNat b t)
  have hcard : (groupInterval b t).card ≤ upperNat b t := by
    unfold groupInterval
    rw [row_endpoint,Nat.card_Ico]
    omega
  have hmem : ∀ s ∈ groupInterval b t, 0<s ∧ s≤upperNat b t := by
    intro s hs
    change s∈Ico (lowerNat b t) (lowerNat b t+rowLength b t) at hs
    rw [row_endpoint] at hs
    have hh := mem_Ico.mp hs
    omega
  have hsub : groupInterval b t ⊆ Icc 1 (upperNat b t) := by
    intro s hs
    have hh := hmem s hs
    exact mem_Icc.mpr ⟨by omega,hh.2⟩
  have hUreal : (upperNat b t : ℝ) ≤ (g : ℝ)^101 := by exact_mod_cast hU
  have henergy : (∑ s ∈ groupInterval b t, ‖groupedCoeff HC j b t s‖^2) ≤
      (upperNat b t : ℝ)*(1+Real.log (upperNat b t))^38 := by
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
    simpa only [groupedCoeff] using subproduct_energy_log38 (H:=HC) hj b t ht (Nat.succ_le_of_lt hup)
  have hlogU0 : 0≤1+Real.log (upperNat b t : ℝ) := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤upperNat b t by exact_mod_cast hup)
    linarith
  have hlogU : 1+Real.log (upperNat b t : ℝ) ≤ g := by
    have hpos : (0 : ℝ)<upperNat b t := by exact_mod_cast hup
    have hUNr : (upperNat b t : ℝ)≤N := by exact_mod_cast hUN
    have hh := Real.log_le_log hpos (show (upperNat b t : ℝ)≤64*(N : ℝ) by nlinarith)
    linarith
  refine ⟨by exact_mod_cast hcard.trans hU, fun s hs => ⟨(hmem s hs).1,(hmem s hs).2.trans hU⟩, ?_⟩
  have hh := mul_le_mul hUreal (pow_le_pow_left₀ hlogU0 hlogU 38)
    (pow_nonneg hlogU0 _) (by positivity)
  apply henergy.trans
  convert hh using 1 <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Actual unconditional residual HB3-box energy on a high-denominator cell.
The displayed polynomial is definitionally the project's `boxPrefix`. -/
theorem residual_box_cell {HC j C N g H R : ℕ} (hj : j<3) (hCN : C≤N)
    (b : Choice j) (t : Finset {i // i ∈ slots j}) (ht : t ⊆ (slots j).attach)
    (hU : upperNat b t ≤ g^101) (hUN : upperNat b t ≤ N)
    (hcard : ((slots j).attach \ t).card ≤ 2)
    (hsmooth : ∀ i ∈ (slots j).attach \ t, i.1<j+1)
    (hg : 1000000≤g) (hN : 1≤N)
    (hH : (g : ℝ)^5000 ≤ H) (hNlo : (H : ℝ)^2≤N) (hNhi : (N : ℝ)≤12*(H : ℝ)^2)
    (hRlo : (H : ℝ)/(2*(g : ℝ)^2000)≤R) (hRhi : (R : ℝ)≤H) (hRN : R≤N)
    (hQR : 2*(g : ℝ)^1000≤R) (hQH : 4*(g : ℝ)^1000*R≤H)
    (hlog : 1+Real.log (64*(N : ℝ))≤g)
    (a : ℚ) (hQq : g^1000<a.den) (hqR : a.den≤R) {α : ℝ}
    (happrox : |α-(a : ℝ)|≤1/((a.den : ℝ)*R)) :
    (∫ θ in α..α+1/(H : ℝ),
      ‖∑ n ∈ Ioc 0 C, (boxProduct HC j b n : ℂ)*GoldbachBeaumontBilinear.E (θ*(n : ℝ))‖^2) ≤
      (N : ℝ)/(g : ℝ)^30 := by
  obtain ⟨A,B,D,F,e,f,hshape⟩ := residual_rectangle_shape (HC:=HC) b t ht hcard hsmooth C
  obtain ⟨hcardS,hmem,hcoeff⟩ := small_group_budget (HC:=HC) hj b t ht hU hUN hlog
  have hgp : (0 : ℝ)<g := by exact_mod_cast ((by decide : 0 < 1000000).trans_le hg)
  have hg1 : (1 : ℝ)≤g := by exact_mod_cast ((by decide : 1 ≤ 1000000).trans hg)
  have hHp : (0 : ℝ)<H := (pow_pos hgp 5000).trans_le hH
  have huv : α≤α+1/(H : ℝ) := le_add_of_nonneg_right (one_div_nonneg.mpr hHp.le)
  have hEach : ∀ s ∈ groupInterval b t,
      (∫ θ in α..α+1/(H : ℝ), ‖smoothRectangle (C/s) 0 A B D F e f ((s : ℝ)*θ)‖^2) ≤
        (N : ℝ)/(g : ℝ)^600 := by
    intro s hs
    exact rectangle_scaled_saving (C/s) N 0 A B D F g H R s e f
      hg hN ((Nat.div_le_self C s).trans hCN) hH hNlo hNhi hRlo hRhi hRN hQR hQH hlog
      (hmem s hs).1 (hmem s hs).2 a hQq hqR happrox
  have hFcont (s : ℕ) : Continuous (fun θ => smoothRectangle (C/s) 0 A B D F e f ((s : ℝ)*θ)) :=
    (continuous_smoothRectangle (C/s) 0 A B D F e f).comp (continuous_const.mul continuous_id)
  have hh := small_product_combination_saving (groupInterval b t) (groupedCoeff HC j b t)
    (fun s θ => smoothRectangle (C/s) 0 A B D F e f ((s : ℝ)*θ)) (fun s _ => hFcont s)
    huv (Nat.cast_nonneg N) hg1 hcardS hcoeff hEach
  calc
    _ = ∫ θ in α..α+1/(H : ℝ), ‖∑ s ∈ groupInterval b t, groupedCoeff HC j b t s *
        smoothRectangle (C/s) 0 A B D F e f ((s : ℝ)*θ)‖^2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [hshape θ]
    _ ≤ (N : ℝ)/(g : ℝ)^360 := hh
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos hgp 30)
      (pow_le_pow_right₀ hg1 (by norm_num : 30≤360))


end
end GoldbachBeaumontResidualSmooth
end

/- Source: BeaumontHighScales.lean -/
section

/-! Elementary size conditions for grouping the Heath--Brown factors and
separating the rational approximations in the high-denominator branch. -/


open Filter
open scoped Topology

namespace BeaumontHighScales

open GoldbachBeaumontParameters BeaumontLowScales

theorem eventually_upper_power :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ)^(17/36 : ℝ) ≤ (upperFactor X : ℝ) := by
  simpa only [upperFactor, physicalWindow, Nat.div_div_eq_div_mul, Nat.mul_comm] using
    eventually_divided_window_power 100

theorem rational_separation_scale {X : ℕ} (hg : 2 ≤ logScale X) :
    4*denominatorCutoff X*approximationBound X ≤ window X := by
  have hpow : 4 ≤ logScale X^1000 := by
    calc
      _ ≤ logScale X^2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by omega : 1 ≤ logScale X) (by norm_num : 2 ≤ 1000)
  have hsq : 4*logScale X^1000 ≤ logScale X^2000 := by
    rw [show 2000 = 1000*2 by norm_num, pow_mul]
    nlinarith
  have hdiv : logScale X^2000*approximationBound X ≤ window X :=
    Nat.mul_div_le (window X) (logScale X^2000)
  exact (Nat.mul_le_mul_right (approximationBound X) hsq).trans hdiv

/-- The exact eventual scalar conditions required by the balanced-factor
grouping and by the endpoint Dirichlet split. The third condition is expressed
using a floor, so it can be rewritten directly with `rangeCutoff`. -/
theorem eventually_grouping_geometry :
    ∀ᶠ X : ℕ in atTop,
      lowerFactor X^2 ≤ upperFactor X ∧
      64*scale X < upperFactor X^3 ∧
      2*⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ ≤ upperFactor X ∧
      4*denominatorCutoff X*approximationBound X ≤ window X ∧
      2*denominatorCutoff X ≤ approximationBound X := by
  filter_upwards [eventually_upper_power, eventually_progression_power,
      eventually_mul_logScale_power_le_rpow 1 (by norm_num) 202 (17/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 384 (by norm_num) 0 (5/12) (by norm_num),
      eventually_mul_logScale_power_le_rpow 6 (by norm_num) 0 (5/36) (by norm_num),
      eventually_mul_logScale_power_le_rpow 1 (by norm_num) 1000 (17/36) (by norm_num),
      logScale_tendsto.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)]
    with X hB hh hA hlarge hroot hQ hg hX
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX0 : 0 ≤ (X : ℝ) := hXp.le
  have hN : (scale X : ℝ) = 3*(X : ℝ) := by simp [scale]
  have hA' : lowerFactor X^2 ≤ upperFactor X := by
    have ha : (logScale X : ℝ)^202 ≤ (upperFactor X : ℝ) := by
      simpa only [one_mul] using hA.trans hB
    exact_mod_cast (by simpa only [lowerFactor, Nat.cast_pow, ← pow_mul] using ha :
      ((lowerFactor X^2 : ℕ) : ℝ) ≤ (upperFactor X : ℝ))
  have hB0 : 0 ≤ (upperFactor X : ℝ) := by positivity
  have hBcube := pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) hB 3
  have hBcube' : (X : ℝ)^(17/12 : ℝ) ≤ (upperFactor X : ℝ)^3 := by
    simpa only [← Real.rpow_mul_natCast hX0, Nat.cast_ofNat, show (17/36 : ℝ)*3 = 17/12 by norm_num] using hBcube
  have hlarge' : 384 ≤ (X : ℝ)^(5/12 : ℝ) := by simpa using hlarge
  have hlargeX := mul_le_mul_of_nonneg_right hlarge' hX0
  have hprod : (X : ℝ)^(5/12 : ℝ)*(X : ℝ) = (X : ℝ)^(17/12 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one (X : ℝ)]
    rw [← Real.rpow_add hXp]
    congr 1
    norm_num
  rw [hprod] at hlargeX
  have hcube : 64*scale X < upperFactor X^3 := by
    have h : 192*(X : ℝ) < (upperFactor X : ℝ)^3 := by
      linarith [hlargeX.trans hBcube']
    have hh : 64*(scale X:ℝ)<(upperFactor X:ℝ)^3 := by rw [hN]; nlinarith only [h]
    exact_mod_cast hh
  have hroot' : 6 ≤ (X : ℝ)^(5/36 : ℝ) := by simpa using hroot
  have hrootX := mul_le_mul_of_nonneg_right hroot' (Real.rpow_nonneg hX0 (1/3 : ℝ))
  rw [← Real.rpow_add hXp] at hrootX
  norm_num only [show (5/36 : ℝ)+1/3 = 17/36 by norm_num] at hrootX
  have hcut : ((⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ : ℕ) : ℝ) ≤
      3*(X : ℝ)^(1/3 : ℝ) := by
    calc
      _ ≤ (scale X : ℝ)^(1/3 : ℝ) := Nat.floor_le (by positivity)
      _ = (3 : ℝ)^(1/3 : ℝ)*(X : ℝ)^(1/3 : ℝ) := by rw [hN,Real.mul_rpow (by norm_num) hX0]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num))
        (Real.rpow_nonneg hX0 _)
  have hcut' : 2*⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ ≤ upperFactor X := by
    have ht : 2*((⌊(scale X : ℝ)^(1/3 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (upperFactor X : ℝ) := by
      linarith [hrootX.trans hB]
    exact_mod_cast ht
  have hQh : denominatorCutoff X ≤ progressionWindow X := by
    exact_mod_cast (by simpa only [one_mul,denominatorCutoff,Nat.cast_pow] using hQ.trans hh :
      (denominatorCutoff X : ℝ) ≤ (progressionWindow X : ℝ))
  have hqR : 2*denominatorCutoff X ≤ approximationBound X := by
    have hr : 24*progressionWindow X ≤ approximationBound X :=
      Nat.mul_div_le (approximationBound X) 24
    omega
  exact ⟨hA',hcube,hcut',rational_separation_scale hg,hqR⟩

set_option maxHeartbeats 100000 in
theorem eventually_auxiliary_geometry :
    ∀ᶠ X : ℕ in atTop,
      0 < physicalWindow X ∧
      (approximationBound X : ℝ)*(logScale X : ℝ)^100 ≤ (physicalWindow X : ℝ) ∧
      4*logScale X^12 ≤ window X ∧
      6*(physicalWindow X : ℝ)/(window X : ℝ) ≤ 1 := by
  filter_upwards [eventually_grouping_geometry,
      logScale_tendsto.eventually_ge_atTop 24] with X hgeom hg
  have hg1 : 1 ≤ logScale X := (by decide : 1 ≤ 24).trans hg
  have hgQ : logScale X ≤ denominatorCutoff X := by
    change logScale X ≤ logScale X^1000
    exact Nat.le_self_pow (n := 1000) (by decide : 1000 ≠ 0) (logScale X)
  have hRH : approximationBound X ≤ window X := Nat.div_le_self _ _
  have hQH : denominatorCutoff X ≤ window X :=
    (Nat.le_mul_of_pos_left (denominatorCutoff X) (by decide : 0 < 2)).trans
      (hgeom.2.2.2.2.trans hRH)
  have hH24 : 24 ≤ window X := hg.trans (hgQ.trans hQH)
  have hHp : 0 < (window X : ℝ) := by
    exact_mod_cast (by decide : 0 < 24).trans_le hH24
  have hphys : 0 < physicalWindow X := Nat.div_pos hH24 (by norm_num)
  have hpow : 24*logScale X^100 ≤ logScale X^2000 := by
    calc
      _ ≤ logScale X*logScale X^100 := Nat.mul_le_mul_right _ hg
      _ = logScale X^101 := (pow_succ' (logScale X) 100).symm
      _ ≤ _ := pow_le_pow_right₀ hg1 (by norm_num : 101 ≤ 2000)
  have hdiv : logScale X^2000*approximationBound X ≤ window X :=
    Nat.mul_div_le (window X) (logScale X^2000)
  have hprod : approximationBound X*logScale X^100 ≤ physicalWindow X := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 24)).2
    calc
      _ = (24*logScale X^100)*approximationBound X := by ac_rfl
      _ ≤ logScale X^2000*approximationBound X := Nat.mul_le_mul_right _ hpow
      _ ≤ window X := hdiv
  have h12 : 4*logScale X^12 ≤ window X := by
    calc
      _ ≤ logScale X*logScale X^12 := Nat.mul_le_mul_right _ ((by decide : 4 ≤ 24).trans hg)
      _ = logScale X^13 := (pow_succ' (logScale X) 12).symm
      _ ≤ logScale X^1000 := pow_le_pow_right₀ hg1 (by norm_num : 13 ≤ 1000)
      _ ≤ window X := by simpa only [denominatorCutoff] using hQH
  have h24 : 24*(physicalWindow X : ℝ) ≤ (window X : ℝ) := by
    exact_mod_cast Nat.mul_div_le (window X) 24
  refine ⟨hphys, by exact_mod_cast hprod, h12, ?_⟩
  exact (div_le_iff₀ hHp).2 (by
    nlinarith only [h24, (Nat.cast_nonneg (physicalWindow X) : (0 : ℝ) ≤ (physicalWindow X : ℝ))])


theorem eventually_residual_geometry :
    ∀ᶠ X : ℕ in atTop,
      logScale X^5000 ≤ window X ∧
      window X^2 ≤ scale X ∧ scale X ≤ 12*window X^2 ∧
      (window X : ℝ)/(2*(logScale X : ℝ)^2000) ≤ (approximationBound X : ℝ) ∧
      approximationBound X ≤ window X ∧
      1+Real.log (64*(scale X : ℝ)) ≤ (logScale X : ℝ) := by
  filter_upwards [eventually_grouping_geometry, eventually_logScale_power_le 10000,
      logScale_tendsto.eventually_ge_atTop 32, eventually_ge_atTop (1 : ℕ)]
    with X hgeom hpower hg hX
  have hgpos : 0 < logScale X := logScale_pos X
  have hgposr : (0 : ℝ) < logScale X := by exact_mod_cast hgpos
  have hH : logScale X^5000 ≤ window X := by
    change logScale X^5000 ≤ Nat.sqrt X
    apply Nat.le_sqrt'.2
    rw [← pow_mul, show 5000*2 = 10000 by norm_num]
    exact hpower
  have hH1 : 1 ≤ window X := Nat.le_sqrt'.2 (by simpa using hX)
  have hsq : window X^2 ≤ X := Nat.sqrt_le' X
  have hsuc : X < (window X+1)^2 := Nat.lt_succ_sqrt' X
  have hNlo : window X^2 ≤ scale X :=
    hsq.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hNhi : scale X ≤ 12*window X^2 := by
    have hww : window X ≤ window X^2 := Nat.le_self_pow (by decide : 2 ≠ 0) _
    change 3*X ≤ 12*window X^2
    nlinarith only [hsuc,hH1,hww]
  have hR1 : 1 ≤ approximationBound X := by
    have hQpos : 0 < denominatorCutoff X := by
      change 0 < logScale X^1000
      exact pow_pos hgpos 1000
    exact hQpos.trans_le ((Nat.le_mul_of_pos_left (denominatorCutoff X)
      (by decide : 0 < 2)).trans hgeom.2.2.2.2)
  have hf : (window X : ℝ) < (logScale X : ℝ)^2000*
      ((approximationBound X : ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ (window X)
      (show 0 < logScale X^2000 from pow_pos hgpos 2000)
  have hR1r : (1 : ℝ) ≤ approximationBound X := by exact_mod_cast hR1
  have hden : 0 < (logScale X : ℝ)^2000 := pow_pos hgposr 2000
  have hRlo : (window X : ℝ)/(2*(logScale X : ℝ)^2000) ≤ (approximationBound X : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).2
    have hm := mul_le_mul_of_nonneg_left
      (show (approximationBound X : ℝ)+1 ≤ 2*(approximationBound X : ℝ) by linarith only [hR1r]) hden.le
    calc
      (window X : ℝ) ≤ (logScale X : ℝ)^2000*(2*(approximationBound X : ℝ)) := hf.le.trans hm
      _ = (approximationBound X : ℝ)*(2*(logScale X : ℝ)^2000) := by ac_rfl
  exact ⟨hH,hNlo,hNhi,hRlo,Nat.div_le_self _ _,
    natural_log_margin hX hg⟩


end BeaumontHighScales



end

/- Source: BeaumontCompletionBase.lean -/
section

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace GoldbachBeaumontCompletion
noncomputable section
open GoldbachBeaumontParameters GoldbachBeaumontHeathBrown
open GoldbachBeaumontSharpBoxes GoldbachBeaumontHigh BeaumontHighScales

def mobiusCutoff (X : ℕ) : ℕ := rangeCutoff (scale X:ℝ) 3

lemma mobiusCutoff_bounds {X : ℕ} (hX : 1 ≤ X) :
    0 < mobiusCutoff X ∧ mobiusCutoff X ≤ scale X ∧
      scale X < (mobiusCutoff X+1)^3 := by
  have hN : (1:ℝ) ≤ (scale X:ℝ) := by
    exact_mod_cast (show 1 ≤ scale X by dsimp [scale]; omega)
  have hr : 0 ≤ (scale X:ℝ)^(1/3:ℝ) := by positivity
  have hroot : 1 ≤ (scale X:ℝ)^(1/3:ℝ) := Real.one_le_rpow hN (by norm_num)
  have hcut1 : 1 ≤ mobiusCutoff X := by
    change 1 ≤ ⌊(scale X:ℝ)^(1/(3:ℝ))⌋₊
    exact (Nat.le_floor_iff hr).2 hroot
  have hcutle : (mobiusCutoff X:ℝ) ≤ (scale X:ℝ) := by
    apply (Nat.floor_le hr).trans
    exact Real.rpow_le_self_of_one_le hN (by norm_num)
  exact ⟨hcut1,by exact_mod_cast hcutle,
    lt_rangeCutoff_power (Nat.cast_nonneg _) (by decide : 0 < 3) le_rfl⟩

def reducedRational (a q : ℕ) (hq : 0 < q) (hc : a.Coprime q) : ℚ :=
  Rat.mk' (a:ℤ) q (Nat.ne_of_gt hq) (by simpa using hc)

lemma reducedRational_den (a q : ℕ) (hq : 0 < q) (hc : a.Coprime q) :
    (reducedRational a q hq hc).den=q := rfl

lemma reducedRational_cast (a q : ℕ) (hq : 0 < q) (hc : a.Coprime q) :
    ((reducedRational a q hq hc):ℝ)=(a:ℝ)/(q:ℝ) := by
  rw [Rat.cast_def]
  simp [reducedRational]

lemma log2_scale_count (X : ℕ) : ((Nat.log 2 (scale X)+1:ℕ):ℝ) ≤ 2*(logScale X:ℝ) := by
  have hm : Nat.log 2 (scale X) ≤ logScale X := Nat.log_mono_right (by dsimp [scale]; omega)
  have hp := logScale_pos X
  exact_mod_cast (by omega : Nat.log 2 (scale X)+1 ≤ 2*logScale X)

lemma typeII_q_log {X q : ℕ} (hX : 1 ≤ X) (hg : 32 ≤ logScale X)
    (hq : 0 < q) (hqR : q ≤ approximationBound X) :
    1+Real.log (2*(q:ℝ)) ≤ (logScale X:ℝ) := by
  have hqH : q ≤ window X := hqR.trans (Nat.div_le_self _ _)
  have hqN : q ≤ scale X := hqH.trans ((Nat.sqrt_le_self X).trans (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))
  have hqr : (q:ℝ) ≤ (scale X:ℝ) := by exact_mod_cast hqN
  have hn := natural_log_margin hX hg
  have hl := Real.log_le_log (show 0 < 2*(q:ℝ) by positivity)
    (show 2*(q:ℝ) ≤ 64*(scale X:ℝ) by nlinarith)
  linarith only [hn,hl]

/-- All active boxes with a balanced grouping satisfy the actual cell estimate. -/
theorem eventually_typeII_cells :
    ∀ᶠ X : ℕ in atTop, ∀ C ≤ scale X, ∀ j < 3, ∀ b ∈ activeChoices
      (scale X) (mobiusCutoff X) j (Ioc 0 C), ∀ α : ℝ, ∀ a q : ℕ,
      denominatorCutoff X < q → q ≤ approximationBound X → a.Coprime q →
      |α-(a:ℝ)/q| ≤ 1/((q:ℝ)*(approximationBound X:ℝ)) →
      (∃ t ⊆ (slots j).attach,
        (lowerFactor X:ℝ) ≤ ∏ i ∈ t,upper j b i ∧
          (∏ i ∈ t,upper j b i) ≤ (upperFactor X:ℝ)) →
      (∫ θ in α..(α+1/(window X:ℝ)),
        ‖boxPrefix (mobiusCutoff X) j b C θ‖^2) ≤ (scale X:ℝ)/(logScale X:ℝ)^30 := by
  filter_upwards [eventually_auxiliary_geometry,
    logScale_tendsto.eventually_ge_atTop 128,eventually_ge_atTop (1:ℕ)] with X haux hg hX
  intro C hCN j hj b hb α a q hqlo hqhi hc ha ht
  obtain ⟨t,ht,hlo,hhi⟩ := ht
  have hq : 0 < q := (pow_pos (logScale_pos X) 1000).trans hqlo
  have hHp : 0 < window X := haux.1.trans_le (Nat.div_le_self _ _)
  have hHr : 0 < (window X:ℝ) := by exact_mod_cast hHp
  have hRp : 0 < (approximationBound X:ℝ) := by exact_mod_cast hq.trans_le hqhi
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hgR : (128:ℝ) ≤ logScale X := by exact_mod_cast hg
  have hg1 : (1:ℝ) ≤ logScale X := by linarith
  have happ : |α-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply ha.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hh : (q:ℝ) ≤ approximationBound X := by exact_mod_cast hqhi
    nlinarith
  have hwidth : 6*(physicalWindow X:ℝ)*(1/(window X:ℝ)) ≤ 1 := by
    simpa only [mul_one_div] using haux.2.2.2
  have hbound : (upperFactor X:ℝ)*(logScale X:ℝ)^100 ≤ physicalWindow X := by
    exact_mod_cast Nat.div_mul_le_self (physicalWindow X) (logScale X^100)
  have hhi' : (∏ i ∈ t,upper j b i)*(logScale X:ℝ)^100 ≤ physicalWindow X :=
    (mul_le_mul_of_nonneg_right hhi (by positivity)).trans hbound
  have hqlo' : (logScale X:ℝ)^100 ≤ (q:ℝ) := by
    have hq' : (logScale X:ℝ)^1000 ≤ (q:ℝ) := by exact_mod_cast hqlo.le
    exact (pow_le_pow_right₀ hg1 (by decide : 100 ≤ 1000)).trans hq'
  have hqhi' : (q:ℝ)*(logScale X:ℝ)^100 ≤ physicalWindow X :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqhi) (by positivity)).trans haux.2.1
  apply typeII_box_cell hj b hb hCN t ht α (1/(window X:ℝ)) (logScale X:ℝ)
    hgR haux.1 hq (by positivity) hwidth (a:ℤ) hc.isCoprime
    (by simpa using happ) (by simpa [lowerFactor] using hlo) hhi' hqlo' hqhi'
    (typeII_q_log hX ((by decide : 32 ≤ 128).trans hg) hq hqhi)
    (natural_log_margin hX ((by decide : 32 ≤ 128).trans hg))

end
end GoldbachBeaumontCompletion


end

/- Source: BeaumontHighAssembly.lean -/
section

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace GoldbachBeaumontCompletion
noncomputable section
open GoldbachBeaumontParameters GoldbachBeaumontHeathBrown
open GoldbachBeaumontSharpBoxes GoldbachBeaumontHigh BeaumontHighScales

/-- This internal interface refers only to actual HB coefficients and actual
prime-polynomial frequencies. It is discharged by the smooth rectangle proof. -/
def residualCells : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ C ≤ scale X, ∀ j < 3, ∀ b : Choice j,
    ∀ t ⊆ (slots j).attach,
    upperNat b t ≤ logScale X^101 → upperNat b t ≤ scale X →
    ((slots j).attach \ t).card ≤ 2 →
    (∀ i ∈ (slots j).attach \ t, i.1 < j+1) →
    ∀ α : ℝ, ∀ a : ℚ,
    denominatorCutoff X < a.den → a.den ≤ approximationBound X →
    |α-(a:ℝ)| ≤ 1/((a.den:ℝ)*(approximationBound X:ℝ)) →
    (∫ θ in α..(α+1/(window X:ℝ)),
      ‖boxPrefix (mobiusCutoff X) j b C θ‖^2) ≤ (scale X:ℝ)/(logScale X:ℝ)^30

theorem eventually_all_box_cells (hres : residualCells) :
    ∀ᶠ X : ℕ in atTop, ∀ C ≤ scale X, ∀ j < 3, ∀ b ∈ activeChoices
      (scale X) (mobiusCutoff X) j (Ioc 0 C), ∀ α : ℝ, ∀ a q : ℕ,
      denominatorCutoff X < q → q ≤ approximationBound X → a.Coprime q →
      |α-(a:ℝ)/q| ≤ 1/((q:ℝ)*(approximationBound X:ℝ)) →
      (∫ θ in α..(α+1/(window X:ℝ)),
        ‖boxPrefix (mobiusCutoff X) j b C θ‖^2) ≤ (scale X:ℝ)/(logScale X:ℝ)^30 := by
  filter_upwards [hres,eventually_typeII_cells,eventually_grouping_geometry,
    eventually_residual_geometry,eventually_ge_atTop (1:ℕ)]
    with X hres htype hgeom hrgeom hX
  intro C hCN j hj b hb α a q hqlo hqhi hc happ
  have hcut := mobiusCutoff_bounds hX
  obtain ⟨n,hn,hnz⟩ := (mem_filter.mp hb).2
  have hnN := (mem_Ioc.mp hn).2.trans hCN
  have hA : (1:ℝ) ≤ lowerFactor X := by
    exact_mod_cast one_le_pow₀ (logScale_pos X) (n:=101)
  have hAB : (lowerFactor X:ℝ)^2 ≤ upperFactor X := by exact_mod_cast hgeom.1
  have hN : (n:ℝ) ≤ scale X := by exact_mod_cast hnN
  have hB : 64*(scale X:ℝ) < (upperFactor X:ℝ)^3 := by exact_mod_cast hgeom.2.1
  rcases box_grouping hj b hnz hA hAB hN hB with hbalanced | hrest
  · exact htype C hCN j hj b hb α a q hqlo hqhi hc happ hbalanced
  let S := (slots j).attach
  let t := S.filter (fun i => upper j b i < (lowerFactor X:ℝ))
  have ht : t ⊆ S := filter_subset _ _
  have hts : upperNat b t ≤ logScale X^101 := by
    have hh : (upperNat b t:ℝ) < (lowerFactor X:ℝ) := by
      simpa only [cast_upperNat] using hrest.1
    exact_mod_cast hh.le
  have hg1 : 1 ≤ logScale X := logScale_pos X
  have htN : upperNat b t ≤ scale X := hts.trans
    ((pow_le_pow_right₀ hg1 (by decide : 101 ≤ 5000)).trans
      (hrgeom.1.trans ((Nat.sqrt_le_self X).trans (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))))
  have hcomp (i : {i // i ∈ slots j}) (hi : i ∈ S \ t) : (upperFactor X:ℝ) < upper j b i := by
    have hh := mem_sdiff.mp hi
    rcases hrest.2.2 i hh.1 with hs | hb
    · exact False.elim (hh.2 (mem_filter.mpr ⟨hh.1,hs⟩))
    · exact hb
  have hcompcard : (S \ t).card ≤ 2 := by
    apply (card_le_card (show S \ t ⊆ S.filter (fun i => (upperFactor X:ℝ) < upper j b i) from
      fun i hi => mem_filter.mpr ⟨(mem_sdiff.mp hi).1,hcomp i hi⟩)).trans hrest.2.1
  have hlarge : ∀ i ∈ S \ t, i.1 < j+1 := by
    intro i hi
    apply large_box_factor_is_smooth (mem_filter.mp hb).1 (Nat.ne_of_gt hcut.1)
      (B:=(upperFactor X:ℝ)) _ (hcomp i hi)
    have hh : 2*mobiusCutoff X ≤ upperFactor X := hgeom.2.2.1
    exact_mod_cast hh
  have hq : 0 < q := (pow_pos (logScale_pos X) 1000).trans hqlo
  let r := reducedRational a q hq hc
  have hrden : r.den=q := rfl
  have hrcast : (r:ℝ)=(a:ℝ)/q := reducedRational_cast a q hq hc
  exact hres C hCN j hj b t ht hts htN hcompcard hlarge α r
    (by simpa only [hrden] using hqlo) (by simpa only [hrden] using hqhi)
    (by simpa only [hrden,hrcast] using happ)

theorem eventually_high_band_cells (hres : residualCells) :
    ∀ᶠ X : ℕ in atTop, ∀ L D : ℕ, L+D+1 ≤ scale X →
      ∀ α : ℝ, ∀ a q : ℕ,
      denominatorCutoff X < q → q ≤ approximationBound X → a.Coprime q →
      |α-(a:ℝ)/q| ≤ 1/((q:ℝ)*(approximationBound X:ℝ)) →
      (∫ θ in α..(α+1/(window X:ℝ)), ‖BulkCircle.S L D θ‖^2) ≤ 
        (scale X:ℝ)/(logScale X:ℝ)^3 := by
  filter_upwards [eventually_all_box_cells hres,eventually_auxiliary_geometry,
    logScale_tendsto.eventually_ge_atTop 128,eventually_ge_atTop (1:ℕ)]
    with X hboxes haux hg hX
  intro L D hupper α a q hqlo hqhi hc happ
  have hcut := mobiusCutoff_bounds hX
  have hHp : 0 < window X := haux.1.trans_le (Nat.div_le_self _ _)
  have hHpR : 0 < (window X:ℝ) := by exact_mod_cast hHp
  have hgR : (16:ℝ) ≤ logScale X := by exact_mod_cast ((by decide : 16 ≤ 128).trans hg)
  have hN : 1 ≤ scale X := hX.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hNpos : 0 < (scale X:ℝ) := by exact_mod_cast hN
  have hlog : Real.log (scale X:ℝ) ≤ (logScale X:ℝ) := by
    have hm := natural_log_margin hX ((by decide : 32 ≤ 128).trans hg)
    have hh := Real.log_le_log hNpos (show (scale X:ℝ) ≤ 64*(scale X:ℝ) by nlinarith)
    linarith only [hm,hh]
  have hlarge : 4*(logScale X:ℝ)^12 ≤ window X := by exact_mod_cast haux.2.2.1
  apply band_cell_of_mangoldt (scale X) L D (window X) α (logScale X:ℝ)
    hN hupper hHp hgR hlog hlarge
  intro C hCN
  have he := mangoldt_prefix_energy (scale X) (mobiusCutoff X) C hCN hcut.2.1 hcut.2.2
    (logScale X:ℝ) α (α+1/(window X:ℝ)) hgR (by linarith [one_div_pos.mpr hHpR])
    (log2_scale_count X) (fun j hj b hb => hboxes C hCN j hj b hb α a q hqlo hqhi hc happ)
  simpa only [mangoldtPrefix_eq_prefixPoly] using he

end
end GoldbachBeaumontCompletion


end

/- Source: BeaumontResidualCompletion.lean -/
section

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace GoldbachBeaumontCompletion
noncomputable section
open GoldbachBeaumontParameters GoldbachBeaumontSharpBoxes
open BeaumontHighScales

/-- The residual-box interface is discharged unconditionally by the concrete
smooth-factor calculation and the proved eventual parameter inequalities. -/
theorem residualCells_true : residualCells := by
  filter_upwards [eventually_grouping_geometry,eventually_residual_geometry,
    logScale_tendsto.eventually_ge_atTop 1000000,eventually_ge_atTop (1:ℕ)]
    with X hgeom hrgeom hg hX
  intro C hCN j hj b t ht hU hUN hcard hsmooth α a hQq hqR happ
  have hN : 1 ≤ scale X := hX.trans (Nat.le_mul_of_pos_left X (by decide : 0 < 3))
  have hRN : approximationBound X ≤ scale X := hrgeom.2.2.2.2.1.trans
    ((Nat.sqrt_le_self X).trans (by exact Nat.le_mul_of_pos_left X (by decide : 0 < 3)))
  have he := GoldbachBeaumontResidualSmooth.residual_box_cell
    (HC:=mobiusCutoff X) (N:=scale X) (g:=logScale X) (H:=window X)
    (R:=approximationBound X) hj hCN b t ht hU hUN hcard hsmooth hg hN
    (by exact_mod_cast hrgeom.1)
    (by exact_mod_cast hrgeom.2.1)
    (by exact_mod_cast hrgeom.2.2.1)
    hrgeom.2.2.2.1 (by exact_mod_cast hrgeom.2.2.2.2.1) hRN
    (by exact_mod_cast hgeom.2.2.2.2)
    (by exact_mod_cast hgeom.2.2.2.1)
    hrgeom.2.2.2.2.2 a hQq hqR happ
  simpa only [boxPrefix,coefficientPolynomial] using he

end
end GoldbachBeaumontCompletion


end

/- Source: BeaumontFinal.lean -/
section

open Finset Filter MeasureTheory
open scoped Topology BigOperators
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachBeaumontParameters GoldbachBeaumontMainArc GoldbachBeaumontFourier
open GoldbachBeaumontHigh GoldbachBeaumontCompletion BeaumontHighScales

namespace GoldbachBeaumontCompletion
noncomputable section

lemma majorArcs_eq_parameters (X : ℕ) :
    majorArcs X=GoldbachBlockGeometry.arcs (logScale X^18) (centralWidth X) := rfl

lemma eventually_central_low_geometry :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2*X →
      scale X ≤ 10*centralStart X y ∧
      centralStart X y+centralWidth X+1 ≤ scale X ∧
      2*logScale X^18 ≤ centralWidth X := by
  filter_upwards [eventually_sqrt_small,
    eventually_mul_logScale_power_le_rpow 64 (by norm_num) 18 1 (by norm_num)]
    with X hs hp
  intro y hy hy2
  have hgeom := fixed_window_geometry hs.1 hs.2 hy hy2
  have hpN : 64*logScale X^18 ≤ X := by
    norm_num only [Real.rpow_one] at hp
    exact_mod_cast hp
  refine ⟨?_,hgeom.2.1,?_⟩
  · dsimp [scale,centralStart,BulkCircle.start,BulkCircle.length]
    omega
  · change 2*logScale X^18 ≤ (3*X)/32
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 32)).mpr
    calc
      _ = 64*logScale X^18 := by ring
      _  ≤  X := hpN
      _  ≤  3*X := by omega

/-- Actual uniform local energy on the complement of the fixed central major arcs. -/
theorem actual_local_minor : GoldbachBeaumontFinish.localMinorBound := by
  change ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, X ≤ y → y ≤ 2*X → ∀ j < Nat.sqrt X, _
  filter_upwards [eventually_central_low_geometry,
    eventually_high_band_cells residualCells_true,
    BeaumontLowScales.eventually_low_denominator_cell,
    eventually_grouping_geometry,eventually_ge_atTop (1:ℕ)]
    with X hcentral hhigh hlow hgeom hX
  intro y hy hy2 j hj
  obtain ⟨hL,hupper,hmajor⟩ := hcentral y hy hy2
  have hQpos : 0 < denominatorCutoff X := pow_pos (logScale_pos X) _
  have hRpos : 0 < approximationBound X := hQpos.trans_le
    ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans hgeom.2.2.2.2)
  have hHp : 0 < window X := hRpos.trans_le (Nat.div_le_self _ _)
  have hHr : 0 < (window X:ℝ) := by exact_mod_cast hHp
  let α : ℝ := (j:ℝ)/(window X:ℝ)
  have hα : α ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · dsimp [α]; positivity
    · apply (div_le_one hHr).mpr
      exact_mod_cast hj.le
  obtain ⟨q,a,hq,hqR,ha,hc,happ⟩ := endpoint_approximant
    (approximationBound X) hRpos α hα
  by_cases hqsmall : q ≤ denominatorCutoff X
  · simpa only [majorArcs_eq_parameters,scale,window,Nat.cast_mul,Nat.cast_ofNat] using
      hlow (centralStart X y) (centralWidth X) q a j hL hupper hmajor hq hqsmall ha hc happ
  · have hqbig : denominatorCutoff X < q := Nat.lt_of_not_ge hqsmall
    have he := hhigh (centralStart X y) (centralWidth X) hupper α a q hqbig hqR hc happ
    have hS : Continuous (BulkCircle.S (centralStart X y) (centralWidth X)) := by
      unfold BulkCircle.S GoldbachMajorArc.primeSum GoldbachMajorArc.phase
      fun_prop
    have hmask := masked_cell_le (majorArcs X)ᶜ (majorArcs_measurable X).compl _ hS
      α (α+1/(window X:ℝ)) (by linarith [one_div_pos.mpr hHr])
    have hend : α+1/(window X:ℝ)=((j:ℝ)+1)/(window X:ℝ) := by dsimp [α]; ring
    have hresult := hmask.trans he
    rw [hend] at hresult
    simpa only [α,scale,window,Nat.cast_mul,Nat.cast_ofNat] using hresult

end
end GoldbachBeaumontCompletion

/-- Frozen research task L-goldbach-beaumont-one-sided-hole-cluster. -/
theorem Conjectures.Goldbach.BeaumontOneSidedHoleCluster :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter
      (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y ≤ 2*X →
      ((((Finset.Icc y (y+Nat.sqrt X)).filter
        (fun n => Even n ∧ H n=0)).card):ℝ) ≤ ε*(Nat.sqrt X:ℝ) :=
  GoldbachBeaumontFinish.frozen_target_of_local_minor
    GoldbachBeaumontCompletion.actual_local_minor

end

end
end
