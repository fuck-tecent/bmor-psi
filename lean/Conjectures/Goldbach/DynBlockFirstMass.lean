import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
# Uniform prime arrivals in three-quarter-power blocks

This file proves the frozen task L-goldbach-dyn-block-first-mass.
It uses one verified community module and no additional analytic assumptions.

Modification notice, 2026-11-27: the short-window assembly below rescales the
accepted module's error budgets by 16, localizes its theta bound to an interior
prime rectangle, and proves the registered block first-moment statement with
constant c = 1/32. The following upstream copyright and contributor notices are
retained for the reused analytic source portions.
-/

/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Authors of the reused source portions: Robby Sneiderman, Matteo Cipollina.

Licensed under the Apache License, Version 2.0.
The full license and original notices accompany this source in the proof archive.
License text: https://www.apache.org/licenses/LICENSE-2.0

Additional adapted source and retained contributor credits:
openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
AlexKontorovich/PrimeNumberTheoremAnd,
commit c39a751132c88b6e8080b74c74023fd95b3d8be0;
rectangle reference commit 2c476fa6441c607096d93c8fc7ac0a227a655dae.
CGandGameEngineLearner/goldbach-proofs:
DNZJSJ, PR 2486, commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f;
muxkin, PR 2458, commit 25c1ef60495052eb22212b5560f90bbc6a4a0917;
DFQDZZ, PR 316, commit e4ab24712555ae8c2c926adf19d368a9fb392c35;
XianWu18, PR 207; wzhxzkk, PR 203.

Modification notice, 2026-11-26: adapted source versions are documented in the
accompanying archive. Unused declarations were removed; module bodies were
joined; auxiliary mathematical identifiers were shortened consistently;
ordinary expressions and local resource limits were normalized. The final
registered theorem name and its statement remain unchanged. Original readable
sources, attribution, exact edits and the identifier map accompany this file.
-/

/-!
Constant-factor short-window consequences of the accepted community module
`Conjectures.Goldbach.DyadicCellShortPrimeFloor` (Goldbach OC-0103).
The pointwise assembly below adapts its public theorem
`GoldbachOC103.actual_principal_window_of_zero_weights`: multiplying the
asymptotic high-frequency and residual constants by 16 allows window lengths
at least `x^(3/4)/16`. All zero-density and explicit-formula inputs remain
those of the imported unconditional proof.
Source: https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/ef8ddfa37003c69f326f69188c774106953d3969/lean/Conjectures/Goldbach/DyadicCellShortPrimeFloor.lean
Reuse follows the repository Apache-2.0 license.
-/

noncomputable section
open Finset
open scoped BigOperators Classical

namespace DynBlockFirstMassAux
open GoldbachOC103 Vx V7e V86 V1e V6i

theorem short_principal_window :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ)/16 ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := actual_zero_weight_bounds
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (16*D) C (16*C) (by positivity)
  refine ⟨max Xz Xb, ?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_right _ _).trans hX)
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/16 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/16) := mul_le_mul_of_nonneg_left hbud.low_budget hh
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/16 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    have hs : 16 * (576*C*X^2*(Real.log X)^14/
        (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2)) =
      576*(16*C)*X^2*(Real.log X)^14/
        (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2) := by ring
    have hb := hbud.high_budget
    rw [← hs] at hb
    linarith only [hb, hlower]
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/8 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/16 := by
    refine hres.trans ?_
    have hs : 16 * (D*(X^(2/3 : ℝ)*Real.log X +
        Real.sqrt X*Real.log X/X^(2/3 : ℝ) +
        X^2*Real.log X/(X^(2/3 : ℝ)*X))) =
      (16*D)*(X^(2/3 : ℝ)*Real.log X +
        Real.sqrt X*Real.log X/X^(2/3 : ℝ) +
        X^2*Real.log X/(X^(2/3 : ℝ)*X)) := by ring
    have hb := hbud.residual_budget
    rw [← hs] at hb
    linarith only [hb, hlower]
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  linarith


/-- The prime-power error is negligible even at the reduced length scale. -/
theorem prime_power_error_small_scaled (C X h : ℝ)
    (hX : max 1 ((128 * |C|)^4) ≤ X)
    (hlower : X^(3/4 : ℝ)/16 ≤ h) (hupper : h ≤ X) :
    C * Real.sqrt (X + h) ≤ h/4 := by
  have hXone : 1 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hfourth : (128 * |C|)^4 ≤ X := (le_max_right _ _).trans hX
  have hroot : 128 * |C| ≤ X^(1/4 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (128 * |C|)^4)
      hfourth (by norm_num : 0 ≤ (1/4 : ℝ))
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ 128 * |C|)] at hh
    norm_num at hh
    exact hh
  have hsqrt : Real.sqrt (X + h) ≤ 2 * Real.sqrt X := by
    calc
      Real.sqrt (X + h) ≤ Real.sqrt (4 * X) :=
        Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt X := by
        rw [Real.sqrt_mul (by norm_num)]
        congr 1
        exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hprod : X^(1/4 : ℝ) * Real.sqrt X = X^(3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg X)
  calc
    C * Real.sqrt (X + h) ≤ |C| * Real.sqrt (X + h) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * (2 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ ≤ h/4 := by nlinarith only [hmul, hlower, hprod]

/-- Uniform prime logarithmic mass in every sufficiently large short window. -/
theorem uniform_short_theta :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x →
      (x : ℝ)^(3/4 : ℝ)/16 ≤ (h : ℝ) → h ≤ x →
      (h : ℝ)/2 ≤ Chebyshev.theta ((x : ℝ) + (h : ℝ)) -
        Chebyshev.theta (x : ℝ) := by
  obtain ⟨X₀, hX₀⟩ := short_principal_window
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨M, hM⟩ := exists_nat_ge (max X₀ (max 1 ((128 * |C|)^4)))
  refine ⟨M, ?_⟩
  intro x h hx hlower hupper
  have hxr : (M : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hstart : X₀ ≤ (x : ℝ) := (le_max_left _ _).trans (hM.trans hxr)
  have hcut : max 1 ((128 * |C|)^4) ≤ (x : ℝ) :=
    (le_max_right _ _).trans (hM.trans hxr)
  have hupperr : (h : ℝ) ≤ (x : ℝ) := by exact_mod_cast hupper
  have herr := hX₀ (x : ℝ) hstart h hlower hupperr
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at herr
  have hlow := (abs_le.mp herr).1
  have hpp := (hC ((x : ℝ) + (h : ℝ))).trans
    (prime_power_error_small_scaled C (x : ℝ) (h : ℝ) hcut hlower hupperr)
  have hbase := Chebyshev.theta_le_psi (x : ℝ)
  linarith

end DynBlockFirstMassAux

end

open Finset Filter
open scoped Topology

namespace DynBlockFirstMassAux

/-- A fixed relative error form of the prime number theorem. -/
private theorem theta_relative_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧
      Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

/-- Bounding each prime logarithm by the logarithm at the right endpoint. -/
private theorem prime_window_log_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc
    ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := mem_Ioc.mp hp'.1
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

/-- There are sufficiently many small prime steps in the square-root interval.
The PNT calculation adapts the verified community proof `DynFirstMass`.
-/
theorem small_prime_mass : ∃ K : ℕ, ∀ X ≥ K,
    (1/4 : ℝ) * Real.sqrt (X:ℝ) ≤
      (((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card : ℝ) *
        Real.log (X:ℝ) := by
  obtain ⟨K, hK⟩ := theta_relative_bounds
  refine ⟨(K+16)^2, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := by nlinarith [Nat.zero_le K]
  set s := Nat.sqrt X with hs
  have hsK : K ≤ s := by
    rw [hs]
    exact le_trans (by omega) (Nat.le_sqrt.mpr
      (by nlinarith [hX] : (K+16)*(K+16) ≤ X))
  have hs4 : 4 ≤ s := by
    rw [hs]
    exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2*s)).filter Nat.Prime
  set R := (Icc s (2*s)).filter Nat.Prime
  have hP1 := prime_window_log_le s (2*s) (by omega)
  have hbs := hK s hsK
  have hb2s := hK (2*s) (by omega)
  push_cast at hb2s hP1
  have hlog2s : Real.log (2 * (s:ℝ)) ≤ Real.log (X:ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < 2*s by omega))
    exact_mod_cast (show 2*s ≤ X by omega)
  have hPc : (0:ℝ) ≤ (P.card:ℝ) := Nat.cast_nonneg _
  have hP2 : (17/20 : ℝ) * s ≤ (P.card:ℝ) * Real.log (X:ℝ) := by
    have h1 : (P.card:ℝ) * Real.log (2*(s:ℝ)) ≤
        (P.card:ℝ) * Real.log (X:ℝ) :=
      mul_le_mul_of_nonneg_left hlog2s hPc
    linarith [hbs.2, hb2s.1]
  have hPR : P.card ≤ R.card := Finset.card_le_card (by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := mem_Ioc.mp hpI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpl.le, hpu⟩, hpp⟩)
  have hlogX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))
  have hcardlog : (P.card:ℝ) * Real.log (X:ℝ) ≤
      (R.card:ℝ) * Real.log (X:ℝ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hPR) hlogX
  have hsr : Real.sqrt (X:ℝ) ≤ 2*(s:ℝ) := by
    have hsl' : (X:ℝ) < ((s:ℝ)+1)*((s:ℝ)+1) := by exact_mod_cast hsl
    have hs4' : (4:ℝ) ≤ s := by exact_mod_cast hs4
    have hr0 : 0 ≤ Real.sqrt (X:ℝ) := Real.sqrt_nonneg _
    have hrr : Real.sqrt (X:ℝ) * Real.sqrt (X:ℝ) = (X:ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hrs : Real.sqrt (X:ℝ) ≤ (s:ℝ)+1 := by
      nlinarith only [hsl', hs4', hr0, hrr]
    linarith only [hrs, hs4']
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  change (1/4:ℝ) * Real.sqrt (X:ℝ) ≤ (R.card:ℝ) * Real.log (X:ℝ)
  linarith

private theorem three_quarters_le_of_cube_le_fourth (x H : ℕ)
    (h : x^3 ≤ H^4) : (x:ℝ)^(3/4:ℝ) ≤ (H:ℝ) := by
  have hc : (x:ℝ)^3 ≤ (H:ℝ)^4 := by exact_mod_cast h
  calc
    (x:ℝ)^(3/4:ℝ) = ((x:ℝ)^3)^(1/4:ℝ) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg x)]
      norm_num
    _ ≤ ((H:ℝ)^4)^(1/4:ℝ) :=
      Real.rpow_le_rpow (by positivity) hc (by norm_num)
    _ = (H:ℝ) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg H)]
      norm_num

/-- Removing both extreme small steps leaves a positive interior interval of
at least half the original block and at least one sixteenth of `y^(3/4)`.
-/
theorem block_scales (X y : ℕ) (hX : 4096 ≤ X) (hy : X ≤ y) (hy2 : y ≤ 2*X) :
    let s := Nat.sqrt X
    let W := s * Nat.sqrt s
    let h := W - 2*s - 1
    0 < h ∧ W ≤ 2*h ∧ h+2*s < W ∧ h ≤ y ∧
      (y:ℝ)^(3/4:ℝ)/16 ≤ (h:ℝ) := by
  let s := Nat.sqrt X
  let t := Nat.sqrt s
  let W := s*t
  let h := W-2*s-1
  change 0<h ∧ W≤2*h ∧ h+2*s<W ∧ h≤y ∧ (y:ℝ)^(3/4:ℝ)/16≤(h:ℝ)
  have hs64 : 64 ≤ s := Nat.le_sqrt.mpr (by omega)
  have ht8 : 8 ≤ t := Nat.le_sqrt.mpr (by omega)
  have hst : s*s ≤ X := Nat.sqrt_le X
  have hXlt : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have hslt : s < (t+1)*(t+1) := Nat.lt_succ_sqrt s
  have ht_le : t ≤ s := Nat.sqrt_le_self s
  have hWlower : 8*s ≤ W := by
    simpa [W, Nat.mul_comm] using Nat.mul_le_mul_left s ht8
  have hWupper : W ≤ X := (Nat.mul_le_mul_left s ht_le).trans hst
  have hstrip : 2*s+1 ≤ W := by omega
  have heq : h+2*s+1 = W := by dsimp [h]; omega
  have hhalf : W ≤ 2*h := by omega
  have htquad : 4*t ≤ t*t := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left t (show 4≤t by omega)
  have hsbound : s ≤ 2*t^2 := by nlinarith only [hslt, htquad, ht8]
  have hXsquare : (s+1)*(s+1) ≤ (2*s)*(2*s) :=
    Nat.mul_self_le_mul_self (by omega)
  have hXbound : X ≤ 4*s^2 := by nlinarith only [hXlt, hXsquare]
  have hybound : y ≤ 8*s^2 := by omega
  have hspow : s^2 ≤ 4*t^4 := by
    calc
      s^2 ≤ (2*t^2)^2 := pow_le_pow_left' hsbound 2
      _ = 4*t^4 := by ring
  have hpow : y^3 ≤ (16*h)^4 := by
    calc
      y^3 ≤ (8*s^2)^3 := pow_le_pow_left' hybound 3
      _ = 512*s^4*s^2 := by ring
      _ ≤ 512*s^4*(4*t^4) := Nat.mul_le_mul_left _ hspow
      _ = 2048*W^4 := by dsimp [W]; ring
      _ ≤ 4096*W^4 := Nat.mul_le_mul_right _ (by norm_num)
      _ = (8*W)^4 := by ring
      _ ≤ (16*h)^4 := pow_le_pow_left' (by omega) 4
  have hreal := three_quarters_le_of_cube_le_fourth y (16*h) hpow
  push_cast at hreal
  refine ⟨by omega, hhalf, by omega, by omega, ?_⟩
  linarith

end DynBlockFirstMassAux

open Finset

namespace DynBlockFirstMassAux

/-- Localize the interior-rectangle injection from `DynInteriorBox` to an
arbitrary block. The second coordinate remembers the first prime, so collisions
of sums do not destroy injectivity. Adapted from the project's Apache-2.0 proof:
https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1894b91f3f607fa2b1ebb12a2bbd7d8ea6a9d419/lean/Conjectures/Goldbach/DynInteriorBox.lean
-/
theorem localized_rectangle (X y W h : ℕ) (hX : 64 ≤ X)
    (hxy : X ≤ y) (hwin : y + W ≤ 2 * X)
    (hmargin : h + 2 * Nat.sqrt X < W) :
    ((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card *
      ((Ioc y (y + h)).filter Nat.Prime).card ≤
    ∑ n ∈ ((Icc X (2 * X)).filter Even).filter
        (fun n => y ≤ n ∧ n < y + W),
      (((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n - p))).card := by
  let P := (Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime
  let Q := (Ioc y (y + h)).filter Nat.Prime
  let B := ((Icc X (2 * X)).filter Even).filter
    (fun n => y ≤ n ∧ n < y + W)
  change P.card * Q.card ≤ ∑ n ∈ B,
    (P.filter (fun p => p ≤ n ∧ Nat.Prime (n - p))).card
  have hs : 8 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]
    omega
  have key : (∑ n ∈ B,
      (P.filter (fun p => p ≤ n ∧ Nat.Prime (n - p))).card) =
      ((B ×ˢ P).filter (fun z => z.2 ≤ z.1 ∧ Nat.Prime (z.1 - z.2))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [Finset.card_filter]
  rw [key, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ => (z.2 + z.1, z.1))
  · intro z hz
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hz
    obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqrange, hqprime⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.mp hprange
    obtain ⟨hq1, hq2⟩ := Finset.mem_Ioc.mp hqrange
    have hpo : Odd z.1 := hpprime.odd_of_ne_two (by omega)
    have hqo : Odd z.2 := hqprime.odd_of_ne_two (by omega)
    apply Finset.mem_filter.mpr
    change (z.2 + z.1, z.1) ∈ B ×ˢ P ∧
      z.1 ≤ z.2 + z.1 ∧ Nat.Prime (z.2 + z.1 - z.1)
    refine ⟨Finset.mem_product.mpr ⟨?_, hp⟩, by omega, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        hqo.add_odd hpo⟩, by omega, by omega⟩
    · simpa using hqprime
  · intro z _ v _ he
    simp only [Prod.mk.injEq] at he
    ext <;> omega

/-- Convert Chebyshev mass on a natural interval to its number of primes. -/
theorem theta_window_count (y h : ℕ) :
    Chebyshev.theta ((y + h : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) ≤
      (((Ioc y (y + h)).filter Nat.Prime).card : ℝ) *
        Real.log ((y + h : ℕ) : ℝ) := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p : ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union
    (f := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := y) (c := y) (d := y + h) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega : y ≤ y + h)] at split
  have hsum : Chebyshev.theta ((y + h : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) =
      ∑ p ∈ (Ioc y (y + h)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [hsum]
  calc
    (∑ p ∈ (Ioc y (y + h)).filter Nat.Prime, Real.log (p : ℝ)) ≤
        ∑ _p ∈ (Ioc y (y + h)).filter Nat.Prime,
          Real.log ((y + h : ℕ) : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hprange, hpprime⟩ := mem_filter.mp hp
      exact Real.log_le_log (by exact_mod_cast hpprime.pos)
        (by exact_mod_cast (mem_Ioc.mp hprange).2)
    _ = _ := by simp

end DynBlockFirstMassAux

open Finset

theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P H W B M
  obtain ⟨K, hK⟩ := DynBlockFirstMassAux.small_prime_mass
  obtain ⟨Kq, hKq⟩ := DynBlockFirstMassAux.uniform_short_theta
  refine ⟨1 / 32, by norm_num, max 4096 (max K Kq), ?_⟩
  intro X hX y hy hwin
  have hX4096 : 4096 ≤ X := (le_max_left _ _).trans hX
  have hXK : K ≤ X := (le_max_left K Kq).trans ((le_max_right _ _).trans hX)
  have hXKq : Kq ≤ X := (le_max_right K Kq).trans ((le_max_right _ _).trans hX)
  let h : ℕ := W X - 2 * Nat.sqrt X - 1
  have hscales := DynBlockFirstMassAux.block_scales X y hX4096 hy (by omega)
  change 0 < h ∧ W X ≤ 2 * h ∧ h + 2 * Nat.sqrt X < W X ∧ h ≤ y ∧
    (y : ℝ) ^ (3 / 4 : ℝ) / 16 ≤ (h : ℝ) at hscales
  obtain ⟨hhpos, hWh, hmargin, hhy, hrpow⟩ := hscales
  let Q := (Ioc y (y + h)).filter Nat.Prime
  let L := Real.log (X : ℝ)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsmall := hK X hXK
  change (1 / 4 : ℝ) * Real.sqrt (X : ℝ) ≤ ((P X).card : ℝ) * L at hsmall
  have htheta := hKq y h (hXKq.trans hy) hrpow hhy
  have hthetaNat : (h : ℝ) / 2 ≤
      Chebyshev.theta ((y + h : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) := by
    simpa only [Nat.cast_add] using htheta
  have hqcount := DynBlockFirstMassAux.theta_window_count y h
  have hlog : Real.log ((y + h : ℕ) : ℝ) ≤ 2 * L := by
    calc
      Real.log ((y + h : ℕ) : ℝ) ≤ Real.log ((X : ℝ) * (X : ℝ)) := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < y + h by omega)
        · have hnat : y + h ≤ X * X := by
            have htwo : 2 * X ≤ X * X := Nat.mul_le_mul_right X (by omega : 2 ≤ X)
            omega
          exact_mod_cast hnat
      _ = 2 * L := by
        rw [Real.log_mul hXpos.ne' hXpos.ne']
        dsimp [L]
        ring
  have hlogmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg Q.card : (0 : ℝ) ≤ Q.card)
  have hWhR : (W X : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hWh
  have hqmass : (W X : ℝ) / 8 ≤ (Q.card : ℝ) * L := by
    change Chebyshev.theta ((y + h : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) ≤
      (Q.card : ℝ) * Real.log ((y + h : ℕ) : ℝ) at hqcount
    linarith only [hthetaNat, hqcount, hlogmul, hWhR]
  have hmult := mul_le_mul hsmall hqmass
    (by positivity : (0 : ℝ) ≤ (W X : ℝ) / 8)
    (mul_nonneg (Nat.cast_nonneg (P X).card) hL.le)
  have hmain : (1 / 32 : ℝ) * (W X : ℝ) *
      (Real.sqrt (X : ℝ) / L ^ 2) ≤ ((P X).card : ℝ) * (Q.card : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hL)]
    convert hmult using 1 <;> ring
  have hcountNat := DynBlockFirstMassAux.localized_rectangle X y (W X) h
    (by omega) hy hwin hmargin
  change (P X).card * Q.card ≤ ∑ n ∈ B X y, H X n at hcountNat
  have hcount : ((P X).card : ℝ) * (Q.card : ℝ) ≤
      ∑ n ∈ B X y, (H X n : ℝ) := by exact_mod_cast hcountNat
  exact hmain.trans hcount
