import Mathlib
import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions
import PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment

open Finset Filter MeasureTheory Set
open scoped BigOperators Classical Interval Topology

/-!
The high-denominator Vaughan argument adapts HymnOfLight's binary-shift
checkpoint (b3e8a9fec6067484ff44957e93f85e23697040a5), in turn using the
Vaughan and Chebyshev estimates in the accepted deep second moment.
-/

private theorem primeApproximation (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k-w k : ℝ):ℂ) *
      e ((k:ℝ)*t)‖ ≤ 2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) *
        e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

private theorem vaughanOuter (ε : ℝ) (hε : 0 < ε) :
    let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let Q := fun n : ℕ => ⌊(n : ℝ)^(1/3:ℝ)⌋₊
    let H : ℕ → ℕ := fun n => 256*Q n*(Nat.log 2 (n+2))^2
    ∀ᶠ n : ℕ in atTop, ∀ (t : ℝ) (q a : ℕ), 1 ≤ q → q ≤ Q n →
      a.Coprime q → (n:ℝ)^(1/4:ℝ) ≤ q → |t-(a:ℝ)/q| ≤ (H n:ℝ)/((q:ℝ)*n) →
      ‖∑ k ∈ Finset.range (n+1), (w k:ℂ)*e ((k:ℝ)*t)‖ ≤ (n:ℝ)^(7/8+ε) := by
  intro e w Q H
  let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * e ((k:ℝ)*t)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).comp_tendsto ht).bound
    (by norm_num : (0:ℝ)<1/100000)
  filter_upwards [eventually_ge_atTop (2:ℕ), hsmall,
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1, GB6Growth.eventual_geometry,
    OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound] with n hn hlogs hL hgeom hv
  intro t q a hqp hqQ hcop hlow hclose
  let x : ℝ := n
  let L := Real.log x
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  change 1 ≤ L at hL
  have hlog4 : L^4 ≤ (1/100000:ℝ)*x^ε := by
    change ‖L^(4:ℝ)‖ ≤ (1/100000:ℝ)*‖x^ε‖ at hlogs
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,
      abs_of_nonneg (show 0 ≤ L^4 by positivity),abs_of_nonneg (Real.rpow_nonneg hx.le ε)] using hlogs
  have hgrid : GB6Growth.grid n = Q n := GB6Growth.grid_eq_floor n
  have hheight : GB6Growth.height n = H n := by simp only [GB6Growth.height,H,hgrid]
  obtain ⟨_,hQH,hQn,_,hsep⟩ := hgeom
  rw [hgrid, hheight] at hQH
  rw [hgrid] at hQn
  rw [hheight] at hsep
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqp
  have hqH : q ≤ H n := hqQ.trans hQH
  have hmult : H n*q ≤ n := (Nat.mul_le_mul_left (H n) hqH).trans (by nlinarith only [hsep])
  have hmultr : (H n:ℝ)*(q:ℝ) ≤ x := by dsimp only [x]; exact_mod_cast hmult
  have hqsec : |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply hclose.trans
    apply (div_le_div_iff₀ (mul_pos hqr hx) (sq_pos_of_pos hqr)).mpr
    change (H n:ℝ)*(q:ℝ)^2 ≤ 1*((q:ℝ)*x)
    nlinarith only [mul_le_mul_of_nonneg_right hmultr hqr.le]
  have hvq := hv t (a:ℤ) q hqp hcop.isCoprime (by simpa using hqsec) (hqQ.trans hQn)
  have hsum : S n ArithmeticFunction.vonMangoldt t = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 n) (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [S,e,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm t (k:ℝ)])
  have hqcube : (q:ℝ) ≤ x^(1/3:ℝ) := (by exact_mod_cast hqQ : (q:ℝ) ≤ Q n).trans
    (Nat.floor_le (Real.rpow_nonneg hx.le _))
  have hroot : x^(1/8:ℝ) ≤ Real.sqrt (q:ℝ) := by
    rw [← show Real.sqrt (x^(1/4:ℝ)) = x^(1/8:ℝ) by
      rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hx.le]; norm_num]
    exact Real.sqrt_le_sqrt hlow
  have hl : x / Real.sqrt q ≤ x^(7/8:ℝ) := by
    calc
      _ ≤ x / x^(1/8:ℝ) := div_le_div_of_nonneg_left hx.le (by positivity) hroot
      _ = _ := by
        apply (div_eq_iff (Real.rpow_pos_of_pos hx (1/8:ℝ)).ne').mpr
        rw [←Real.rpow_add hx]
        norm_num
  have hr : Real.sqrt (x*q) ≤ x^(7/8:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ x * x^(1/3:ℝ) := mul_le_mul_of_nonneg_left hqcube hx.le
      _ = x^(4/3:ℝ) := by rw [mul_comm, ←Real.rpow_add_one hx.ne']; norm_num
      _ ≤ _ := by
        rw [←Real.rpow_mul_natCast hx.le]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (4/5:ℝ) ≤ 7/8)
  have hbound : ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ 48600*L^4*x^(7/8:ℝ) := by
    rw [hsum]
    apply hvq.trans
    change 16200*L^4*(x/Real.sqrt q+x^(4/5:ℝ)+Real.sqrt (x*q)) ≤ _
    calc
      _ ≤ 16200*L^4*(3*x^(7/8:ℝ)) := by gcongr; linarith only [hl,hr,hmiddle]
      _ = _ := by ring
  have herr : ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ 2*Real.sqrt x*L := by
    simpa only [S, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub] using primeApproximation n (by omega) t
  have hsqrt : Real.sqrt x ≤ x^(7/8:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlogle : L ≤ L^4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
  have hres : 2*Real.sqrt x*L ≤ 2*L^4*x^(7/8:ℝ) := by
    calc
      _ = 2*(L*Real.sqrt x) := by ring
      _ ≤ 2*(L^4*x^(7/8:ℝ)) := by gcongr
      _ = _ := by ring
  have htriangle := norm_sub_le (S n ArithmeticFunction.vonMangoldt t)
    (S n ArithmeticFunction.vonMangoldt t - S n w t)
  rw [sub_sub_cancel] at htriangle
  change ‖S n w t‖ ≤ x^(7/8+ε)
  rw [Real.rpow_add hx]
  have hsave := mul_le_mul_of_nonneg_right hlog4 (Real.rpow_nonneg hx.le (7/8:ℝ))
  nlinarith only [htriangle,herr,hbound,hres,hsave,
    mul_nonneg (show 0≤L^4 by positivity) (Real.rpow_nonneg hx.le (7/8:ℝ))]

set_option maxHeartbeats 1800000 in
private theorem shiftUnionCutComplement :
    let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (Y : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (Y+1)).filter Nat.Prime,
      (Real.log p : ℂ) * e ((p : ℝ) * t);
    let F := fun (Y m : ℕ) (t : ℝ) => (S Y t)^2 * e (-(m : ℝ) * t);
    let A := fun Y : ℕ =>
      let Q := ⌊(Y : ℝ)^(1/3 : ℝ)⌋₊
      let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) < (Y : ℝ)^(1/4 : ℝ) ∧
        q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)};
    let C := fun (D : Set ℝ) (Y m : ℕ) =>
      intervalIntegral (D.indicator (F Y m)) 0 1 MeasureTheory.volume;
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ Y ≥ N,
      (((Finset.Icc Y (2*Y)).filter (fun m => (C (A Y)ᶜ Y m).re ≤ -(Y:ℝ)/32)).card : ℝ)
        ≤ K*(Y:ℝ)^(19/25:ℝ) := by
  classical
  intro e S F A C
  let w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
  have sumAsWeight (Y : ℕ) (t : ℝ) :
      S Y t = ∑ k ∈ Finset.range (Y+1), (w k:ℂ)*e ((k:ℝ)*t) := by
    dsimp [S]
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun k _ => by by_cases hk : k.Prime <;> simp [w,hk])
  have measurableA (Y : ℕ) : MeasurableSet (A Y) := by
    let Q := ⌊(Y:ℝ)^(1/3:ℝ)⌋₊
    let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
    let good (q a : ℕ) := 1 ≤ q ∧ (q:ℝ) < (Y:ℝ)^(1/4:ℝ) ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q
    let arc (q a : ℕ) := {t : ℝ | |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)}
    have hGrouped : A Y = {t | ∃ q a : ℕ, good q a ∧ t ∈ arc q a} := by
      ext t
      simp only [A, good, arc, Q, H, Set.mem_ofPred_eq, and_assoc]
    have hAeq : A Y = ⋃ q : ℕ, ⋃ a : ℕ, if good q a then arc q a else ∅ := by
      rw [hGrouped]
      ext t
      simp only [Set.mem_ofPred_eq, mem_iUnion]
      refine exists_congr (fun q => exists_congr (fun a => ?_))
      by_cases h : good q a <;> simp [h]
    rw [hAeq]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro a
    by_cases h : good q a
    · rw [ite_eq_left h]
      exact measurableSet_le (((continuous_id.sub continuous_const).abs).measurable) measurable_const
    · simp [h]
  obtain ⟨N₀, hN₀⟩ := frontierSourceFiveSixths (1/1000) (by norm_num)
  have hout := vaughanOuter (1/1000) (by norm_num)
  have hlog := GB6Growth.polylog_le_power 2 (by norm_num) 2 (1/125) (by norm_num)
  have hsup : ∀ᶠ Y : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      t ∉ A Y → ‖S Y t‖ ≤ (Y:ℝ)^(219/250:ℝ) := by
    filter_upwards [eventually_ge_atTop (max 1 N₀), hout] with Y hY hOuter
    intro t ht hA
    let Q := ⌊(Y:ℝ)^(1/3:ℝ)⌋₊
    let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
    have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
    rw [sumAsWeight]
    by_cases hWide : ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)
    · obtain ⟨q,a,hq,hqQ,ha,hcop,hdist⟩ := hWide
      have hquart : (Y:ℝ)^(1/4:ℝ) ≤ q := by
        by_contra! h
        exact hA ⟨q,a,hq,h,hqQ,ha,hcop,hdist⟩
      simpa only [show (7/8+1/1000:ℝ) = 219/250 by norm_num] using
        hOuter t q a hq hqQ hcop hquart hdist
    · exact (hN₀ Y (by omega) t ht hWide).trans
        (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  have hEnergy : ∀ᶠ Y : ℕ in atTop,
      (∑ m ∈ Finset.Icc Y (2*Y), ‖C (A Y)ᶜ Y m‖^2) ≤ (Y:ℝ)^(69/25:ℝ) := by
    filter_upwards [hsup,hlog,eventually_ge_atTop (1:ℕ)] with Y hsupY hlogY hY
    have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast hY
    have hYp : 0 < (Y:ℝ) := zero_lt_one.trans_le hY1
    let u := (Y:ℝ)^(219/250:ℝ)
    let f := ((A Y)ᶜ).indicator (fun t => (S Y t)^2)
    have hS : Continuous (S Y) := by dsimp [S,e]; fun_prop
    have hf : MemLp f 2 GB5Variance.unitMeasure := by
      apply MemLp.indicator (measurableA Y).compl.nullMeasurableSet
      apply (memLp_two_iff_integrable_sq_norm (hS.pow 2).aestronglyMeasurable).mpr
      exact ((((hS.pow 2).norm).pow 2).intervalIntegrable (μ:=volume) 0 1).1
    have hFourier (m : ℕ) : C (A Y)ᶜ Y m = GB5Variance.modeCoeff f m := by
      apply intervalIntegral.integral_congr
      intro t _
      change (A Y)ᶜ.indicator (F Y m) t = f t * GB5Variance.phase (-(m:ℝ)*t)
      by_cases h : t ∈ (A Y)ᶜ
      · simp only [f, indicator_of_mem h, F, e, GB5Variance.phase]
      · simp only [f, indicator_of_notMem h, zero_mul]
    have hParseval : (∫ t in (0:ℝ)..1, ‖S Y t‖^2) ≤ ((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2 := by
      have hh (t : ℝ) : S Y t = GB6Var.S Y t := by
        simpa only [GB6Var.S,GB6Var.weight,GB5Variance.phase,w,e] using sumAsWeight Y t
      simpa only [hh] using (show (∫ t in (0:ℝ)..1, ‖GB6Var.S Y t‖^2) ≤ _ from GB6Var.S_energy Y)
    have hI : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1 := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    have hlog2 : 2*(1+Real.log ((Y:ℝ)+2))^2 ≤ (Y:ℝ)^(1/125:ℝ) := by
      refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ (GB6Growth.log_le_logFactor Y) 2)
        (by norm_num)).trans hlogY
      have hl := Real.log_nonneg (show (1:ℝ) ≤ (Y:ℝ)+2 by linarith)
      linarith
    have hu : u^2*(Y:ℝ) = (Y:ℝ)^(344/125:ℝ) := by
      dsimp [u]
      rw [←Real.rpow_mul_natCast hYp.le, ←Real.rpow_add_one hYp.ne']
      norm_num
    calc
      _ = ∑ m ∈ Finset.Icc Y (2*Y), ‖GB5Variance.modeCoeff f m‖^2 := by simp_rw [hFourier]
      _ ≤ ∫ t in (0:ℝ)..1, ‖f t‖^2 := GB5Variance.finite_bessel _ f hf
      _ ≤ ∫ t in (0:ℝ)..1, u^2*‖S Y t‖^2 := by
        have hBoundInt : IntervalIntegrable (fun t => u^2*‖S Y t‖^2) volume 0 1 :=
          ((hS.norm.pow 2).intervalIntegrable 0 1).const_mul (u^2)
        apply intervalIntegral.integral_mono_on zero_le_one hI hBoundInt
        intro t ht
        by_cases ha : t ∈ (A Y)ᶜ
        · have hb : ‖S Y t‖ ≤ u := hsupY t ht ha
          simp only [f, indicator_of_mem ha, norm_pow]
          rw [show (‖S Y t‖^2)^2 = ‖S Y t‖^2*‖S Y t‖^2 by ring]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
        · simp only [f, indicator_of_notMem ha, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)]
          exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      _ ≤ u^2*(((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2) := by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left hParseval (sq_nonneg _)
      _ ≤ (u^2*(Y:ℝ))*(2*(1+Real.log ((Y:ℝ)+2))^2) := by
        have hc : (Y:ℝ)+1 ≤ 2*(Y:ℝ) := by linarith
        calc
          _ ≤ u^2*((2*(Y:ℝ))*(1+Real.log ((Y:ℝ)+2))^2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (sq_nonneg _)
          _ = _ := by ring
      _ ≤ (Y:ℝ)^(69/25:ℝ) := by
        rw [hu, show (69/25:ℝ) = 344/125+1/125 by norm_num, Real.rpow_add hYp]
        exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEnergy
  refine ⟨1024,by norm_num,max 1 N,?_⟩
  intro Y hY
  have hp : 0 < (Y:ℝ) := by exact_mod_cast (show 0 < Y by omega)
  let B := (Finset.Icc Y (2*Y)).filter (fun m => (C (A Y)ᶜ Y m).re ≤ -(Y:ℝ)/32)
  have hB (m : ℕ) (hm : m ∈ B) : ((Y:ℝ)/32)^2 ≤ ‖C (A Y)ᶜ Y m‖^2 := by
    apply pow_le_pow_left₀ (by positivity)
    have hreal := (Finset.mem_filter.mp hm).2
    apply (le_trans (b := -(C (A Y)ᶜ Y m).re) (by linarith))
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hc : (B.card:ℝ)*((Y:ℝ)/32)^2 ≤ (Y:ℝ)^(69/25:ℝ) := by
    calc
      _ = ∑ _m ∈ B, ((Y:ℝ)/32)^2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ m ∈ B, ‖C (A Y)ᶜ Y m‖^2 := Finset.sum_le_sum hB
      _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)).trans
        (hN Y (by omega))
  apply (le_of_mul_le_mul_right _ (show 0 < ((Y:ℝ)/32)^2 by positivity))
  refine hc.trans_eq ?_
  rw [show (69/25:ℝ)=19/25+2 by norm_num, Real.rpow_add hp, Real.rpow_ofNat]
  ring


theorem Conjectures.Cuts.Taskd10f8d67b42eba65212607c6 : (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range (x2 + (1 : ℕ)) with Nat.Prime x4, (↑(Real.log (↑x4 : ℝ)) : ℂ) * x1 ((↑x4 : ℝ) * x3); have x3 : ℕ → ℕ → ℝ → ℂ := fun (x3 x4 : ℕ) (x5 : ℝ) => x2 x3 x5 ^ (2 : ℕ) * x1 (-(↑x4 : ℝ) * x5); have x4 : ℕ → Set ℝ := fun (x4 : ℕ) =>   have x5 : ℕ := ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊;   have x6 : ℕ := (256 : ℕ) * x5 * Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ);   {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ (↑x8 : ℝ) < (↑x4 : ℝ) ^ (1 / 4 : ℝ) ∧ x8 ≤ x5 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑x6 : ℝ) / ((↑x8 : ℝ) * (↑x4 : ℝ))}; have x5 : Set ℝ → ℕ → ℕ → ℂ := fun (x5 : Set ℝ) (x6 x7 : ℕ) => intervalIntegral (x5.indicator (x3 x6 x7)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; ∃ (x6 : ℝ), (0 : ℝ) < x6 ∧ ∃ (x7 : ℕ), ∀ x8 ≥ x7, (↑{x10 ∈ Finset.Icc x8 ((2 : ℕ) * x8) | (x5 (x4 x8)ᶜ x8 x10).re ≤ -(↑x8 : ℝ) / (32 : ℝ)}.card : ℝ) ≤ x6 * (↑x8 : ℝ) ^ (19 / 25 : ℝ)) :=
  shiftUnionCutComplement
