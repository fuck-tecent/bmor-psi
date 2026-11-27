import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-switching-sieve-edge-integrals`

Switching-sieve edge integrals: the two numeric edge estimates
`8 * log (10/9) ≤ 0.84289` and `8 * ∫_2^{8/3} log (t-1)/t ≤ 0.60962`.

The second is proved by the Möbius substitution `w = (t-2)/t`, i.e. `t = 2/(1-w)`,
which turns the integral into `∫_0^{1/4} (log (1+w) - log (1-w))/(1-w) dw`.  On `[0,1/4]`
the artanh series `log ((1+w)/(1-w)) = 2 ∑ w^{2i-1}/(2i-1)` is majorized by its first four
terms plus `10^{-6}` (derivative test), and each `∫ w^{2i-1}/(1-w)` is elementary.
Self-contained, Mathlib only.
-/

open MeasureTheory Filter

namespace PEqualNP.Outside

lemma log_ten_nine_le : Real.log (10 / 9) ≤ 0.10536125 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 10/9)]
  have h1 : (10:ℝ)/9 ≤ 1.1111112 := by norm_num
  have h2 : (1.1111112 : ℝ) ≤ Real.exp 0.10536125 := by dyadic_interval [prec := 80]
  linarith

lemma log_four_three_le : Real.log (4 / 3) ≤ 0.2876822 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 4/3)]
  have h1 : (4:ℝ)/3 ≤ 1.3333334 := by norm_num
  have h2 : (1.3333334 : ℝ) ≤ Real.exp 0.2876822 := by dyadic_interval [prec := 80]
  linarith

lemma log_five_three_le : Real.log (5 / 3) ≤ 0.5108257 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 5/3)]
  have h1 : (5:ℝ)/3 ≤ 1.6666667 := by norm_num
  have h2 : (1.6666667 : ℝ) ≤ Real.exp 0.5108257 := by dyadic_interval [prec := 80]
  linarith

private lemma L_goldbach_switching_sieve_edge_integrals :
    8 * Real.log (10 / 9) ≤ (0.84289 : ℝ) ∧ 8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (0.60962 : ℝ) := by
  constructor
  · linarith [log_ten_nine_le]
  · set A : ℝ → ℝ := fun w => (Real.log (1+w) - Real.log (1-w))/(1-w) with hA
    set B : ℝ → ℝ := fun w => (2*(w + w^3/3 + w^5/5 + w^7/7) + 1/1000000)/(1-w) with hB
    set Q : ℝ → ℝ := fun w => (352/105:ℝ)*w + (71/105)*w^2 + (142/315)*w^3 + (6/35)*w^4
      + (24/175)*w^5 + (1/21)*w^6 + (2/49)*w^7 with hQ
    set H : ℝ → ℝ := fun w => (352/105 + 1/1000000)*(-Real.log (1-w)) - Q w with hH
    -- continuity / integrability
    have hAcont : ContinuousOn A (Set.uIcc (0:ℝ) (1/4)) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)]
      have h1 : ContinuousOn (fun w : ℝ => 1+w) (Set.Icc (0:ℝ) (1/4)) := by fun_prop
      have h2 : ContinuousOn (fun w : ℝ => 1-w) (Set.Icc (0:ℝ) (1/4)) := by fun_prop
      have hl1 : ContinuousOn (fun w : ℝ => Real.log (1+w)) (Set.Icc (0:ℝ) (1/4)) :=
        h1.log (fun x hx => by linarith [hx.1])
      have hl2 : ContinuousOn (fun w : ℝ => Real.log (1-w)) (Set.Icc (0:ℝ) (1/4)) :=
        h2.log (fun x hx => by linarith [hx.2])
      exact (hl1.sub hl2).div h2 (fun x hx => by linarith [hx.2])
    have hAint : IntervalIntegrable A volume (0:ℝ) (1/4) := hAcont.intervalIntegrable
    have hBcont : ContinuousOn B (Set.uIcc (0:ℝ) (1/4)) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)]
      have h2 : ContinuousOn (fun w : ℝ => 1-w) (Set.Icc (0:ℝ) (1/4)) := by fun_prop
      have hp : ContinuousOn (fun w : ℝ => 2*(w + w^3/3 + w^5/5 + w^7/7) + 1/1000000)
          (Set.Icc (0:ℝ) (1/4)) := by fun_prop
      exact hp.div h2 (fun x hx => by linarith [hx.2])
    have hBint : IntervalIntegrable B volume (0:ℝ) (1/4) := hBcont.intervalIntegrable
    -- pointwise majorant of the artanh series on [0,1/4]
    have hDbound : ∀ w ∈ Set.Icc (0:ℝ) (1/4),
        Real.log (1+w) - Real.log (1-w) ≤ 2*(w + w^3/3 + w^5/5 + w^7/7) + 1/1000000 := by
      intro w hw
      obtain ⟨hw0, hw4⟩ := hw
      set D : ℝ → ℝ := fun v =>
        1/1000000 + (2*(v + v^3/3 + v^5/5 + v^7/7) - (Real.log (1+v) - Real.log (1-v))) with hD
      have hcont : ContinuousOn D (Set.Icc (0:ℝ) (1/4)) := by
        have hp : ContinuousOn (fun v : ℝ => 2*(v + v^3/3 + v^5/5 + v^7/7)) (Set.Icc (0:ℝ) (1/4)) := by
          fun_prop
        have h1 : ContinuousOn (fun v : ℝ => 1+v) (Set.Icc (0:ℝ) (1/4)) := by fun_prop
        have h2 : ContinuousOn (fun v : ℝ => 1-v) (Set.Icc (0:ℝ) (1/4)) := by fun_prop
        have hl1 := h1.log (fun x hx => by linarith [hx.1])
        have hl2 := h2.log (fun x hx => by linarith [hx.2])
        have hpoly : ContinuousOn (fun v : ℝ =>
            1/1000000 + (2*(v + v^3/3 + v^5/5 + v^7/7) - (Real.log (1+v) - Real.log (1-v))))
            (Set.Icc (0:ℝ) (1/4)) := continuousOn_const.add (hp.sub (hl1.sub hl2))
        simpa only [hD] using hpoly
      have hDd : ∀ v ∈ Set.Ioo (0:ℝ) (1/4), HasDerivAt D (-2*v^8/(1-v^2)) v := by
        intro v hv
        obtain ⟨hv0, hv4⟩ := hv
        have h1v : (1:ℝ) + v ≠ 0 := by linarith
        have h1vm : (1:ℝ) - v ≠ 0 := by linarith
        have hp : HasDerivAt (fun v : ℝ => 2*(v + v^3/3 + v^5/5 + v^7/7))
            (2*(1 + v^2 + v^4 + v^6)) v := by
          have h1 : HasDerivAt (fun v : ℝ => v) 1 v := hasDerivAt_id v
          have h3 : HasDerivAt (fun v : ℝ => v^3) (3*v^2) v := by simpa using hasDerivAt_pow 3 v
          have h5 : HasDerivAt (fun v : ℝ => v^5) (5*v^4) v := by simpa using hasDerivAt_pow 5 v
          have h7 : HasDerivAt (fun v : ℝ => v^7) (7*v^6) v := by simpa using hasDerivAt_pow 7 v
          have h := (((h1.add (h3.div_const 3)).add (h5.div_const 5)).add (h7.div_const 7)).const_mul 2
          convert h using 1
          ring_nf
        have hl1 : HasDerivAt (fun v : ℝ => Real.log (1+v)) ((1+v)⁻¹) v := by
          have h : HasDerivAt (fun v : ℝ => 1+v) 1 v := by simpa using (hasDerivAt_id v).const_add 1
          simpa only [Function.comp_def, mul_one] using (Real.hasDerivAt_log h1v).comp v h
        have hl2 : HasDerivAt (fun v : ℝ => Real.log (1-v)) (-(1-v)⁻¹) v := by
          have h : HasDerivAt (fun v : ℝ => 1-v) (-1) v := by simpa using (hasDerivAt_id v).const_sub 1
          simpa only [Function.comp_def, mul_neg, mul_one] using (Real.hasDerivAt_log h1vm).comp v h
        have hcomb : HasDerivAt D (2*(1 + v^2 + v^4 + v^6) - ((1+v)⁻¹ - (-(1-v)⁻¹))) v := by
          have h' := (hp.sub (hl1.sub hl2)).const_add (1/1000000)
          simpa only [hD, Pi.sub_apply, Pi.add_apply] using h'
        have hval : 2*(1 + v^2 + v^4 + v^6) - ((1+v)⁻¹ - (-(1-v)⁻¹)) = -2*v^8/(1-v^2) := by
          have h1v2 : (1:ℝ) - v^2 ≠ 0 := by nlinarith
          field_simp
          ring
        exact hval ▸ hcomb
      have hanti : AntitoneOn D (Set.Icc (0:ℝ) (1/4)) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont
          (f' := fun v => -2*v^8/(1-v^2)) ?_ ?_
        · intro v hv
          rw [interior_Icc] at hv
          exact (hDd v hv).hasDerivWithinAt
        · intro v hv
          rw [interior_Icc] at hv
          obtain ⟨hv0, hv4⟩ := hv
          have h8 : (0:ℝ) < v^8 := pow_pos hv0 8
          have hden : (0:ℝ) < 1 - v^2 := by nlinarith
          exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hden)
      have hmem : (1/4:ℝ) ∈ Set.Icc (0:ℝ) (1/4) := by norm_num
      have hmono : D (1/4) ≤ D w := hanti ⟨hw0, hw4⟩ hmem hw4
      have hD14 : 0 ≤ D (1/4) := by
        have hlog : Real.log (1 + 1/4) - Real.log (1 - 1/4) = Real.log (5/3) := by
          rw [show (1:ℝ)+1/4 = 5/4 by norm_num, show (1:ℝ)-1/4 = 3/4 by norm_num]
          rw [← Real.log_div (by norm_num : (5:ℝ)/4 ≠ 0) (by norm_num : (3:ℝ)/4 ≠ 0)]
          norm_num
        have h : (0.5108257:ℝ) ≤
            2*((1:ℝ)/4 + ((1:ℝ)/4)^3/3 + ((1:ℝ)/4)^5/5 + ((1:ℝ)/4)^7/7) + 1/1000000 := by
          norm_num
        simp only [hD]
        rw [hlog]
        linarith [log_five_three_le, h]
      have hkey : 0 ≤ D w := le_trans hD14 hmono
      simp only [hD] at hkey
      linarith
    -- pointwise bound for the integrands
    have hAB : ∀ w ∈ Set.Icc (0:ℝ) (1/4), A w ≤ B w := by
      intro w hw
      obtain ⟨hw0, hw4⟩ := hw
      have hpos : (0:ℝ) < 1 - w := by linarith
      have h := hDbound w ⟨hw0, hw4⟩
      simp only [hA, hB]
      exact div_le_div_of_nonneg_right h (le_of_lt hpos)
    -- step 1: shift the integration variable by 2
    have hI1 : (∫ t in (2:ℝ)..(8/3:ℝ), Real.log (t - 1) / t)
        = ∫ s in (0:ℝ)..(2/3:ℝ), Real.log (1 + s) / (2 + s) := by
      have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := (2/3:ℝ))
        (fun t : ℝ => Real.log (t - 1) / t) 2
      rw [show (0:ℝ) + 2 = 2 by norm_num, show (2:ℝ)/3 + 2 = 8/3 by norm_num] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro x hx
      show Real.log (x + 2 - 1) / (x + 2) = Real.log (1 + x) / (2 + x)
      rw [show x + 2 - 1 = 1 + x by ring]
      ring_nf
    -- step 2: Moebius substitution t = 2/(1-w)
    have hI2 : (∫ s in (0:ℝ)..(2/3:ℝ), Real.log (1 + s) / (2 + s)) = ∫ w in (0:ℝ)..(1/4), A w := by
      have hderiv : ∀ w ∈ Set.uIcc (0:ℝ) (1/4),
          HasDerivAt (fun w : ℝ => ∫ s in (0:ℝ)..(2*w/(1-w)), Real.log (1+s)/(2+s)) (A w) w := by
        intro w hw
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hw
        obtain ⟨hw0, hw4⟩ := hw
        have hw1 : (1:ℝ) - w ≠ 0 := by linarith
        have hw1pos : (0:ℝ) < 1 - w := by linarith
        have hb_le : 2*w/(1-w) ≤ 2/3 := by
          rw [div_le_iff₀ hw1pos]; linarith
        have hb_nonneg : 0 ≤ 2*w/(1-w) := by
          apply div_nonneg <;> linarith
        have hfcont : ContinuousOn (fun s : ℝ => Real.log (1+s)/(2+s)) (Set.Icc (0:ℝ) (2/3)) := by
          have h1 : ContinuousOn (fun s : ℝ => 1+s) (Set.Icc (0:ℝ) (2/3)) := by fun_prop
          have hlog : ContinuousOn (fun s : ℝ => Real.log (1+s)) (Set.Icc (0:ℝ) (2/3)) :=
            h1.log (fun x hx => by linarith [hx.1])
          have h2 : ContinuousOn (fun s : ℝ => 2+s) (Set.Icc (0:ℝ) (2/3)) := by fun_prop
          exact hlog.div h2 (fun x hx => by linarith [hx.1])
        have hbcont : ContinuousAt (fun s : ℝ => Real.log (1+s)/(2+s)) (2*w/(1-w)) := by
          have h1 : ContinuousAt (fun s : ℝ => 1+s) (2*w/(1-w)) := by fun_prop
          have hlog : ContinuousAt (fun s : ℝ => Real.log (1+s)) (2*w/(1-w)) :=
            (Real.continuousAt_log (by linarith [hb_nonneg] : (1 + 2*w/(1-w)) ≠ 0)).comp h1
          have h2 : ContinuousAt (fun s : ℝ => 2+s) (2*w/(1-w)) := by fun_prop
          exact hlog.div h2 (by linarith [hb_nonneg])
        have hsub : Set.uIcc (0:ℝ) (2*w/(1-w)) ⊆ Set.Icc (0:ℝ) (2/3) := by
          intro x hx
          simp only [Set.uIcc_of_le hb_nonneg, Set.mem_Icc] at hx
          exact ⟨hx.1, hx.2.trans hb_le⟩
        have hint : IntervalIntegrable (fun s : ℝ => Real.log (1+s)/(2+s)) volume
            (0:ℝ) (2*w/(1-w)) := (hfcont.mono hsub).intervalIntegrable
        have hsm : StronglyMeasurableAtFilter (fun s : ℝ => Real.log (1+s)/(2+s))
            (nhds (2*w/(1-w))) :=
          ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi (-1)) isOpen_Ioi
            (fun x hx => by
              have hx' : (-1:ℝ) < x := hx
              have hx1 : (1 + x) ≠ 0 := by linarith
              have hx2 : (2 + x) ≠ 0 := by linarith
              exact ((Real.continuousAt_log hx1).comp (by fun_prop)).div (by fun_prop) hx2)
            (2*w/(1-w)) (by show (-1:ℝ) < 2*w/(1-w); linarith [hb_nonneg])
        have hInt : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, Real.log (1+s)/(2+s))
            (Real.log (1+(2*w/(1-w)))/(2+(2*w/(1-w)))) (2*w/(1-w)) :=
          intervalIntegral.integral_hasDerivAt_right hint hsm hbcont
        have hb : HasDerivAt (fun w : ℝ => 2*w/(1-w)) (2/(1-w)^2) w := by
          have h1 : HasDerivAt (fun w : ℝ => 2*w) 2 w := by
            simpa using (hasDerivAt_id w).const_mul 2
          have h2 : HasDerivAt (fun w : ℝ => 1-w) (-1) w := by
            simpa using (hasDerivAt_id w).const_sub 1
          have h3 := h1.div h2 hw1
          convert h3 using 1
          field_simp
          ring
        have hcomp := hInt.comp w hb
        have hstep : HasDerivAt (fun w : ℝ => ∫ s in (0:ℝ)..(2*w/(1-w)),
              Real.log (1+s)/(2+s)) (Real.log ((1+w)/(1-w))/(1-w)) w := by
          convert hcomp using 1
          · ext s
            rfl
          · have e1 : 1 + 2*w/(1-w) = (1+w)/(1-w) := by field_simp; ring
            have e2 : 2 + 2*w/(1-w) = 2/(1-w) := by field_simp; ring
            rw [e1, e2]
            field_simp
        have hlogdiv : Real.log ((1+w)/(1-w)) = Real.log (1+w) - Real.log (1-w) :=
          Real.log_div (by linarith : (1:ℝ)+w ≠ 0) (hw1)
        simpa only [hA, hlogdiv] using hstep
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hAint
      have h14 : (∫ s in (0:ℝ)..(2*(1/4)/(1-1/4)), Real.log (1+s)/(2+s))
          = ∫ s in (0:ℝ)..(2/3:ℝ), Real.log (1+s)/(2+s) := by norm_num
      have h0 : (∫ s in (0:ℝ)..(2*0/(1-0)), Real.log (1+s)/(2+s)) = 0 := by simp
      have hFTC' : (∫ w in (0:ℝ)..(1/4), A w)
          = ∫ s in (0:ℝ)..(2/3:ℝ), Real.log (1+s)/(2+s) := by
        rw [hFTC, h14, h0]
        ring
      exact hFTC'.symm
    -- step 3: integral monotonicity
    have hmono : (∫ w in (0:ℝ)..(1/4), A w) ≤ ∫ w in (0:ℝ)..(1/4), B w :=
      intervalIntegral.integral_mono_on (by norm_num) hAint hBint (fun x hx => hAB x hx)
    -- step 4: the antiderivative of the majorant
    have hHderiv : ∀ w ∈ Set.uIcc (0:ℝ) (1/4), HasDerivAt H (B w) w := by
      intro w hw
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hw
      obtain ⟨hw0, hw4⟩ := hw
      have hw1 : (1:ℝ) - w ≠ 0 := by linarith
      have hlogd : HasDerivAt (fun w : ℝ => Real.log (1-w)) ((1-w)⁻¹ * (-1)) w := by
        have hinner : HasDerivAt (fun w : ℝ => 1-w) (-1) w := by
          simpa using (hasDerivAt_id w).const_sub 1
        simpa only [Function.comp_def] using (Real.hasDerivAt_log hw1).comp w hinner
      have hl : HasDerivAt (fun w : ℝ => -Real.log (1-w)) ((1-w)⁻¹) w := by
        have h' := hlogd.neg
        convert h' using 1
        ring
      have hQd : HasDerivAt Q ((352/105:ℝ) + (71/105)*(2*w) + (142/315)*(3*w^2) + (6/35)*(4*w^3)
          + (24/175)*(5*w^4) + (1/21)*(6*w^5) + (2/49)*(7*w^6)) w := by
        have m1 : HasDerivAt (fun w : ℝ => (352/105:ℝ)*w) (352/105) w := by
          simpa using (hasDerivAt_id w).const_mul (352/105 : ℝ)
        have m2 : HasDerivAt (fun w : ℝ => (71/105:ℝ)*w^2) ((71/105)*(2*w)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^2) (2*w) w := by simpa using hasDerivAt_pow 2 w
          simpa [mul_assoc] using h'.const_mul (71/105 : ℝ)
        have m3 : HasDerivAt (fun w : ℝ => (142/315:ℝ)*w^3) ((142/315)*(3*w^2)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^3) (3*w^2) w := by simpa using hasDerivAt_pow 3 w
          simpa [mul_assoc] using h'.const_mul (142/315 : ℝ)
        have m4 : HasDerivAt (fun w : ℝ => (6/35:ℝ)*w^4) ((6/35)*(4*w^3)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^4) (4*w^3) w := by simpa using hasDerivAt_pow 4 w
          simpa [mul_assoc] using h'.const_mul (6/35 : ℝ)
        have m5 : HasDerivAt (fun w : ℝ => (24/175:ℝ)*w^5) ((24/175)*(5*w^4)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^5) (5*w^4) w := by simpa using hasDerivAt_pow 5 w
          simpa [mul_assoc] using h'.const_mul (24/175 : ℝ)
        have m6 : HasDerivAt (fun w : ℝ => (1/21:ℝ)*w^6) ((1/21)*(6*w^5)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^6) (6*w^5) w := by simpa using hasDerivAt_pow 6 w
          simpa [mul_assoc] using h'.const_mul (1/21 : ℝ)
        have m7 : HasDerivAt (fun w : ℝ => (2/49:ℝ)*w^7) ((2/49)*(7*w^6)) w := by
          have h' : HasDerivAt (fun w : ℝ => w^7) (7*w^6) w := by simpa using hasDerivAt_pow 7 w
          simpa [mul_assoc] using h'.const_mul (2/49 : ℝ)
        have hsum := ((((((m1.add m2).add m3).add m4).add m5).add m6).add m7)
        have hgoal : HasDerivAt (fun w : ℝ => (352/105:ℝ)*w + (71/105)*w^2 + (142/315)*w^3
            + (6/35)*w^4 + (24/175)*w^5 + (1/21)*w^6 + (2/49)*w^7)
            ((352/105:ℝ) + (71/105)*(2*w) + (142/315)*(3*w^2) + (6/35)*(4*w^3)
              + (24/175)*(5*w^4) + (1/21)*(6*w^5) + (2/49)*(7*w^6)) w := by
          convert hsum using 1
        simpa only [hQ] using hgoal
      have hHd : HasDerivAt H ((352/105 + 1/1000000)*(1-w)⁻¹ - ((352/105:ℝ) + (71/105)*(2*w)
          + (142/315)*(3*w^2) + (6/35)*(4*w^3) + (24/175)*(5*w^4) + (1/21)*(6*w^5)
          + (2/49)*(7*w^6))) w := by
        have h' := (hl.const_mul (352/105 + 1/1000000)).sub hQd
        convert h' using 1
      have hid : (352/105 + 1/1000000)*(1-w)⁻¹ - ((352/105:ℝ) + (71/105)*(2*w)
          + (142/315)*(3*w^2) + (6/35)*(4*w^3) + (24/175)*(5*w^4) + (1/21)*(6*w^5)
          + (2/49)*(7*w^6)) = B w := by
        simp only [hB]
        field_simp
        ring
      rw [hid] at hHd
      exact hHd
    have hFTC2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hHderiv hBint
    have hH0 : H 0 = 0 := by
      simp [hH, hQ]
    have hH14 : H (1/4) ≤ 0.2876822*(352/105 + 1/1000000) - Q (1/4) := by
      have h34 : -Real.log (1 - 1/4) = Real.log (4/3) := by
        rw [show (1:ℝ) - 1/4 = (4/3)⁻¹ by norm_num, Real.log_inv]
        ring
      simp only [hH]
      rw [h34]
      nlinarith [log_four_three_le]
    have hnum : 8*(0.2876822*(352/105 + 1/1000000) - Q (1/4)) ≤ 0.60962 := by
      simp only [hQ]
      norm_num
    rw [hI1, hI2]
    have hstep1 : 8 * (∫ w in (0:ℝ)..(1/4), A w) ≤ 8 * (∫ w in (0:ℝ)..(1/4), B w) := by
      linarith [hmono]
    have hstep2 : 8 * (∫ w in (0:ℝ)..(1/4), B w) = 8 * (H (1/4) - H 0) := by rw [hFTC2]
    have hstep3 : 8 * (H (1/4) - H 0) = 8 * H (1/4) := by rw [hH0]; ring
    have hstep4 : 8 * H (1/4) ≤ 8*(0.2876822*(352/105 + 1/1000000) - Q (1/4)) := by
      linarith [hH14]
    linarith [hstep1, hstep2, hstep3, hstep4, hnum]

end PEqualNP.Outside

/-! Canonical module-named statement (platform checker requires a declaration
named exactly after the gap module: `Conjectures.Goldbach.SwitchingSieveEdgeIntegrals`). -/

theorem Conjectures.Goldbach.SwitchingSieveEdgeIntegrals :
    8 * Real.log (10 / 9) ≤ (0.84289 : ℝ) ∧ 8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (0.60962 : ℝ) := by
  exact PEqualNP.Outside.L_goldbach_switching_sieve_edge_integrals
