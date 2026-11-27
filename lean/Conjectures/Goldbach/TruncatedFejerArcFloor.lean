import Mathlib

open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.TruncatedFejerArcFloor_aux

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def K (N : ℕ) (b : ℝ) : ℂ := ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b)

noncomputable def F (N : ℕ) (b : ℝ) : ℂ := (K N b) ^ 2 * E (-(N : ℝ) * b)

end Conjectures.Goldbach.TruncatedFejerArcFloor_aux

open Conjectures.Goldbach.TruncatedFejerArcFloor_aux

theorem Conjectures.Goldbach.TruncatedFejerArcFloor :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let K (N : ℕ) (b : ℝ) := ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b); ∀ (N : ℕ) (W : ℝ), 0 < W → W ≤ 1 / 2 → ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤ (intervalIntegral (fun b => (K N b)^2 * E (-(N : ℝ) * b)) (-W) W MeasureTheory.volume).re := by
  dsimp only
  intro N W hW hWhalf
  change ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤
    (intervalIntegral (fun b => F N b) (-W) W MeasureTheory.volume).re
  have hWne : W ≠ 0 := ne_of_gt hW
  have hE_add : ∀ x y : ℝ, E (x + y) = E x * E y := by
    intro x y
    show Complex.exp (((2 * Real.pi * (x + y) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hE_zero : E 0 = 1 := by
    show Complex.exp (((2 * Real.pi * 0 : ℝ) : ℂ) * Complex.I) = 1
    norm_num [Complex.exp_zero]
  have hE_norm : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    show ‖Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ = 1
    exact Complex.norm_exp_ofReal_mul_I _
  have hE_cont : Continuous E := by
    show Continuous (fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    fun_prop
  have hE_pow : ∀ (b : ℝ) (k : ℕ), E ((k : ℝ) * b) = (E b) ^ k := by
    intro b k
    show Complex.exp (((2 * Real.pi * ((k : ℝ) * b) : ℝ) : ℂ) * Complex.I)
        = (Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I)) ^ k
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hK_cont : ∀ M : ℕ, Continuous (K M) := by
    intro M
    unfold K
    exact continuous_finsetSum _ (fun k _ => hE_cont.comp (by fun_prop))
  have hF_cont : Continuous (F N) := by
    have h1 : Continuous (fun b : ℝ => -(N : ℝ) * b) := by fun_prop
    unfold F
    exact ((hK_cont N).pow 2).mul (hE_cont.comp h1)
  have horth : ∀ m : ℤ, intervalIntegral (fun b : ℝ => E ((m : ℝ) * b)) (-(1 / 2)) (1 / 2)
      MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have hg : (fun b : ℝ => E (((0 : ℤ) : ℝ) * b)) = fun _ => (1 : ℂ) := by
        funext b
        rw [show (((0 : ℤ) : ℝ) * b) = 0 by simp, hE_zero]
      rw [hg, intervalIntegral.integral_const, if_pos rfl, Complex.real_smul]
      norm_num
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hz
        refine hm ?_
        exact_mod_cast hz
      set c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I with hcdef
      have hcne : c ≠ 0 := by
        have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          intro hz
          have hz' := congrArg Complex.re hz
          simp only [Complex.ofReal_re, Complex.zero_re] at hz'
          exact h1 hz'
        rw [hcdef]
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hexpc : Complex.exp c = 1 := by
        have hstep : c = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          rw [hcdef]; push_cast; ring
        rw [hstep, Complex.exp_int_mul_two_pi_mul_I]
      have hrewrite : (fun b : ℝ => E ((m : ℝ) * b))
          = fun b : ℝ => Complex.exp (c * (b : ℂ)) := by
        funext b
        show Complex.exp (((2 * Real.pi * ((m : ℝ) * b) : ℝ) : ℂ) * Complex.I)
            = Complex.exp (c * (b : ℂ))
        rw [hcdef]
        congr 1
        push_cast
        ring
      rw [hrewrite, integral_exp_mul_complex hcne, if_neg hm]
      have hnum : Complex.exp (c * ((1 / 2 : ℝ) : ℂ))
          - Complex.exp (c * ((-(1 / 2) : ℝ) : ℂ)) = 0 := by
        have h2d : (2 : ℂ) * (c * ((1 / 2 : ℝ) : ℂ)) = c := by
          rw [hcdef]; push_cast; ring
        have e1 : Complex.exp (c * ((-(1 / 2) : ℝ) : ℂ))
            = Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) := by
          have hstep : c * ((-(1 / 2) : ℝ) : ℂ)
              = c * ((1 / 2 : ℝ) : ℂ) - 2 * (c * ((1 / 2 : ℝ) : ℂ)) := by
            rw [hcdef]; push_cast; ring
          rw [hstep, h2d, Complex.exp_sub, hexpc, div_one]
        rw [e1, sub_self]
      rw [hnum, zero_div]
  have hF_expand : ∀ b : ℝ, F N b = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b) := by
    intro b
    simp only [F, K]
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hE_add, ← hE_add]
    congr 1
    push_cast
    ring
  have hii_E : ∀ m : ℤ, IntervalIntegrable (fun b : ℝ => E ((m : ℝ) * b))
      MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
    intro m
    exact (hE_cont.comp (by fun_prop)).intervalIntegrable _ _
  have hsum1 : ∑ _j ∈ Finset.range (N + 1), (1 : ℂ) = ((N + 1 : ℕ) : ℂ) := by
    rw [Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
  have hfull : intervalIntegral (fun b => F N b) (-(1 / 2)) (1 / 2) MeasureTheory.volume
      = ((N + 1 : ℕ) : ℂ) := by
    have hrw : (fun b : ℝ => F N b) = fun b : ℝ => ∑ j ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N + 1), E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b) :=
      funext hF_expand
    have hcont_inner : ∀ j : ℕ, Continuous (fun b : ℝ => ∑ k ∈ Finset.range (N + 1),
        E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b)) :=
      fun j => continuous_finsetSum _ (fun k _ => hE_cont.comp (by fun_prop))
    have hinner : ∀ j : ℕ, intervalIntegral (fun b : ℝ => ∑ k ∈ Finset.range (N + 1),
        E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b)) (-(1 / 2)) (1 / 2) MeasureTheory.volume
        = ∑ k ∈ Finset.range (N + 1),
            intervalIntegral (fun b : ℝ => E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b))
              (-(1 / 2)) (1 / 2) MeasureTheory.volume :=
      fun j => intervalIntegral.integral_finsetSum (fun k _ => hii_E _)
    rw [hrw, intervalIntegral.integral_finsetSum
      (fun j _ => (hcont_inner j).intervalIntegrable _ _),
      Finset.sum_congr rfl (fun j _ => hinner j)]
    have hstep : ∀ j ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N + 1),
          intervalIntegral (fun b : ℝ => E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b))
            (-(1 / 2)) (1 / 2) MeasureTheory.volume = 1 := by
      intro j hj
      have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
      have hsum : (∑ k ∈ Finset.range (N + 1),
          intervalIntegral (fun b : ℝ => E ((((j : ℤ) + (k : ℤ) - (N : ℤ) : ℤ) : ℝ) * b))
            (-(1 / 2)) (1 / 2) MeasureTheory.volume)
          = ∑ k ∈ Finset.range (N + 1),
              (if ((j : ℤ) + (k : ℤ) - (N : ℤ)) = 0 then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl (fun k _ => horth _)
      rw [hsum]
      have hcond : ∀ k : ℕ, (((j : ℤ) + (k : ℤ) - (N : ℤ)) = 0) ↔ (k = N - j) := by
        intro k; omega
      simp_rw [hcond]
      have hsub : ({N - j} : Finset ℕ) ⊆ Finset.range (N + 1) := by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        simp only [Finset.mem_range]
        omega
      have hz : ∀ k ∈ Finset.range (N + 1), k ∉ ({N - j} : Finset ℕ) →
          (if k = N - j then (1 : ℂ) else 0) = 0 := by
        intro k _ hk
        have hk' : k ≠ N - j := by
          intro h
          exact hk (by simp [h])
        simp [hk']
      have hss := Finset.sum_subset hsub hz
      rw [← hss]
      simp
    rw [Finset.sum_congr rfl hstep, hsum1]
  have hfullre : (intervalIntegral (fun b => F N b) (-(1 / 2)) (1 / 2) MeasureTheory.volume).re
      = ((N + 1 : ℕ) : ℝ) := by
    rw [hfull]
    simp
  have hpt : ∀ b : ℝ, b ≠ 0 → |b| ≤ 1 / 2 → ‖F N b‖ ≤ (1 / 4) * b ^ (-2 : ℤ) := by
    intro b hbne habs
    have habsp : 0 < |b| := abs_pos.mpr hbne
    have hz : K N b = ∑ k ∈ Finset.range (N + 1), (E b) ^ k := by
      simp only [K]
      exact Finset.sum_congr rfl (fun k _ => hE_pow b k)
    have hgm : K N b * (E b - 1) = (E b) ^ (N + 1) - 1 := by
      rw [hz]
      exact geom_sum_mul (E b) (N + 1)
    have h1 : ‖K N b‖ * ‖E b - 1‖ ≤ 2 := by
      have hn := congrArg norm hgm
      rw [norm_mul] at hn
      rw [hn]
      calc ‖(E b) ^ (N + 1) - 1‖ ≤ ‖(E b) ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_pow, hE_norm b, one_pow, norm_one]
        _ = 2 := by ring
    have hchord : ‖E b - 1‖ = 2 * |Real.sin (Real.pi * b)| := by
      have hrw : E b - 1 = Complex.exp (Complex.I * ((2 * Real.pi * b : ℝ) : ℂ)) - 1 := by
        show Complex.exp (((2 * Real.pi * b : ℝ) : ℂ) * Complex.I) - 1
            = Complex.exp (Complex.I * ((2 * Real.pi * b : ℝ) : ℂ)) - 1
        rw [mul_comm]
      rw [hrw, Complex.norm_exp_I_mul_ofReal_sub_one,
        show (2 * Real.pi * b : ℝ) / 2 = Real.pi * b by ring]
      simp [Real.norm_eq_abs]
    have hsinlb : 2 * |b| ≤ |Real.sin (Real.pi * b)| := by
      have h1' : |Real.pi * b| ≤ Real.pi / 2 := by
        rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
        calc Real.pi * |b| ≤ Real.pi * (1 / 2) := by nlinarith [Real.pi_pos]
          _ = Real.pi / 2 := by ring
      have h2 := Real.mul_abs_le_abs_sin (x := Real.pi * b) h1'
      rw [abs_mul, abs_of_nonneg Real.pi_pos.le] at h2
      have h3 : 2 / Real.pi * (Real.pi * |b|) = 2 * |b| := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
      rw [h3] at h2
      exact h2
    have hKn : ‖K N b‖ ≤ 1 / (2 * |b|) := by
      have hmul : ‖K N b‖ * (4 * |b|) ≤ 2 := by
        calc ‖K N b‖ * (4 * |b|) ≤ ‖K N b‖ * ‖E b - 1‖ := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              rw [hchord]; nlinarith [hsinlb]
          _ ≤ 2 := h1
      have hden : (0 : ℝ) < 2 * |b| := by positivity
      rw [le_div_iff₀ hden]
      nlinarith [hmul]
    have hFnorm : ‖F N b‖ = ‖K N b‖ ^ 2 := by
      simp only [F]
      rw [norm_mul, norm_pow, hE_norm, mul_one]
    rw [hFnorm]
    have hKsq : ‖K N b‖ ^ 2 ≤ (1 / (2 * |b|)) ^ 2 := by
      have ha : (0 : ℝ) ≤ ‖K N b‖ := norm_nonneg _
      have hb : (0 : ℝ) ≤ 1 / (2 * |b|) := by positivity
      nlinarith [hKn, ha, hb]
    calc ‖K N b‖ ^ 2 ≤ (1 / (2 * |b|)) ^ 2 := hKsq
      _ = 1 / (4 * b ^ 2) := by rw [div_pow, one_pow, mul_pow, sq_abs]; norm_num
      _ = (1 / 4) * b ^ (-2 : ℤ) := by
          have hb2 : (b ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hbne
          rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
          field_simp
  have h0W' : (0 : ℝ) ∉ Set.uIcc W (1 / 2) := by
    rw [Set.uIcc_of_le hWhalf, Set.mem_Icc]
    intro ⟨h1, _⟩
    linarith
  have h0N : (0 : ℝ) ∉ Set.uIcc (-(1 / 2)) (-W) := by
    have hle : (-(1 / 2) : ℝ) ≤ -W := by linarith
    rw [Set.uIcc_of_le hle, Set.mem_Icc]
    intro ⟨_, h2⟩
    linarith
  have hii_zpow : ∀ a b : ℝ, (0 : ℝ) ∉ Set.uIcc a b →
      IntervalIntegrable (fun x : ℝ => (1 / 4) * x ^ (-2 : ℤ)) MeasureTheory.volume a b := by
    intro a b h0
    have hx0 : ∀ x ∈ Set.uIcc a b, (x : ℝ) ≠ 0 := by
      intro x hx hx0
      exact h0 (hx0 ▸ hx)
    have h1 : ContinuousOn (fun x : ℝ => ((x ^ 2))⁻¹) (Set.uIcc a b) :=
      (continuousOn_id.pow 2).inv₀ (fun x hx => pow_ne_zero 2 (hx0 x hx))
    have h2 : (fun x : ℝ => (1 / 4) * x ^ (-2 : ℤ)) = fun x : ℝ => (1 / 4) * ((x ^ 2))⁻¹ := by
      funext x
      rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    rw [h2]
    exact (continuousOn_const.mul h1).intervalIntegrable
  have htail_pos : intervalIntegral (fun b : ℝ => (1 / 4) * b ^ (-2 : ℤ)) W (1 / 2)
      MeasureTheory.volume = 1 / (4 * W) - 1 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      integral_zpow (a := W) (b := (1 / 2)) (n := -2) (Or.inr ⟨by norm_num, h0W'⟩)]
    have ha : W ^ ((-2 : ℤ) + 1) = W⁻¹ := by
      rw [show (-2 : ℤ) + 1 = -(1 : ℤ) by norm_num, zpow_neg, zpow_one]
    have hb : ((1 / 2 : ℝ)) ^ ((-2 : ℤ) + 1) = 2 := by
      rw [show (-2 : ℤ) + 1 = -(1 : ℤ) by norm_num, zpow_neg, zpow_one]
      norm_num
    have hc : (((-2 : ℤ) + 1) : ℝ) = -1 := by norm_num
    rw [ha, hb, hc]
    field_simp
    ring
  have htail_neg : intervalIntegral (fun b : ℝ => (1 / 4) * b ^ (-2 : ℤ)) (-(1 / 2)) (-W)
      MeasureTheory.volume = 1 / (4 * W) - 1 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      integral_zpow (a := (-(1 / 2))) (b := (-W)) (n := -2) (Or.inr ⟨by norm_num, h0N⟩)]
    have ha : (-(1 / 2) : ℝ) ^ ((-2 : ℤ) + 1) = -2 := by
      rw [show (-2 : ℤ) + 1 = -(1 : ℤ) by norm_num, zpow_neg, zpow_one]
      norm_num
    have hb : (-W : ℝ) ^ ((-2 : ℤ) + 1) = -(W⁻¹) := by
      rw [show (-2 : ℤ) + 1 = -(1 : ℤ) by norm_num, zpow_neg, zpow_one, inv_neg]
    have hc : (((-2 : ℤ) + 1) : ℝ) = -1 := by norm_num
    rw [ha, hb, hc]
    field_simp
    ring
  have hbound_neg : (intervalIntegral (fun b => F N b) (-(1 / 2)) (-W) MeasureTheory.volume).re
      ≤ 1 / (4 * W) := by
    calc (intervalIntegral (fun b => F N b) (-(1 / 2)) (-W) MeasureTheory.volume).re
        ≤ ‖intervalIntegral (fun b => F N b) (-(1 / 2)) (-W) MeasureTheory.volume‖ :=
          Complex.re_le_norm _
      _ ≤ intervalIntegral (fun b => ‖F N b‖) (-(1 / 2)) (-W) MeasureTheory.volume :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ intervalIntegral (fun b : ℝ => (1 / 4) * b ^ (-2 : ℤ)) (-(1 / 2)) (-W)
          MeasureTheory.volume := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hF_cont.norm.intervalIntegrable _ _) (hii_zpow _ _ h0N) (fun b hb => ?_)
          refine hpt b (by linarith [hb.2]) ?_
          rw [abs_of_nonpos (by linarith [hb.2])]
          linarith [hb.1]
      _ = 1 / (4 * W) - 1 / 2 := htail_neg
      _ ≤ 1 / (4 * W) := by linarith
  have hbound_pos : (intervalIntegral (fun b => F N b) W (1 / 2) MeasureTheory.volume).re
      ≤ 1 / (4 * W) := by
    calc (intervalIntegral (fun b => F N b) W (1 / 2) MeasureTheory.volume).re
        ≤ ‖intervalIntegral (fun b => F N b) W (1 / 2) MeasureTheory.volume‖ :=
          Complex.re_le_norm _
      _ ≤ intervalIntegral (fun b => ‖F N b‖) W (1 / 2) MeasureTheory.volume :=
          intervalIntegral.norm_integral_le_integral_norm hWhalf
      _ ≤ intervalIntegral (fun b : ℝ => (1 / 4) * b ^ (-2 : ℤ)) W (1 / 2)
          MeasureTheory.volume := by
          refine intervalIntegral.integral_mono_on hWhalf
            (hF_cont.norm.intervalIntegrable _ _) (hii_zpow _ _ h0W') (fun b hb => ?_)
          refine hpt b (by linarith [hb.1]) ?_
          rw [abs_of_nonneg (by linarith [hb.1])]
          exact hb.2
      _ = 1 / (4 * W) - 1 / 2 := htail_pos
      _ ≤ 1 / (4 * W) := by linarith
  have hF_ii : ∀ a b : ℝ, IntervalIntegrable (F N) MeasureTheory.volume a b :=
    fun a b => hF_cont.intervalIntegrable a b
  have hre : (intervalIntegral (fun b => F N b) (-W) W MeasureTheory.volume).re
      = (intervalIntegral (fun b => F N b) (-(1 / 2)) (1 / 2) MeasureTheory.volume).re
        - (intervalIntegral (fun b => F N b) (-(1 / 2)) (-W) MeasureTheory.volume).re
        - (intervalIntegral (fun b => F N b) W (1 / 2) MeasureTheory.volume).re := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hF_ii (-(1 / 2)) (-W)) (hF_ii (-W) (1 / 2))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hF_ii (-W) W) (hF_ii W (1 / 2))
    have hsplit : intervalIntegral (fun b => F N b) (-W) W MeasureTheory.volume
        = intervalIntegral (fun b => F N b) (-(1 / 2)) (1 / 2) MeasureTheory.volume
          - intervalIntegral (fun b => F N b) (-(1 / 2)) (-W) MeasureTheory.volume
          - intervalIntegral (fun b => F N b) W (1 / 2) MeasureTheory.volume := by
      rw [← h1, ← h2]
      ring
    rw [hsplit, Complex.sub_re, Complex.sub_re]
  have hkey : 1 / (2 * W) = 2 * (1 / (4 * W)) := by
    field_simp
    ring
  rw [hre, hfullre]
  have hsum : 1 / (4 * W) + 1 / (4 * W) ≤ 1 / (2 * W) := by
    rw [hkey]
    linarith
  linarith [hbound_neg, hbound_pos]
