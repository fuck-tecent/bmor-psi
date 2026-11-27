import Mathlib

open Finset Filter

noncomputable def hcG (d : ℕ) : ℝ :=
  if d % 2 = 1 then (∏ p ∈ d.primeFactors, (-1 / ((p : ℝ) - 1))) / d else 0

noncomputable def hcMo (y : ℕ) : ℝ :=
  ∑ e ∈ (Finset.Icc 1 y).filter (fun e => e % 2 = 1), (ArithmeticFunction.moebius e : ℝ) / e

noncomputable def hcTo (y : ℕ) : ℝ :=
  ∑ e ∈ (Finset.Icc 1 y).filter (fun e => e % 2 = 1), -(ArithmeticFunction.moebius e : ℝ) * Real.log e / e

theorem hc_moebius_aux_mu_littleO_aux_lim :
    Tendsto (fun s : ℂ => (riemannZeta s - 1 / (s - 1)) + (riemannZeta s)⁻¹)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds (Real.eulerMascheroniConstant : ℂ)) := by
  have h1 := tendsto_riemannZeta_sub_one_div
  have h2 : Tendsto (fun s : ℂ => (riemannZeta s)⁻¹)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 0) := by
    have ha : Tendsto (fun s : ℂ => ((s - 1) * riemannZeta s)⁻¹)
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 1) := by
      simpa using riemannZeta_residue_one.inv₀ one_ne_zero
    have hb : Tendsto (fun s : ℂ => s - 1)
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 0) := by
      have h0 : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds ((1 : ℂ) - 1)) :=
        (continuousAt_id.sub continuousAt_const).tendsto
      simpa using h0.mono_left nhdsWithin_le_nhds
    have hab : Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹)
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 0) := by
      simpa using hb.mul ha
    refine hab.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 1 := hs
    have hs1 : (s - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs'
    by_cases h0 : riemannZeta s = 0
    · simp [h0]
    · field_simp
  simpa using h1.add h2

theorem hc_moebius_aux_mu_littleO_aux_cont :
    ContinuousOn (Function.update
      (fun s : ℂ => (riemannZeta s - 1 / (s - 1)) + (riemannZeta s)⁻¹) 1
      (Real.eulerMascheroniConstant : ℂ)) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  have hsre : 1 ≤ s.re := hs
  by_cases hs1 : s = 1
  · subst hs1
    have h : ContinuousAt (Function.update
        (fun t : ℂ => (riemannZeta t - 1 / (t - 1)) + (riemannZeta t)⁻¹) 1
        (Real.eulerMascheroniConstant : ℂ)) 1 := by
      rw [continuousAt_update_same]
      exact hc_moebius_aux_mu_littleO_aux_lim
    exact h.continuousWithinAt
  · have hζ : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta hs1).continuousAt
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
    have hsub : ContinuousAt (fun t : ℂ => t - 1) s := by fun_prop
    have hdiv : ContinuousAt (fun t : ℂ => (1 : ℂ) / (t - 1)) s := by
      have h : ContinuousAt (fun t : ℂ => (t - 1)⁻¹) s := hsub.inv₀ (sub_ne_zero.mpr hs1)
      simpa [div_eq_mul_inv] using h
    have hcont : ContinuousAt
        (fun t : ℂ => (riemannZeta t - 1 / (t - 1)) + (riemannZeta t)⁻¹) s :=
      (hζ.sub hdiv).add (hζ.inv₀ hne)
    have hG : ContinuousAt (Function.update
        (fun t : ℂ => (riemannZeta t - 1 / (t - 1)) + (riemannZeta t)⁻¹) 1
        (Real.eulerMascheroniConstant : ℂ)) s := by
      refine hcont.congr ?_
      filter_upwards [eventually_ne_nhds hs1] with t ht
      exact (Function.update_of_ne ht (Real.eulerMascheroniConstant : ℂ)
        (fun t : ℂ => (riemannZeta t - 1 / (t - 1)) + (riemannZeta t)⁻¹)).symm
    exact hG.continuousWithinAt

theorem hc_moebius_aux_mu_littleO_aux_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((1 + (ArithmeticFunction.moebius n : ℝ) : ℝ) : ℂ)) s
      = riemannZeta s + (riemannZeta s)⁻¹ := by
  have hf' : (fun n : ℕ => ((1 + (ArithmeticFunction.moebius n : ℝ) : ℝ) : ℂ))
      = (1 : ℕ → ℂ) + (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) := by
    funext n
    simp only [Pi.add_apply, Pi.one_apply]
    push_cast
    ring
  rw [hf', LSeries_add (LSeriesSummable_one_iff.mpr hs)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs), LSeries_one_eq_riemannZeta hs]
  congr 1
  have hmul := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hmul
  exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem hc_moebius_aux_mu_littleO_aux_eqOn :
    Set.EqOn (Function.update
      (fun s : ℂ => (riemannZeta s - 1 / (s - 1)) + (riemannZeta s)⁻¹) 1
      (Real.eulerMascheroniConstant : ℂ))
      (fun s : ℂ => LSeries (fun n : ℕ => ((1 + (ArithmeticFunction.moebius n : ℝ) : ℝ) : ℂ)) s
        - (1 : ℝ) / (s - 1))
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hsre : 1 < s.re := hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    simp at hsre
  dsimp only
  rw [Function.update_of_ne hs1, hc_moebius_aux_mu_littleO_aux_LSeries hsre]
  push_cast
  ring

theorem hc_moebius_aux_mu_littleO_aux_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 + (ArithmeticFunction.moebius n : ℝ) := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  have h' : ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
  have h'' : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by simpa [Int.cast_abs] using h'
  linarith [(abs_le.mp h'').1]

theorem hc_moebius_aux_mu_littleO_aux_bound (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 + (ArithmeticFunction.moebius i : ℝ)) ≤ 2 * (n : ℝ) := by
  have hle : ∀ i ∈ Finset.range n, (1 + (ArithmeticFunction.moebius i : ℝ)) ≤ 2 := by
    intro i _
    have h := ArithmeticFunction.abs_moebius_le_one (n := i)
    have h' : ((|ArithmeticFunction.moebius i| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    have h'' : |(ArithmeticFunction.moebius i : ℝ)| ≤ 1 := by simpa [Int.cast_abs] using h'
    linarith [(abs_le.mp h'').2]
  calc ∑ i ∈ Finset.range n, (1 + (ArithmeticFunction.moebius i : ℝ))
      ≤ ∑ i ∈ Finset.range n, (2 : ℝ) := Finset.sum_le_sum hle
    _ = 2 * (n : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem hc_moebius_aux_mu_littleO_aux_sum (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), (1 + (ArithmeticFunction.moebius i : ℝ)))
      = ((N : ℝ) + 1) + ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) := by
  rw [Finset.sum_add_distrib]
  have h2 : (∑ i ∈ Finset.range (N + 1), (1 : ℝ)) = ((N : ℝ) + 1) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have h3 : (∑ i ∈ Finset.range (N + 1), (ArithmeticFunction.moebius i : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) := by
    rw [Nat.range_succ_eq_Icc_zero]
    have hins : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp)]
    simp
  rw [h2, h3]

theorem hc_moebius_aux_mu_littleO :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)) / N)
      atTop (nhds 0) := by
  have hWI : Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, (1 + (ArithmeticFunction.moebius i : ℝ))) / (N : ℝ))
      atTop (nhds 1) :=
    WienerIkehara.tendsto_sum_range_div (f := fun n : ℕ => 1 + (ArithmeticFunction.moebius n : ℝ))
      (C := 2) (A := 1)
      (G := Function.update
        (fun s : ℂ => (riemannZeta s - 1 / (s - 1)) + (riemannZeta s)⁻¹) 1
        (Real.eulerMascheroniConstant : ℂ))
      hc_moebius_aux_mu_littleO_aux_bound hc_moebius_aux_mu_littleO_aux_cont hc_moebius_aux_mu_littleO_aux_eqOn (fun n => hc_moebius_aux_mu_littleO_aux_nonneg n)
  have hcomp : Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range (N + 1), (1 + (ArithmeticFunction.moebius i : ℝ))) / ((N : ℝ) + 1))
      atTop (nhds 1) := by
    have h := hWI.comp (tendsto_add_atTop_nat 1)
    refine h.congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hz : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)) / ((N : ℝ) + 1))
      atTop (nhds 0) := by
    have h3 : Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range (N + 1), (1 + (ArithmeticFunction.moebius i : ℝ))) / ((N : ℝ) + 1) - 1)
        atTop (nhds 0) := by
      simpa using hcomp.sub (tendsto_const_nhds (x := (1 : ℝ)))
    refine h3.congr' ?_
    filter_upwards with N
    rw [hc_moebius_aux_mu_littleO_aux_sum]
    have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hratio : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (nhds 1) := by
    have h : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hfin : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)) / ((N : ℝ) + 1)
        * (((N : ℝ) + 1) / (N : ℝ))) atTop (nhds 0) := by
    simpa using hz.mul hratio
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma hc_moebius_aux_axer_aux_block_fiber_eq (N j : ℕ) (hj : 1 ≤ j) :
    (Finset.Icc 1 N).filter (fun n => N / n = j) =
      Finset.Ioc (N / (j + 1)) (N / j) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hdiv⟩
    have hnpos : 0 < n := by omega
    have hspec := (Nat.div_eq_iff hnpos).mp hdiv
    constructor
    · apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).2
      have heq : n * (j + 1) = j * n + n := by ring
      rw [heq]
      omega
    · apply (Nat.le_div_iff_mul_le hj).2
      simpa [Nat.mul_comm] using hspec.1
  · rintro ⟨hlo, hhi⟩
    have hnpos : 0 < n := (Nat.zero_le (N / (j + 1))).trans_lt hlo
    have hnN : n ≤ N := hhi.trans (Nat.div_le_self N j)
    have hmulhi : n * j ≤ N := (Nat.le_div_iff_mul_le hj).mp hhi
    have hmullo : N < n * (j + 1) :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlo
    refine ⟨⟨by omega, hnN⟩, (Nat.div_eq_iff hnpos).2 ?_⟩
    constructor
    · simpa [Nat.mul_comm] using hmulhi
    · have heq : n * (j + 1) = j * n + n := by ring
      omega

lemma hc_moebius_aux_axer_aux_high_sum_eq_fibers (N K : ℕ) (hK : 2 ≤ K) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N with N / K < n, f n) =
      ∑ j ∈ Finset.Icc 1 (K - 1),
        ∑ n ∈ Finset.Icc 1 N with N / n = j, f n := by
  symm
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  apply Finset.filter_congr
  intro n hn
  have hnIcc := Finset.mem_Icc.mp hn
  have hnpos : 0 < n := by omega
  have hqlo : 1 ≤ N / n := by
    apply (Nat.le_div_iff_mul_le hnpos).2
    simpa using hnIcc.2
  constructor
  · intro hq
    have hq' := Finset.mem_Icc.mp hq
    have hqlt : N / n < K := by omega
    have hmul : N < K * n := (Nat.div_lt_iff_lt_mul hnpos).mp hqlt
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < K)).2
      (by simpa [Nat.mul_comm] using hmul)
  · intro hnhigh
    have hmul : N < n * K :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < K)).mp hnhigh
    have hqlt : N / n < K := (Nat.div_lt_iff_lt_mul hnpos).2
      (by simpa [Nat.mul_comm] using hmul)
    exact Finset.mem_Icc.mpr ⟨hqlo, by omega⟩

lemma hc_moebius_aux_axer_aux_block_prefix (L k : ℕ) :
    (∑ i ∈ Finset.range k, (ArithmeticFunction.moebius (L + 1 + i) : ℝ)) =
      (∑ n ∈ Finset.Icc 1 (L + k), (ArithmeticFunction.moebius n : ℝ)) -
        ∑ n ∈ Finset.Icc 1 L, (ArithmeticFunction.moebius n : ℝ) := by
  have hr := Finset.sum_Ico_eq_sum_range
    (fun n => (ArithmeticFunction.moebius n : ℝ)) (L + 1) (L + 1 + k)
  rw [show L + 1 + k - (L + 1) = k by omega] at hr
  rw [← hr]
  rw [show L + 1 + k = L + k + 1 by omega]
  rw [Finset.Ico_add_one_add_one_eq_Ioc]
  have hIcc : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x := by
    intro x
    simpa using (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) x)
  rw [hIcc (L + k), hIcc L]
  have h := Finset.sum_Ioc_consecutive
    (fun n => (ArithmeticFunction.moebius n : ℝ)) (m := 0) (n := L) (k := L + k)
    (Nat.zero_le L) (Nat.le_add_right L k)
  linarith

lemma hc_moebius_aux_axer_aux_abel_block
    (L U : ℕ) (w : ℕ → ℝ) (A : ℝ)
    (hLU : L < U)
    (hM : ∀ x, L ≤ x → x ≤ U →
      |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| ≤ A)
    (hw0 : 0 ≤ w (L + 1))
    (hw_nonneg : ∀ x, L < x → x ≤ U → 0 ≤ w x)
    (hw1 : w (L + 1) ≤ 1)
    (hwanti : ∀ x y, L < x → x ≤ y → y ≤ U → w y ≤ w x) :
    |∑ n ∈ Finset.Ioc L U,
      (ArithmeticFunction.moebius n : ℝ) * w n| ≤ 2 * A := by
  let g : ℕ → ℝ := fun i => if L + 1 + i ≤ U then w (L + 1 + i) else 0
  have hsum :
      (∑ n ∈ Finset.Ioc L U,
        (ArithmeticFunction.moebius n : ℝ) * w n) =
      ∑ i ∈ Finset.range (U - L),
        (ArithmeticFunction.moebius (L + 1 + i) : ℝ) * g i := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show U + 1 - (L + 1) = U - L by omega]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < U - L := Finset.mem_range.mp hi
    have hiu : L + 1 + i ≤ U := by omega
    simp [g, hiu]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hM L le_rfl hLU.le)
  have hprefix : ∀ k ≤ U - L,
      |∑ i ∈ Finset.range k,
        (ArithmeticFunction.moebius (L + 1 + i) : ℝ)| ≤ 2 * A := by
    intro k hk
    rw [hc_moebius_aux_axer_aux_block_prefix]
    have hkU : L + k ≤ U := by omega
    calc
      |(∑ n ∈ Finset.Icc 1 (L + k), (ArithmeticFunction.moebius n : ℝ)) -
          ∑ n ∈ Finset.Icc 1 L, (ArithmeticFunction.moebius n : ℝ)| ≤
          |∑ n ∈ Finset.Icc 1 (L + k), (ArithmeticFunction.moebius n : ℝ)| +
            |∑ n ∈ Finset.Icc 1 L, (ArithmeticFunction.moebius n : ℝ)| :=
        abs_sub _ _
      _ ≤ A + A := add_le_add (hM (L + k) (by omega) hkU) (hM L le_rfl hLU.le)
      _ = 2 * A := by ring
  have hg0 : 0 ≤ g := by
    intro i
    change 0 ≤ g i
    by_cases hiu : L + 1 + i ≤ U
    · simpa [g, hiu] using hw_nonneg (L + 1 + i) (by omega) hiu
    · simp [g, hiu]
  have hg1 : g 0 ≤ 1 := by
    have hzero : L + 1 + 0 ≤ U := by omega
    simpa [g, hzero] using hw1
  have hg : AntitoneOn g (Set.Iio (U - L)) := by
    intro x hx y hy hxy
    have hx' : x < U - L := hx
    have hy' : y < U - L := hy
    have hxu : L + 1 + x ≤ U := by omega
    have hyu : L + 1 + y ≤ U := by omega
    simp only [g, if_pos hxu, if_pos hyu]
    exact hwanti (L + 1 + x) (L + 1 + y) (by omega) (by omega) hyu
  have habel := Finset.abs_sum_mul_le_mul_of_abs_sum_range_le
    (f := fun i => (ArithmeticFunction.moebius (L + 1 + i) : ℝ))
    (g := g) (M := 2 * A) (n := U - L)
    hprefix hg0 hg
  rw [hsum]
  calc
    |∑ i ∈ Finset.range (U - L),
        (ArithmeticFunction.moebius (L + 1 + i) : ℝ) * g i| ≤
        (2 * A) * g 0 := habel
    _ ≤ (2 * A) * 1 := mul_le_mul_of_nonneg_left hg1 (by positivity)
    _ = 2 * A := by ring

lemma hc_moebius_aux_axer_aux_weight_bounds (N j n : ℕ) (hj : 1 ≤ j)
    (hlo : N / (j + 1) < n) (hhi : n ≤ N / j) :
    0 ≤ (N : ℝ) / n - j ∧ (N : ℝ) / n - j ≤ 1 := by
  have hnpos : 0 < n := (Nat.zero_le (N / (j + 1))).trans_lt hlo
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmulhiNat : n * j ≤ N := (Nat.le_div_iff_mul_le hj).mp hhi
  have hmulloNat : N < n * (j + 1) :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlo
  have hmulhi : (n : ℝ) * j ≤ N := by exact_mod_cast hmulhiNat
  have hmullo : (N : ℝ) < (n : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hmulloNat
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hnRpos).2
    simpa [mul_comm] using hmulhi
  · have hdivlt : (N : ℝ) / n < (j : ℝ) + 1 := by
      apply (div_lt_iff₀ hnRpos).2
      simpa [mul_comm] using hmullo
    linarith

lemma hc_moebius_aux_axer_aux_weight_anti (N j : ℕ) {m n : ℕ}
    (hlo : N / (j + 1) < m) (hmn : m ≤ n) (hhi : n ≤ N / j) :
    (N : ℝ) / n - j ≤ (N : ℝ) / m - j := by
  have hmpos : 0 < m := (Nat.zero_le (N / (j + 1))).trans_lt hlo
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdiv : (N : ℝ) / n ≤ (N : ℝ) / m :=
    div_le_div_of_nonneg_left (by positivity) hmRpos hmnR
  linarith

lemma hc_moebius_aux_axer_aux_divisor_identity (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  rw [← Finset.Icc_succ_left_eq_Ioc] at h
  norm_num at h
  simpa [ArithmeticFunction.one_apply, hN] using h.symm

lemma hc_moebius_aux_axer_aux_block_div_eq (N j n : ℕ) (hj : 1 ≤ j)
    (hlo : N / (j + 1) < n) (hhi : n ≤ N / j) :
    N / n = j := by
  have hnpos : 0 < n := (Nat.zero_le (N / (j + 1))).trans_lt hlo
  have hmulhi : n * j ≤ N := (Nat.le_div_iff_mul_le hj).mp hhi
  have hmullo : N < n * (j + 1) :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlo
  apply (Nat.div_eq_iff hnpos).2
  constructor
  · simpa [Nat.mul_comm] using hmulhi
  · have heq : n * (j + 1) = j * n + n := by ring
    omega

lemma hc_moebius_aux_axer_aux_frac_bounds (N n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (N : ℝ) / n - ((N / n : ℕ) : ℝ) ∧
      (N : ℝ) / n - ((N / n : ℕ) : ℝ) < 1 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 ≤ (N : ℝ) / n := div_nonneg (by positivity) hnpos.le
  have hfloor : ((N / n : ℕ) : ℝ) = ⌊(N : ℝ) / n⌋₊ := by
    rw [Nat.floor_div_eq_div]
  constructor
  · apply sub_nonneg.mpr
    rw [hfloor]
    exact Nat.floor_le hx
  · rw [hfloor]
    have := Nat.lt_floor_add_one ((N : ℝ) / n)
    linarith

lemma hc_moebius_aux_axer_aux_term_abs_le_one (N n : ℕ) (hn : 1 ≤ n) :
    |(ArithmeticFunction.moebius n : ℝ) *
      ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| ≤ 1 := by
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have hi := ArithmeticFunction.abs_moebius_le_one (n := n)
    have hiR : ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) ≤ 1 := by
      exact_mod_cast hi
    simpa only [Int.cast_abs] using hiR
  have hfrac := hc_moebius_aux_axer_aux_frac_bounds N n hn
  rw [abs_mul, abs_of_nonneg hfrac.1]
  calc
    |(ArithmeticFunction.moebius n : ℝ)| *
        ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) ≤
        1 * ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hmu hfrac.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hfrac.2.le (by norm_num)
    _ = 1 := by ring

lemma hc_moebius_aux_axer_aux_finite_estimate
    (N K N₀ : ℕ) (η : ℝ)
    (hK : 2 ≤ K) (hη : 0 ≤ η) (hN : 1 ≤ N) (hKN : K * N₀ ≤ N)
    (hM : ∀ x, N₀ ≤ x →
      |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| ≤ η * x) :
    |(Finset.Icc 1 N).sum
        (fun n => (ArithmeticFunction.moebius n : ℝ) / n)| ≤
      1 / (N : ℝ) + 1 / (K : ℝ) + 2 * (K : ℝ) * η := by
  let R : ℝ := ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℝ) *
      ((N : ℝ) / n - ((N / n : ℕ) : ℝ))
  let low : ℝ := ∑ n ∈ Finset.Icc 1 N with n ≤ N / K,
    (ArithmeticFunction.moebius n : ℝ) *
      ((N : ℝ) / n - ((N / n : ℕ) : ℝ))
  let high : ℝ := ∑ n ∈ Finset.Icc 1 N with N / K < n,
    (ArithmeticFunction.moebius n : ℝ) *
      ((N : ℝ) / n - ((N / n : ℕ) : ℝ))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hKpos : 0 < K := by omega
  have hKrealpos : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hNS :
      (N : ℝ) * (Finset.Icc 1 N).sum
        (fun n => (ArithmeticFunction.moebius n : ℝ) / n) = 1 + R := by
    dsimp only [R]
    calc
      (N : ℝ) * (Finset.Icc 1 N).sum
          (fun n => (ArithmeticFunction.moebius n : ℝ) / n) =
          ∑ n ∈ Finset.Icc 1 N,
            (N : ℝ) * ((ArithmeticFunction.moebius n : ℝ) / n) := by
        rw [Finset.mul_sum]
      _ = ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / n) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [div_eq_mul_inv]
        ring
      _ = (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) * ((N / n : ℕ) : ℝ)) +
          ∑ n ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius n : ℝ) *
              ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = 1 + ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius n : ℝ) *
            ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) := by
        rw [hc_moebius_aux_axer_aux_divisor_identity N hN]
  have hS :
      (Finset.Icc 1 N).sum (fun n => (ArithmeticFunction.moebius n : ℝ) / n) =
        1 / (N : ℝ) + R / (N : ℝ) := by
    calc
      (Finset.Icc 1 N).sum (fun n => (ArithmeticFunction.moebius n : ℝ) / n) =
          (1 + R) / (N : ℝ) := (eq_div_iff hNpos.ne').2
            (by simpa [mul_comm] using hNS)
      _ = 1 / (N : ℝ) + R / (N : ℝ) := by ring
  have hsplit : R = low + high := by
    dsimp only [R, low, high]
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
      (fun n => n ≤ N / K)
      (fun n => (ArithmeticFunction.moebius n : ℝ) *
        ((N : ℝ) / n - ((N / n : ℕ) : ℝ)))
    simpa only [not_le] using hs.symm
  have hlowcard :
      Finset.card ((Finset.Icc 1 N).filter (fun n => n ≤ N / K)) ≤ N / K := by
    calc
      Finset.card ((Finset.Icc 1 N).filter (fun n => n ≤ N / K)) ≤
          Finset.card (Finset.Icc 1 (N / K)) := by
        apply Finset.card_le_card
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hbase := Finset.mem_Icc.mp hn'.1
        exact Finset.mem_Icc.mpr ⟨hbase.1, hn'.2⟩
      _ = N / K := by simp
  have hlow : |low| ≤ ((N / K : ℕ) : ℝ) := by
    dsimp only [low]
    calc
      |∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ N / K),
          (ArithmeticFunction.moebius n : ℝ) *
            ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| ≤
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ N / K),
            |(ArithmeticFunction.moebius n : ℝ) *
              ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ N / K), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hc_moebius_aux_axer_aux_term_abs_le_one N n (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      _ = (Finset.card ((Finset.Icc 1 N).filter (fun n => n ≤ N / K)) : ℝ) := by simp
      _ ≤ ((N / K : ℕ) : ℝ) := by exact_mod_cast hlowcard
  have hinner : ∀ j ∈ Finset.Icc 1 (K - 1),
      |∑ n ∈ Finset.Icc 1 N with N / n = j,
        (ArithmeticFunction.moebius n : ℝ) *
          ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| ≤ 2 * η * (N : ℝ) := by
    intro j hjmem
    have hj : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
    rw [hc_moebius_aux_axer_aux_block_fiber_eq N j hj]
    let L := N / (j + 1)
    let U := N / j
    have heq :
        (∑ n ∈ Finset.Ioc L U,
          (ArithmeticFunction.moebius n : ℝ) *
            ((N : ℝ) / n - ((N / n : ℕ) : ℝ))) =
        ∑ n ∈ Finset.Ioc L U,
          (ArithmeticFunction.moebius n : ℝ) * ((N : ℝ) / n - j) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      rw [hc_moebius_aux_axer_aux_block_div_eq N j n hj hn'.1 hn'.2]
    rw [heq]
    by_cases hLU : L < U
    · have hjhi : j ≤ K - 1 := (Finset.mem_Icc.mp hjmem).2
      have hden : j + 1 ≤ K := by omega
      have hdivK : N / K ≤ N / (j + 1) := by
        apply (Nat.le_div_iff_mul_le (Nat.succ_pos j)).2
        have hmul := Nat.mul_le_mul_right (N / K) hden
        have hbase := Nat.mul_div_le N K
        have hmul' : (N / K) * (j + 1) ≤ (N / K) * K := by
          simpa [Nat.mul_comm] using hmul
        exact hmul'.trans (by simpa [Nat.mul_comm] using hbase)
      have hN₀div : N₀ ≤ N / K := by
        apply (Nat.le_div_iff_mul_le hKpos).2
        simpa [Nat.mul_comm] using hKN
      have hblockM : ∀ x, L ≤ x → x ≤ U →
          |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| ≤
            η * (N : ℝ) := by
        intro x hxL hxU
        have hxN₀ : N₀ ≤ x := hN₀div.trans (hdivK.trans (by simpa [L] using hxL))
        have hxN : x ≤ N := by
          exact hxU.trans (by simpa [U] using Nat.div_le_self N j)
        calc
          |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| ≤
              η * (x : ℝ) := hM x hxN₀
          _ ≤ η * (N : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxN) hη
      have hw := hc_moebius_aux_axer_aux_weight_bounds N j (L + 1) hj (by omega) (by omega)
      have hbound := hc_moebius_aux_axer_aux_abel_block L U (fun n => (N : ℝ) / n - j) (η * (N : ℝ))
        hLU hblockM hw.1
        (fun x hx hxU => (hc_moebius_aux_axer_aux_weight_bounds N j x hj (by simpa [L] using hx)
          (by simpa [U] using hxU)).1)
        hw.2
        (fun x y hx hxy hy => hc_moebius_aux_axer_aux_weight_anti N j (by simpa [L] using hx) hxy
          (by simpa [U] using hy))
      simpa [mul_assoc] using hbound
    · have hUL : U ≤ L := Nat.le_of_not_gt hLU
      rw [Finset.Ioc_eq_empty_of_le hUL, Finset.sum_empty, abs_zero]
      positivity
  have hhigh : |high| ≤ 2 * (K : ℝ) * η * (N : ℝ) := by
    dsimp only [high]
    rw [hc_moebius_aux_axer_aux_high_sum_eq_fibers N K hK]
    calc
      |∑ j ∈ Finset.Icc 1 (K - 1),
          ∑ n ∈ Finset.Icc 1 N with N / n = j,
            (ArithmeticFunction.moebius n : ℝ) *
              ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| ≤
          ∑ j ∈ Finset.Icc 1 (K - 1),
            |∑ n ∈ Finset.Icc 1 N with N / n = j,
              (ArithmeticFunction.moebius n : ℝ) *
                ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 (K - 1), 2 * η * (N : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hinner j hj
      _ = ((K - 1 : ℕ) : ℝ) * (2 * η * (N : ℝ)) := by simp
      _ ≤ (K : ℝ) * (2 * η * (N : ℝ)) := by
        gcongr
        exact_mod_cast (by omega : K - 1 ≤ K)
      _ = 2 * (K : ℝ) * η * (N : ℝ) := by ring
  have hR : |R| ≤ ((N / K : ℕ) : ℝ) + 2 * (K : ℝ) * η * (N : ℝ) := by
    rw [hsplit]
    calc
      |low + high| ≤ |low| + |high| := abs_add_le _ _
      _ ≤ ((N / K : ℕ) : ℝ) + 2 * (K : ℝ) * η * (N : ℝ) := add_le_add hlow hhigh
  have hfloorNat : (N / K) * K ≤ N := by
    simpa [Nat.mul_comm] using Nat.mul_div_le N K
  have hfloorReal : ((N / K : ℕ) : ℝ) * (K : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hfloorNat
  have hlowNorm :
      ((N / K : ℕ) : ℝ) / (N : ℝ) ≤ 1 / (K : ℝ) := by
    apply (div_le_div_iff₀ hNpos hKrealpos).2
    simpa using hfloorReal
  rw [hS]
  calc
    |1 / (N : ℝ) + R / (N : ℝ)| ≤
        |1 / (N : ℝ)| + |R / (N : ℝ)| := abs_add_le _ _
    _ = 1 / (N : ℝ) + |R| / (N : ℝ) := by
      rw [abs_of_nonneg (by positivity), abs_div, abs_of_nonneg hNpos.le]
    _ ≤ 1 / (N : ℝ) +
        (((N / K : ℕ) : ℝ) + 2 * (K : ℝ) * η * (N : ℝ)) / (N : ℝ) := by
      gcongr
    _ = 1 / (N : ℝ) + ((N / K : ℕ) : ℝ) / (N : ℝ) +
        2 * (K : ℝ) * η := by
      field_simp [hNpos.ne']
      <;> ring
    _ ≤ 1 / (N : ℝ) + 1 / (K : ℝ) + 2 * (K : ℝ) * η := by
      gcongr

lemma hc_moebius_aux_axer_aux_mertens_eventual_bound
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)) / N)
      atTop (nhds 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ x, N₀ ≤ x →
      |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| ≤ η * x := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h η hη)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro x hx
  have hxN : N ≤ x := (le_max_left N 1).trans hx
  have hx1 : 1 ≤ x := (le_max_right N 1).trans hx
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hdist := hN x hxN
  have hdiv : |∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ)| /
      (x : ℝ) < η := by
    simpa [Real.dist_eq] using hdist
  exact ((div_lt_iff₀ hxpos).mp hdiv).le

theorem hc_moebius_aux_axer
    (h : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ)) / N)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (ArithmeticFunction.moebius n : ℝ)/n))
      atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro δ hδ
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (3 / δ)
  let K := K₀ + 2
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hKpos : 0 < K := by omega
  have hKrealpos : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hKgt : 3 / δ < (K : ℝ) := by
    exact hK₀.trans (by dsimp [K]; norm_num)
  have hthree : 3 < δ * (K : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hKgt
  have hKrecip : 1 / (K : ℝ) < δ / 3 := by
    apply (div_lt_iff₀ hKrealpos).2
    nlinarith
  let η : ℝ := δ / (12 * (K : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N₀, hN₀, hM⟩ := hc_moebius_aux_axer_aux_mertens_eventual_bound h hη
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (6 / δ)
  let B := max (K * N₀) N₁
  refine ⟨B, ?_⟩
  intro N hN
  have hKN : K * N₀ ≤ N := (le_max_left (K * N₀) N₁).trans hN
  have hNN₁ : N₁ ≤ N := (le_max_right (K * N₀) N₁).trans hN
  have hN1 : 1 ≤ N := by
    have : 1 ≤ K * N₀ := Nat.le_trans hN₀ (Nat.le_mul_of_pos_left N₀ hKpos)
    exact this.trans hKN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN₁N : (N₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNN₁
  have hNgt : 6 / δ < (N : ℝ) := hN₁.trans_le hN₁N
  have hsix : 6 < δ * (N : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hNgt
  have hNrecip : 1 / (N : ℝ) < δ / 6 := by
    apply (div_lt_iff₀ hNpos).2
    nlinarith
  have hconst : 2 * (K : ℝ) * η = δ / 6 := by
    dsimp [η]
    field_simp [hKrealpos.ne']
    <;> ring
  have hest := hc_moebius_aux_axer_aux_finite_estimate N K N₀ η hK hη.le hN1 hKN hM
  rw [Real.dist_eq, sub_zero]
  exact hest.trans_lt (by rw [hconst]; nlinarith)

namespace MmPsiBoundRef

namespace GoldbachSmoothing

open Complex MeasureTheory Set

noncomputable section

def triangle (x t : ℝ) : ℂ := (max (x - t) 0 : ℝ)

def cutoff (x h t : ℝ) : ℂ := (triangle (x + h) t - triangle x t) / (h : ℂ)

def kernel (x h : ℝ) (s : ℂ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) / ((h : ℂ) * s * (s + 1))

private theorem shift_nonzero {s : ℂ} (hs : 0 < s.re) : s + 1 ≠ 0 := by
  intro he
  have hz := congrArg Complex.re he
  simp only [add_re, one_re, zero_re] at hz
  linarith

private theorem triangle_one_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin (triangle 1) s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp only [one_re]; linarith)
  have hdiff := hasMellin_sub h1.1 h2.1
  have heq : EqOn (triangle 1)
      (fun t => (Set.Ioc 0 1).indicator (fun _ : ℝ => 1 : ℝ → ℂ) t -
        (Set.Ioc 0 1).indicator (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) t) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      simp [triangle, hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [triangle, hm, max_eq_right (sub_nonpos.mpr (le_of_not_ge ht1))]
  have heqMul : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • triangle 1 t) _ (Ioi 0) :=
    fun t ht => congrArg (fun w : ℂ => (t : ℂ) ^ (s - 1) • w) (heq ht)
  refine ⟨(integrableOn_congr_fun heqMul measurableSet_Ioi).2 hdiff.1, ?_⟩
  have h0 : s ≠ 0 := fun hz => by simp [hz] at hs
  calc
    mellin (triangle 1) s = _ := setIntegral_congr_fun measurableSet_Ioi heqMul
    _ = _ := hdiff.2
    _ = _ := by
      rw [h1.2, h2.2]
      field_simp [h0, shift_nonzero hs]
      ring

theorem triangle_hasMellin {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (triangle x) s ((x : ℂ) ^ (s + 1) / (s * (s + 1))) := by
  have h1 := triangle_one_hasMellin hs
  have hxInv : 0 < x⁻¹ := inv_pos.mpr hx
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : triangle x = fun t => (x : ℂ) • triangle 1 (x⁻¹ * t) := by
    funext t
    have hxmul : x * (1 - x⁻¹ * t) = x - t := by field_simp [hx.ne']
    simp only [triangle, smul_eq_mul, ← ofReal_mul, mul_max_of_nonneg _ _ hx.le,
      mul_zero, hxmul]
  have hscaled := (MellinConvergent.comp_mul_left hxInv).mpr h1.1
  have hsmul := hasMellin_const_smul hscaled (x : ℂ)
  refine ⟨hscale ▸ hsmul.1, ?_⟩
  rw [hscale, hsmul.2, mellin_comp_mul_left _ _ hxInv, h1.2, ofReal_inv,
    inv_cpow_ofReal_nonneg hx.le, cpow_neg, inv_inv, cpow_add _ _ hxC, cpow_one]
  simp only [smul_eq_mul]
  ring

theorem cutoff_hasMellin {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (cutoff x h) s (kernel x h s) := by
  have hLeft := triangle_hasMellin hx hs
  have hRight := triangle_hasMellin (add_pos hx hh) hs
  have hsub := hasMellin_sub hRight.1 hLeft.1
  refine ⟨hsub.1.div_const _, ?_⟩
  change mellin (fun t => (triangle (x + h) t - triangle x t) / (h : ℂ)) s = _
  rw [mellin_div_const, hsub.2, hRight.2, hLeft.2, ← sub_div, div_div, kernel]
  congr 1
  ring

theorem kernel_eq_interval {x h : ℝ} {s : ℂ} (hs : 0 < s.re) :
    kernel x h s = (∫ y in x..x+h, (y : ℂ) ^ s) / ((h : ℂ) * s) := by
  rw [integral_cpow (Or.inl (show -1 < s.re by linarith)), div_div, kernel]
  congr 1
  ring

theorem norm_kernel_le {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ‖kernel x h s‖ ≤ (x + h) ^ s.re / ‖s‖ := by
  have h0 : s ≠ 0 := fun hz => by simp [hz] at hs
  have hb : ∀ y ∈ uIoc x (x + h), ‖(y : ℂ) ^ s‖ ≤ (x + h) ^ s.re := by
    intro y hy
    rw [uIoc_of_le (le_add_of_nonneg_right hh.le)] at hy
    have hy0 := hx.trans hy.1
    rw [norm_cpow_eq_rpow_re_of_pos hy0]
    exact Real.rpow_le_rpow hy0.le hy.2 hs.le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show x + h - x = h by ring, abs_of_pos hh] at hi
  rw [kernel_eq_interval hs, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ (x + h) ^ s.re * h / (h * ‖s‖) :=
      div_le_div_of_nonneg_right hi (mul_nonneg hh.le (norm_nonneg s))
    _ = _ := by field_simp [hh.ne', norm_ne_zero_iff.mpr h0]

theorem norm_kernel_le_tail {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} :
    ‖kernel x h s‖ ≤
      ((x + h) ^ (s.re + 1) + x ^ (s.re + 1)) / (h * ‖s‖ * ‖s + 1‖) := by
  rw [kernel, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (norm_sub_le _ _).trans_eq ?_
  rw [norm_cpow_eq_rpow_re_of_pos (add_pos hx hh), norm_cpow_eq_rpow_re_of_pos hx,
    Complex.add_re, Complex.one_re]

theorem cutoff_continuous (x h : ℝ) : Continuous (cutoff x h) := by
  unfold cutoff triangle
  fun_prop

theorem kernel_verticalIntegrable {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ) :
    VerticalIntegrable (kernel x h) σ := by
  let A := (x + h) ^ (σ + 1) + x ^ (σ + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h₀ (t : ℝ) : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    exact hσ.ne' this
  have h₁ (t : ℝ) : ((σ : ℂ) + (t : ℂ) * I) + 1 ≠ 0 := by
    apply shift_nonzero
    simpa using hσ
  have hcontinuous : Continuous (fun t : ℝ => kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
    let line (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hline : Continuous line := continuous_const.add (continuous_ofReal.mul continuous_const)
    have hshift : Continuous (fun t => line t + 1) := hline.add continuous_const
    have hp (b : ℝ) (hb : 0 < b) : Continuous (fun t => (b : ℂ) ^ (line t + 1)) := by
      simp_rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hb.ne')]
      exact continuous_exp.comp (continuous_const.mul hshift)
    change Continuous fun t => kernel x h (line t)
    unfold kernel
    refine ((hp (x + h) (add_pos hx hh)).sub (hp x hx)).div
      ((continuous_const.mul hline).mul hshift) fun t => ?_
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hh.ne') (h₀ t)) (h₁ t)
  have hb := (integrable_inv_one_add_mul_sq (inv_ne_zero hσ.ne')).const_mul (A / (h * σ ^ 2))
  apply hb.mono' hcontinuous.aestronglyMeasurable
  filter_upwards with t
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hzRe : z.re = σ := by simp [z]
  have hzIm : z.im = t := by simp [z]
  have hzSquare : ‖z‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, hzRe, hzIm]
    ring
  have hzNextSquare : ‖z + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero, hzRe, hzIm]
    ring
  have hn : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hzSquare, hzNextSquare]
    nlinarith
  have hden : h * σ ^ 2 * (1 + (σ⁻¹ * t) ^ 2) ≤ h * ‖z‖ * ‖z + 1‖ := by
    calc
      _ = h * (σ ^ 2 + t ^ 2) := by field_simp [hσ.ne']
      _ = h * (‖z‖ * ‖z‖) := by rw [← hzSquare, pow_two]
      _ ≤ h * (‖z‖ * ‖z + 1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) hh.le
      _ = _ := by ring
  calc
    _ ≤ A / (h * ‖z‖ * ‖z + 1‖) := by simpa [hzRe, A] using norm_kernel_le_tail hx hh (s := z)
    _ ≤ A / (h * σ ^ 2 * (1 + (σ⁻¹ * t) ^ 2)) :=
      div_le_div_of_nonneg_left hA (by positivity) hden
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem mellinInv_kernel_eq {x h σ y : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ)
    (hy : 0 < y) : mellinInv σ (kernel x h) y = cutoff x h y := by
  have hline (t : ℝ) : mellin (cutoff x h) ((σ : ℂ) + (t : ℂ) * I) =
      kernel x h ((σ : ℂ) + (t : ℂ) * I) :=
    (cutoff_hasMellin hx hh (by simpa using hσ)).2
  have hvert : VerticalIntegrable (mellin (cutoff x h)) σ := by
    unfold VerticalIntegrable
    simp only [hline]
    exact kernel_verticalIntegrable hx hh hσ
  have hm := (cutoff_hasMellin hx hh (s := (σ : ℂ)) (by simpa using hσ)).1
  have hi := mellinInv_mellin_eq σ (cutoff x h) hy hm hvert (cutoff_continuous x h).continuousAt
  simpa only [mellinInv, hline] using hi

theorem cutoff_eq_one {x h t : ℝ} (hh : 0 < h) (ht : t ≤ x) : cutoff x h t = 1 := by
  unfold cutoff triangle
  rw [max_eq_left (by linarith : 0 ≤ x + h - t), max_eq_left (sub_nonneg.mpr ht),
    ← ofReal_sub, show x + h - t - (x - t) = h by ring,
    div_self (ofReal_ne_zero.mpr hh.ne')]

theorem cutoff_eq_zero {x h t : ℝ} (hh : 0 ≤ h) (ht : x + h ≤ t) : cutoff x h t = 0 := by
  unfold cutoff triangle
  rw [max_eq_right (sub_nonpos.mpr ht), max_eq_right (by linarith : x - t ≤ 0)]
  simp

theorem norm_cutoff_le_one (x : ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) : ‖cutoff x h t‖ ≤ 1 := by
  by_cases ht : t ≤ x
  · simp [cutoff_eq_one hh ht]
  by_cases hu : x + h ≤ t
  · simp [cutoff_eq_zero hh.le hu]
  unfold cutoff triangle
  have hp : 0 ≤ x + h - t := by linarith [le_of_not_ge hu]
  rw [max_eq_left hp, max_eq_right (sub_nonpos.mpr (le_of_not_ge ht)), ofReal_zero,
    sub_zero, ← ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one hh).mpr (by linarith [le_of_not_ge ht])

theorem kernel_at_one {x h : ℝ} (hh : 0 < h) : kernel x h 1 = (x + h / 2 : ℝ) := by
  have hhC : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  rw [kernel, show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, cpow_natCast]
  push_cast
  field_simp [hhC]
  ring

theorem kernel_analytic {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    AnalyticOnNhd ℂ (kernel x h) {s | 0 < s.re} := by
  intro s hs
  have hsR : 0 < s.re := hs
  have hs0 : s ≠ 0 := fun hz => by simp [hz] at hsR
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
  have hp (a : ℝ) (ha : 0 < a) : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) ^ (z + 1)) s := by
    simp_rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne')]
    exact (analyticAt_const.mul hshift).cexp'
  exact ((hp (x + h) (add_pos hx hh)).sub (hp x hx)).div
    ((analyticAt_const.mul analyticAt_id).mul hshift)
    (mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hh.ne') hs0) (shift_nonzero hsR))

end

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex
open scoped BigOperators

theorem norm_cutoff_sub_sharp (a : ℕ → ℂ) (X : ℕ) {h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (ha : ∀ n : ℕ, (n : ℝ) ≤ (X : ℝ) + h → ‖a n‖ ≤ M) :
    ‖(∑' n, a n * cutoff (X : ℝ) h n) - ∑ n ∈ Finset.range (X + 1), a n‖ ≤ h * M := by
  let B := ⌊(X : ℝ) + h⌋₊
  have hXB : X ≤ B := Nat.le_floor (le_add_of_nonneg_right hh.le)
  have hB : (B : ℝ) ≤ (X : ℝ) + h := Nat.floor_le (by positivity)
  have hfinite : (∑' n, a n * cutoff (X : ℝ) h n) =
      ∑ n ∈ Finset.range (B + 1), a n * cutoff (X : ℝ) h n := by
    apply tsum_eq_sum
    intro n hn
    have hnB : B + 1 ≤ n := by
      rw [Finset.mem_range] at hn
      omega
    have hnBR : (B : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnB
    have htop : (X : ℝ) + h < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [cutoff_eq_zero hh.le (htop.le.trans hnBR), mul_zero]
  have hbelow : (∑ n ∈ Finset.range (X + 1), a n * cutoff (X : ℝ) h n) =
      ∑ n ∈ Finset.range (X + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [cutoff_eq_one hh (by exact_mod_cast hnX), mul_one]
  have hcount : ((Finset.Ico (X + 1) (B + 1)).card : ℝ) ≤ h := by
    rw [Nat.card_Ico, Nat.add_sub_add_right, Nat.cast_sub hXB]
    linarith
  rw [hfinite, ← Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hXB 1),
    hbelow, add_sub_cancel_left]
  calc
    _ ≤ ∑ n ∈ Finset.Ico (X + 1) (B + 1), ‖a n * cutoff (X : ℝ) h n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (X + 1) (B + 1), M := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hnB : n ≤ B := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hn).2
      have hnBR : (n : ℝ) ≤ (B : ℝ) := by exact_mod_cast hnB
      rw [norm_mul]
      calc
        _ ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left (norm_cutoff_le_one X hh n) (norm_nonneg _)
        _ ≤ M := by simpa only [mul_one] using ha n (hnBR.trans hB)
    _ = ((Finset.Ico (X + 1) (B + 1)).card : ℝ) * M := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hM

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable section

private theorem term_norm_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term a (σ : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [LSeries.term_of_ne_zero hn, norm_div,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), add_re, ofReal_re, mul_I_re, ofReal_im,
      neg_zero, add_zero]

private theorem term_continuous_vertical (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    simp_rw [LSeries.term_of_ne_zero hn, cpow_def_of_ne_zero hnC]
    exact continuous_const.div (continuous_exp.comp (continuous_const.mul hline))
      (fun _ => exp_ne_zero _)

theorem integrable_LSeries_mul_kernel (a : ℕ → ℂ) {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hσ : 0 < σ) (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    Integrable (fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℂ) * I) *
      kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hK : Integrable (fun t : ℝ => kernel x h (z t)) := kernel_verticalIntegrable hx hh hσ
  have hc : Continuous (fun t : ℝ => LSeries a (z t)) := by
    exact continuous_tsum (term_continuous_vertical a σ) hAbs
      (fun n t => le_of_eq (term_norm_vertical a σ t n))
  refine (hK.norm.const_mul (∑' n, ‖LSeries.term a (σ : ℂ) n‖)).mono'
    (hc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hS : Summable (fun n => ‖LSeries.term a (z t) n‖) :=
    hAbs.congr (fun n => (term_norm_vertical a σ t n).symm)
  exact (norm_tsum_le_tsum_norm hS).trans_eq (tsum_congr (term_norm_vertical a σ t))

theorem cutoff_tsum_eq_vertical (a : ℕ → ℂ) (ha0 : a 0 = 0)
    {x h σ : ℝ} (hx : 0 < x) (hh : 0 < h) (hσ : 0 < σ)
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    (∑' n, a n * cutoff x h n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * kernel x h ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let F (n : ℕ) (t : ℝ) : ℂ := LSeries.term a (z t) n * kernel x h (z t)
  have hK : Integrable (fun t : ℝ => kernel x h (z t)) := kernel_verticalIntegrable hx hh hσ
  have hN (n : ℕ) (t : ℝ) : ‖F n t‖ =
      ‖LSeries.term a (σ : ℂ) n‖ * ‖kernel x h (z t)‖ := by
    dsimp only [F]
    rw [norm_mul, term_norm_vertical]
  have hF (n : ℕ) : Integrable (F n) := by
    refine (hK.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' ?_ ?_
    · exact (term_continuous_vertical a σ n).aestronglyMeasurable.mul hK.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hN n t)
  have hFsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hN, integral_const_mul]
    exact hAbs.mul_right _
  have hInv (n : ℕ) : a n * cutoff x h n =
      (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := by
    by_cases hn : n = 0
    · subst n
      simp [F, ha0]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← mellinInv_kernel_eq hx hh hσ hnR]
    unfold mellinInv
    simp only [F, z, LSeries.term_def₀ ha0, ofReal_natCast, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp only [Algebra.smul_def]
    ring
  calc
    _ = ∑' n, (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := tsum_congr hInv
    _ = (1 / (2 * Real.pi)) • (∑' n, ∫ t : ℝ, F n t) := tsum_const_smul'' _
    _ = (1 / (2 * Real.pi)) • (∫ t : ℝ, ∑' n, F n t) :=
      congrArg ((1 / (2 * Real.pi)) • ·) (integral_tsum_of_summable_integral_norm hF hFsum)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, z, LSeries, tsum_mul_right]

end

end GoldbachSmoothing

namespace GoldbachSmoothing

open Complex DirichletCharacter MeasureTheory
open scoped BigOperators

noncomputable section

def twistedCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))

theorem twistedCoefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedCoefficient χ 0 = 0 := by
  simp [twistedCoefficient]

theorem LSeries_twistedCoefficient_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedCoefficient χ) s = -logDeriv (LFunction χ) s := by
  rw [twistedCoefficient, χ.LSeries_twist_vonMangoldt_eq hs,
    ← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs]
  simp only [logDeriv, Pi.div_apply, neg_div]

theorem smoothed_twist_eq_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    (∑' n, twistedCoefficient χ n * cutoff x h n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        (-logDeriv (LFunction χ) (2 + (t : ℂ) * I)) * kernel x h (2 + (t : ℂ) * I)) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2 : ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2 + (t : ℂ) * I) =
      -logDeriv (LFunction χ) (2 + (t : ℂ) * I) :=
    LSeries_twistedCoefficient_eq χ (by norm_num)
  simpa only [ofReal_ofNat, hEq] using
    cutoff_tsum_eq_vertical (twistedCoefficient χ) (twistedCoefficient_zero χ) hx hh
      (σ := 2) (by norm_num) hAbs

theorem integrable_twist_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    Integrable (fun t : ℝ =>
      (-logDeriv (LFunction χ) (2 + (t : ℂ) * I)) * kernel x h (2 + (t : ℂ) * I)) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2 : ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2 + (t : ℂ) * I) =
      -logDeriv (LFunction χ) (2 + (t : ℂ) * I) :=
    LSeries_twistedCoefficient_eq χ (by norm_num)
  simpa only [ofReal_ofNat, hEq] using
    integrable_LSeries_mul_kernel (twistedCoefficient χ) hx hh (σ := 2) (by norm_num) hAbs

theorem norm_twisted_smoothing_error {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ)
    (hX : 2 ≤ X) :
    ‖(∑' n, twistedCoefficient χ n * cutoff (X : ℝ) (Real.sqrt X) n) -
        ∑ n ∈ Finset.range (X + 1), twistedCoefficient χ n‖ ≤
      Real.sqrt (X : ℝ) * Real.log (2 * (X : ℝ)) := by
  have hXR : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hsqrt : Real.sqrt (X : ℝ) ≤ (X : ℝ) := by
    calc
      _ ≤ Real.sqrt ((X : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq (by positivity)
  apply norm_cutoff_sub_sharp _ _ (by positivity) (Real.log_nonneg (by linarith))
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [twistedCoefficient_zero, norm_zero]
    exact Real.log_nonneg (by linarith)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  change ‖χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ 1 * ArithmeticFunction.vonMangoldt n :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ Real.log (n : ℝ) := by simpa only [one_mul] using ArithmeticFunction.vonMangoldt_le_log
    _ ≤ _ := Real.log_le_log hnR (by linarith)

end

end GoldbachSmoothing

open scoped BigOperators
open ArithmeticFunction

namespace GoldbachProgression

noncomputable def twistedVonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (X + 1), χ (k : ZMod q) * (vonMangoldt k : ℂ)

open scoped Classical in

noncomputable def principalMainTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  if χ = 1 then (X : ℂ) else 0

theorem progressionBound_of_twistedBound
    (hTwisted : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ ≤
          C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → q = 1 → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  classical
  obtain ⟨C, hC, hEstimate⟩ := hTwisted
  refine ⟨C, hC, ?_⟩
  intro q a X hq hq1 ha hX
  have : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have haUnit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have haInv : IsUnit ((a : ZMod q)⁻¹) :=
    isUnit_of_dvd_one ⟨(a : ZMod q), (ZMod.inv_mul_of_unit _ haUnit).symm⟩
  have hTotient : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hCount : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  let weight (χ : DirichletCharacter ℂ q) : ℂ := χ ((a : ZMod q)⁻¹)
  let apSum : ℝ := ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k % q = a % q), vonMangoldt k
  let bound : ℝ := C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2

  have hResidueSum : apSum =
      ∑ k ∈ Finset.range (X + 1), vonMangoldt.residueClass (a : ZMod q) k := by
    simp only [apSum, Finset.sum_filter, vonMangoldt.residueClass, Set.indicator_apply,
      Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  have hProjection : (apSum : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, weight χ * twistedVonMangoldt χ X := by
    calc
      (apSum : ℂ) =
          ∑ k ∈ Finset.range (X + 1), (vonMangoldt.residueClass (a : ZMod q) k : ℂ) := by
        change Complex.ofRealHom apSum = _
        rw [hResidueSum, map_sum]
        simp only [Complex.ofRealHom_eq_coe]
      _ = ∑ k ∈ Finset.range (X + 1), (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, weight χ * (χ (k : ZMod q) * (vonMangoldt k : ℂ)) := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [weight, mul_assoc] using vonMangoldt.residueClass_apply haUnit k
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [twistedVonMangoldt, Finset.mul_sum]
  have hMain : (∑ χ : DirichletCharacter ℂ q, weight χ * principalMainTerm χ X) = (X : ℂ) := by
    rw [Finset.sum_eq_single_of_mem (1 : DirichletCharacter ℂ q) (Finset.mem_univ _)]
    · simp [weight, principalMainTerm, MulChar.one_apply haInv]
    · intro χ _ hχ
      simp [principalMainTerm, hχ]

  have hDiscrepancy : ((apSum - (X : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div]
    simp only [Complex.ofReal_natCast, hProjection, mul_sub, Finset.sum_sub_distrib, hMain,
      div_eq_inv_mul]
  have hBound : ‖(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X)‖ ≤ bound := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul, div_le_iff₀ hTotient]
    calc
      ‖∑ χ : DirichletCharacter ℂ q, weight χ *
          (twistedVonMangoldt χ X - principalMainTerm χ X)‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ‖weight χ * (twistedVonMangoldt χ X - principalMainTerm χ X)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : DirichletCharacter ℂ q, bound := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        calc
          ‖weight χ‖ * ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ ≤
              1 * ‖twistedVonMangoldt χ X - principalMainTerm χ X‖ :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ ≤ bound := by simpa only [one_mul, bound] using hEstimate q hq1 χ X hX
      _ = bound * (q.totient : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, hCount, nsmul_eq_mul, mul_comm]
  change |apSum - (X : ℝ) / (q.totient : ℝ)| ≤ bound
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hDiscrepancy]
  exact hBound

end GoldbachProgression

open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace GoldbachGrhGrowth

variable {q : ℕ} [NeZero q]

def charMean (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, χ a

open scoped Classical in
theorem charMean_eq (χ : DirichletCharacter ℂ q) :
    charMean χ = if χ = 1 then (q.totient : ℂ) / (q : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [charMean, MulChar.sum_one_eq_card_units,
      ZMod.card_units_eq_totient, div_eq_inv_mul]
  · simp only [charMean, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem level_mul_charMean (χ : DirichletCharacter ℂ q) :
    (q : ℂ) * charMean χ = ∑ a : ZMod q, χ a := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [charMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem norm_charMean_le_one (χ : DirichletCharacter ℂ q) : ‖charMean χ‖ ≤ 1 := by
  classical
  by_cases hχ : χ = 1
  · simp only [charMean_eq, ite_eq_left hχ, norm_div, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast q.pos_of_neZero)).2
    exact_mod_cast q.totient_le
  · simp [charMean_eq, hχ]

def charPartialSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)

omit [NeZero q] in
theorem norm_charPartialSum_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖charPartialSum χ n‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range n, ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = n := by simp

private theorem sum_character_block (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun k => (k.val : ZMod q)
      invFun := fun a => ⟨a.val, a.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt])
      right_inv := ZMod.natCast_zmod_val }
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => χ ((m + k : ℕ) : ZMod q)) q]
  refine Fintype.sum_equiv (e.trans (Equiv.addRight (m : ZMod q))) _ _ fun k => ?_
  change χ ((m + k.val : ℕ) : ZMod q) = χ ((k.val : ZMod q) + (m : ZMod q))
  rw [Nat.cast_add, add_comm]

def integerRemainder (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  charPartialSum χ n - (n : ℂ) * charMean χ

theorem integerRemainder_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (integerRemainder χ) q := by
  intro n
  have hBlock : (∑ k ∈ range q, χ ((n + k + 1 : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using sum_character_block χ (n + 1)
  simp only [integerRemainder, charPartialSum, Finset.sum_range_add]
  rw [hBlock]
  simp only [Nat.cast_add, add_mul, level_mul_charMean]
  abel

theorem norm_integerRemainder_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖integerRemainder χ n‖ ≤ 2 * (q : ℝ) := by
  rw [← (integerRemainder_periodic χ).map_mod_nat n]
  let r := n % q
  have hr : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n q.pos_of_neZero).le
  calc
    _ ≤ ‖charPartialSum χ r‖ + ‖(r : ℂ) * charMean χ‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := by
      refine add_le_add (norm_charPartialSum_le χ r) ?_
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_charMean_le_one χ) r.cast_nonneg
    _ ≤ _ := by linarith

def periodicRemainder (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ

theorem norm_periodicRemainder_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖periodicRemainder χ x‖ ≤ 3 * (q : ℝ) := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
    have hd : ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx0))]
      linarith [Nat.lt_floor_add_one x]
    have hsplit : charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ =
        integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ := by
      unfold integerRemainder
      ring
    rw [periodicRemainder, indicator_of_mem hx, hsplit]
    calc
      _ ≤ ‖integerRemainder χ ⌊x⌋₊‖ + ‖((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ‖ :=
        norm_add_le _ _
      _ ≤ 2 * (q : ℝ) + 1 := by
        refine add_le_add (norm_integerRemainder_le χ _) ?_
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hd (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
        linarith
  · rw [periodicRemainder, indicator_of_notMem hx, norm_zero]
    positivity

omit [NeZero q] in
private theorem measurable_partialSum_floor (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊) :=
  (measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor

private theorem measurable_centeredCharSum (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) :=
  (measurable_partialSum_floor χ).sub (continuous_ofReal.measurable.mul_const _)

theorem measurable_periodicRemainder (χ : DirichletCharacter ℂ q) :
    Measurable (periodicRemainder χ) :=
  (measurable_centeredCharSum χ).indicator measurableSet_Ioi

def remainderMellin (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  mellin (periodicRemainder χ) (-s)

theorem remainderMellin_eq_integral (χ : DirichletCharacter ℂ q) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) := by
  have hIntegrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • periodicRemainder χ x) =
      (Ioi (1 : ℝ)).indicator (fun x => (x : ℂ) ^ (-s - 1) *
        (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) := by
    ext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [periodicRemainder, indicator_of_mem hx, smul_eq_mul]
    · simp only [periodicRemainder, indicator_of_notMem hx, smul_zero]
  rw [remainderMellin, mellin, hIntegrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)]

private theorem norm_weightedRemainder_le (χ : DirichletCharacter ℂ q) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)‖ ≤
      (3 * (q : ℝ)) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hBound := norm_periodicRemainder_le χ x
  rw [periodicRemainder, indicator_of_mem hx] at hBound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg hx0.le _)).trans_eq (mul_comm _ _)

private theorem weightedRemainder_integrableOn (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) := by
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine Integrable.mono' hBound ?_ ?_
  · have hKernel : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      intro x hx
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt
    exact (hKernel.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_centeredCharSum χ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx

theorem norm_remainderMellin_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    ‖remainderMellin χ s‖ ≤ (3 * (q : ℝ)) / s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine (norm_integral_le_of_norm_le hBound ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
    rw [show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
    simp only [div_neg, neg_div, neg_neg, mul_one_div]

theorem differentiableAt_remainderMellin (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (remainderMellin χ) s := by
  have hLoc : LocallyIntegrableOn (periodicRemainder χ) (Ioi (0 : ℝ)) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_periodicRemainder χ).aestronglyMeasurable
      (Eventually.of_forall (norm_periodicRemainder_le χ))
  have hTop : periodicRemainder χ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (3 * (q : ℝ)) (Eventually.of_forall fun x => ?_)
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_periodicRemainder_le χ x
  have hBot : periodicRemainder χ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    have hNear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hNear] with x hx
    have hOutside : x ∉ Ioi (1 : ℝ) := fun h => (mem_Iio.mp hx).not_gt (mem_Ioi.mp h)
    simp only [periodicRemainder, indicator_of_notMem hOutside, norm_zero, zero_mul, le_refl]
  have hNeg : (-s).re < 0 := by simpa only [neg_re, neg_lt_zero] using hs
  have hAbove : -s.re - 1 < (-s).re := by rw [neg_re]; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hNeg hBot hAbove).comp s
    differentiableAt_id.neg

omit [NeZero q] in
private def seriesCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

omit [NeZero q] in
private theorem sum_seriesCoefficient_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [seriesCoefficient, charPartialSum]

private theorem integral_centeringTerm (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) ∧
      (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) =
        charMean χ / (s - 1) := by
  have hPower : (-s).re < -1 := by rw [neg_re]; linarith
  have hIntegrand (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) = charMean χ * (x : ℂ) ^ (-s) := by
    have hx0 : 0 < x := zero_lt_one.trans (Set.mem_Ioi.mp hx)
    have hProd : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
      simpa only [sub_add_cancel, cpow_one] using
        (cpow_add (-s - 1) 1 (ofReal_ne_zero.mpr hx0.ne')).symm
    rw [← mul_assoc, hProd, mul_comm]
  constructor
  · have hInt : IntegrableOn (fun x : ℝ => charMean χ * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt hPower zero_lt_one).const_mul (charMean χ)
    exact hInt.congr_fun (fun x hx => (hIntegrand x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand, integral_const_mul,
      integral_Ioi_cpow_of_lt hPower zero_lt_one]
    rw [show -s + 1 = -(s - 1) by ring]
    simp only [ofReal_one, one_cpow, div_neg, neg_div, neg_neg, mul_one_div]

theorem LFunction_eq_centeredMellin_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s =
      s * (remainderMellin χ s + charMean χ / (s - 1)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hDiff : ∀ x ∈ Ici (1 : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne'
      (neg_ne_zero.mpr hs0)).differentiableAt
  have hDerivLoc : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    have hNeg : (-s).re < 0 := by rw [neg_re]; linarith
    refine ((integrableOn_Ioi_deriv_ofReal_cpow (t := (1 / 2 : ℝ)) (by norm_num) hNeg).mono_set
      (fun x hx => ?_)).locallyIntegrableOn
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)
  have hPowerLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
  have hBoundary : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hPowerLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [f, norm_mul, Complex.ofReal_natCast, norm_natCast_cpow_of_pos hn, neg_re,
      sum_seriesCoefficient_eq]
    calc
      _ ≤ (n : ℝ) ^ (-s.re) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_charPartialSum_le χ n) (Real.rpow_nonneg n.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_add_one (Nat.cast_ne_zero.mpr hn.ne'), neg_add_eq_sub]
  have hSumDom : (fun x : ℝ => ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k) =O[atTop]
      fun x : ℝ => x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sum_seriesCoefficient_eq, one_mul, Real.norm_of_nonneg hx.le]
    exact (norm_charPartialSum_le χ _).trans (Nat.floor_le hx.le)
  have hDerivativeDom : (fun x : ℝ => deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k)
      =O[atTop] fun x : ℝ => x ^ (-s.re) := by
    refine ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul hSumDom).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_re, ← Real.rpow_add_one hx.ne', sub_add_cancel]
  have hDominatingIntegral : IntegrableAtFilter (fun x : ℝ => x ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop _, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (seriesCoefficient χ)
    (by simp [seriesCoefficient]) hDiff hDerivLoc hBoundary hDerivativeDom hDominatingIntegral
  have hCoeff (n : ℕ) : f n * seriesCoefficient χ n =
      LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [seriesCoefficient]
    · simp [f, seriesCoefficient, hn, cpow_neg, div_eq_inv_mul]
  have hSum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      f k * seriesCoefficient χ k) atTop (𝓝 (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
    simp_rw [hCoeff, ← Nat.range_succ_eq_Icc_zero]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSeriesIdentity : DirichletCharacter.LFunction χ s = (0 : ℂ) -
      ∫ x : ℝ in Ioi (1 : ℝ), deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique hSum hAbel
  calc
    _ = (0 : ℂ) - ∫ x : ℝ in Ioi (1 : ℝ), (-s) *
        ((x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [hSeriesIdentity]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : x ≠ 0 := (zero_lt_one.trans (Set.mem_Ioi.mp hx)).ne'
      simp only [f, deriv_ofReal_cpow_const (-s) hx0, sum_seriesCoefficient_eq, mul_assoc]
    _ = s * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [integral_const_mul, zero_sub, neg_mul, neg_neg]
    _ = _ := by
      have hSplit (x : ℝ) : (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊ =
          (x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) +
            (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) := by ring
      simp_rw [hSplit]
      rw [integral_add (weightedRemainder_integrableOn χ (zero_lt_one.trans hs))
        (integral_centeringTerm χ hs).1, ← remainderMellin_eq_integral, (integral_centeringTerm χ hs).2]

private theorem eq_on_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ g z)
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) {s : ℂ} (hs : 0 < s.re) : f s = g s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUConnected : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have hFA : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUOpen
  have hGA : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUOpen
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hAbsConv : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hEq : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hAbsConv] with z hz
    exact hfg z hz
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hGA hUConnected h2 hEq hs

theorem LFunction_eq_remainderMellin (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = s * remainderMellin χ s := by
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunction χ)
    (g := fun z : ℂ => z * remainderMellin χ z)
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z) ?_ ?_ hs
  · intro z hz
    exact differentiableAt_id.mul (differentiableAt_remainderMellin χ hz)
  · intro z hz
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    simp only [charMean_eq, ite_eq_right hχ, zero_div, add_zero]

theorem LFunctionTrivChar₁_eq_remainderMellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      (s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s +
        s * charMean (1 : DirichletCharacter ℂ q) := by
  let χ : DirichletCharacter ℂ q := 1
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunctionTrivChar₁ q)
    (g := fun z : ℂ => (z - 1) * z * remainderMellin χ z + z * charMean χ)
    (fun z _ => DirichletCharacter.differentiable_LFunctionTrivChar₁ q z) ?_ ?_ hs
  · intro z hz
    have hId : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hSub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := hId.sub_const 1
    exact (((hSub.mul hId).mul (differentiableAt_remainderMellin χ hz)).add (hId.mul_const _))
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      norm_num [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    change (z - 1) * DirichletCharacter.LFunction χ z = _
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    field_simp [sub_ne_zero.mpr hz1]

open scoped Classical in

theorem norm_regularizedLFunction_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 8 ≤ s.re) :
    ‖(if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
      else DirichletCharacter.LFunction χ s)‖ ≤ 25 * (q : ℝ) * (1 + ‖s‖) ^ 2 := by
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hs
  have hRemainder : ‖remainderMellin χ s‖ ≤ 24 * (q : ℝ) := by
    calc
      _ ≤ (3 * (q : ℝ)) / s.re := norm_remainderMellin_le χ hs0
      _ ≤ (3 * (q : ℝ)) / (1 / 8 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
      _ = _ := by ring
  let M := 1 + ‖s‖
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [norm_nonneg s]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hSM : ‖s‖ ≤ M := by
    dsimp [M]
    linarith
  have hSubM : ‖s - 1‖ ≤ M := by
    simpa only [M, norm_one, add_comm] using norm_sub_le s (1 : ℂ)
  have hMSq : M ≤ M ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right hM0 hM
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
  have hMq : M ≤ (q : ℝ) * M ^ 2 :=
    hMSq.trans (le_mul_of_one_le_left (sq_nonneg _) hq)
  change ‖(if χ = 1 then _ else _)‖ ≤ 25 * (q : ℝ) * M ^ 2
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl, LFunctionTrivChar₁_eq_remainderMellin hs0]
    calc
      _ ≤ ‖(s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s‖ +
          ‖s * charMean (1 : DirichletCharacter ℂ q)‖ := norm_add_le _ _
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + M := by
        apply add_le_add
        · simp only [norm_mul, pow_two]
          exact mul_le_mul (mul_le_mul hSubM hSM (norm_nonneg _) hM0) hRemainder
            (norm_nonneg _) (mul_nonneg hM0 hM0)
        · rw [norm_mul]
          simpa only [mul_one] using mul_le_mul hSM (norm_charMean_le_one (1 : DirichletCharacter ℂ q))
            (norm_nonneg _) hM0
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + (q : ℝ) * M ^ 2 := add_le_add le_rfl hMq
      _ = _ := by ring
  · rw [ite_eq_right hχ, LFunction_eq_remainderMellin χ hχ hs0, norm_mul]
    calc
      _ ≤ M ^ 2 * (24 * (q : ℝ)) :=
        mul_le_mul (hSM.trans hMSq) hRemainder (norm_nonneg _) (sq_nonneg _)
      _ = 24 * (q : ℝ) * M ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) q.cast_nonneg) (sq_nonneg _)

end GoldbachGrhGrowth

namespace Goldbach

private theorem summable_inv_sq_shift (k : ℕ) :
    Summable (fun n : ℕ ↦ (((n + k : ℕ) : ℝ) ^ 2)⁻¹) :=
  (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) k).mpr
    (Real.summable_nat_pow_inv.mpr (by decide))

private theorem inv_sq_tail_le_three_fourths :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (3 / 4 : ℝ) := by
  let u : ℕ → ℝ := fun n ↦ ((n + 2 : ℕ) : ℝ)⁻¹
  have hTail : (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (1 / 2 : ℝ) := by
    apply le_of_tendsto' (summable_inv_sq_shift 3).hasSum.tendsto_sum_nat
    intro n
    calc
      _ ≤ ∑ m ∈ Finset.range n, (u m - u (m + 1)) := by
        apply Finset.sum_le_sum
        intro m _
        have hm₂ : 0 < (m : ℝ) + 2 := by positivity
        have hm₃ : 0 < (m : ℝ) + 3 := by positivity
        calc
          _ ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3))⁻¹ := by
            rw [Nat.cast_add, Nat.cast_ofNat]
            apply inv_anti₀ (mul_pos hm₂ hm₃)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) hm₃.le
          _ = _ := by
            simp only [u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
            rw [show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
            field_simp [hm₂.ne', hm₃.ne']
            ring
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ _ := (sub_le_self _ (by dsimp [u]; positivity)).trans_eq (by norm_num [u])
  have hSplit := (summable_inv_sq_shift 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.zero_add, Nat.add_assoc,
    show (1 + 2 : ℕ) = 3 by decide, Nat.cast_ofNat] at hSplit
  rw [← hSplit, show ((2 : ℝ) ^ 2)⁻¹ = 1 / 4 by norm_num]
  linarith only [hTail]

theorem one_fourth_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  let s : ℂ := ⟨2, t⟩
  let term : ℕ → ℂ := LSeries.term (fun n : ℕ ↦ χ (n : ZMod q)) s
  have hs : 1 < s.re := by norm_num [s]
  have hTerm : Summable term := χ.LSeriesSummable_of_one_lt_re hs
  have hLFunction : χ.LFunction s = ∑' n : ℕ, term n := χ.LFunction_eq_LSeries hs
  have hTerm01 : (∑ n ∈ Finset.range 2, term n) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    simp [term]
  have hSplit := hTerm.sum_add_tsum_nat_add 2
  rw [hTerm01] at hSplit
  have hTermTail : Summable (fun n : ℕ ↦ term (n + 2)) :=
    (summable_nat_add_iff (f := term) 2).mpr hTerm
  have hTermNorm (n : ℕ) : ‖term (n + 2)‖ ≤ (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    dsimp [term]
    rw [LSeries.norm_term_eq, ite_eq_right (by omega : n + 2 ≠ 0), show s.re = 2 from rfl,
      show (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) = (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) by
        exact Real.rpow_natCast _ 2, ← one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hNormTail : ‖∑' n : ℕ, term (n + 2)‖ ≤ (3 / 4 : ℝ) :=
    (norm_tsum_le_tsum_norm hTermTail.norm).trans
      ((hTermTail.norm.tsum_le_tsum hTermNorm (summable_inv_sq_shift 2)).trans
        inv_sq_tail_le_three_fourths)
  have hSumNorm : (1 : ℝ) ≤ ‖χ.LFunction s‖ + ‖∑' n : ℕ, term (n + 2)‖ := calc
    _ = ‖(1 : ℂ)‖ := norm_one.symm
    _ = ‖χ.LFunction s - ∑' n : ℕ, term (n + 2)‖ := by
      rw [hLFunction, ← hSplit, add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
  change (1 / 4 : ℝ) ≤ ‖χ.LFunction s‖
  linarith only [hNormTail, hSumNorm]

theorem one_fourth_le_norm_mul_sub_one_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖((⟨2, t⟩ : ℂ) - 1) * χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  have hFactor : (1 : ℝ) ≤ ‖(⟨2, t⟩ : ℂ) - 1‖ := by
    have h := Complex.re_le_norm ((⟨2, t⟩ : ℂ) - 1)
    change (2 : ℝ) - 1 ≤ _ at h
    linarith only [h]
  rw [norm_mul]
  exact (one_fourth_le_norm_LFunction_anchor χ t).trans
    (le_mul_of_one_le_left (norm_nonneg _) hFactor)

end Goldbach

namespace Goldbach

open Metric Set MeromorphicOn

def criticalZeroSlice (f : ℂ → ℂ) (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ f z = 0}

private theorem jensen_mem_inner {z : ℂ} {t : ℝ} (hre : z.re = 1 / 2)
    (him : |z.im - t| ≤ 1) : z ∈ closedBall (⟨2, t⟩ : ℂ) (29 / 16) := by
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 29 / 16)).mp
  have himSq : (z.im - t) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, hre]
  nlinarith only [himSq]

private theorem jensen_re_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 / 8 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - (⟨2, t⟩ : ℂ))).trans hz
  simp only [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1]

private theorem jensen_norm_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  let center : ℂ := ⟨2, t⟩
  have hcenter : ‖center‖ ≤ 2 + |t| := by
    simpa [center] using Complex.norm_le_abs_re_add_abs_im center
  have hnorm : ‖z‖ ≤ ‖z - center‖ + ‖center‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - center) center
  linarith only [hz, hcenter, hnorm, abs_nonneg t]

private theorem jensen_analytic_outer {f : ℂ → ℂ} {t : ℝ}
    (hAnalytic : AnalyticOnNhd ℂ f {z | 0 < z.re}) :
    AnalyticOnNhd ℂ f (closedBall (⟨2, t⟩ : ℂ) (15 / 8)) := by
  intro z hz
  exact hAnalytic z (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8)
    (jensen_re_of_mem_outer hz))

theorem jensen_diskDivisor_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      ((∑ᶠ z : ℂ, divisor f (closedBall (⟨2, t⟩ : ℂ) (29 / 16)) z : ℤ) : ℝ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  let B : ℝ := 1 + 9 * A
  let bMin : ℝ := min 1 b
  let D : ℝ := B / bMin
  let logRatio : ℝ := Real.log (R / r)
  let logFactor : ℝ := 2 + Real.log D / Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hA]
  have hbMin : 0 < bMin := lt_min zero_lt_one hb
  have hD : 1 ≤ D := by
    apply (le_div_iff₀ hbMin).mpr
    simpa only [one_mul] using (min_le_left (1 : ℝ) b).trans hB
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 < logRatio := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlogCoeff : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlogD hlog2.le
  have hlogFactor : 0 < logFactor := by dsimp [logFactor]; linarith only [hlogCoeff]
  refine ⟨logFactor / logRatio, div_pos hlogFactor hlogRatio, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor
  let c : ℂ := ⟨2, t⟩
  let v : ℝ := 2 + |t|
  let w : ℝ := 2 * (q : ℝ) * v
  let M : ℝ := B * w ^ 2
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hv : 2 ≤ v := by dsimp [v]; linarith only [abs_nonneg t]
  have hw : 2 ≤ w := by
    have hq₂ : (1 : ℝ) ≤ 2 * (q : ℝ) := by linarith only [hq₁]
    exact hv.trans (le_mul_of_one_le_left (by linarith only [hv]) hq₂)
  have hw₀ : 0 < w := by linarith only [hw]
  have hM : 1 ≤ M := by
    have hWs : 1 ≤ w ^ 2 := by nlinarith only [hw, sq_nonneg (w - 2)]
    exact one_le_mul_of_one_le_of_one_le hB hWs
  have hAnchorMin : bMin ≤ ‖f c‖ := (min_le_right 1 b).trans hAnchor
  have hFpos : 0 < ‖f c‖ := hbMin.trans_le hAnchorMin
  have hFc : f c ≠ 0 := norm_pos_iff.mp hFpos
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := by
    exact jensen_analytic_outer hAnalytic
  have hBound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M := by
    intro z hz
    have hnorm : 1 + ‖z‖ ≤ 3 * v := jensen_norm_of_mem_outer hz
    have hnormSq : (1 + ‖z‖) ^ 2 ≤ (3 * v) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith only [hv])).mpr hnorm
    have hqSq : (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      have hqSelf : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hq₀
      nlinarith only [hqSelf, sq_nonneg (q : ℝ)]
    have hqvSq : (q : ℝ) * v ^ 2 ≤ w ^ 2 := calc
      _ ≤ (2 * (q : ℝ)) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSq (sq_nonneg v)
      _ = _ := by dsimp [w]; ring
    calc
      ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2 := hGrowth z (jensen_re_of_mem_outer hz)
      _ ≤ A * (q : ℝ) * (3 * v) ^ 2 := mul_le_mul_of_nonneg_left hnormSq (mul_nonneg hA.le hq₀)
      _ = 9 * A * ((q : ℝ) * v ^ 2) := by ring
      _ ≤ 9 * A * w ^ 2 := mul_le_mul_of_nonneg_left hqvSq (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg w)
  have hJensen : ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / logRatio := by
    have hOuterAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hOuter
    have hCircle : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by
      intro z hz
      apply hBound z
      simpa only [abs_of_pos hR] using sphere_subset_closedBall hz
    exact AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hOuterAbs hFc hCircle
  have hLogW : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hLogBound : Real.log (M / ‖f c‖) ≤ logFactor * Real.log w := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hDivBound : M / ‖f c‖ ≤ D * w ^ 2 := calc
      _ ≤ M / bMin := div_le_div_of_nonneg_left hMpos.le hbMin hAnchorMin
      _ = _ := by dsimp [M, D]; ring
    calc
      _ ≤ Real.log (D * w ^ 2) := Real.log_le_log (div_pos hMpos hFpos) hDivBound
      _ = 2 * Real.log w + Real.log D := by
        rw [Real.log_mul (by linarith only [hD]) (pow_ne_zero _ hw₀.ne'), Real.log_pow]
        norm_num [add_comm]
      _ = 2 * Real.log w + (Real.log D / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ 2 * Real.log w + (Real.log D / Real.log 2) * Real.log w :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLogW hlogCoeff))
      _ = _ := by dsimp [logFactor]; ring
  change ((∑ᶠ z : ℂ, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    (logFactor / logRatio) * Real.log w
  calc
    _ = ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) :=
      congrArg (fun U : Set ℂ ↦ ((∑ᶠ z : ℂ, divisor f U z : ℤ) : ℝ))
        (congrArg (closedBall c) (abs_of_pos hr).symm)
    _ ≤ Real.log (M / ‖f c‖) / logRatio := hJensen
    _ ≤ (logFactor * Real.log w) / logRatio :=
      div_le_div_of_nonneg_right hLogBound hlogRatio.le
    _ = _ := by ring

theorem jensen_criticalZeroSlice_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      (∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 → z.re = 1 / 2) →
      (criticalZeroSlice f t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice f t).indicator
          (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤
          K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  obtain ⟨K, hK, hDiskBound⟩ := jensen_diskDivisor_bound hA hb
  refine ⟨K, hK, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor hLine
  let c : ℂ := ⟨2, t⟩
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hFc : f c ≠ 0 := norm_pos_iff.mp (hb.trans_le hAnchor)
  have hCenter : c ∈ closedBall c R := mem_closedBall_self (by norm_num [R])
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := jensen_analytic_outer hAnalytic
  have hInnerSubset : closedBall c r ⊆ closedBall c R :=
    closedBall_subset_closedBall (by norm_num [r, R])
  have hInner : AnalyticOnNhd ℂ f (closedBall c r) := hOuter.mono hInnerSubset
  have hOrderCenter : analyticOrderAt f c ≠ ⊤ := by
    rw [(hOuter c hCenter).analyticOrderAt_eq_zero.mpr hFc]
    exact ENat.zero_ne_top
  let countDivisor : ℂ → ℤ := fun z ↦ divisor f (closedBall c r) z
  let countSlice : ℂ → ℝ := (criticalZeroSlice f t).indicator
    (fun z ↦ (analyticOrderNatAt f z : ℝ))
  have hSliceOrder (z : ℂ) (hz : z ∈ criticalZeroSlice f t) :
      countDivisor z = (analyticOrderNatAt f z : ℤ) ∧ 0 < analyticOrderNatAt f z := by
    have hre := hLine z hz.1 hz.2.1 hz.2.2.2
    have hzInner : z ∈ closedBall c r := jensen_mem_inner hre hz.2.2.1
    have hzOuter : z ∈ closedBall c R := hInnerSubset hzInner
    have hOrder : analyticOrderAt f z ≠ ⊤ := hOuter.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_closedBall hCenter hzOuter hOrderCenter
    constructor
    · change divisor f (closedBall c r) z = _
      rw [hInner.divisor_apply hzInner, ← Nat.cast_analyticOrderNatAt hOrder,
        ENat.map_natCast, WithTop.untop₀_coe]
    · apply Nat.pos_of_ne_zero
      intro hZero
      apply (hInner z hzInner).analyticOrderAt_ne_zero.mpr hz.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hOrder, hZero, Nat.cast_zero]
  have hDivFinite : (Function.support countDivisor).Finite :=
    (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hSliceFinite : (criticalZeroSlice f t).Finite := by
    apply hDivFinite.subset
    intro z hz
    change countDivisor z ≠ 0
    rw [(hSliceOrder z hz).1]
    exact_mod_cast (hSliceOrder z hz).2.ne'
  refine ⟨hSliceFinite, ?_⟩
  have hSliceCountFinite : (Function.support countSlice).Finite := by
    apply hSliceFinite.subset
    intro z hz
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  let divisorOverReal : ℂ → ℝ := fun z ↦ (countDivisor z : ℝ)
  have hDivCountFinite : (Function.support divisorOverReal).Finite := by
    apply hDivFinite.subset
    intro z hz
    simpa [Function.mem_support, divisorOverReal] using hz
  change (∑ᶠ z : ℂ, countSlice z) ≤ K * Real.log (2 * (q : ℝ) * (2 + |t|))
  calc
    _ ≤ ∑ᶠ z : ℂ, divisorOverReal z := by
      apply finsum_le_finsum hSliceCountFinite hDivCountFinite
      intro z
      by_cases hz : z ∈ criticalZeroSlice f t
      · simp [countSlice, divisorOverReal, Set.indicator_of_mem hz, (hSliceOrder z hz).1]
      · rw [show countSlice z = 0 from Set.indicator_of_notMem hz _]
        have hNonnegative : (0 : ℤ) ≤ countDivisor z := hInner.divisor_nonneg z
        change (0 : ℝ) ≤ (countDivisor z : ℝ)
        exact_mod_cast hNonnegative
    _ = ((∑ᶠ z : ℂ, countDivisor z : ℤ) : ℝ) :=
      (map_finsum (Int.castRingHom ℝ) hDivFinite).symm
    _ ≤ _ := hDiskBound q f t hq hAnalytic hGrowth hAnchor

end Goldbach

namespace Goldbach

open Complex DirichletCharacter Set

abbrev GRH := ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

abbrev GRH1 := ∀ (χ : DirichletCharacter ℂ 1) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

noncomputable def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ

noncomputable def principalFlag {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ = 1 then 1 else 0

theorem analytic_regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (regularizedL χ) univ := by
  intro s _
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt s
  · simpa only [regularizedL, hχ, ite_false] using (differentiable_LFunction hχ).analyticAt s

theorem regularizedL_zero_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hGRH : GRH1)
    (hq1 : q = 1) {s : ℂ} (hs : 0 < s.re) (hz : regularizedL χ s = 0) : s.re = 1 / 2 := by
  by_cases hχ : χ = 1
  · subst χ
    have hzero : LFunctionTrivChar₁ q s = 0 := by simpa only [regularizedL, eq_self, ite_true] using hz
    by_cases hs1 : s = 1
    · subst s
      exact False.elim (LFunctionTrivChar₁_apply_one_ne_zero q hzero)
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, mul_eq_zero] at hzero
    have hL : LFunction (1 : DirichletCharacter ℂ q) s = 0 :=
      hzero.resolve_left (sub_ne_zero.mpr hs1)
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (Or.inr hs1) hge hL
    subst hq1
    exact hGRH 1 s hs hslt hL
  · have hL : LFunction χ s = 0 := by simpa only [regularizedL, hχ, ite_false] using hz
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hL
    subst hq1
    exact hGRH χ s hs hslt hL

theorem norm_regularizedL_anchor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖regularizedL χ (⟨2, t⟩ : ℂ)‖ := by
  by_cases hχ : χ = 1
  · subst χ
    have hs : (⟨2, t⟩ : ℂ) ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
    simp only [regularizedL, eq_self, ite_true]
    rw [LFunctionTrivChar₁, Function.update_of_ne hs]
    exact one_fourth_le_norm_mul_sub_one_LFunction_anchor (1 : DirichletCharacter ℂ q) t
  · simpa only [regularizedL, hχ, ite_false] using one_fourth_le_norm_LFunction_anchor χ t

theorem uniform_dirichlet_zero_slice (hGRH : GRH1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      (criticalZeroSlice (regularizedL χ) t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice (regularizedL χ) t).indicator
          (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)) z) ≤
          C * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  obtain ⟨C, hC, hJensen⟩ :=
    jensen_criticalZeroSlice_bound (A := 25) (b := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q _ hq1 χ t
  exact hJensen q (regularizedL χ) t (Nat.pos_of_ne_zero (NeZero.ne q))
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL, hχ, ite_true] using hg
      · simpa only [regularizedL, hχ, ite_false] using hg)
    (norm_regularizedL_anchor χ t) (fun s hs _ hzero => regularizedL_zero_line χ hGRH hq1 hs hzero)

theorem logDeriv_regularizedL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) (hL : LFunction χ s ≠ 0) :
    logDeriv (regularizedL χ) s = logDeriv (LFunction χ) s + principalFlag χ / (s - 1) := by
  by_cases hχ : χ = 1
  · subst χ
    simp only [regularizedL, principalFlag, eq_self, ite_true, logDeriv, Pi.div_apply]
    rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q hs,
      LFunctionTrivChar₁, Function.update_of_ne hs]
    field_simp [sub_ne_zero.mpr hs, hL]
  · simp [regularizedL, principalFlag, hχ]

end Goldbach

open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section

namespace GoldbachGrhLogDerivative

private theorem exists_normalizedLog_on_ball {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R))
    (hg0 : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0) :
    ∃ J : ℂ → ℂ, J 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt J (logDeriv g z) z) ∧
      (∀ z ∈ ball (0 : ℂ) R, (J z).re = Real.log ‖g z‖ - Real.log ‖g 0‖) := by
  let U : Set ℂ := ball 0 R
  have hLog : DifferentiableOn ℂ (logDeriv g) U := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w => deriv g w / g w) U z
    exact ((hg z hz).deriv.differentiableAt.div (hg z hz).differentiableAt
      (hg0 z hz)).differentiableWithinAt
  obtain ⟨J, hJ0, hJ⟩ := hLog.isExactOn_ball.with_val_at 0 0
  refine ⟨J, hJ0, hJ, ?_⟩
  let k : ℂ → ℂ := fun z => exp (-J z) * g z
  have hk (z : ℂ) (hz : z ∈ U) : HasDerivAt k 0 z := by
    have hD := (hJ z hz).neg.cexp.mul (hg z hz).differentiableAt.hasDerivAt
    convert hD using 1
    simp only [logDeriv_apply]
    field_simp [hg0 z hz]
    norm_num
  have hc : (0 : ℂ) ∈ U := mem_ball_self hR
  have hConst : EqOn k (fun _ => g 0) U := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt) (differentiableOn_const (g 0))
      ?_ hc (by simp [k, hJ0])
    intro z hz
    rw [(hk z hz).deriv, deriv_const]
  intro z hz
  have hAt := hConst hz
  change exp (-J z) * g z = g 0 at hAt
  have hExp : exp (J z) * g 0 = g z := by
    rw [← hAt, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hNorm := congrArg norm hExp
  rw [norm_mul, norm_exp] at hNorm
  have hLn := congrArg Real.log hNorm
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (hg0 0 hc)), Real.log_exp] at hLn
  linarith

theorem norm_logDeriv_of_zeroFree_ball {g : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) (22 / 25)))
    (hg0 : ∀ z ∈ ball (0 : ℂ) (22 / 25), g z ≠ 0)
    (hgBound : ∀ z ∈ ball (0 : ℂ) (22 / 25),
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 83 / 100) :
    ‖logDeriv g z‖ ≤ 4200 * M := by
  have hR : (0 : ℝ) < 22 / 25 := by norm_num
  obtain ⟨J, hJ0, hJDeriv, hJRe⟩ := exists_normalizedLog_on_ball hR hg hg0
  have hJDiff : DifferentiableOn ℂ J (ball (0 : ℂ) (22 / 25)) :=
    fun w hw => (hJDeriv w hw).differentiableAt.differentiableWithinAt
  have hRadius : (0 : ℝ) < 1 / 100 := by norm_num
  have hLocalNorm (w : ℂ) (hw : w ∈ closedBall z (1 / 100)) : ‖w‖ ≤ 21 / 25 := by
    rw [mem_closedBall, Complex.dist_eq] at hw
    linarith [norm_le_norm_sub_add w z]
  have hLocal : closedBall z (1 / 100) ⊆ ball (0 : ℂ) (22 / 25) := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((hLocalNorm w hw).trans_lt (by norm_num))
  have hLocalDiff : DiffContOnCl ℂ J (ball z (1 / 100)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hRadius.ne']
    exact hJDiff.mono hLocal
  have hJImage : MapsTo J (ball (0 : ℂ) (22 / 25)) {w | w.re ≤ M} := by
    intro w hw
    change (J w).re ≤ M
    rw [hJRe w hw]
    exact hgBound w hw
  have hLocalBound (w : ℂ) (hw : w ∈ sphere z (1 / 100)) : ‖J w‖ ≤ 42 * M := by
    have hws := sphere_subset_closedBall hw
    have hwBig := hLocal hws
    have hSmall := hLocalNorm w hws
    have hDpos : 0 < (22 / 25 : ℝ) - ‖w‖ := by linarith
    refine (borelCaratheodory_zero hM hJDiff hJImage hR hwBig hJ0).trans ?_
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hSmall)]
  have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hRadius hLocalDiff hLocalBound
  have hzBig : z ∈ ball (0 : ℂ) (22 / 25) :=
    mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
  rw [(hJDeriv z hzBig).deriv] at hCauchy
  calc
    _ ≤ (42 * M) / (1 / 100 : ℝ) := hCauchy
    _ = _ := by ring

open MeromorphicOn in
private theorem factor_inner_divisor {f : ℂ → ℂ} {U V : Set ℂ}
    (hVU : V ⊆ U) (hCompact : IsCompact V) (hf : AnalyticOnNhd ℂ f U)
    (hFiniteOrder : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ V, g z ≠ 0) ∧
      EqOn f ((∏ᶠ ρ, (· - ρ) ^ divisor f V ρ) * g)
        (U \ Function.support (divisor f V)) := by
  let D := divisor f V
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  let Q : ℂ → ℂ := P⁻¹ • f
  let g := toMeromorphicNFOn Q U
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport hCompact
  have hPNF : MeromorphicNFOn P U := Function.FactorizedRational.meromorphicNFOn D U
  have hQMer : MeromorphicOn Q U := hPNF.meromorphicOn.inv.smul hf.meromorphicOn
  have hGNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn Q U
  have hPOrd (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hDfin
  have hGOrd (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [← meromorphicOrderAt_congr (hQMer.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm]
    change meromorphicOrderAt (P⁻¹ • f) z = _
    rw [meromorphicOrderAt_smul (hPNF.meromorphicOn z hz).inv (hf.meromorphicOn z hz),
      meromorphicOrderAt_inv, hPOrd]
  have hOrdInner (z : ℂ) (hz : z ∈ V) : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    change (divisor f V z : WithTop ℤ) = _
    rw [(hf.mono hVU).meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using hFiniteOrder z (hVU hz) with n hn
    simp
  have hGZeroOrder (z : ℂ) (hz : z ∈ V) : meromorphicOrderAt g z = 0 := by
    rw [hGOrd z (hVU hz), ← hOrdInner z hz, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    simp
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    apply (hGNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hzV : z ∈ V
    · rw [hGZeroOrder z hzV]
    · have hzD : D z = 0 := by
        by_contra h
        exact hzV (D.supportWithinDomain h)
      rw [hGOrd z hz, hzD, WithTop.coe_zero, neg_zero, zero_add]
      exact (hf z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hf z hz)
  · intro z hz
    exact (hGNF (hVU hz)).meromorphicOrderAt_eq_zero_iff.mp (hGZeroOrder z hz)
  · intro z hz
    have hzD : D z = 0 := by simpa only [Function.mem_support, not_not] using hz.2
    have hPOrd0 : meromorphicOrderAt P z = 0 := by rw [hPOrd, hzD, WithTop.coe_zero]
    have hPNZ : P z ≠ 0 := (hPNF hz.1).meromorphicOrderAt_eq_zero_iff.mp hPOrd0
    have hPA : AnalyticAt ℂ P z :=
      (hPNF hz.1).meromorphicOrderAt_nonneg_iff_analyticAt.mp hPOrd0.ge
    have hQA : AnalyticAt ℂ Q z := (hPA.inv hPNZ).mul (hf z hz.1)
    have hGQ : g z = Q z := by
      change toMeromorphicNFOn Q U z = Q z
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQMer hz.1,
        toMeromorphicNFAt_eq_self.mpr hQA.meromorphicNFAt]
    change f z = P z * g z
    rw [hGQ]
    change f z = P z * ((P z)⁻¹ * f z)
    rw [← mul_assoc, mul_inv_cancel₀ hPNZ, one_mul]

private theorem logDeriv_finset_zeroFactors {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  have hd (ρ : ℂ) : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have hProd : (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) =
      ∏ ρ ∈ Z, (fun w : ℂ => (w - ρ) ^ m ρ) := by
    funext w
    rw [Finset.prod_apply]
  rw [hProd, logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => (hd ρ).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [logDeriv_fun_pow (hd ρ).differentiableAt, logDeriv_apply, (hd ρ).deriv]
  ring

open MeromorphicOn in

theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ sphere (0 : ℂ) (24 / 25), ‖f w‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (0 : ℂ) (22 / 25) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ z : ℂ, ‖z‖ ≤ 83 / 100 → f z ≠ 0 →
        ‖logDeriv f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          130200 * Real.log B := by
  classical
  let U := closedBall (0 : ℂ) 1
  let V := closedBall (0 : ℂ) (22 / 25)
  let W := closedBall (0 : ℂ) (24 / 25)
  have hVU : V ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hWU : W ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hVW : V ⊆ W := closedBall_subset_closedBall (by norm_num)
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self (by norm_num)
  have hf0NZ : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hFinA (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall _ _).isPreconnected h0U hz
      (by simp [(hf 0 h0U).analyticOrderAt_eq_zero.mpr hf0NZ])
  have hFinM (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf z hz).meromorphicOrderAt_eq]
    lift analyticOrderAt f z to ℕ using hFinA z hz with n hn
    simp
  let D := divisor f V
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall ..)
  let Z := hDfin.toFinset
  let K := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hSupport : V ∩ f ⁻¹' {0} = Function.support D :=
    (hf.mono hVU).meromorphicNFOn.zero_set_eq_divisor_support (fun v => hFinM v (hVU v.2))
  have hZeq : (↑Z : Set ℂ) = {ρ ∈ V | f ρ = 0} := by
    rw [show (↑Z : Set ℂ) = Function.support D from hDfin.coe_toFinset, ← hSupport]
    rfl
  have hρV (ρ : ℂ) (hρ : ρ ∈ Z) : ρ ∈ V := D.supportWithinDomain (hDfin.mem_toFinset.mp hρ)
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : D ρ = (analyticOrderNatAt f ρ : ℤ) := by
    change divisor f V ρ = _
    rw [(hf.mono hVU).divisor_apply (hρV ρ hρ), ← Nat.cast_analyticOrderNatAt (hFinA ρ (hVU (hρV ρ hρ)))]
    simp
  have hCount : (K : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
    have hFsum : (∑ᶠ u, D u) = ∑ ρ ∈ Z, D ρ :=
      finsum_eq_sum_of_support_subset _ fun _ hu => hDfin.mem_toFinset.mpr hu
    have hK : (K : ℤ) = ∑ ρ ∈ Z, D ρ := by
      simp only [K, Nat.cast_sum]
      exact Finset.sum_congr rfl fun ρ hρ => (hm ρ hρ).symm
    have hJ := AnalyticOnNhd.sum_divisor_le (r := (22 / 25 : ℝ)) (R := 24 / 25) (M := B)
      (by norm_num) (by norm_num) (by linarith)
      (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hf.mono hWU)
      hf0NZ (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hfB)
    have hRatio : (24 / 25 : ℝ) / (22 / 25) = 12 / 11 := by norm_num
    have hAbs : |(22 / 25 : ℝ)| = 22 / 25 := abs_of_nonneg (by norm_num)
    rw [hAbs] at hJ
    have hJ' : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
      simpa only [D, V, hf0, norm_one, div_one, hRatio] using hJ
    rw [hFsum, ← hK, Int.cast_natCast] at hJ'
    exact hJ'
  obtain ⟨g, hg, hgNZ, hFactor⟩ := factor_inner_divisor hVU (isCompact_closedBall ..) hf hFinM
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ
  have hProd : (∏ᶠ ρ, (· - ρ) ^ D ρ) = P := by
    have hDiff : (fun ρ : ℂ => (· - ρ) ^ D ρ).mulSupport ⊆ Z := by
      intro ρ hρ
      refine hDfin.mem_toFinset.mpr ?_
      by_contra hOutside
      have hD0 : D ρ = 0 := by simpa only [Function.mem_support, not_not] using hOutside
      exact hρ (by simp [hD0])
    rw [finprod_eq_prod_of_mulSupport_subset _ hDiff]
    funext w
    rw [Finset.prod_apply]
    exact Finset.prod_congr rfl fun ρ hρ => by simp [hm ρ hρ]
  have hFac : EqOn f (P * g) (U \ Function.support D) := by
    simpa only [← hProd] using hFactor
  have hOuter (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) :
      ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    have hwNorm : ‖w‖ = 24 / 25 := mem_sphere_zero_iff_norm.mp hw
    have hwU : w ∈ U := hWU (sphere_subset_closedBall hw)
    have hwNot : w ∉ Function.support D := by
      intro hwD
      have hwV : w ∈ V := D.supportWithinDomain hwD
      have hN : ‖w‖ ≤ 22 / 25 := by simpa only [V, mem_closedBall_iff_norm, sub_zero] using hwV
      linarith
    have hEq : f w = P w * g w := hFac ⟨hwU, hwNot⟩
    have hDist (ρ : ℂ) (hρ : ρ ∈ Z) : (2 / 25 : ℝ) ≤ ‖w - ρ‖ := by
      have hRho : ‖ρ‖ ≤ 22 / 25 := by
        simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
      exact (show (2 / 25 : ℝ) ≤ ‖w‖ - ‖ρ‖ by linarith).trans (norm_sub_norm_le w ρ)
    have hPBound : (2 / 25 : ℝ) ^ K ≤ ‖P w‖ := by
      simp only [P, norm_prod, norm_pow, K, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun ρ hρ => pow_le_pow_left₀ (by norm_num) (hDist ρ hρ) _)
    have hAt := hfB w hw
    rw [hEq, norm_mul] at hAt
    have hMul : ‖g w‖ * (2 / 25 : ℝ) ^ K ≤ B := by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right hPBound (norm_nonneg _)).trans hAt
    have hDiv := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2 / 25) K)).mpr hMul
    rw [div_eq_mul_inv, ← inv_pow, show ((2 / 25 : ℝ)⁻¹) = 25 / 2 by norm_num] at hDiv
    exact hDiv
  have hMax (w : ℂ) (hw : w ∈ W) : ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    apply norm_le_of_forall_mem_frontier_norm_le (U := W) isBounded_closedBall
    · apply DifferentiableOn.diffContOnCl
      simpa only [W, closure_closedBall] using (hg.mono hWU).differentiableOn
    · simpa only [W, frontier_closedBall'] using hOuter
    · simpa only [W, closure_closedBall] using hw
  have h0Not : (0 : ℂ) ∉ Function.support D := by
    rw [← hSupport]
    simp [hf0]
  have hP0 : ‖P 0‖ ≤ 1 := by
    simp only [P, norm_prod, norm_pow, zero_sub, norm_neg]
    refine Finset.prod_le_one₀ (fun _ _ => by positivity) fun ρ hρ => ?_
    have hρN : ‖ρ‖ ≤ 22 / 25 := by
      simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
    exact pow_le_one₀ (norm_nonneg _) (hρN.trans (by norm_num))
  have hG0 : 1 ≤ ‖g 0‖ := by
    have hFactor0 : f 0 = P 0 * g 0 := hFac ⟨h0U, h0Not⟩
    calc
      1 = ‖f 0‖ := by simp [hf0]
      _ = ‖P 0‖ * ‖g 0‖ := by rw [hFactor0, norm_mul]
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP0 (norm_nonneg _)
  have hLogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hLogRatio : 0 < Real.log (12 / 11 : ℝ) := Real.log_pos (by norm_num)
  have hLogPow : Real.log (25 / 2 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
    calc
      _ ≤ Real.log ((12 / 11 : ℝ) ^ (30 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hKLog : (K : ℝ) * Real.log (25 / 2 : ℝ) ≤ 30 * Real.log B := by
    calc
      _ ≤ (K : ℝ) * (30 * Real.log (12 / 11 : ℝ)) := mul_le_mul_of_nonneg_left hLogPow K.cast_nonneg
      _ = 30 * ((K : ℝ) * Real.log (12 / 11 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hLogRatio).mp hCount) (by norm_num)
  have hReg (w : ℂ) (hw : w ∈ ball (0 : ℂ) (22 / 25)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ 31 * Real.log B := by
    have hwV := ball_subset_closedBall hw
    have hL : Real.log ‖g w‖ ≤ Real.log (B * (25 / 2 : ℝ) ^ K) :=
      Real.log_le_log (norm_pos_iff.mpr (hgNZ w hwV)) (hMax w (hVW hwV))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hL
    linarith [Real.log_nonneg hG0]
  refine ⟨Z, hZeq, ?_, ?_⟩
  · simpa only [K, Nat.cast_sum] using hCount
  · intro z hz hfz
    have hzI : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
    have hzNot : z ∉ Function.support D := by
      rw [← hSupport]
      simp [hfz]
    have hLocal : f =ᶠ[𝓝 z] fun w => P w * g w := by
      filter_upwards [(isOpen_ball.sdiff hDfin.isClosed).mem_nhds ⟨hzI, hzNot⟩] with w hw
      exact hFac ⟨ball_subset_closedBall hw.1, hw.2⟩
    have hfacZ : f z = P z * g z := hLocal.eq_of_nhds
    have hPZ : P z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hGZ : g z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hdP : DifferentiableAt ℂ P z := DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
    have hFrac : logDeriv f z = logDeriv P z + logDeriv g z := by
      have hEq : logDeriv f z = logDeriv (fun w => P w * g w) z := by
        simp only [logDeriv_apply, hLocal.deriv_eq, hfacZ]
      rw [hEq]
      exact logDeriv_mul z hPZ hGZ hdP (hg z (ball_subset_closedBall hzI)).differentiableAt
    have hNonzero (ρ : ℂ) (hρ : ρ ∈ Z) : z ≠ ρ := by
      intro h
      have hρD : ρ ∈ Function.support D := hDfin.mem_toFinset.mp hρ
      exact hzNot (h ▸ hρD)
    rw [hFrac, show logDeriv P z = _ from logDeriv_finset_zeroFactors hNonzero, add_sub_cancel_left]
    calc
      _ ≤ 4200 * (31 * Real.log B) := norm_logDeriv_of_zeroFree_ball (by positivity)
        (hg.mono (ball_subset_closedBall.trans hVU))
        (fun w hw => hgNZ w (ball_subset_closedBall hw)) hReg hz
      _ = _ := by ring

theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf0 : f c ≠ 0) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ closedBall c (24 / 25 * R), ‖f w‖ ≤ B * ‖f c‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall c (22 / 25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ s ∈ closedBall c (83 / 100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          130200 / R * Real.log B := by
  let A : ℂ → ℂ := fun w => c + (R : ℂ) * w
  let G : ℂ → ℂ := fun w => (f c)⁻¹ * f (A w)
  have hRC : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hAanalytic (w : ℂ) : AnalyticAt ℂ A w :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hADeriv (w : ℂ) : deriv A w = (R : ℂ) := by
    simp [A]
  have hAinj : Function.Injective A := by
    intro z w hEq
    change c + (R : ℂ) * z = c + (R : ℂ) * w at hEq
    exact mul_left_cancel₀ hRC (add_left_cancel hEq)
  have hANorm (w : ℂ) : ‖A w - c‖ = R * ‖w‖ := by
    simp only [A, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hR.le]
  have hAInv (s : ℂ) : A ((s - c) / (R : ℂ)) = s := by
    simp only [A]
    field_simp [hRC]
    ring
  have hAMem {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) : A w ∈ closedBall c (r * R) := by
    rw [mem_closedBall_iff_norm, hANorm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw hR.le
  have hInvNorm {s : ℂ} {r : ℝ} (hs : s ∈ closedBall c (r * R)) :
      ‖(s - c) / (R : ℂ)‖ ≤ r := by
    rw [mem_closedBall_iff_norm] at hs
    rw [norm_div, Complex.norm_of_nonneg hR.le]
    exact (div_le_iff₀ hR).mpr hs
  have hAMemOne {w : ℂ} (hw : ‖w‖ ≤ 1) : A w ∈ closedBall c R := by
    simpa only [one_mul] using hAMem hw
  have hGanalytic : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 1 := by simpa only [mem_closedBall_iff_norm, sub_zero] using hw
    exact analyticAt_const.mul ((hf (A w) (hAMemOne hwNorm)).comp (hAanalytic w))
  have hG0 : G 0 = 1 := by simp [G, A, hf0]
  have hGBound (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) : ‖G w‖ ≤ B := by
    have hwNorm : ‖w‖ ≤ 24 / 25 := (mem_sphere_zero_iff_norm.mp hw).le
    have hNormPos := norm_pos_iff.mpr hf0
    calc
      _ = ‖f c‖⁻¹ * ‖f (A w)‖ := by simp only [G, norm_mul, norm_inv]
      _ ≤ ‖f c‖⁻¹ * (B * ‖f c‖) := mul_le_mul_of_nonneg_left (hfB (A w) (hAMem hwNorm))
        (inv_nonneg.mpr hNormPos.le)
      _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hNormPos.ne', one_mul]
  have hOrd (w : ℂ) (hw : ‖w‖ ≤ 1) :
      analyticOrderNatAt G w = analyticOrderNatAt f (A w) := by
    have hComp : AnalyticAt ℂ (f ∘ A) w := (hf (A w) (hAMemOne hw)).comp (hAanalytic w)
    calc
      _ = analyticOrderNatAt (f ∘ A) w := analyticOrderNatAt_fun_const_mul hComp (inv_ne_zero hf0)
      _ = _ := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_comp_of_deriv_ne_zero (hAanalytic w) (by rw [hADeriv]; exact hRC)]
  obtain ⟨Z₀, hZ₀, hCount, hBound⟩ := logDeriv_partial_fraction_unit hGanalytic hG0 hB hGBound
  have hZero (w : ℂ) : w ∈ Z₀ ↔ ‖w‖ ≤ 22 / 25 ∧ f (A w) = 0 := by
    change w ∈ (↑Z₀ : Set ℂ) ↔ _
    rw [hZ₀]
    simp [G, hf0]
  have hZeroNorm (w : ℂ) (hw : w ∈ Z₀) : ‖w‖ ≤ 1 :=
    ((hZero w).mp hw).1.trans (by norm_num)
  let embedding : ℂ ↪ ℂ := ⟨A, hAinj⟩
  let Z := Z₀.map embedding
  refine ⟨Z, ?_, ?_, ?_⟩
  · ext ρ
    change ρ ∈ Z ↔ ρ ∈ closedBall c (22 / 25 * R) ∧ f ρ = 0
    simp only [Z, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwNorm, hwZero⟩ := (hZero w).mp hw
      exact ⟨hAMem hwNorm, hwZero⟩
    · rintro ⟨hρ, hρZero⟩
      refine ⟨(ρ - c) / (R : ℂ), (hZero _).mpr ⟨hInvNorm hρ, ?_⟩, hAInv ρ⟩
      rwa [hAInv]
  · simp only [Z, Finset.sum_map]
    have hSum : (∑ w ∈ Z₀, (analyticOrderNatAt f (A w) : ℝ)) =
        ∑ w ∈ Z₀, (analyticOrderNatAt G w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by rw [hOrd w (hZeroNorm w hw)]
    exact hSum.le.trans hCount
  · intro s hs hfs
    let w := (s - c) / (R : ℂ)
    have hAw : A w = s := hAInv s
    have hw : ‖w‖ ≤ 83 / 100 := hInvNorm hs
    have hw₁ : ‖w‖ ≤ 1 := hw.trans (by norm_num)
    have hGw : G w ≠ 0 := by simp [G, hAw, hf0, hfs]
    have hG := hBound w hw hGw
    have hLD : logDeriv G w = (R : ℂ) * logDeriv f s := by
      calc
        _ = logDeriv (f ∘ A) w := logDeriv_const_mul w _ (inv_ne_zero hf0)
        _ = _ := by
          rw [logDeriv_comp (hf (A w) (hAMemOne hw₁)).differentiableAt
            (hAanalytic w).differentiableAt, hADeriv, hAw, mul_comm]
    have hLDF : logDeriv f s = (R : ℂ)⁻¹ * logDeriv G w := by
      rw [hLD, ← mul_assoc, inv_mul_cancel₀ hRC, one_mul]
    have hTerms : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) =
        (R : ℂ)⁻¹ * ∑ u ∈ Z₀, (analyticOrderNatAt G u : ℂ) / (w - u) := by
      simp only [Z, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      change (analyticOrderNatAt f (A u) : ℂ) / (s - A u) = _
      rw [← hOrd u (hZeroNorm u hu)]
      have hShift : s - A u = (R : ℂ) * (w - u) := by
        rw [← hAw]
        simp only [A]
        ring
      calc
        _ = ((analyticOrderNatAt G u : ℂ) / (w - u)) / (R : ℂ) := by
          rw [hShift, div_div, mul_comm]
        _ = _ := div_eq_inv_mul _ _
    rw [hLDF, hTerms, ← mul_sub, norm_mul, norm_inv, Complex.norm_of_nonneg hR.le]
    calc
      _ ≤ R⁻¹ * (130200 * Real.log B) := mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr hR.le)
      _ = _ := by ring

end GoldbachGrhLogDerivative

namespace Goldbach

open Complex Metric Set
open scoped BigOperators

theorem norm_logDeriv_regularizedL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t σ d : ℝ),
      9 / 20 ≤ σ → σ ≤ 2 → 0 < d →
      (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖(⟨σ, t⟩ : ℂ) - ρ‖) →
      ‖logDeriv (regularizedL χ) (⟨σ, t⟩ : ℂ)‖ ≤
        C * Real.log (2 * (q : ℝ) * (2 + |t|)) * (1 + d⁻¹) := by
  let R : ℝ := 15 / 8
  let A : ℝ := 130200 / R
  let E : ℝ := (Real.log (12 / 11 : ℝ))⁻¹
  have hR : 0 < R := by norm_num [R]
  have hA : 0 < A := div_pos (by norm_num) hR
  have hE : 0 < E := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨13 * (A + E), mul_pos (by norm_num) (add_pos hA hE), ?_⟩
  intro q _ χ t σ d hσlo hσhi hd hSep
  let f := regularizedL χ
  let c : ℂ := ⟨2, t⟩
  let s : ℂ := ⟨σ, t⟩
  let K : ℝ := 2 + |t|
  let B : ℝ := 900 * (q : ℝ) * K ^ 2
  let L : ℝ := Real.log (2 * (q : ℝ) * K)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt q.pos_of_neZero
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (abs_nonneg t)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hB2 : 2 ≤ B := by
    calc
      (2 : ℝ) ≤ 900 * 1 * 1 := by norm_num
      _ ≤ B := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num))
        (one_le_pow₀ hK1) zero_le_one (by positivity)
  have hReLower (w : ℂ) (hw : w ∈ closedBall c R) : (1 / 8 : ℝ) ≤ w.re := by
    have hDist := mem_closedBall_iff_norm.mp hw
    have hRe := abs_re_le_norm (w - c)
    rw [sub_re, show c.re = 2 from rfl] at hRe
    have hLower := neg_le_abs (w.re - 2)
    dsimp only [R] at hDist
    linarith
  have hcform : c = (2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
  have hcnorm : ‖c‖ ≤ K := by
    rw [hcform]
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by simp [K, norm_real, Real.norm_eq_abs]
  have hAnchor : (1 / 4 : ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hf0 : f c ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hAnchor)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := (analytic_regularizedL χ).mono (subset_univ _)
  have hfB (w : ℂ) (hw : w ∈ closedBall c (24 / 25 * R)) : ‖f w‖ ≤ B * ‖f c‖ := by
    have hwBig := closedBall_subset_closedBall (show (24 / 25 : ℝ) * R ≤ R by norm_num [R]) hw
    have hDist := mem_closedBall_iff_norm.mp hwBig
    have hwNorm : 1 + ‖w‖ ≤ 3 * K := by
      dsimp only [R] at hDist
      linarith only [norm_le_norm_sub_add w c, hDist, hcnorm, hK2]
    have hGrowth : ‖f w‖ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := by
      have hRaw := GoldbachGrhGrowth.norm_regularizedLFunction_le χ (hReLower w hwBig)
      by_cases hχ : χ = 1 <;> simpa [f, regularizedL, hχ] using hRaw
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hGrowth
      _ ≤ 25 * (q : ℝ) * (3 * K) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hwNorm 2) (by positivity)
      _ = B * (1 / 4 : ℝ) := by
        dsimp only [B]
        ring
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hAnchor hB0.le
  have hS : s ∈ closedBall c (83 / 100 * R) := by
    have hSub : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [mem_closedBall_iff_norm, hSub, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hσhi)]
    dsimp only [R]
    linarith
  have hS0 : f s ≠ 0 := by
    intro hsz
    have hs : 0 < s.re := (by norm_num : (0 : ℝ) < 9 / 20).trans_le hσlo
    have h := hSep s hs hsz
    rw [sub_self, norm_zero] at h
    exact hd.not_ge h
  obtain ⟨Z, hZ, hMass, hApprox⟩ :=
    GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk hR hf hf0 hB2 hfB
  have hTerms : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * d⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hZmem : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at hZmem
    have hρLarge := closedBall_subset_closedBall (show (22 / 25 : ℝ) * R ≤ R by norm_num [R])
      hZmem.1
    have hρPos := (by norm_num : (0 : ℝ) < 1 / 8).trans_le (hReLower ρ hρLarge)
    have hρdist : d ≤ ‖s - ρ‖ := hSep ρ hρPos hZmem.2
    have hRecip : ‖s - ρ‖⁻¹ ≤ d⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hd hρdist
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg _)
  have hLFormula : L = Real.log 2 + Real.log (q : ℝ) + Real.log K := by
    dsimp only [L]
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_mul (by norm_num) hq0.ne']
  have hBLFormula : Real.log B = Real.log 900 + Real.log (q : ℝ) + 2 * Real.log K := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hK0.ne'),
      Real.log_mul (by norm_num) hq0.ne', Real.log_pow]
    norm_num
  have hLog900 : Real.log 900 ≤ 10 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.log_pow]
        norm_num
  have hLPos : 0 < L := by
    rw [hLFormula]
    linarith only [Real.log_nonneg hq1, Real.log_nonneg hK1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hScaleLog : Real.log B ≤ 13 * L := by
    rw [hBLFormula, hLFormula]
    linarith only [hLog900, Real.log_nonneg hq1, Real.log_nonneg hK1,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hRecip0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hBudget : A + E * d⁻¹ ≤ (A + E) * (1 + d⁻¹) := by
    nlinarith only [hE.le, mul_nonneg hA.le hRecip0]
  have hMass' := mul_le_mul_of_nonneg_right hMass hRecip0
  change ‖logDeriv f s‖ ≤ 13 * (A + E) * L * (1 + d⁻¹)
  calc
    _ ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ A * Real.log B + (Real.log B / Real.log (12 / 11)) * d⁻¹ :=
      (add_le_add (hApprox s hS hS0) (hTerms.trans hMass'))
    _ = Real.log B * (A + E * d⁻¹) := by
      dsimp only [E]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (13 * L) * (A + E * d⁻¹) := mul_le_mul_of_nonneg_right hScaleLog (by positivity)
    _ ≤ (13 * L) * ((A + E) * (1 + d⁻¹)) := mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by ring

end Goldbach

namespace Goldbach

theorem exists_goodHeight {α : Type*} (S : Finset α) (ordinate : α → ℝ) (T : ℝ) :
    ∃ u ∈ Set.Icc T (T + 1),
      ∀ a ∈ S, (1 : ℝ) / (2 * (1 + (S.card : ℝ))) ≤ |u - ordinate a| := by
  classical
  let den : ℝ := 1 + (S.card : ℝ)
  let gap : ℝ := 1 / (2 * den)
  let grid (j : Fin (S.card + 1)) : ℝ := T + (j.val : ℝ) / den
  have hDen : 0 < den := by dsimp [den]; positivity
  have hGrid (j : Fin (S.card + 1)) : grid j ∈ Set.Icc T (T + 1) := by
    have hj : (j.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hLower : 0 ≤ (j.val : ℝ) / den := div_nonneg (by positivity) hDen.le
    have hUpper : (j.val : ℝ) / den ≤ 1 := by
      apply (div_le_one hDen).mpr
      dsimp [den]
      linarith only [hj]
    exact ⟨by dsimp [grid]; linarith only [hLower], add_le_add le_rfl hUpper⟩
  have hGridGap {j k : Fin (S.card + 1)} (hjk : j ≠ k) :
      gap + gap ≤ |grid j - grid k| := by
    have hNat : j.val ≠ k.val := fun heq ↦ hjk (Fin.ext heq)
    have hInt : (j.val : ℤ) ≠ (k.val : ℤ) := by exact_mod_cast hNat
    have hAbsInt : (1 : ℤ) ≤ |(j.val : ℤ) - (k.val : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hInt)
    have hAbs : (1 : ℝ) ≤ |(j.val : ℝ) - (k.val : ℝ)| := by exact_mod_cast hAbsInt
    have hGridSub : grid j - grid k = ((j.val : ℝ) - (k.val : ℝ)) / den := by
      dsimp [grid]
      ring
    calc
      gap + gap = 1 / den := by
        dsimp [gap]
        field_simp [hDen.ne']
        norm_num
      _ ≤ |(j.val : ℝ) - (k.val : ℝ)| / den := div_le_div_of_nonneg_right hAbs hDen.le
      _ = |grid j - grid k| := by rw [hGridSub, abs_div, abs_of_pos hDen]
  by_contra hNoGood
  have hBad (j : Fin (S.card + 1)) : ∃ a : S, |grid j - ordinate a| < gap := by
    by_contra hNoBad
    apply hNoGood
    refine ⟨grid j, hGrid j, ?_⟩
    intro a ha
    exact le_of_not_gt (fun h ↦ hNoBad ⟨⟨a, ha⟩, h⟩)
  let badAt (j : Fin (S.card + 1)) : S := (hBad j).choose
  have hBadAt (j : Fin (S.card + 1)) : |grid j - ordinate (badAt j)| < gap :=
    (hBad j).choose_spec
  have hInjective : Function.Injective badAt := by
    intro j k hEqual
    by_contra hDifferent
    have hPair : |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| < gap + gap :=
      (add_lt_add (hBadAt j) (by simpa only [hEqual] using hBadAt k))
    have hTri : |grid j - grid k| ≤
        |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| := by
      simpa only [abs_sub_comm (ordinate (badAt j)) (grid k)] using
        abs_sub_le (grid j) (ordinate (badAt j)) (grid k)
    exact not_lt_of_ge (hGridGap hDifferent) (hTri.trans_lt hPair)
  have hCard : S.card + 1 ≤ S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective badAt hInjective
  omega

theorem exists_goodHeight_of_stripCount {f : ℂ → ℂ} (T countBound : ℝ)
    (hAnalytic : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hAnchor : f (⟨2, T + 1 / 2⟩ : ℂ) ≠ 0) :
    let slice : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - (T + 1 / 2)| ≤ 1 ∧ f z = 0}
    slice.Finite →
      (∑ᶠ z : ℂ, slice.indicator (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤ countBound →
      ∃ u ∈ Set.Icc T (T + 1), ∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 →
        (1 : ℝ) / (2 * (1 + countBound)) ≤ |u - z.im| := by
  classical
  intro slice hFinite hCount
  let zeros := hFinite.toFinset
  let weight : ℂ → ℝ := fun z ↦ (analyticOrderNatAt f z : ℝ)
  have hSupport : Function.support (slice.indicator weight) ⊆ (zeros : Set ℂ) := by
    intro z hz
    apply hFinite.mem_toFinset.mpr
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  have hCountEq : (∑ᶠ z : ℂ, slice.indicator weight z) = ∑ z ∈ zeros, weight z := by
    rw [finsum_eq_sum_of_support_subset _ hSupport]
    exact Finset.sum_congr rfl fun z hz ↦ Set.indicator_of_mem (hFinite.mem_toFinset.mp hz) _
  let center : ℂ := ⟨2, T + 1 / 2⟩
  have hCenterMem : center ∈ {z : ℂ | 0 < z.re} := by norm_num [center]
  have hCenterOrder : analyticOrderAt f center ≠ ⊤ := by
    rw [(hAnalytic center hCenterMem).analyticOrderAt_eq_zero.mpr hAnchor]
    exact ENat.zero_ne_top
  have hWeight (z : ℂ) (hz : z ∈ zeros) : 1 ≤ weight z := by
    have hzSlice : 0 < z.re ∧ z.re < 1 ∧ |z.im - (T + 1 / 2)| ≤ 1 ∧ f z = 0 :=
      hFinite.mem_toFinset.mp hz
    have hFiniteOrder : analyticOrderAt f z ≠ ⊤ :=
      hAnalytic.analyticOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt 0).isPreconnected
        hCenterMem hzSlice.1 hCenterOrder
    have hNonzero : analyticOrderNatAt f z ≠ 0 := by
      intro hZero
      apply (hAnalytic z hzSlice.1).analyticOrderAt_ne_zero.mpr hzSlice.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hFiniteOrder, hZero, Nat.cast_zero]
    change (1 : ℝ) ≤ (analyticOrderNatAt f z : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNonzero
  have hCard : (zeros.card : ℝ) ≤ countBound := calc
    _ = ∑ _z ∈ zeros, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ zeros, weight z := Finset.sum_le_sum hWeight
    _ = ∑ᶠ z : ℂ, slice.indicator weight z := hCountEq.symm
    _ ≤ countBound := hCount
  have hCountNonnegative : 0 ≤ countBound := (by positivity : (0 : ℝ) ≤ zeros.card).trans hCard
  have hGapBound : (1 : ℝ) / (2 * (1 + countBound)) ≤ 1 / (2 * (1 + (zeros.card : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hCard])
  obtain ⟨u, hu, hNear⟩ := exists_goodHeight zeros Complex.im T
  refine ⟨u, hu, ?_⟩
  intro z hzPos hzLt hzZero
  by_cases hz : z ∈ slice
  · exact hGapBound.trans (hNear z (hFinite.mem_toFinset.mpr hz))
  · have hFar : 1 < |z.im - (T + 1 / 2)| := by
      apply lt_of_not_ge
      intro h
      exact hz ⟨hzPos, hzLt, h, hzZero⟩
    have hMid : |u - (T + 1 / 2)| ≤ 1 / 2 := by
      have huLower := hu.1
      have huUpper := hu.2
      exact abs_le.mpr ⟨by linarith only [huLower], by linarith only [huUpper]⟩
    have hTri : |z.im - (T + 1 / 2)| ≤ |u - z.im| + |u - (T + 1 / 2)| := by
      simpa only [abs_sub_comm z.im u] using abs_sub_le z.im u (T + 1 / 2)
    have hFarGap : (1 / 2 : ℝ) ≤ |u - z.im| := by linarith only [hFar, hMid, hTri]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith only [hCountNonnegative])).trans hFarGap

end Goldbach

namespace Goldbach

open Filter Set

theorem exists_height_sequences (P : ℝ → Prop)
    (hFind : ∀ T : ℝ, (1 ≤ T ∨ T + 1 ≤ -1) → ∃ u ∈ Icc T (T + 1), P u) :
    ∃ lower upper : ℕ → ℝ,
      (∀ n : ℕ, lower n ∈ Icc (-(n : ℝ) - 2) (-(n : ℝ) - 1) ∧
        upper n ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      (∀ n, lower n < 0 ∧ 0 < upper n) ∧ (∀ n, P (lower n) ∧ P (upper n)) ∧
      Tendsto lower atTop atBot ∧ Tendsto upper atTop atTop ∧
      Tendsto (fun n ↦ |lower n|) atTop atTop ∧ Tendsto (fun n ↦ |upper n|) atTop atTop := by
  classical
  have hFindLower (n : ℕ) : ∃ u ∈ Icc (-(n : ℝ) - 2) (-(n : ℝ) - 1), P u := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hT : -(n : ℝ) - 2 + 1 ≤ -1 := by linarith only [hn]
    simpa only [show -(n : ℝ) - 2 + 1 = -(n : ℝ) - 1 by ring] using
      hFind (-(n : ℝ) - 2) (Or.inr hT)
  have hFindUpper (n : ℕ) : ∃ u ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2), P u := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hT : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using
      hFind ((n : ℝ) + 1) (Or.inl hT)
  choose lower hLower hLowerP using hFindLower
  choose upper hUpper hUpperP using hFindUpper
  have hSign (n : ℕ) : lower n < 0 ∧ 0 < upper n := by
    have hn : (0 : ℝ) ≤ n := by positivity
    exact ⟨by linarith only [(hLower n).2, hn], by linarith only [(hUpper n).1, hn]⟩
  have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hNegNat : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hNat
  have hLowerLim : Tendsto lower atTop atBot :=
    tendsto_atBot_mono (fun n ↦ by linarith only [(hLower n).2]) hNegNat
  have hUpperLim : Tendsto upper atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith only [(hUpper n).1]) hNat
  have hLowerAbs : Tendsto (fun n ↦ |lower n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    rw [abs_of_nonpos (hSign n).1.le]
    linarith only [(hLower n).2]
  have hUpperAbs : Tendsto (fun n ↦ |upper n|) atTop atTop := by
    apply tendsto_atTop_mono _ hNat
    intro n
    rw [abs_of_pos (hSign n).2]
    linarith only [(hUpper n).1]
  exact ⟨lower, upper, fun n ↦ ⟨hLower n, hUpper n⟩, hSign,
    fun n ↦ ⟨hLowerP n, hUpperP n⟩, hLowerLim, hUpperLim, hLowerAbs, hUpperAbs⟩

end Goldbach

namespace Goldbach

open Complex Set

noncomputable section

def logHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (2 * (q : ℝ) * (2 + |t|))

def contourLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) z + principalFlag χ / (z - 1)

def UniformDirichletLogDerivative (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t d : ℝ),
    σ ∈ Icc (9 / 20 : ℝ) 2 → 0 < d →
    (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖((σ : ℂ) + (t : ℂ) * I) - ρ‖) →
    ‖logDeriv (regularizedL χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * logHeight q t * (1 + d⁻¹)

theorem logHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ logHeight q t := by
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have harg : (4 : ℝ) ≤ 2 * (q : ℝ) * (2 + |t|) := calc
    _ ≤ 2 * (1 : ℝ) * (2 + |t|) := by linarith [abs_nonneg t]
    _ ≤ _ := by gcongr
  exact hlog4.trans (Real.log_le_log (by norm_num) harg)

private theorem logHeight_compare {q : ℕ} [NeZero q] {t u : ℝ} (ht : |t| ≤ |u| + 1) :
    logHeight q t ≤ 2 * logHeight q u := by
  let v : ℝ := 2 * (q : ℝ) * (2 + |u|)
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hv : 2 ≤ v := by
    calc
      _ ≤ 2 * (1 : ℝ) * (2 + |u|) := by linarith [abs_nonneg u]
      _ ≤ _ := by dsimp [v]; gcongr
  have hx : 2 * (q : ℝ) * (2 + |t|) ≤ v ^ 2 := by
    have ht' : 2 + |t| ≤ 2 * (2 + |u|) := by linarith [abs_nonneg u]
    calc
      _ ≤ 2 * (q : ℝ) * (2 * (2 + |u|)) := by gcongr
      _ = 2 * v := by dsimp [v]; ring
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ v - 2 by linarith)]
  have hh := Real.log_le_log (show 0 < 2 * (q : ℝ) * (2 + |t|) by positivity) hx
  rw [Real.log_pow] at hh
  simpa only [logHeight, v, Nat.cast_ofNat] using hh

private theorem norm_flag_pole_le {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℂ} {d : ℝ}
    (hd : 0 < d) (hz : d ≤ ‖z - 1‖) : ‖principalFlag χ / (z - 1)‖ ≤ 1 / d := by
  have hFlag : ‖principalFlag χ‖ ≤ 1 := by
    by_cases hχ : χ = 1 <;> simp [principalFlag, hχ]
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hFlag (norm_nonneg _)).trans (one_div_le_one_div_of_le hd hz)

set_option maxHeartbeats 6000000 in
theorem contourLog_continuous_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hGRH : GRH1) (hq1 : q = 1) : Continuous (fun t : ℝ => contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
  have hcz : Continuous z := continuous_const.add (continuous_ofReal.mul continuous_const)
  have hzr (t : ℝ) : (z t).re = 9 / 20 := by
    simp only [z, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  have hnz (t : ℝ) : regularizedL χ (z t) ≠ 0 := by
    intro hz
    have h := regularizedL_zero_line χ hGRH hq1 (by rw [hzr]; norm_num) hz
    rw [hzr] at h
    norm_num at h
  have ho (t : ℝ) : z t - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := congrArg Complex.re h
    rw [hzr, one_re] at hh
    norm_num at hh
  apply continuous_iff_continuousAt.mpr
  intro t
  have hF : AnalyticAt ℂ (regularizedL χ) (z t) :=
    analytic_regularizedL χ (z t) (Set.mem_univ _)
  have hLog : AnalyticAt ℂ (logDeriv (regularizedL χ)) (z t) := by
    simpa only [logDeriv, Pi.div_apply] using hF.deriv.div hF (hnz t)
  have hDen : AnalyticAt ℂ (fun w : ℂ => w - 1) (z t) := analyticAt_id.sub analyticAt_const
  have hFlag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) (z t) := analyticAt_const
  have hPole : AnalyticAt ℂ (fun w : ℂ => principalFlag χ / (w - 1)) (z t) :=
    hFlag.div hDen (ho t)
  have hContour : AnalyticAt ℂ (contourLog χ) (z t) := hLog.neg.add hPole
  exact hContour.continuousAt.comp (hcz.continuousAt : ContinuousAt z t)

set_option maxHeartbeats 2000000 in
theorem dirichlet_contour_bounds (hGRH : GRH1)
    (hLocal : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀ (χ : DirichletCharacter ℂ q),
      (∀ t : ℝ, ‖contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * logHeight q t) ∧
      ∀ T : ℝ, (1 ≤ T ∨ T + 1 ≤ -1) → ∃ u ∈ Icc T (T + 1),
        (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → ρ.im ≠ u) ∧
        (∀ σ ∈ Icc (9 / 20 : ℝ) 2,
          ‖contourLog χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ B * logHeight q u ^ 2) := by
  obtain ⟨C, hC, hLog⟩ := hLocal
  obtain ⟨K, hK, hCount⟩ := uniform_dirichlet_zero_slice hGRH
  refine ⟨21 * C + 2, C * (3 + 4 * K) + 1, by positivity, by positivity, ?_⟩
  intro q _ hq1 χ
  constructor
  · intro t
    let z : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
    have hzr : z.re = 9 / 20 := by simp [z]
    have hDist (ρ : ℂ) (hρ : 0 < ρ.re) (hz : regularizedL χ ρ = 0) :
        (1 / 20 : ℝ) ≤ ‖z - ρ‖ := by
      have h := Complex.re_le_norm (ρ - z)
      rw [sub_re, regularizedL_zero_line χ hGRH hq1 hρ hz, hzr, norm_sub_rev] at h
      norm_num at h ⊢
      exact h
    have hPole : (1 / 2 : ℝ) ≤ ‖z - 1‖ := by
      have h := Complex.re_le_norm (1 - z)
      rw [sub_re, one_re, hzr, norm_sub_rev] at h
      linarith
    have hld := hLog q χ (9 / 20) t (1 / 20) (by norm_num) (by norm_num) hDist
    have hpd := norm_flag_pole_le χ (by norm_num) hPole
    have hl := logHeight_ge_one q t
    calc
      _ ≤ ‖logDeriv (regularizedL χ) z‖ + ‖principalFlag χ / (z - 1)‖ := by
        simpa only [contourLog, norm_neg, z] using
          norm_add_le (-logDeriv (regularizedL χ) z) (principalFlag χ / (z - 1))
      _ ≤ C * logHeight q t * (1 + (1 / 20 : ℝ)⁻¹) + 1 / (1 / 2 : ℝ) := add_le_add hld hpd
      _ ≤ _ := by norm_num; nlinarith
  · intro T hT
    let middle := T + 1 / 2
    let Cnt := K * logHeight q middle
    have hCnt : 0 ≤ Cnt := mul_nonneg hK.le (zero_le_one.trans (logHeight_ge_one q middle))
    obtain ⟨hFinit, hN⟩ := hCount q hq1 χ middle
    have hF := (analytic_regularizedL χ).mono (subset_univ {z : ℂ | 0 < z.re})
    have hAn := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (norm_regularizedL_anchor χ middle))
    obtain ⟨u, hu, hGap⟩ := exists_goodHeight_of_stripCount T Cnt hF hAn hFinit hN
    let d := 1 / (2 * (1 + Cnt))
    have hd : 0 < d := by dsimp [d]; positivity
    have sep (ρ : ℂ) (hρ : 0 < ρ.re) (hZ : regularizedL χ ρ = 0) : d ≤ |u - ρ.im| :=
      hGap ρ hρ (by rw [regularizedL_zero_line χ hGRH hq1 hρ hZ]; norm_num) hZ
    refine ⟨u, hu, ?_, ?_⟩
    · intro ρ hρ hZ hEq
      have e := sep ρ hρ hZ
      rw [hEq, sub_self, abs_zero] at e
      exact (not_le_of_gt hd) e
    · intro σ hσ
      let z : ℂ := (σ : ℂ) + (u : ℂ) * I
      have huAbs : 1 ≤ |u| := by
        rcases hT with ht | ht
        · have hu1 := ht.trans hu.1
          rwa [abs_of_nonneg (by linarith)]
        · have hu1 := hu.2.trans ht
          rw [abs_of_nonpos (by linarith)]
          linarith
      have hdist (ρ : ℂ) (hρ : 0 < ρ.re) (hZ : regularizedL χ ρ = 0) : d ≤ ‖z - ρ‖ :=
        (sep ρ hρ hZ).trans (by simpa [z] using Complex.abs_im_le_norm (z - ρ))
      have hPole : 1 ≤ ‖z - 1‖ := huAbs.trans
        (by simpa [z] using Complex.abs_im_le_norm (z - 1))
      have hdiff : |middle - u| ≤ 1 / 2 :=
        abs_le.mpr ⟨by dsimp [middle]; linarith [hu.2], by dsimp [middle]; linarith [hu.1]⟩
      have hmabs : |middle| ≤ |u| + 1 := calc
        _ = |(middle - u) + u| := by rw [sub_add_cancel]
        _ ≤ |middle - u| + |u| := abs_add_le _ _
        _ ≤ _ := by linarith
      have hB : Cnt ≤ 2 * K * logHeight q u := calc
        _ ≤ K * (2 * logHeight q u) := mul_le_mul_of_nonneg_left (logHeight_compare hmabs) hK.le
        _ = _ := by ring
      have hInv : 1 + d⁻¹ = 3 + 2 * Cnt := by dsimp [d]; rw [one_div, inv_inv]; ring
      have hl := logHeight_ge_one q u
      have hFactor : 1 + d⁻¹ ≤ (3 + 4 * K) * logHeight q u := by
        rw [hInv]
        nlinarith only [hB, hl]
      have hSq : 1 ≤ logHeight q u ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ logHeight q u - 1 by linarith)
          (show 0 ≤ logHeight q u by linarith)]
      have hld := hLog q χ σ u d hσ hd hdist
      have hpd := norm_flag_pole_le χ (by norm_num) hPole
      calc
        _ ≤ ‖logDeriv (regularizedL χ) z‖ + ‖principalFlag χ / (z - 1)‖ := by
          simpa only [contourLog, norm_neg, z] using
            norm_add_le (-logDeriv (regularizedL χ) z) (principalFlag χ / (z - 1))
        _ ≤ C * logHeight q u * (1 + d⁻¹) + 1 / 1 := add_le_add hld hpd
        _ ≤ C * logHeight q u * ((3 + 4 * K) * logHeight q u) + 1 / 1 :=
          (add_le_add (mul_le_mul_of_nonneg_left hFactor
            (mul_nonneg hC.le (zero_le_one.trans hl))) le_rfl)
        _ ≤ _ := by nlinarith only [hSq]

end

end Goldbach

namespace Goldbach

open Complex DirichletCharacter MeromorphicOn Set

theorem regularizedL_ne_zero_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    regularizedL χ 1 ≠ 0 := by
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using LFunctionTrivChar₁_apply_one_ne_zero q
  · simpa only [regularizedL, hχ, ite_false] using LFunction_apply_one_ne_zero hχ

theorem regularizedL_analyticOrder_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : analyticOrderAt (regularizedL χ) z ≠ ⊤ := by
  let c : ℂ := ⟨2, 0⟩
  have hC : regularizedL χ c ≠ 0 := norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 4).trans_le (norm_regularizedL_anchor χ 0))
  have hOrderC : analyticOrderAt (regularizedL χ) c ≠ ⊤ := by
    rw [((analytic_regularizedL χ) c (mem_univ c)).analyticOrderAt_eq_zero.mpr hC]
    exact ENat.zero_ne_top
  exact (analytic_regularizedL χ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ c) (mem_univ z) hOrderC

theorem regularizedL_analyticOrderNatAt_pos_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    0 < analyticOrderNatAt (regularizedL χ) z ↔ regularizedL χ z = 0 := by
  constructor
  · intro h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro hzero
    apply ((analytic_regularizedL χ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z), hzero, Nat.cast_zero]

theorem regularizedL_divisor_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor (regularizedL χ) U z = (analyticOrderNatAt (regularizedL χ) z : ℤ) := by
  rw [((analytic_regularizedL χ).mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z),
    ENat.map_natCast, WithTop.untop₀_coe]

theorem exists_regularizedL_contourZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hGRH : GRH1) (hq1 : q = 1) (lower upper : ℝ)
    (hLower : ∀ z : ℂ, 0 < z.re → regularizedL χ z = 0 → z.im ≠ lower)
    (hUpper : ∀ z : ℂ, 0 < z.re → regularizedL χ z = 0 → z.im ≠ upper) :
    ∃ S : Finset ℂ,
      (∀ z : ℂ, z ∈ S ↔ z ∈ (Icc (9 / 20 : ℝ) 2 ×ℂ Icc lower upper) ∧ regularizedL χ z = 0) ∧
      (∀ z ∈ S, z ∈ (Ioo (9 / 20 : ℝ) 2 ×ℂ Ioo lower upper)) ∧
      (∀ z ∈ S, 0 < z.re ∧ regularizedL χ z = 0) := by
  classical
  let rectangle : Set ℂ := Icc (9 / 20 : ℝ) 2 ×ℂ Icc lower upper
  let zeros : Set ℂ := {z | z ∈ rectangle ∧ regularizedL χ z = 0}
  have hCompact : IsCompact rectangle := isCompact_Icc.reProdIm isCompact_Icc
  have hSupportFinite := (divisor (regularizedL χ) rectangle).finiteSupport hCompact
  have hFinite : zeros.Finite := by
    apply hSupportFinite.subset
    intro z hz
    change divisor (regularizedL χ) rectangle z ≠ 0
    rw [regularizedL_divisor_apply χ hz.1]
    exact_mod_cast ((regularizedL_analyticOrderNatAt_pos_iff χ z).mpr hz.2).ne'
  let S := hFinite.toFinset
  have hPos (z : ℂ) (hz : z ∈ S) : 0 < z.re ∧ regularizedL χ z = 0 := by
    have hmem := hFinite.mem_toFinset.mp hz
    exact ⟨(by norm_num : (0 : ℝ) < 9 / 20).trans_le (mem_reProdIm.mp hmem.1).1.1, hmem.2⟩
  refine ⟨S, fun z ↦ hFinite.mem_toFinset, ?_, hPos⟩
  intro z hz
  have hmem := hFinite.mem_toFinset.mp hz
  have him := (mem_reProdIm.mp hmem.1).2
  have hzPos := hPos z hz
  have hre := regularizedL_zero_line χ hGRH hq1 hzPos.1 hzPos.2
  apply mem_reProdIm.mpr
  refine ⟨?_, ?_⟩
  · change (9 / 20 : ℝ) < z.re ∧ z.re < 2
    rw [hre]
    norm_num
  · exact ⟨lt_of_le_of_ne him.1 (hLower z hzPos.1 hzPos.2).symm,
      lt_of_le_of_ne him.2 (hUpper z hzPos.1 hzPos.2)⟩

end Goldbach

namespace Goldbach

private theorem one_le_log_four_for_tail : (1 : ℝ) ≤ Real.log 4 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := calc
    _ = 1 - (2 : ℝ)⁻¹ := by norm_num
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
    convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0) using 1
    norm_num
  linarith only [hlog2, hlog4]

private theorem log_tail_step {q j : ℝ} (hq : 1 ≤ q) (hj : 1 ≤ j) :
    Real.log (2 * q * (j + 1)) / j ^ 2 ≤
      2 * ((Real.log (2 * q * j) + 2) / j - (Real.log (2 * q * (j + 1)) + 2) / (j + 1)) := by
  have hq₀ : 0 < q := by linarith only [hq]
  have hj₀ : 0 < j := by linarith only [hj]
  have hNext₀ : 0 < j + 1 := by linarith only [hj]
  let L := Real.log (2 * q * j)
  let Lnext := Real.log (2 * q * (j + 1))
  have hJump : Lnext - L ≤ 1 / j := by
    have hRatio : (2 * q * (j + 1)) / (2 * q * j) = (j + 1) / j := by
      field_simp [hq₀.ne', hj₀.ne']
    dsimp [L, Lnext]
    rw [← Real.log_div (by positivity) (by positivity), hRatio]
    calc
      _ ≤ (j + 1) / j - 1 := Real.log_le_sub_one_of_pos (div_pos hNext₀ hj₀)
      _ = _ := by field_simp [hj₀.ne']; ring
  have hJumpOne : Lnext - L ≤ 1 := hJump.trans ((div_le_one hj₀).mpr hj)
  have hScaledJump : (Lnext - L) * j ≤ 1 := (le_div_iff₀ hj₀).mp hJump
  have hNumerator : Lnext ≤ (L + 2) * (j + 1) - j * (Lnext + 2) := by
    nlinarith only [hJumpOne, hScaledJump]
  have hDrop : Lnext / (j * (j + 1)) ≤ (L + 2) / j - (Lnext + 2) / (j + 1) := calc
    _ ≤ ((L + 2) * (j + 1) - j * (Lnext + 2)) / (j * (j + 1)) :=
      div_le_div_of_nonneg_right hNumerator (mul_pos hj₀ hNext₀).le
    _ = _ := (div_sub_div (L + 2) (Lnext + 2) hj₀.ne' hNext₀.ne').symm
  have hNextLog : 0 ≤ Lnext := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by linarith only [hq]) (by linarith only [hj]))
  have hDen : j * (j + 1) ≤ 2 * j ^ 2 := calc
    _ ≤ j * (2 * j) := mul_le_mul_of_nonneg_left (by linarith only [hj]) hj₀.le
    _ = _ := by ring
  change Lnext / j ^ 2 ≤ 2 * ((L + 2) / j - (Lnext + 2) / (j + 1))
  calc
    _ = (2 * Lnext) / (2 * j ^ 2) := by field_simp [hj₀.ne']
    _ ≤ (2 * Lnext) / (j * (j + 1)) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hNextLog) (mul_pos hj₀ hNext₀) hDen
    _ = 2 * (Lnext / (j * (j + 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDrop (by norm_num)

theorem log_tail_Icc_le {q : ℝ} (hq : 1 ≤ q) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Icc N M, Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2) ≤
      6 * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
  let F (k : ℕ) := (Real.log (2 * q * ((k : ℝ) + 1)) + 2) / ((k : ℝ) + 1)
  have hstep (k : ℕ) : Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2 ≤
      2 * (F k - F (k + 1)) := by
    have hj : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      linarith only [(by positivity : (0 : ℝ) ≤ (k : ℝ))]
    simpa only [F, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      log_tail_step hq hj
  have hTel : (∑ k ∈ Finset.Icc N M, (F k - F (k + 1))) = F N - F (M + 1) := by
    simpa only [neg_sub_neg] using Finset.sum_Icc_sub hNM (fun k ↦ -F k)
  have hFend : 0 ≤ F (M + 1) := by
    have hDen : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) + 1 := by
      linarith only [(by positivity : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))]
    have hLog : 0 ≤ Real.log (2 * q * (((M + 1 : ℕ) : ℝ) + 1)) := Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le (by linarith only [hq]) hDen)
    dsimp [F]
    exact div_nonneg (add_nonneg hLog (by norm_num)) (by positivity)
  have hDenN : (2 : ℝ) ≤ (N : ℝ) + 1 := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hNR]
  have hArgN : (4 : ℝ) ≤ 2 * q * ((N : ℝ) + 1) := calc
    _ = 2 * 2 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith only [hq]) hDenN (by norm_num) (by linarith only [hq])
  have hLogN : 1 ≤ Real.log (2 * q * ((N : ℝ) + 1)) :=
    one_le_log_four_for_tail.trans (Real.log_le_log (by norm_num) hArgN)
  calc
    _ ≤ ∑ k ∈ Finset.Icc N M, 2 * (F k - F (k + 1)) := Finset.sum_le_sum fun k _ ↦ hstep k
    _ = 2 * (F N - F (M + 1)) := by rw [← Finset.mul_sum, hTel]
    _ ≤ 2 * F N := mul_le_mul_of_nonneg_left (sub_le_self _ hFend) (by norm_num)
    _ = (2 * (Real.log (2 * q * ((N : ℝ) + 1)) + 2)) / ((N : ℝ) + 1) := by
      dsimp [F]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hLogN]) (by positivity)

theorem weighted_log_tail_Icc_le {q K : ℝ} (hq : 1 ≤ q) (hK : 0 ≤ K)
    (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc N M, w k ≤ K * Real.log (2 * q * ((k : ℝ) + 2))) :
    (∑ k ∈ Finset.Icc N M, w k / ((k : ℝ) + 1) ^ 2) ≤
      6 * K * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc N M, (K * Real.log (2 * q * ((k : ℝ) + 2))) / ((k : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right (hw k hk) (sq_nonneg _)
    _ = K * (∑ k ∈ Finset.Icc N M, Real.log (2 * q * ((k : ℝ) + 2)) / ((k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      simp only [mul_div_assoc]
    _ ≤ K * (6 * Real.log (2 * q * ((N : ℝ) + 1)) / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (log_tail_Icc_le hq N M hN hNM) hK
    _ = _ := by ring

end Goldbach

namespace Goldbach

private theorem half_bucket_le_norm {s : ℂ} (hre : (1 / 2 : ℝ) ≤ s.re) :
    ((Nat.floor |s.im| : ℝ) + 1) / 2 ≤ ‖s‖ := by
  let k := Nat.floor |s.im|
  change ((k : ℝ) + 1) / 2 ≤ ‖s‖
  have hhalf := hre.trans (Complex.re_le_norm s)
  have hfloor : (k : ℝ) ≤ ‖s‖ :=
    (Nat.floor_le (abs_nonneg _)).trans (Complex.abs_im_le_norm s)
  by_cases hk : k = 0
  · simpa only [hk, Nat.cast_zero, zero_add] using hhalf
  · have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith only [hk₁, hfloor]

private theorem sqrt_le_self_for_smoothing {x : ℝ} (hx : 2 ≤ x) : Real.sqrt x ≤ x := by
  refine Real.sqrt_le_iff.mpr ⟨by linarith only [hx], ?_⟩
  nlinarith only [hx, sq_nonneg (x - 1)]

theorem norm_smoothed_kernel_le_bucket {x : ℝ} (hx : 2 ≤ x) {s : ℂ}
    (hre : s.re = 1 / 2) :
    let k := Nat.floor |s.im|
    ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖ ≤ 4 * Real.sqrt x / ((k : ℝ) + 1) ∧
    ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖ ≤ 20 * x / ((k : ℝ) + 1) ^ 2 := by
  intro k
  let h := Real.sqrt x
  let d := ((k : ℝ) + 1) / 2
  have hx₀ : 0 < x := by linarith only [hx]
  have hh : 0 < h := Real.sqrt_pos.mpr hx₀
  have hhSq : h ^ 2 = x := Real.sq_sqrt hx₀.le
  have hSelf : h ≤ x := sqrt_le_self_for_smoothing hx
  have hd : 0 < d := by dsimp [d]; positivity
  have hSqrtSum : Real.sqrt (x + h) ≤ 2 * h := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith only [hx, hSelf, hhSq]
  have hsDen : d ≤ ‖s‖ := half_bucket_le_norm (le_of_eq hre.symm)
  have hsNextDen : d ≤ ‖s + 1‖ := by
    have hreNext : (1 / 2 : ℝ) ≤ (s + 1).re := by
      rw [Complex.add_re, Complex.one_re, hre]
      norm_num
    simpa only [d, k, Complex.add_im, Complex.one_im, add_zero] using
      half_bucket_le_norm hreNext
  have hks : ‖GoldbachSmoothing.kernel x h s‖ ≤ Real.sqrt (x + h) / ‖s‖ := by
    have hs : 0 < s.re := by rw [hre]; norm_num
    simpa only [hre, ← Real.sqrt_eq_rpow] using GoldbachSmoothing.norm_kernel_le hx₀ hh hs
  constructor
  · calc
      _ ≤ Real.sqrt (x + h) / ‖s‖ := hks
      _ ≤ 2 * h / ‖s‖ := div_le_div_of_nonneg_right hSqrtSum (norm_nonneg _)
      _ ≤ 2 * h / d := div_le_div_of_nonneg_left (by positivity) hd hsDen
      _ = _ := by dsimp [d]; rw [div_div_eq_mul_div]; ring
  · have hPowSum : (x + h) ^ ((1 / 2 : ℝ) + 1) + x ^ ((1 / 2 : ℝ) + 1) ≤ 5 * x * h := calc
      _ = Real.sqrt (x + h) * (x + h) + h * x := by
        rw [Real.rpow_add_one (add_pos hx₀ hh).ne', Real.rpow_add_one hx₀.ne', ← Real.sqrt_eq_rpow,
          ← Real.sqrt_eq_rpow]
      _ ≤ (2 * h) * (2 * x) + h * x :=
        (add_le_add (mul_le_mul hSqrtSum (by linarith only [hSelf]) (by positivity) (by positivity)) le_rfl)
      _ = _ := by ring
    have hDen : h * d ^ 2 ≤ h * ‖s‖ * ‖s + 1‖ := calc
      h * d ^ 2 = h * (d * d) := by rw [pow_two]
      _ ≤ h * (‖s‖ * ‖s + 1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsDen hsNextDen hd.le (norm_nonneg _)) hh.le
      _ = _ := by ring
    calc
      _ ≤ ((x + h) ^ ((1 / 2 : ℝ) + 1) + x ^ ((1 / 2 : ℝ) + 1)) /
          (h * ‖s‖ * ‖s + 1‖) := by
        simpa only [hre] using GoldbachSmoothing.norm_kernel_le_tail hx₀ hh (s := s)
      _ ≤ (5 * x * h) / (h * ‖s‖ * ‖s + 1‖) :=
        div_le_div_of_nonneg_right hPowSum (by positivity)
      _ ≤ (5 * x * h) / (h * d ^ 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen
      _ = _ := by
        have hk₀ : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        dsimp [d]
        field_simp [hh.ne', hk₀.ne']
        ring

theorem smoothed_zero_sum_le {q x K : ℝ} (hq : 1 ≤ q) (hx : 2 ≤ x) (hK : 0 ≤ K)
    (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ s ∈ S, 0 ≤ m s)
    (hre : ∀ s ∈ S, s.re = 1 / 2)
    (hbuckets : ∀ k : ℕ,
      (∑ s ∈ S.filter (fun s ↦ Nat.floor |s.im| = k), m s) ≤
        K * Real.log (2 * q * ((k : ℝ) + 2))) :
    (∑ s ∈ S, m s * ‖GoldbachSmoothing.kernel x (Real.sqrt x) s‖) ≤
      256 * K * Real.sqrt x * Real.log (2 * q * x) ^ 2 := by
  classical
  let h := Real.sqrt x
  let N := Nat.floor h
  let height (s : ℂ) := Nat.floor |s.im|
  let M := max N (S.sup height)
  let mass (k : ℕ) := ∑ s ∈ S.filter (fun s ↦ height s = k), m s
  let weight (k : ℕ) : ℝ :=
    if k < N then 4 * h / ((k : ℝ) + 1) else 20 * x / ((k : ℝ) + 1) ^ 2
  let L := Real.log (2 * q * x)
  have hx₀ : 0 < x := by linarith only [hx]
  have hq₀ : 0 < q := by linarith only [hq]
  have hh : 0 < h := Real.sqrt_pos.mpr hx₀
  have hh₁ : 1 ≤ h := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx₀.le).mpr
    norm_num
    linarith only [hx]
  have hhLe : h ≤ x := sqrt_le_self_for_smoothing hx
  have hN : 1 ≤ N := (Nat.one_le_floor_iff h).mpr hh₁
  have hNLe : (N : ℝ) ≤ x := (Nat.floor_le hh.le).trans hhLe
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hNM : N ≤ M := le_max_left _ _
  have hBUpper : ∀ k : ℕ, mass k ≤ K * Real.log (2 * q * ((k : ℝ) + 2)) := hbuckets
  have hFourW : (4 : ℝ) ≤ 2 * q * x := calc
    _ = 2 * 2 := by norm_num
    _ ≤ _ := mul_le_mul (by linarith only [hq]) hx (by norm_num) (by positivity)
  have hOneL : 1 ≤ L := by
    have hTwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hTwo
    have hFour : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith only [hTwo]
    exact hFour.trans (Real.log_le_log (by norm_num) hFourW)
  have hL₀ : 0 ≤ L := zero_le_one.trans hOneL
  have hLsq : L ≤ L ^ 2 := by
    rw [pow_two]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneL hL₀
  have hLog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith only [hFourW])
  have hLogScaled {y : ℝ} (hy₀ : 0 < y) (hy : y ≤ 2 * x) : Real.log (2 * q * y) ≤ 2 * L := calc
    _ ≤ Real.log (2 * q * (2 * x)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hy (by positivity))
    _ = Real.log 2 + L := by
      rw [show 2 * q * (2 * x) = 2 * (2 * q * x) by ring, Real.log_mul (by norm_num) (by positivity)]
    _ ≤ _ := by linarith only [hLog2]
  have hLowLog (k : ℕ) (hk : k < N) : Real.log (2 * q * ((k : ℝ) + 2)) ≤ 2 * L := by
    have hkR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
    exact hLogScaled (by positivity) (by linarith only [hNLe, hkR, hx])
  have hLogN : Real.log (N : ℝ) ≤ L :=
    Real.log_le_log hNpos (hNLe.trans (le_mul_of_one_le_left hx₀.le (by linarith only [hq])))
  have hHarmonic : (harmonic N : ℝ) ≤ 2 * L :=
    (harmonic_le_one_add_log N).trans (by linarith only [hLogN, hOneL])
  have hHarmonicEq : (harmonic N : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp only [Nat.cast_add, Nat.cast_one, one_div]
  have hLow : (∑ k ∈ Finset.range N, mass k * (4 * h / ((k : ℝ) + 1))) ≤ 16 * K * h * L ^ 2 := calc
    _ ≤ ∑ k ∈ Finset.range N, (K * (2 * L)) * (4 * h / ((k : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (hBUpper k).trans (mul_le_mul_of_nonneg_left (hLowLog k (Finset.mem_range.mp hk)) hK)
    _ = (8 * K * h * L) * (harmonic N : ℝ) := by
      rw [hHarmonicEq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ (8 * K * h * L) * (2 * L) := mul_le_mul_of_nonneg_left hHarmonic (by positivity)
    _ = _ := by ring
  let LN := Real.log (2 * q * ((N : ℝ) + 1))
  have hLN₀ : 0 ≤ LN := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith only [hq])
    (by linarith only [(by positivity : (0 : ℝ) ≤ (N : ℝ))]))
  have hLN : LN ≤ 2 * L := hLogScaled (by positivity) (by linarith only [hNLe, hx])
  have hXdiv : x / ((N : ℝ) + 1) ≤ h := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr
    calc
      x = h * h := (Real.mul_self_sqrt hx₀.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one h).le hh.le
  have hHigh : (∑ k ∈ Finset.Icc N M, mass k * (20 * x / ((k : ℝ) + 1) ^ 2)) ≤
      240 * K * h * L ^ 2 := calc
    _ = (20 * x) * (∑ k ∈ Finset.Icc N M, mass k / ((k : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ (20 * x) * (6 * K * LN / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left
      (weighted_log_tail_Icc_le hq hK N M hN hNM mass fun k _ ↦ hBUpper k) (by positivity)
    _ = 120 * K * (x / ((N : ℝ) + 1)) * LN := by ring
    _ ≤ 120 * K * h * LN :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXdiv (by positivity)) hLN₀
    _ ≤ (120 * K * h) * (2 * L) := mul_le_mul_of_nonneg_left hLN (by positivity)
    _ = (240 * K * h) * L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hMaps : ∀ s ∈ S, height s ∈ Finset.range (M + 1) := by
    intro s hs
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := height) hs).trans (le_max_right _ _))
  have hSplit : (∑ k ∈ Finset.range (M + 1), mass k * weight k) =
      (∑ k ∈ Finset.range N, mass k * (4 * h / ((k : ℝ) + 1))) +
        (∑ k ∈ Finset.Icc N M, mass k * (20 * x / ((k : ℝ) + 1) ^ 2)) := by
    have hIco : Finset.Ico N M.succ = Finset.Icc N M := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
    rw [← Finset.sum_range_add_sum_Ico (fun k ↦ mass k * weight k) (Nat.le_succ_of_le hNM),
      hIco]
    congr 1
    · exact Finset.sum_congr rfl fun k hk ↦ by simp only [weight, ite_eq_left (Finset.mem_range.mp hk)]
    · exact Finset.sum_congr rfl fun k hk ↦ by
        simp only [weight, ite_eq_right (not_lt_of_ge (Finset.mem_Icc.mp hk).1)]
  change (∑ s ∈ S, m s * ‖GoldbachSmoothing.kernel x h s‖) ≤ 256 * K * h * L ^ 2
  calc
    _ ≤ ∑ s ∈ S, m s * weight (height s) := by
      refine Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left ?_ (hm s hs)
      have hTerm := norm_smoothed_kernel_le_bucket hx (hre s hs)
      by_cases hk : height s < N
      · simpa only [weight, ite_eq_left hk] using hTerm.1
      · simpa only [weight, ite_eq_right hk] using hTerm.2
    _ = ∑ k ∈ Finset.range (M + 1),
        ∑ s ∈ S.filter (fun s ↦ height s = k), m s * weight (height s) :=
      (Finset.sum_fiberwise_of_maps_to hMaps (fun s ↦ m s * weight (height s))).symm
    _ = ∑ k ∈ Finset.range (M + 1), mass k * weight k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      unfold mass
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s hs ↦ by rw [(Finset.mem_filter.mp hs).2]
    _ = _ := hSplit
    _ ≤ 16 * K * h * L ^ 2 + 240 * K * h * L ^ 2 := add_le_add hLow hHigh
    _ = _ := by ring

end Goldbach

namespace Goldbach

open Complex Set
open scoped BigOperators

theorem uniform_smoothed_dirichlet_residues (hGRH : GRH1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀ (χ : DirichletCharacter ℂ q)
      (x : ℝ) (S : Finset ℂ), 2 ≤ x →
      (∀ ρ ∈ S, 0 < ρ.re ∧ regularizedL χ ρ = 0) →
      ‖∑ ρ ∈ S, (analyticOrderNatAt (regularizedL χ) ρ : ℂ) *
          GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ ≤
        D * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 := by
  classical
  obtain ⟨K, hK, hCount⟩ := uniform_dirichlet_zero_slice hGRH
  refine ⟨1024 * K, by positivity, ?_⟩
  intro q _ hq1 χ x S hx hS
  let F := regularizedL χ
  let m (z : ℂ) : ℝ := analyticOrderNatAt F z
  have hm (z : ℂ) : 0 ≤ m z := by dsimp [m]; positivity
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hLine : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ =>
    regularizedL_zero_line χ hGRH hq1 (hS ρ hρ).1 (hS ρ hρ).2
  have hCount' (t : ℝ) :
      (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F t), m ρ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
    obtain ⟨hfin, hbound⟩ := hCount q hq1 χ t
    let zeros := hfin.toFinset
    have hSub : S.filter (fun ρ => ρ ∈ criticalZeroSlice F t) ⊆ zeros := by
      intro ρ hρ
      exact hfin.mem_toFinset.mpr (Finset.mem_filter.mp hρ).2
    have hSupp : Function.support ((criticalZeroSlice F t).indicator m) ⊆ (zeros : Set ℂ) := by
      intro ρ hρ
      apply hfin.mem_toFinset.mpr
      by_contra hn
      exact hρ (indicator_of_notMem hn _)
    have hEq : (∑ᶠ ρ : ℂ, (criticalZeroSlice F t).indicator m ρ) = ∑ ρ ∈ zeros, m ρ := by
      rw [finsum_eq_sum_of_support_subset _ hSupp]
      exact Finset.sum_congr rfl fun ρ hρ => indicator_of_mem (hfin.mem_toFinset.mp hρ) _
    exact (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun ρ _ _ => hm ρ)).trans
      (hEq.symm.le.trans hbound)
  have hBucket (k : ℕ) : (∑ ρ ∈ S.filter (fun ρ => Nat.floor |ρ.im| = k), m ρ) ≤
      (4 * K) * Real.log (2 * (q : ℝ) * ((k : ℝ) + 2)) := by
    let t : ℝ := (k : ℝ) + 1 / 2
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hincl (ρ : ℂ) (hρ : ρ ∈ S) (hk : Nat.floor |ρ.im| = k) :
        ρ ∈ criticalZeroSlice F t ∨ ρ ∈ criticalZeroSlice F (-t) := by
      have hlo := Nat.floor_le (abs_nonneg ρ.im)
      have hhi := Nat.lt_floor_add_one |ρ.im|
      rw [hk] at hlo hhi
      have hre := hLine ρ hρ
      have hpos := (hS ρ hρ).1
      have hlt : ρ.re < 1 := by linarith
      have hz := (hS ρ hρ).2
      by_cases hsign : 0 ≤ ρ.im
      · left
        rw [abs_of_nonneg hsign] at hlo hhi
        exact ⟨hpos, hlt, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, hz⟩
      · right
        rw [abs_of_neg (lt_of_not_ge hsign)] at hlo hhi
        exact ⟨hpos, hlt, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩, hz⟩
    have hsplit : (∑ ρ ∈ S.filter (fun ρ => Nat.floor |ρ.im| = k), m ρ) ≤
        (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F t), m ρ) +
        (∑ ρ ∈ S.filter (fun ρ => ρ ∈ criticalZeroSlice F (-t)), m ρ) := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hnneg (p : Prop) [Decidable p] : 0 ≤ (if p then m ρ else 0) := by
        split
        · exact hm ρ
        · exact le_rfl
      by_cases hk : Nat.floor |ρ.im| = k
      · rcases hincl ρ hρ hk with hp | hn
        · simp only [hk, ite_true, hp]
          exact le_add_of_nonneg_right (hnneg _)
        · simp only [hk, ite_true, hn]
          exact le_add_of_nonneg_left (hnneg _)
      · simp only [hk, ite_false]
        exact add_nonneg (hnneg _) (hnneg _)
    let U : ℝ := 2 * (q : ℝ) * ((k : ℝ) + 2)
    have hU : 2 ≤ U := by
      have k0 : (0 : ℝ) ≤ k := by positivity
      calc
        _ ≤ 2 * (1 : ℝ) * ((k : ℝ) + 2) := by linarith
        _ ≤ _ := by dsimp [U]; gcongr
    have hArg : 2 * (q : ℝ) * (2 + |t|) ≤ U ^ 2 := by
      rw [abs_of_nonneg ht]
      have h0 : 2 + t ≤ 2 * ((k : ℝ) + 2) := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ 2 * (q : ℝ) * (2 * ((k : ℝ) + 2)) := by gcongr
        _ = 2 * U := by dsimp [U]; ring
        _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ U by linarith) (show 0 ≤ U - 2 by linarith)]
    have hlog := Real.log_le_log (show 0 < 2 * (q : ℝ) * (2 + |t|) by positivity) hArg
    rw [Real.log_pow] at hlog
    norm_num at hlog
    have hs := hsplit.trans (add_le_add (hCount' t) (hCount' (-t)))
    rw [abs_neg] at hs
    change _ ≤ (4 * K) * Real.log U
    have htBound := mul_le_mul_of_nonneg_left hlog hK.le
    exact hs.trans ((add_le_add htBound htBound).trans_eq (by ring))
  calc
    _ ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt F ρ : ℂ) * GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ :=
      norm_sum_le _ _
    _ = ∑ ρ ∈ S, m ρ * ‖GoldbachSmoothing.kernel x (Real.sqrt x) ρ‖ := by
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp [m]
    _ ≤ 256 * (4 * K) * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 :=
      smoothed_zero_sum_le hq hx (by positivity) S m (fun ρ _ => hm ρ) hLine hBucket
    _ = _ := by ring

end Goldbach

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace Goldbach

noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private lemma integral_div_affine (u v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ [[a, b]], (t : ℂ) * v + u ∈ slitPlane) :
    (∫ t : ℝ in a..b, v / ((t : ℂ) * v + u)) =
      log ((b : ℂ) * v + u) - log ((a : ℂ) * v + u) := by
  have hint : IntervalIntegrable (fun t : ℝ => v / ((t : ℂ) * v + u)) volume a b :=
    (continuousOn_const.div (by fun_prop) fun t ht => slitPlane_ne_zero (hpath t ht)).intervalIntegrable
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => log ((s : ℂ) * v + u)) (fun t ht => ?_) hint
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    have hf : (ofRealCLM : ℝ → ℂ) = (fun s : ℝ => (s : ℂ)) := rfl
    simpa only [hf, ofRealCLM_apply, ofReal_one] using (ofRealCLM.hasDerivAt (x := t))
  have haff : HasDerivAt (fun s : ℝ => (s : ℂ) * v + u) v t := by
    simpa only [one_mul] using (hreal.mul_const v).add_const u
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    (hasDerivAt_log (hpath t ht)).scomp t haff

private lemma horizontal_inv (p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((b : ℂ) + y * I - p) - log ((a : ℂ) + y * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * 1 + ((y : ℂ) * I - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa [add_im, sub_im, mul_im] using sub_ne_zero.mpr hy
  simpa only [mul_one, one_div, add_sub_assoc] using
    integral_div_affine ((y : ℂ) * I - p) 1 a b (fun t _ => hs t)

private lemma vertical_inv_right (p : ℂ) (x a b : ℝ) (hx : p.re < x) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((x : ℂ) + b * I - p) - log ((x : ℂ) + a * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * I + ((x : ℂ) - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  simpa only [div_eq_mul_inv, ← add_sub_assoc, add_comm ((x : ℂ))] using
    integral_div_affine ((x : ℂ) - p) I a b (fun t _ => hs t)

private lemma vertical_inv_left (p : ℂ) (x a b : ℝ) (hx : x < p.re) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log (-((x : ℂ) + b * I - p)) - log (-((x : ℂ) + a * I - p)) := by
  have harg (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) = -((x : ℂ) + t * I - p) := by ring
  have hs (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re, neg_re, neg_im] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  have h := integral_div_affine (p - (x : ℂ)) (-I) a b (fun t _ => hs t)
  simp only [harg] at h
  simpa only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg] using h

private lemma log_sub_log_neg_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private lemma log_sub_log_neg_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re, neg_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

theorem rectBoundaryIntegral_inv_sub {a b c d : ℝ} {p : ℂ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d) :
    rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  have htop : 0 < ((a : ℂ) + d * I - p).im := by
    simpa [add_im, sub_im, mul_im] using sub_pos.mpr hd
  have hbot : ((a : ℂ) + c * I - p).im < 0 := by
    simpa [add_im, sub_im, mul_im] using sub_neg.mpr hc
  unfold rectBoundaryIntegral
  rw [horizontal_inv p a b c hc.ne, horizontal_inv p a b d hd.ne',
    vertical_inv_right p b c d hb, vertical_inv_left p a c d ha]
  calc
    _ = (log ((a : ℂ) + d * I - p) - log (-((a : ℂ) + d * I - p))) -
        (log ((a : ℂ) + c * I - p) - log (-((a : ℂ) + c * I - p))) := by ring
    _ = _ := by rw [log_sub_log_neg_pos htop, log_sub_log_neg_neg hbot]; ring

private lemma integral_decompose {a b : ℝ} {f g : ℂ → ℂ}
    (S : Finset ℂ) (r : ℂ → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hg : ContinuousOn (g ∘ γ) [[a, b]]) (haway : ∀ t ∈ [[a, b]], γ t ∉ S)
    (he : ∀ t ∈ [[a, b]], f (γ t) = g (γ t) + ∑ p ∈ S, r p / (γ t - p)) :
    (∫ t : ℝ in a..b, f (γ t)) =
      (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, r p * (∫ t : ℝ in a..b, (γ t - p)⁻¹) := by
  have hterms (p : ℂ) (hp : p ∈ S) :
      ContinuousOn (fun t : ℝ => r p / (γ t - p)) [[a, b]] := by
    have hnum : ContinuousOn (fun _ : ℝ => r p) [[a, b]] := continuousOn_const
    have hdenom : ContinuousOn (fun t : ℝ => γ t - p) [[a, b]] :=
      (hγ.sub continuous_const).continuousOn
    exact hnum.div hdenom fun t ht => sub_ne_zero.mpr fun htp => haway t ht (htp.symm ▸ hp)
  have hsum : ContinuousOn (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) [[a, b]] :=
    continuousOn_finsetSum S hterms
  calc
    _ = ∫ t : ℝ in a..b, g (γ t) + ∑ p ∈ S, r p / (γ t - p) :=
      intervalIntegral.integral_congr he
    _ = (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, ∫ t : ℝ in a..b, r p / (γ t - p) := by
      have hgi : IntervalIntegrable (fun t : ℝ => g (γ t)) volume a b := hg.intervalIntegrable
      have hsi : IntervalIntegrable (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) volume a b :=
        hsum.intervalIntegrable
      rw [intervalIntegral.integral_add hgi hsi]
      congr 1
      exact intervalIntegral.integral_finsetSum (fun p hp => (hterms p hp).intervalIntegrable)
    _ = _ := by simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]

private lemma rect_sum_combine (S : Finset ℂ) (r bot top right left : ℂ → ℂ) :
    (∑ p ∈ S, r p * bot p) - (∑ p ∈ S, r p * top p) +
      I * (∑ p ∈ S, r p * right p) - I * (∑ p ∈ S, r p * left p) =
    ∑ p ∈ S, r p * (bot p - top p + I * right p - I * left p) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem rectBoundaryIntegral_eq_sum_residues {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f g : ℂ → ℂ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hpoles : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hg : ContinuousOn g (Icc a b ×ℂ Icc c d))
    (hgd : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (S : Set ℂ), DifferentiableAt ℂ g z)
    (hfg : EqOn f (fun z => g z + ∑ p ∈ S, r p / (z - p))
      ((Icc a b ×ℂ Icc c d) \ (S : Set ℂ))) :
    rectBoundaryIntegral f a b c d = (2 * (Real.pi : ℂ) * I) * ∑ p ∈ S, r p := by
  have hgc : ContinuousOn g ([[a, b]] ×ℂ [[c, d]]) := by
    simpa only [uIcc_of_le hab, uIcc_of_le hcd] using hg
  have hgd' : ∀ z ∈ (Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d)) \ (S : Set ℂ),
      DifferentiableAt ℂ g z := by
    simpa only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] using hgd
  have hzero : rectBoundaryIntegral g a b c d = 0 := by
    simpa only [rectBoundaryIntegral, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        g (⟨a, c⟩ : ℂ) (⟨b, d⟩ : ℂ) (S : Set ℂ) S.finite_toSet.countable hgc hgd'
  have edge {u v : ℝ} (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hmem : MapsTo γ [[u, v]] (Icc a b ×ℂ Icc c d))
      (haway : ∀ t ∈ [[u, v]], γ t ∉ S) :=
    integral_decompose S r γ hγ (hg.comp hγ.continuousOn hmem) haway
      (fun t ht => hfg ⟨hmem ht, haway t ht⟩)
  have horizontal (y : ℝ) (hy : y ∈ Icc c d) (hy' : ∀ p ∈ S, y ≠ p.im) :=
    edge (u := a) (v := b) (fun x : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re, uIcc_of_le hab] using ht
        · simpa [add_im, mul_im] using hy)
      (fun t _ hp => (hy' _ hp) (by simp [add_im, mul_im]))
  have vertical (x : ℝ) (hx : x ∈ Icc a b) (hx' : ∀ p ∈ S, x ≠ p.re) :=
    edge (u := c) (v := d) (fun y : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re] using hx
        · simpa [add_im, mul_im, uIcc_of_le hcd] using ht)
      (fun t _ hp => (hx' _ hp) (by simp [add_re, mul_re]))
  have hdecomp :
      rectBoundaryIntegral f a b c d =
        rectBoundaryIntegral g a b c d +
          ∑ p ∈ S, r p * rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d := by
    unfold rectBoundaryIntegral
    rw [horizontal c ⟨le_rfl, hcd⟩ (fun p hp => (hpoles p hp).2.2.1.ne),
        horizontal d ⟨hcd, le_rfl⟩ (fun p hp => (hpoles p hp).2.2.2.ne'),
        vertical b ⟨hab, le_rfl⟩ (fun p hp => (hpoles p hp).2.1.ne'),
        vertical a ⟨le_rfl, hab⟩ (fun p hp => (hpoles p hp).1.ne)]
    rw [← rect_sum_combine]
    ring
  rw [hdecomp, hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hpoles p hp
  rw [rectBoundaryIntegral_inv_sub ha hb hc hd]
  ring

end Goldbach

open Filter Set
open scoped BigOperators Topology

namespace Goldbach

private lemma analyticAt_logDeriv_of_ne_zero {F : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (hFw : F w ≠ 0) : AnalyticAt ℂ (logDeriv F) w :=
  hF.deriv.div hF hFw

theorem logDeriv_mul_local_polar_part {F K : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (horder : analyticOrderAt F w ≠ ⊤)
    (hK : AnalyticAt ℂ K w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => logDeriv F z * K z - (analyticOrderNatAt F w : ℂ) * K w / (z - w))
        =ᶠ[𝓝[≠] w] G := by
  obtain ⟨A, hA, hA0, hfactor⟩ := hF.analyticOrderAt_ne_top.mp horder
  let m := analyticOrderNatAt F w
  let D : ℂ → ℂ := fun z => z - w
  have hD : Differentiable ℂ D := by dsimp [D]; fun_prop
  have hlogD (z : ℂ) : logDeriv D z = 1 / (z - w) := by
    simp [D, logDeriv_apply]
  have hfac : F =ᶠ[𝓝 w] fun z => D z ^ m * A z := by
    simpa only [D, m, smul_eq_mul] using hfactor
  have hz_ne : ∀ᶠ z in 𝓝[≠] w, z ≠ w := by
    simpa using (eventually_mem_nhdsWithin (a := w) (s := {w}ᶜ))
  have hlog : logDeriv F =ᶠ[𝓝[≠] w] fun z => (m : ℂ) / (z - w) + logDeriv A z := by
    filter_upwards [(logDeriv_congr_nhds hfac).filter_mono nhdsWithin_le_nhds,
      hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hA.continuousAt.eventually_ne hA0).filter_mono nhdsWithin_le_nhds, hz_ne]
      with z hdz hAz hAnz hzne
    have hDz : D z ≠ 0 := sub_ne_zero.mpr hzne
    rw [hdz, logDeriv_fun_mul (f := fun t => D t ^ m) (g := A) z (pow_ne_zero m hDz) hAnz
      (hD.differentiableAt.pow m) hAz.differentiableAt,
      logDeriv_fun_pow (f := D) hD.differentiableAt m, hlogD, mul_one_div]
  refine ⟨fun z => (m : ℂ) * dslope K w z + logDeriv A z * K z, ?_, ?_⟩
  · exact (analyticAt_const.mul (hK.dslope w)).add
      ((analyticAt_logDeriv_of_ne_zero hA hA0).mul hK)
  · filter_upwards [hlog, hz_ne] with z hz hzne
    have hds : dslope K w z = (K z - K w) / (z - w) := by
      apply (eq_div_iff (sub_ne_zero.mpr hzne)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K w z
    change logDeriv F z * K z - (m : ℂ) * K w / (z - w) =
      (m : ℂ) * dslope K w z + logDeriv A z * K z
    rw [hz, hds]
    ring

private lemma analyticAt_principal_term (r p z : ℂ) (hz : z ≠ p) :
    AnalyticAt ℂ (fun t : ℂ => r / (t - p)) z := by
  have hnum : AnalyticAt ℂ (fun _ : ℂ => r) z := analyticAt_const
  have hdenom : AnalyticAt ℂ (fun t : ℂ => t - p) z := by fun_prop
  exact hnum.div hdenom (sub_ne_zero.mpr hz)

theorem logDeriv_mul_exists_analytic_remainder {F K : ℂ → ℂ} {U : Set ℂ}
    (S : Finset ℂ) (hSU : (S : Set ℂ) ⊆ U) (hF : AnalyticOnNhd ℂ F U)
    (hK : AnalyticOnNhd ℂ K U) (hzeros : ∀ z ∈ U, F z = 0 → z ∈ S)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      EqOn (fun z => logDeriv F z * K z)
        (fun z => G z + ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p / (z - p))
        (U \ (S : Set ℂ)) := by
  classical
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  have hlocal (p : ℂ) (hp : p ∈ S) :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        (fun z => logDeriv F z * K z - r p / (z - p)) =ᶠ[𝓝[≠] p] g :=
    logDeriv_mul_local_polar_part (hF p (hSU hp)) (horder p hp) (hK p (hSU hp))
  choose localPart hlocalA hlocalEq using hlocal
  let regular : ℂ → ℂ := fun z => logDeriv F z * K z - ∑ p ∈ S, r p / (z - p)
  let G : ℂ → ℂ := fun z =>
    if hz : z ∈ S then localPart z hz z - ∑ p ∈ S.erase z, r p / (z - p) else regular z
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ S
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S.erase z :=
        (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have heq : ∀ᶠ t in 𝓝 z, t ≠ z →
          logDeriv F t * K t - r z / (t - z) = localPart z hzS t := by
        simpa using (eventually_nhdsWithin_iff.mp (hlocalEq z hzS))
      have hG : G =ᶠ[𝓝 z] fun t =>
          localPart z hzS t - ∑ p ∈ S.erase z, r p / (t - p) := by
        filter_upwards [havoid, heq] with t ht hEq
        by_cases htz : t = z
        · subst t
          simp only [G, dite_eq_left hzS]
        · have htS : t ∉ S := fun h => ht (Finset.mem_erase.mpr ⟨htz, h⟩)
          simp only [G, dite_eq_right htS, regular]
          rw [← Finset.sum_erase_add S (fun p => r p / (t - p)) hzS, ← hEq htz]
          ring
      have hA : AnalyticAt ℂ (fun t => ∑ p ∈ S.erase z, r p / (t - p)) z :=
        (S.erase z).analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (Finset.ne_of_mem_erase hp).symm
      exact ((hlocalA z hzS).sub hA).congr hG.symm
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS
      have hG : G =ᶠ[𝓝 z] regular := by
        filter_upwards [havoid] with t ht
        simp only [G, dite_eq_right ht]
      have hFz : F z ≠ 0 := fun hzF => hzS (hzeros z hz hzF)
      have hsum : AnalyticAt ℂ (fun t => ∑ p ∈ S, r p / (t - p)) z :=
        S.analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (fun h => hzS (h.symm ▸ hp))
      exact (((analyticAt_logDeriv_of_ne_zero (hF z hz) hFz).mul (hK z hz)).sub hsum).congr
        hG.symm
  · intro z hz
    have hzS : z ∉ S := hz.2
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p)
    simp only [G, dite_eq_right hzS, regular, sub_add_cancel]

end Goldbach

open Complex Filter Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Goldbach

theorem rectBoundaryIntegral_neg_logDeriv_add_pole_mul
    {a b c d : ℝ} (F K : ℂ → ℂ) (S : Finset ℂ) (δ : ℂ)
    (ha : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hF : AnalyticOnNhd ℂ F (Icc a b ×ℂ Icc c d))
    (hK : AnalyticOnNhd ℂ K (Icc a b ×ℂ Icc c d))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc c d, F z = 0 ↔ z ∈ S)
    (hinterior : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) (hF1 : F 1 ≠ 0) :
    rectBoundaryIntegral (fun z => (-logDeriv F z + δ / (z - 1)) * K z) a b c d =
      (2 * (Real.pi : ℂ) * I) * (δ * K 1 - ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p) := by
  classical
  let U := Icc a b ×ℂ Icc c d
  let T := insert (1 : ℂ) S
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  let coeff : ℂ → ℂ := fun p => if p = 1 then δ * K 1 else -r p
  have h1U : (1 : ℂ) ∈ U := by
    exact mem_reProdIm.mpr ⟨by simpa only [one_re] using Set.mem_Icc.mpr ⟨ha.le, hb.le⟩,
      by simpa only [one_im] using Set.mem_Icc.mpr ⟨hc.le, hd.le⟩⟩
  have h1S : (1 : ℂ) ∉ S := fun h => hF1 ((hzeros 1 h1U).mpr h)
  have hSU : (S : Set ℂ) ⊆ U := by
    intro p hp
    obtain ⟨hpa, hpb, hpc, hpd⟩ := hinterior p hp
    exact mem_reProdIm.mpr ⟨⟨hpa.le, hpb.le⟩, ⟨hpc.le, hpd.le⟩⟩
  have hT : ∀ p ∈ T, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [one_re, one_im] using And.intro ha (And.intro hb (And.intro hc hd))
    · exact hinterior p hp
  have hcoeff1 : coeff 1 = δ * K 1 := ite_eq_left rfl
  have hcoeff (p : ℂ) (hp : p ∈ S) : coeff p = -r p := by
    have hp1 : p ≠ (1 : ℂ) := fun heq => h1S (heq ▸ hp)
    exact ite_eq_right hp1
  have hsum (z : ℂ) :
      (∑ p ∈ T, coeff p / (z - p)) =
        δ * K 1 / (z - 1) - ∑ p ∈ S, r p / (z - p) := by
    have hsumS : (∑ p ∈ S, coeff p / (z - p)) = -(∑ p ∈ S, r p / (z - p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp, neg_div]
    change (∑ p ∈ insert (1 : ℂ) S, coeff p / (z - p)) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS]
    exact (sub_eq_add_neg _ _).symm
  have hsum_coeff : (∑ p ∈ T, coeff p) = δ * K 1 - ∑ p ∈ S, r p := by
    have hsumS : (∑ p ∈ S, coeff p) = -(∑ p ∈ S, r p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hcoeff
    change (∑ p ∈ insert (1 : ℂ) S, coeff p) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS, sub_eq_add_neg]
  obtain ⟨G, hG, hG_eq⟩ := logDeriv_mul_exists_analytic_remainder S hSU hF hK
    (fun z hz => (hzeros z hz).mp) horder
  let J : ℂ → ℂ := fun z => -G z + δ * dslope K 1 z
  have hJ : AnalyticOnNhd ℂ J U := by
    intro z hz
    exact (hG z hz).neg.add (analyticAt_const.mul ((hK z hz).dslope 1))
  have hJ_diff : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (T : Set ℂ), DifferentiableAt ℂ J z := by
    intro z hz
    obtain ⟨hr, hi⟩ := mem_reProdIm.mp hz.1
    exact (hJ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hr, Ioo_subset_Icc_self hi⟩)).differentiableAt
  have hEq : EqOn (fun z => (-logDeriv F z + δ / (z - 1)) * K z)
      (fun z => J z + ∑ p ∈ T, coeff p / (z - p)) (U \ (T : Set ℂ)) := by
    intro z hz
    have hzT : z ∉ T := hz.2
    have hzS : z ∉ S := fun h => hzT (Finset.mem_insert_of_mem h)
    have hz1 : z ≠ (1 : ℂ) := fun h => hzT (Finset.mem_insert.mpr (Or.inl h))
    have hGK := hG_eq ⟨hz.1, hzS⟩
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p) at hGK
    have hds : dslope K 1 z = (K z - K 1) / (z - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hz1)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K 1 z
    change (-logDeriv F z + δ / (z - 1)) * K z =
      (-G z + δ * dslope K 1 z) + ∑ p ∈ T, coeff p / (z - p)
    rw [hsum, hds]
    calc
      _ = -(logDeriv F z * K z) + δ / (z - 1) * K z := by ring
      _ = _ := by rw [hGK]; ring
  rw [rectBoundaryIntegral_eq_sum_residues (ha.le.trans hb.le) (hc.le.trans hd.le)
    _ J T coeff hT hJ.continuousOn hJ_diff hEq, hsum_coeff]

theorem right_vertical_integral_of_rect {f : ℂ → ℂ} {a b c d : ℝ} {R : ℂ}
    (h : rectBoundaryIntegral f a b c d = 2 * (Real.pi : ℂ) * I * R) :
    (∫ y : ℝ in c..d, f (b + y * I)) =
      (∫ y : ℝ in c..d, f (a + y * I)) + 2 * (Real.pi : ℂ) * R +
        I * ((∫ x : ℝ in a..b, f (x + c * I)) - ∫ x : ℝ in a..b, f (x + d * I)) := by
  unfold rectBoundaryIntegral at h
  set bottom := (∫ x : ℝ in a..b, f (x + c * I))
  set top := (∫ x : ℝ in a..b, f (x + d * I))
  set left := (∫ y : ℝ in c..d, f (a + y * I))
  set right := (∫ y : ℝ in c..d, f (b + y * I))
  calc
    right = left - I * (bottom - top + I * right - I * left) + I * (bottom - top) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      rw [h]
      ring_nf
      simp only [I_sq]
      ring

end Goldbach

open Filter MeasureTheory
open scoped Topology Interval

namespace Goldbach

theorem scaled_contour_error_le {ι E : Type*} {l : Filter ι} [NeBot l]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R L Z H : ι → E} {fullRight main : E} {scale Lbound Zbound : ℝ}
    (hscale : 0 < scale) (hR : Tendsto R l (𝓝 fullRight)) (hH : Tendsto H l (𝓝 0))
    (hrect : ∀ᶠ i in l, R i = L i + scale • (main - Z i) + H i)
    (hL : ∀ᶠ i in l, ‖L i‖ ≤ Lbound) (hZ : ∀ᶠ i in l, ‖Z i‖ ≤ Zbound) :
    ‖(1 / scale) • fullRight - main‖ ≤ (1 / scale) * Lbound + Zbound := by
  have hfactor : 0 ≤ 1 / scale := one_div_nonneg.mpr hscale.le
  have hlim : Tendsto (fun i => ‖(1 / scale) • (R i - H i) - main‖) l
      (𝓝 ‖(1 / scale) • fullRight - main‖) := by
    simpa only [sub_zero] using (((hR.sub hH).const_smul (1 / scale)).sub_const main).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [hrect, hL, hZ] with i hi hLi hZi
  have herror : (1 / scale) • (R i - H i) - main = (1 / scale) • L i - Z i := by
    rw [hi, add_sub_cancel_right, smul_add, smul_smul, one_div_mul_cancel hscale.ne', one_smul]
    abel
  have hLn : ‖(1 / scale) • L i‖ ≤ (1 / scale) * Lbound := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfactor]
    exact mul_le_mul_of_nonneg_left hLi hfactor
  rw [herror]
  exact (norm_sub_le _ _).trans (add_le_add hLn hZi)

theorem vertical_contour_error_le {ι E : Type*} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f) {lower upper : ι → ℝ}
    (hlower : Tendsto lower l atBot) (hupper : Tendsto upper l atTop)
    {L Z H : ι → E} {main : E} {Lbound Zbound : ℝ}
    (hH : Tendsto H l (𝓝 0))
    (hrect : ∀ᶠ i in l,
      (∫ t : ℝ in lower i..upper i, f t) = L i + (2 * Real.pi) • (main - Z i) + H i)
    (hL : ∀ᶠ i in l, ‖L i‖ ≤ Lbound) (hZ : ∀ᶠ i in l, ‖Z i‖ ≤ Zbound) :
    ‖(1 / (2 * Real.pi)) • (∫ t : ℝ, f t) - main‖ ≤
      (1 / (2 * Real.pi)) * Lbound + Zbound :=
  scaled_contour_error_le (mul_pos zero_lt_two Real.pi_pos)
    (intervalIntegral_tendsto_integral hf hlower hupper) hH hrect hL hZ

end Goldbach

open Complex Filter MeasureTheory
open scoped Interval

namespace GoldbachSmoothing

private lemma rpow_eq_sqrt_rpow_mul_two {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    x ^ r = (Real.sqrt x) ^ (2 * r) := by
  rw [Real.rpow_mul (Real.sqrt_nonneg x), Real.rpow_two, Real.sq_sqrt hx]

private lemma add_sqrt_rpow_le {x r : ℝ} (hx : 2 ≤ x) (hr : 0 ≤ r) (hr' : r ≤ 2) :
    (x + Real.sqrt x) ^ r ≤ 4 * (Real.sqrt x) ^ (2 * r) := by
  have hx0 : 0 ≤ x := by linarith
  have hsx : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hp : (2 : ℝ) ^ r ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr'
      _ = _ := by norm_num [Real.rpow_two]
  calc
    _ ≤ (2 * x) ^ r := Real.rpow_le_rpow (by positivity) (by linarith) hr
    _ = (2 : ℝ) ^ r * x ^ r := Real.mul_rpow (by norm_num) hx0
    _ ≤ 4 * x ^ r := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hx0 _)
    _ = _ := by rw [rpow_eq_sqrt_rpow_mul_two hx0 r]

theorem norm_left_vertical_kernel_le {x : ℝ} (hx : 2 ≤ x) (t : ℝ) :
    ‖kernel x (Real.sqrt x) (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      40 * Real.sqrt x * (1 + |t|) ^ (-(11 / 10 : ℝ)) := by
  let h := Real.sqrt x
  let u := 1 + |t|
  let s : ℂ := ((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := Real.sqrt_pos.2 hx0
  have hu : 0 < u := by dsimp [u]; positivity
  have hre : s.re = 9 / 20 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hn : u / 4 ≤ ‖s‖ := by
    have hr : (9 / 20 : ℝ) ≤ ‖s‖ := hre ▸ re_le_norm s
    have hi : |t| ≤ ‖s‖ := by simpa only [hsim] using abs_im_le_norm s
    dsimp [u]
    linarith
  have hn' : u / 2 ≤ ‖s + 1‖ := by
    have hr : (9 / 20 : ℝ) + 1 ≤ ‖s + 1‖ := by
      simpa only [add_re, hre, one_re] using re_le_norm (s + 1)
    have hi : |t| ≤ ‖s + 1‖ := by
      simpa only [add_im, hsim, one_im, add_zero] using abs_im_le_norm (s + 1)
    dsimp [u]
    linarith
  have hlow : ‖kernel x h s‖ ≤ 16 * h ^ (9 / 10 : ℝ) / u := by
    have hs : 0 < s.re := by rw [hre]; norm_num
    have hnum : (x + h) ^ s.re ≤ 4 * h ^ (9 / 10 : ℝ) := by
      have hl := add_sqrt_rpow_le (r := 9 / 20) hx (by norm_num) (by norm_num)
      rw [hre]
      change (x + Real.sqrt x) ^ (9 / 20 : ℝ) ≤ 4 * (Real.sqrt x) ^ (9 / 10 : ℝ)
      convert hl using 1
      norm_num
    calc
      _ ≤ (x + h) ^ s.re / ‖s‖ := norm_kernel_le hx0 hh hs
      _ ≤ (4 * h ^ (9 / 10 : ℝ)) / (u / 4) :=
        (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hn)
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have hhigh : ‖kernel x h s‖ ≤ 40 * h ^ (19 / 10 : ℝ) / u ^ 2 := by
    have hr : s.re + 1 = (29 / 20 : ℝ) := by rw [hre]; norm_num
    have hnum : (x + h) ^ (s.re + 1) + x ^ (s.re + 1) ≤ 5 * h ^ (29 / 10 : ℝ) := by
      rw [hr]
      have h₁ := add_sqrt_rpow_le (r := 29 / 20) hx (by norm_num) (by norm_num)
      have h₂ : x ^ (29 / 20 : ℝ) = h ^ (29 / 10 : ℝ) := by
        convert rpow_eq_sqrt_rpow_mul_two hx0.le (29 / 20 : ℝ) using 1
        norm_num [h]
      have hb : (x + h) ^ (29 / 20 : ℝ) ≤ 4 * h ^ (29 / 10 : ℝ) := by
        convert h₁ using 1
        norm_num [h]
      linarith
    have hden : h * (u / 4) * (u / 2) ≤ h * ‖s‖ * ‖s + 1‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn hh.le) hn' (by positivity) (by positivity)
    have hdiv : h ^ (29 / 10 : ℝ) / h = h ^ (19 / 10 : ℝ) := by
      rw [show (19 / 10 : ℝ) = 29 / 10 - 1 by norm_num, Real.rpow_sub hh, Real.rpow_one]
    calc
      _ ≤ ((x + h) ^ (s.re + 1) + x ^ (s.re + 1)) / (h * ‖s‖ * ‖s + 1‖) :=
        norm_kernel_le_tail hx0 hh
      _ ≤ (5 * h ^ (29 / 10 : ℝ)) / (h * (u / 4) * (u / 2)) :=
        (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = 40 * (h ^ (29 / 10 : ℝ) / h) / u ^ 2 := by
        field_simp [hh.ne', hu.ne']
        ring
      _ = _ := by rw [hdiv]
  change ‖kernel x h s‖ ≤ 40 * h * u ^ (-(11 / 10 : ℝ))
  by_cases ht : u ≤ h
  · have hpowu : u ^ (1 / 10 : ℝ) ≤ h ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow hu.le ht (by norm_num)
    have huinv : u⁻¹ = u ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) := by
      rw [← Real.rpow_add hu]
      norm_num [Real.rpow_neg_one]
    have hpowh : h ^ (9 / 10 : ℝ) * h ^ (1 / 10 : ℝ) = h := by
      rw [← Real.rpow_add hh]
      norm_num
    calc
      _ ≤ 16 * h ^ (9 / 10 : ℝ) / u := hlow
      _ ≤ 40 * h ^ (9 / 10 : ℝ) / u :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hu.le
      _ = 40 * h ^ (9 / 10 : ℝ) * u ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) := by
        rw [div_eq_mul_inv, huinv]
        ring
      _ ≤ 40 * h ^ (9 / 10 : ℝ) * h ^ (1 / 10 : ℝ) * u ^ (-(11 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowu (by positivity)) (by positivity)
      _ = _ := by rw [mul_assoc 40, hpowh]
  · have hpowu : h ^ (9 / 10 : ℝ) ≤ u ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow hh.le (le_of_not_ge ht) (by norm_num)
    have hpowh : h ^ (19 / 10 : ℝ) = h * h ^ (9 / 10 : ℝ) := by
      rw [show (19 / 10 : ℝ) = 9 / 10 + 1 by norm_num, Real.rpow_add_one hh.ne', mul_comm]
    have huTail : u ^ (9 / 10 : ℝ) / u ^ 2 = u ^ (-(11 / 10 : ℝ)) := by
      rw [show (-(11 / 10 : ℝ)) = 9 / 10 - 2 by norm_num, Real.rpow_sub hu, Real.rpow_two]
    calc
      _ ≤ 40 * h ^ (19 / 10 : ℝ) / u ^ 2 := hhigh
      _ = (40 * h) * h ^ (9 / 10 : ℝ) / u ^ 2 := by rw [hpowh, mul_assoc]
      _ ≤ (40 * h) * u ^ (9 / 10 : ℝ) / u ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpowu (by positivity)) (by positivity)
      _ = _ := by rw [mul_div_assoc, huTail]

private lemma log_left_vertical_le {x q : ℝ} (hx : 2 ≤ x) (hq : 1 ≤ q) (t : ℝ) :
    Real.log (2 * q * (2 + |t|)) ≤ 21 * Real.log (2 * q * x) ^ 2 *
      (1 + |t|) ^ (1 / 20 : ℝ) := by
  let u := 1 + |t|
  let L := Real.log (2 * q * x)
  have hu1 : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hq2 : 0 < 2 * q := by linarith
  have hx0 : 0 < x := by linarith
  have h4 : (4 : ℝ) ≤ 2 * q * x := by
    have hf : (2 : ℝ) * 2 ≤ (2 * q) * x :=
      mul_le_mul (by linarith) hx (by norm_num) hq2.le
    norm_num at hf
    exact hf
  have hL : 1 ≤ L := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    exact hlog4.trans (Real.log_le_log (by norm_num) h4)
  have hLpos : 0 ≤ L := zero_le_one.trans hL
  have hLsq : L ≤ L ^ 2 := by nlinarith [mul_nonneg hLpos (sub_nonneg.mpr hL)]
  have huPow : 1 ≤ u ^ (1 / 20 : ℝ) :=
    Real.one_le_rpow hu1 (by norm_num)
  have harg : 2 + |t| ≤ x * u := by
    calc
      _ ≤ 2 * u := by dsimp [u]; linarith [abs_nonneg t]
      _ ≤ _ := mul_le_mul_of_nonneg_right hx hu.le
  have hlog : Real.log (2 * q * (2 + |t|)) ≤ L + Real.log u := by
    have harg' := mul_le_mul_of_nonneg_left harg hq2.le
    rw [← mul_assoc] at harg'
    have hp := Real.log_le_log (show 0 < 2 * q * (2 + |t|) by positivity) harg'
    rwa [Real.log_mul (mul_ne_zero hq2.ne' hx0.ne') hu.ne'] at hp
  have hlogu : Real.log u ≤ 20 * u ^ (1 / 20 : ℝ) := by
    have h := Real.log_le_rpow_div hu.le (show (0 : ℝ) < 1 / 20 by norm_num)
    convert h using 1
    ring
  have hLu : L ≤ L ^ 2 * u ^ (1 / 20 : ℝ) :=
    hLsq.trans (le_mul_of_one_le_right (sq_nonneg L) huPow)
  have h1L : (1 : ℝ) ≤ L ^ 2 := hL.trans hLsq
  have h20 : 20 * u ^ (1 / 20 : ℝ) ≤ 20 * (L ^ 2 * u ^ (1 / 20 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact le_mul_of_one_le_left (by positivity) h1L
  change _ ≤ 21 * L ^ 2 * u ^ (1 / 20 : ℝ)
  linarith

theorem norm_left_vertical_integral_le :
    ∃ D : ℝ, 0 < D ∧
      ∀ (g : ℝ → ℂ) (x q A a b : ℝ), 2 ≤ x → 1 ≤ q → 0 ≤ A → Continuous g →
        (∀ t, ‖g t‖ ≤ A * Real.log (2 * q * (2 + |t|))) →
        ‖∫ t : ℝ in a..b, g t * kernel x (Real.sqrt x) (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          D * A * Real.sqrt x * Real.log (2 * q * x) ^ 2 := by
  let w : ℝ → ℝ := fun t => (1 + |t|) ^ (-(21 / 20 : ℝ))
  have hwNonneg (t : ℝ) : 0 ≤ w t := by dsimp [w]; positivity
  have hw : Integrable w := by
    have hw' := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 21 / 20) (by norm_num)
    simpa only [w, Real.norm_eq_abs] using hw'
  have hwIntegral : 0 ≤ ∫ t : ℝ, w t := integral_nonneg hwNonneg
  refine ⟨840 * (1 + ∫ t : ℝ, w t), by positivity, ?_⟩
  intro g x q A a b hx hq hA hg hbound
  let h := Real.sqrt x
  let L := Real.log (2 * q * x)
  let C := 840 * A * h * L ^ 2
  let f : ℝ → ℂ := fun t => g t * kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  have hC : 0 ≤ C := by dsimp [C, h]; positivity
  have point (t : ℝ) : ‖f t‖ ≤ C * w t := by
    let u := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have hgBound : ‖g t‖ ≤ A * (21 * L ^ 2 * u ^ (1 / 20 : ℝ)) :=
      (hbound t).trans (mul_le_mul_of_nonneg_left (log_left_vertical_le hx hq t) hA)
    change ‖g t * kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (A * (21 * L ^ 2 * u ^ (1 / 20 : ℝ))) * (40 * h * u ^ (-(11 / 10 : ℝ))) :=
        mul_le_mul hgBound (norm_left_vertical_kernel_le hx t) (norm_nonneg _) (by positivity)
      _ = C * (u ^ (1 / 20 : ℝ) * u ^ (-(11 / 10 : ℝ))) := by dsimp [C]; ring
      _ = _ := by rw [← Real.rpow_add hu]; norm_num [w, u]
  have hker : Integrable (fun t : ℝ => kernel x h (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)) :=
    kernel_verticalIntegrable (by linarith : 0 < x) (Real.sqrt_pos.2 (by linarith)) (by norm_num)
  have hmajor : Integrable (fun t : ℝ => C * w t) := hw.const_mul C
  have hfi : Integrable f :=
    hmajor.mono' (hg.aestronglyMeasurable.mul hker.aestronglyMeasurable)
      (Eventually.of_forall point)
  change ‖∫ t : ℝ in a..b, f t‖ ≤ _
  calc
    _ ≤ ∫ t in Ι a b, ‖f t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t : ℝ, ‖f t‖ := setIntegral_le_integral hfi.norm (ae_of_all _ fun _ => norm_nonneg _)
    _ ≤ ∫ t : ℝ, C * w t := integral_mono hfi.norm hmajor point
    _ = C * ∫ t : ℝ, w t := integral_const_mul C w
    _ ≤ C * (1 + ∫ t : ℝ, w t) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by dsimp [C, h, L]; ring

end GoldbachSmoothing

namespace Goldbach

open Filter Set
open scoped Topology

private theorem horizontal_log_sq_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    Real.log (2 * q * (2 + |t|)) ^ 2 ≤ 24 * q * |t| := by
  let v : ℝ := 2 * q * (2 + |t|)
  have hq₀ : 0 < q := by linarith only [hq]
  have hv₁ : 1 ≤ v := one_le_mul_of_one_le_of_one_le (by linarith only [hq])
    (by linarith only [ht])
  have hv₀ := zero_le_one.trans hv₁
  have hsqrt : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv₀
  have hlog : Real.log v ≤ 2 * Real.sqrt v := calc
    _ = Real.log ((Real.sqrt v) ^ 2) := by rw [hsqrt]
    _ = 2 * Real.log (Real.sqrt v) := by rw [Real.log_pow]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg _)) (by norm_num)
  change Real.log v ^ 2 ≤ 24 * q * |t|
  calc
    _ ≤ (2 * Real.sqrt v) ^ 2 :=
      (sq_le_sq₀ (Real.log_nonneg hv₁) (by positivity)).mpr hlog
    _ = 4 * v := by nlinarith only [hsqrt]
    _ = (8 * q) * (2 + |t|) := by dsimp [v]; ring
    _ ≤ (8 * q) * (3 * |t|) := mul_le_mul_of_nonneg_left (by linarith only [ht]) (by positivity)
    _ = _ := by ring

private theorem norm_horizontal_kernel_le {x h σ t : ℝ} (hx : 2 ≤ x) (hh : 0 < h)
    (hσ : σ ≤ 2) (ht : 1 ≤ |t|) :
    ‖GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((x + h) ^ 3 + x ^ 3) / (h * |t| ^ 2) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hzRe : z.re = σ := by simp [z]
  have hzIm : z.im = t := by simp [z]
  have hzNextIm : (z + 1).im = t := by simp [hzIm]
  have hAbs₀ : 0 < |t| := zero_lt_one.trans_le ht
  have htZ : |t| ≤ ‖z‖ := by simpa only [hzIm] using Complex.abs_im_le_norm z
  have htZNext : |t| ≤ ‖z + 1‖ := by simpa only [hzNextIm] using Complex.abs_im_le_norm (z + 1)
  have hExp : z.re + 1 ≤ (3 : ℝ) := by linarith only [hzRe, hσ]
  have hXOne : (1 : ℝ) ≤ x := by linarith only [hx]
  have hXHOne : (1 : ℝ) ≤ x + h := by linarith only [hx, hh]
  have hNum : (x + h) ^ (z.re + 1) + x ^ (z.re + 1) ≤ (x + h) ^ 3 + x ^ 3 := by
    have h := add_le_add (Real.rpow_le_rpow_of_exponent_le hXHOne hExp)
      (Real.rpow_le_rpow_of_exponent_le hXOne hExp)
    simpa only [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hDen : h * |t| ^ 2 ≤ h * ‖z‖ * ‖z + 1‖ := calc
    _ = h * (|t| * |t|) := by rw [pow_two]
    _ ≤ h * (‖z‖ * ‖z + 1‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul htZ htZNext (abs_nonneg _) (norm_nonneg _)) hh.le
    _ = _ := by ring
  change ‖GoldbachSmoothing.kernel x h z‖ ≤ ((x + h) ^ 3 + x ^ 3) / (h * |t| ^ 2)
  calc
    _ ≤ ((x + h) ^ (z.re + 1) + x ^ (z.re + 1)) / (h * ‖z‖ * ‖z + 1‖) :=
      GoldbachSmoothing.norm_kernel_le_tail (by linarith only [hx]) hh
    _ ≤ ((x + h) ^ 3 + x ^ 3) / (h * ‖z‖ * ‖z + 1‖) :=
      div_le_div_of_nonneg_right hNum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen

theorem norm_horizontal_kernel_integral_le {x h a q A t : ℝ} (hx : 2 ≤ x) (hh : 0 < h)
    (ha : a ≤ 2) (hq : 1 ≤ q) (hA : 0 ≤ A) (ht : 1 ≤ |t|) (f : ℂ → ℂ)
    (hf : ∀ σ ∈ Set.Icc a (2 : ℝ),
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * Real.log (2 * q * (2 + |t|)) ^ 2) :
    ‖∫ σ in a..2, f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((2 - a) * (A * (24 * q) * ((x + h) ^ 3 + x ^ 3) / h)) / |t| := by
  let B := (x + h) ^ 3 + x ^ 3
  let C := A * (24 * q) * B / h
  have hx₀ : 0 < x := by linarith only [hx]
  have hAbs₀ : 0 < |t| := zero_lt_one.trans_le ht
  have hBound (σ : ℝ) (hσ : σ ∈ Set.uIoc a (2 : ℝ)) :
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / |t| := by
    rw [Set.uIoc_of_le ha] at hσ
    let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hK : ‖GoldbachSmoothing.kernel x h z‖ ≤ B / (h * |t| ^ 2) :=
      norm_horizontal_kernel_le hx hh hσ.2 ht
    have hF : ‖f z‖ ≤ A * Real.log (2 * q * (2 + |t|)) ^ 2 := hf σ ⟨hσ.1.le, hσ.2⟩
    have hLog := mul_le_mul_of_nonneg_left (horizontal_log_sq_le hq ht) hA
    change ‖f z * GoldbachSmoothing.kernel x h z‖ ≤ C / |t|
    calc
      _ = ‖f z‖ * ‖GoldbachSmoothing.kernel x h z‖ := norm_mul _ _
      _ ≤ (A * Real.log (2 * q * (2 + |t|)) ^ 2) * (B / (h * |t| ^ 2)) :=
        mul_le_mul hF hK (norm_nonneg _) (by positivity)
      _ ≤ (A * (24 * q * |t|)) * (B / (h * |t| ^ 2)) :=
        mul_le_mul_of_nonneg_right hLog (by dsimp [B]; positivity)
      _ = _ := by
        dsimp [C, B]
        field_simp [hh.ne', hAbs₀.ne']
  change ‖∫ σ in a..2, f ((σ : ℂ) + (t : ℂ) * Complex.I) *
    GoldbachSmoothing.kernel x h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ((2 - a) * C) / |t|
  calc
    _ ≤ (C / |t|) * |2 - a| := intervalIntegral.norm_integral_le_of_norm_le_const hBound
    _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr ha)]; ring

theorem tendsto_horizontal_kernel_integral_zero {ι : Type*} {l : Filter ι}
    {x h a q A : ℝ} (hx : 2 ≤ x) (hh : 0 < h) (ha : a ≤ 2) (hq : 1 ≤ q) (hA : 0 ≤ A)
    (f : ℂ → ℂ) (u : ι → ℝ) (hu : Tendsto (fun i ↦ |u i|) l atTop)
    (hf : ∀ᶠ i in l, ∀ σ ∈ Set.Icc a (2 : ℝ),
      ‖f ((σ : ℂ) + (u i : ℂ) * Complex.I)‖ ≤ A * Real.log (2 * q * (2 + |u i|)) ^ 2) :
    Tendsto (fun i ↦ ∫ σ in a..2, f ((σ : ℂ) + (u i : ℂ) * Complex.I) *
      GoldbachSmoothing.kernel x h ((σ : ℂ) + (u i : ℂ) * Complex.I)) l (𝓝 0) := by
  let C := (2 - a) * (A * (24 * q) * ((x + h) ^ 3 + x ^ 3) / h)
  have hInv : Tendsto (fun i ↦ (|u i|)⁻¹) l (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hu
  have hLimit : Tendsto (fun i ↦ C / |u i|) l (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ C) l (𝓝 C)).mul hInv
  refine squeeze_zero_norm' ?_ hLimit
  filter_upwards [hu.eventually_ge_atTop 1, hf] with i hHeight hF
  exact norm_horizontal_kernel_integral_le hx hh ha hq hA hHeight f hF

end Goldbach

namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

theorem uniform_dirichlet_log_control : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C := by
  obtain ⟨C, hC, h⟩ := norm_logDeriv_regularizedL_le
  refine ⟨C, hC, ?_⟩
  intro q _ χ σ t d hσ hd hdist
  have hpoint : (⟨σ, t⟩ : ℂ) = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hpoint] at hdist ⊢
  exact h q χ t σ d hσ.1 hσ.2 hd hdist

set_option maxHeartbeats 3000000 in

theorem uniform_smoothed_dirichlet_estimate (hGRH : GRH1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀ (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
      ‖(∑' n, GoldbachSmoothing.twistedCoefficient χ n *
          GoldbachSmoothing.cutoff (X : ℝ) (Real.sqrt X) n) -
        principalFlag χ * GoldbachSmoothing.kernel (X : ℝ) (Real.sqrt X) 1‖ ≤
        D * Real.sqrt (X : ℝ) * Real.log (2 * (q : ℝ) * (X : ℝ)) ^ 2 := by
  classical
  obtain ⟨A, B, hA, hB, hBounds⟩ := dirichlet_contour_bounds hGRH uniform_dirichlet_log_control
  obtain ⟨L, hL, hVertical⟩ := GoldbachSmoothing.norm_left_vertical_integral_le
  obtain ⟨Z, hZ, hResidues⟩ := uniform_smoothed_dirichlet_residues hGRH
  let c : ℝ := 1 / (2 * Real.pi)
  refine ⟨c * (L * A) + Z, by dsimp [c]; positivity, ?_⟩
  intro q _ hq1 χ X hX
  let x : ℝ := X
  let h : ℝ := Real.sqrt x
  let K := GoldbachSmoothing.kernel x h
  let F := regularizedL χ
  let δ := principalFlag χ
  let G (z : ℂ) : ℂ := contourLog χ z * K z
  let left (t : ℝ) : ℂ := contourLog χ (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  let right (t : ℝ) : ℂ :=
    (-logDeriv (DirichletCharacter.LFunction χ) (2 + (t : ℂ) * I)) * K (2 + (t : ℂ) * I)
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := Real.sqrt_pos.2 hx0
  have hq : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  obtain ⟨hbLeft, hbGood⟩ := hBounds q hq1 χ
  let good (u : ℝ) : Prop :=
    (∀ ρ : ℂ, 0 < ρ.re → F ρ = 0 → ρ.im ≠ u) ∧
      ∀ σ ∈ Icc (9 / 20 : ℝ) 2,
        ‖contourLog χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ B * logHeight q u ^ 2
  obtain ⟨lo, up, _, hSign, hGood, hLoLimit, hUpLimit, hLoAbs, hUpAbs⟩ :=
    exists_height_sequences good hbGood
  choose S hZeros hInside hReal using
    fun n : ℕ => exists_regularizedL_contourZeros χ hGRH hq1 (lo n) (up n)
      (hGood n).1.1 (hGood n).2.1
  let zeros (n : ℕ) : ℂ := ∑ ρ ∈ S n, (analyticOrderNatAt F ρ : ℂ) * K ρ
  let leftInt (n : ℕ) :=
    ∫ t : ℝ in lo n..up n, G (((9 / 20 : ℝ) : ℂ) + (t : ℂ) * I)
  let horizontal (u : ℝ) := ∫ σ : ℝ in (9 / 20 : ℝ)..2, G ((σ : ℂ) + (u : ℂ) * I)
  let err (n : ℕ) := I * (horizontal (lo n) - horizontal (up n))
  have hRight (t : ℝ) : G (2 + (t : ℂ) * I) = right t := by
    let s : ℂ := 2 + (t : ℂ) * I
    have hsr : s.re = 2 := by simp [s]
    have hne : s ≠ 1 := by
      intro hs
      have e := congrArg Complex.re hs
      rw [hsr, one_re] at e
      norm_num at e
    have hLne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne)
      (by rw [hsr]; norm_num)
    change (-logDeriv F s + δ / (s - 1)) * K s =
      (-logDeriv (DirichletCharacter.LFunction χ) s) * K s
    rw [logDeriv_regularizedL_eq χ hne hLne]
    ring
  have hRint : Integrable right := GoldbachSmoothing.integrable_twist_vertical χ hx0 hh
  have hLeftBound (n : ℕ) : ‖leftInt n‖ ≤
      L * A * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 :=
    hVertical left x q A (lo n) (up n) hx hq hA.le (contourLog_continuous_left χ hGRH hq1) hbLeft
  have hZeroBound (n : ℕ) : ‖zeros n‖ ≤
      Z * Real.sqrt x * Real.log (2 * (q : ℝ) * x) ^ 2 := hResidues q hq1 χ x (S n) hx (hReal n)
  have hHorizLo : Tendsto (fun n => horizontal (lo n)) atTop (𝓝 0) :=
    tendsto_horizontal_kernel_integral_zero hx hh (by norm_num) hq hB.le (contourLog χ) lo
      hLoAbs (Eventually.of_forall fun n => (hGood n).1.2)
  have hHorizUp : Tendsto (fun n => horizontal (up n)) atTop (𝓝 0) :=
    tendsto_horizontal_kernel_integral_zero hx hh (by norm_num) hq hB.le (contourLog χ) up
      hUpAbs (Eventually.of_forall fun n => (hGood n).2.2)
  have hErr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, sub_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I)).mul (hHorizLo.sub hHorizUp)
  have hRect (n : ℕ) : (∫ t : ℝ in lo n..up n, right t) =
      leftInt n + (2 * Real.pi) • (δ * K 1 - zeros n) + err n := by
    have hFanalytic : AnalyticOnNhd ℂ F (Icc (9 / 20 : ℝ) 2 ×ℂ Icc (lo n) (up n)) :=
      (analytic_regularizedL χ).mono (subset_univ _)
    have hKanalytic : AnalyticOnNhd ℂ K (Icc (9 / 20 : ℝ) 2 ×ℂ Icc (lo n) (up n)) := by
      refine (GoldbachSmoothing.kernel_analytic hx0 hh).mono ?_
      intro z hz
      exact (by norm_num : (0 : ℝ) < 9 / 20).trans_le hz.1.1
    have hr := rectBoundaryIntegral_neg_logDeriv_add_pole_mul F K (S n) δ
      (by norm_num) (by norm_num) (hSign n).1 (hSign n).2 hFanalytic hKanalytic
      (fun z hz => ⟨fun h => (hZeros n z).2 ⟨hz, h⟩, fun h => ((hZeros n z).1 h).2⟩)
      (fun z hz => ⟨(hInside n z hz).1.1, (hInside n z hz).1.2,
        (hInside n z hz).2.1, (hInside n z hz).2.2⟩)
      (fun z _ => regularizedL_analyticOrder_ne_top χ z) (regularizedL_ne_zero_at_one χ)
    have hr' := right_vertical_integral_of_rect hr
    change (∫ t : ℝ in lo n..up n, G (((2 : ℝ) : ℂ) + (t : ℂ) * I)) = _ at hr'
    have hIntegral : (∫ t : ℝ in lo n..up n, G (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ in lo n..up n, right t := by
      simp only [ofReal_ofNat, hRight]
    rw [hIntegral] at hr'
    simpa only [Complex.real_smul, ofReal_mul, ofReal_ofNat, leftInt, horizontal, err, zeros,
      G, contourLog] using hr'
  have hf := vertical_contour_error_le hRint hLoLimit hUpLimit hErr
    (Eventually.of_forall hRect) (Eventually.of_forall hLeftBound) (Eventually.of_forall hZeroBound)
  rw [GoldbachSmoothing.smoothed_twist_eq_vertical χ hx0 hh]
  change ‖c • (∫ t : ℝ, right t) - δ * K 1‖ ≤ _
  exact hf.trans_eq (by dsimp [c, x]; ring)

end Goldbach

namespace GoldbachProgression

open GoldbachSmoothing

set_option maxHeartbeats 1000000 in

theorem progressionBound_of_smoothedTwistedBound
    (hSmoothed : ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q], q = 1 → ∀
      (χ : DirichletCharacter ℂ q) (X : ℕ), 2 ≤ X →
        ‖(∑' n, twistedCoefficient χ n * cutoff (X : ℝ) (Real.sqrt X) n) -
          Goldbach.principalFlag χ * kernel (X : ℝ) (Real.sqrt X) 1‖ ≤
          D * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → q = 1 → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  classical
  apply progressionBound_of_twistedBound
  obtain ⟨D, hD, hEstimate⟩ := hSmoothed
  refine ⟨D + 2, by linarith, ?_⟩
  intro q _ hq1 χ X hX
  let h := Real.sqrt (X : ℝ)
  let L := Real.log (2 * (q : ℝ) * (X : ℝ))
  let A : ℂ := ∑' n, twistedCoefficient χ n * cutoff (X : ℝ) h n
  let M : ℂ := Goldbach.principalFlag χ * kernel (X : ℝ) h 1
  let S : ℂ := twistedVonMangoldt χ X
  let P : ℂ := principalMainTerm χ X
  have hXR : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hqR : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hh : 0 < h := Real.sqrt_pos.2 (by linarith)
  have hArg : 2 * (X : ℝ) ≤ 2 * (q : ℝ) * (X : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hL : 1 ≤ L := by
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    exact hlog4.trans (Real.log_le_log (by norm_num)
      ((by linarith : (4 : ℝ) ≤ 2 * (X : ℝ)).trans hArg))
  have hLsq : L ≤ L ^ 2 := by
    nlinarith [mul_nonneg (zero_le_one.trans hL) (sub_nonneg.mpr hL)]
  have hXS : ‖S - A‖ ≤ h * L ^ 2 := by
    calc
      ‖S - A‖ = ‖A - S‖ := norm_sub_rev _ _
      _ ≤ h * Real.log (2 * (X : ℝ)) := norm_twisted_smoothing_error χ X hX
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left
        ((Real.log_le_log (by linarith) hArg).trans hLsq) hh.le
  have hAM : ‖A - M‖ ≤ D * h * L ^ 2 := hEstimate q hq1 χ X hX
  have hP : P = Goldbach.principalFlag χ * (X : ℂ) := by
    by_cases hχ : χ = 1 <;> simp [P, principalMainTerm, Goldbach.principalFlag, hχ]
  have hFlag : ‖Goldbach.principalFlag χ‖ ≤ 1 := by
    by_cases hχ : χ = 1 <;> simp [Goldbach.principalFlag, hχ]
  have hKernel : kernel (X : ℝ) h 1 - (X : ℂ) = ((h / 2 : ℝ) : ℂ) := by
    simp only [kernel_at_one hh, Complex.ofReal_add, Complex.ofReal_natCast, add_sub_cancel_left]
  have hHalf : 0 ≤ h / 2 := div_nonneg hh.le (by norm_num)
  have hMP : ‖M - P‖ ≤ h * L ^ 2 := by
    change ‖Goldbach.principalFlag χ * kernel (X : ℝ) h 1 - P‖ ≤ _
    rw [hP, ← mul_sub, hKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hHalf]
    calc
      _ ≤ 1 * (h / 2) := mul_le_mul_of_nonneg_right hFlag hHalf
      _ ≤ h := by linarith
      _ = h * 1 := (mul_one _).symm
      _ ≤ h * L ^ 2 := mul_le_mul_of_nonneg_left (hL.trans hLsq) hh.le
  change ‖S - P‖ ≤ (D + 2) * h * L ^ 2
  calc
    ‖S - P‖ ≤ ‖S - A‖ + ‖A - P‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖S - A‖ + (‖A - M‖ + ‖M - P‖) :=
      (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ h * L ^ 2 + (D * h * L ^ 2 + h * L ^ 2) :=
      (add_le_add hXS (add_le_add hAM hMP))
    _ = _ := by ring

end GoldbachProgression

theorem RHSquare.rh_psi_bound (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % 1 = 0 % 1))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient 1 : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * ((1 : ℕ) : ℝ) * (X : ℝ))) ^ 2 := by
  have hGRH1 : Goldbach.GRH1 := by
    intro χ s hs hs1 hL
    have hζ : riemannZeta s = 0 := by
      rwa [DirichletCharacter.LFunction_modOne_eq] at hL
    apply hRH s hζ
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.neg_im,
        Complex.im_ofNat, Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.add_im,
        Complex.natCast_im, Complex.one_im] at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    · rintro rfl
      simp at hs1
  obtain ⟨C, hC, h⟩ := GoldbachProgression.progressionBound_of_smoothedTwistedBound
    (Goldbach.uniform_smoothed_dirichlet_estimate hGRH1)
  exact ⟨C, hC, fun X hX => h 1 0 X one_pos rfl (Nat.coprime_zero_left 1 |>.mpr rfl) hX⟩

open Real Finset

namespace RHSquare

lemma abel_sum (a b : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ range (X + 1), a n * b n =
      (∑ k ∈ range (X + 1), a k) * b X -
        ∑ m ∈ range X, (∑ k ∈ range (m + 1), a k) * (b (m + 1) - b m) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun m => (∑ k ∈ range (m + 1), a k) *
      (b (m + 1) - b m)), sum_range_succ a (X + 1)]
    ring

lemma sum_inv_sqrt_le (X : ℕ) :
    ∑ m ∈ range (X + 1), (if m = 0 then (0 : ℝ) else 1 / √(m : ℝ)) ≤ 2 * √(X : ℝ) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_range_succ, if_neg (Nat.succ_ne_zero X)]
    have ha : 0 < √((X + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
    have ha2 : √((X + 1 : ℕ) : ℝ) ^ 2 = (X : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hb2 : √(X : ℝ) ^ 2 = (X : ℝ) := Real.sq_sqrt (by positivity)
    have hab : √(X : ℝ) ≤ √((X + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have key : 1 / √((X + 1 : ℕ) : ℝ) ≤ 2 * √((X + 1 : ℕ) : ℝ) - 2 * √(X : ℝ) := by
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (√((X + 1 : ℕ) : ℝ) - √(X : ℝ))]
    linarith

lemma log_succ_sub_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hmR.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by push_cast; field_simp; ring
  linarith

lemma log_succ_sub_nonneg (m : ℕ) :
    0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hm) (by push_cast; linarith)
    linarith

lemma mul_log_succ_sub_ge (m : ℕ) (hm : 1 ≤ m) :
    1 - 1 / ((m : ℝ) + 1) ≤ (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hmR.ne']
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : 1 - (((m + 1 : ℕ) : ℝ) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by push_cast; field_simp; ring
  rw [e] at h
  have e2 : 1 - 1 / ((m : ℝ) + 1) = (m : ℝ) * (1 / ((m : ℝ) + 1)) := by field_simp; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left h hmR.le

lemma mul_log_succ_sub_ge' (m : ℕ) :
    1 - 1 / ((m : ℝ) + 1) ≤ (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact mul_log_succ_sub_ge m hm

lemma mul_log_succ_sub_le_one (m : ℕ) :
    (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := log_succ_sub_le m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    calc (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ (m : ℝ) * (1 / m) :=
          mul_le_mul_of_nonneg_left h hmR.le
      _ = 1 := by field_simp

lemma sum_inv_succ_eq_harmonic (X : ℕ) :
    ∑ m ∈ range X, 1 / ((m : ℝ) + 1) = (harmonic X : ℝ) := by
  unfold harmonic
  push_cast
  simp [one_div]

lemma main_term_bound (X : ℕ) :
    |(X : ℝ) - ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))| ≤
      1 + Real.log X := by
  have hup : ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ X := by
    calc ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ))
        ≤ ∑ m ∈ range X, (1 : ℝ) := Finset.sum_le_sum fun m _ => mul_log_succ_sub_le_one m
      _ = X := by simp
  have hlow : ∑ m ∈ range X, (1 - 1 / ((m : ℝ) + 1)) ≤
      ∑ m ∈ range X, (m : ℝ) * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) :=
    Finset.sum_le_sum fun m _ => mul_log_succ_sub_ge' m
  rw [Finset.sum_sub_distrib, sum_inv_succ_eq_harmonic] at hlow
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hlow
  have hH : (harmonic X : ℝ) ≤ 1 + Real.log X := harmonic_le_one_add_log X
  rw [abs_le]
  constructor <;> linarith

lemma sum_not_prime_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n ≤
      2 * √(X : ℝ) * Real.log X := by
  calc ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n
      = Chebyshev.psi X - Chebyshev.theta X := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hk ⊢
          exact ⟨by omega, hk.2⟩
        · intro k hk hk'
          have hk0 : k = 0 := by
            by_contra h
            apply hk'
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hk ⊢
            exact ⟨⟨by omega, by omega⟩, hk.2⟩
          subst hk0
          simp
    _ ≤ 2 * √(X : ℝ) * Real.log X := Chebyshev.psi_sub_theta_le (by exact_mod_cast hX)

set_option maxHeartbeats 2000000 in
theorem derive
    (hψ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      |(∑ k ∈ range (X + 1), ArithmeticFunction.vonMangoldt k) - X| ≤
        C * √(X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, 2 ≤ X →
      |(∑ n ∈ range (X + 1), ArithmeticFunction.vonMangoldt n ^ 2) - ((X : ℝ) * Real.log X - X)| ≤
        K * √(X : ℝ) * Real.log (2 + (X : ℝ)) ^ 3 := by
  obtain ⟨C, hC, hE⟩ := hψ
  refine ⟨12 * C + 6, by positivity, ?_⟩
  intro X hX
  set Lam := ArithmeticFunction.vonMangoldt with hLam
  set ψN : ℕ → ℝ := fun m => ∑ k ∈ range (m + 1), Lam k with hψN
  set Δ : ℕ → ℝ := fun m => Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) with hΔ
  set S1 := ∑ n ∈ range (X + 1), Lam n * Real.log (n : ℝ) with hS1
  set C0 := ∑ n ∈ range (X + 1), Lam n ^ 2 with hC0
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : 1 ≤ X := by omega

  have hdiff : 0 ≤ S1 - C0 ∧ S1 - C0 ≤ Real.log X * (2 * √(X : ℝ) * Real.log X) := by
    have heq : S1 - C0 = ∑ n ∈ range (X + 1), Lam n * (Real.log (n : ℝ) - Lam n) := by
      rw [hS1, hC0, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [heq]
    have hterm : ∀ n ∈ range (X + 1), 0 ≤ Lam n * (Real.log (n : ℝ) - Lam n) ∧
        Lam n * (Real.log (n : ℝ) - Lam n) ≤
          (if n.Prime then 0 else Lam n * Real.log X) := by
      intro n hn
      have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hLam0 : 0 ≤ Lam n := ArithmeticFunction.vonMangoldt_nonneg
      have hLamle : Lam n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      by_cases hp : n.Prime
      · rw [if_pos hp, hLam, ArithmeticFunction.vonMangoldt_apply_prime hp]
        simp
      · rw [if_neg hp]
        refine ⟨mul_nonneg hLam0 (by linarith), ?_⟩
        have hlogn : Real.log (n : ℝ) ≤ Real.log X := by
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simp; exact Real.log_nonneg (by linarith)
          · exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnX)
        nlinarith
    constructor
    · exact Finset.sum_nonneg fun n hn => (hterm n hn).1
    · calc ∑ n ∈ range (X + 1), Lam n * (Real.log (n : ℝ) - Lam n)
          ≤ ∑ n ∈ range (X + 1), (if n.Prime then 0 else Lam n * Real.log X) :=
            Finset.sum_le_sum fun n hn => (hterm n hn).2
        _ = Real.log X * ∑ n ∈ (range (X + 1)).filter (fun n => ¬ n.Prime), Lam n := by
            rw [Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun n _ => ?_
            split_ifs <;> ring
        _ ≤ Real.log X * (2 * √(X : ℝ) * Real.log X) :=
            mul_le_mul_of_nonneg_left (sum_not_prime_le X hX1)
              (Real.log_nonneg (by linarith))

  have habel : S1 = ψN X * Real.log X - ∑ m ∈ range X, ψN m * Δ m := by
    rw [hS1, abel_sum Lam (fun n => Real.log (n : ℝ)) X]
  have hsplit : S1 - ((X : ℝ) * Real.log X - X) =
      (ψN X - X) * Real.log X +
        ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m) -
        ∑ m ∈ range X, (ψN m - m) * Δ m := by
    rw [habel]
    have : ∑ m ∈ range X, ψN m * Δ m =
        ∑ m ∈ range X, (m : ℝ) * Δ m + ∑ m ∈ range X, (ψN m - m) * Δ m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [this]
    ring

  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set l2 := Real.log (2 * (X : ℝ)) with hl2
  have hl20 : 0 ≤ l2 := Real.log_nonneg (by linarith)
  have hsq1 : 1 ≤ √(X : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have t1 : |(ψN X - X) * Real.log X| ≤ C * √(X : ℝ) * l2 ^ 2 * Real.log X := by
    rw [abs_mul, abs_of_nonneg hlogX0]
    exact mul_le_mul_of_nonneg_right (hE X hX) hlogX0
  have t2 : |(X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m| ≤ 1 + Real.log X := main_term_bound X

  set g : ℕ → ℝ := fun m => if m = 0 then 0 else 1 / √(m : ℝ) with hg
  have hterm3 : ∀ m ∈ range X, |(ψN m - m) * Δ m| ≤
      (if m = 1 then (1 : ℝ) else 0) + C * l2 ^ 2 * g m := by
    intro m hm
    have hmX : m < X := Finset.mem_range.mp hm
    have hΔ0 : 0 ≤ Δ m := log_succ_sub_nonneg m
    have hgm : 0 ≤ g m := by
      simp only [hg]; split_ifs <;> positivity
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · simp [hΔ, hψN]
        positivity
      · have hψ1 : ψN 1 = 0 := by simp [hψN, Finset.sum_range_succ, hLam]
        have hΔ1 : Δ 1 = Real.log 2 := by simp [hΔ]; norm_num
        rw [hψ1, hΔ1, if_pos rfl]
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_two_lt_d9; linarith
        have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        rw [abs_of_nonpos (by push_cast; nlinarith)]
        push_cast
        nlinarith [mul_nonneg (mul_nonneg hC.le (sq_nonneg l2)) hgm]
    · rw [if_neg (by omega)]
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hEm := hE m hm2
      have hlogm : Real.log (2 * (m : ℝ)) ≤ l2 := by
        rw [hl2]; apply Real.log_le_log (by linarith)
        have : (m : ℝ) ≤ X := by exact_mod_cast hmX.le
        linarith
      have hlogm0 : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
      have hΔle : Δ m ≤ 1 / (m : ℝ) := log_succ_sub_le m (by omega)
      have hsqm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hgm' : g m = 1 / √(m : ℝ) := by simp only [hg]; rw [if_neg (by omega)]
      rw [hgm', zero_add, abs_mul, abs_of_nonneg hΔ0]
      have hsq : √(m : ℝ) * (1 / (m : ℝ)) = 1 / √(m : ℝ) := by
        have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ m by linarith)
        calc √(m : ℝ) * (1 / (m : ℝ)) = √(m : ℝ) / (√(m : ℝ) * √(m : ℝ)) := by rw [h]; ring
          _ = 1 / √(m : ℝ) := by field_simp
      calc |ψN m - (m : ℝ)| * Δ m
          ≤ (C * √(m : ℝ) * Real.log (2 * (m : ℝ)) ^ 2) * (1 / (m : ℝ)) :=
            mul_le_mul hEm hΔle hΔ0 (by positivity)
        _ ≤ (C * √(m : ℝ) * l2 ^ 2) * (1 / (m : ℝ)) := by
            gcongr
        _ = C * l2 ^ 2 * (√(m : ℝ) * (1 / (m : ℝ))) := by ring
        _ = C * l2 ^ 2 * (1 / √(m : ℝ)) := by rw [hsq]
  have t3 : |∑ m ∈ range X, (ψN m - m) * Δ m| ≤ 1 + C * l2 ^ 2 * (2 * √(X : ℝ)) := by
    calc |∑ m ∈ range X, (ψN m - m) * Δ m|
        ≤ ∑ m ∈ range X, |(ψN m - m) * Δ m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ range X, ((if m = 1 then (1 : ℝ) else 0) + C * l2 ^ 2 * g m) :=
          Finset.sum_le_sum hterm3
      _ = (∑ m ∈ range X, (if m = 1 then (1 : ℝ) else 0)) + C * l2 ^ 2 * ∑ m ∈ range X, g m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 1 + C * l2 ^ 2 * (2 * √(X : ℝ)) := by
          have h1 : (∑ m ∈ range X, (if m = 1 then (1 : ℝ) else 0)) ≤ 1 := by
            rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
          have hg0 : ∀ m, 0 ≤ g m := fun m => by simp only [hg]; split_ifs <;> positivity
          have h2 : ∑ m ∈ range X, g m ≤ 2 * √(X : ℝ) :=
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => hg0 m)).trans (sum_inv_sqrt_le X)
          have hCl : 0 ≤ C * l2 ^ 2 := by positivity
          nlinarith

  set L := Real.log (2 + (X : ℝ)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have : Real.exp 1 ≤ 2 + (X : ℝ) := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hlogXL : Real.log X ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) (by linarith)
  have hl2L : l2 ≤ 2 * L := by
    rw [hl2, hL, ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show ((2 : ℝ) + X) ^ (2 : ℝ) = (2 + X) ^ 2 by norm_cast]
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hsX0 : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
  have key : |C0 - ((X : ℝ) * Real.log X - X)| ≤
      C * √(X : ℝ) * l2 ^ 2 * Real.log X + (1 + Real.log X) + (1 + C * l2 ^ 2 * (2 * √(X : ℝ)))
        + Real.log X * (2 * √(X : ℝ) * Real.log X) := by
    have e : C0 - ((X : ℝ) * Real.log X - X) =
        (S1 - ((X : ℝ) * Real.log X - X)) - (S1 - C0) := by ring
    rw [e, hsplit]
    have a1 := abs_sub ((ψN X - X) * Real.log X + ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m) -
        ∑ m ∈ range X, (ψN m - m) * Δ m) (S1 - C0)
    have a2 := abs_sub ((ψN X - X) * Real.log X + ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m))
        (∑ m ∈ range X, (ψN m - m) * Δ m)
    have a3 := abs_add_le ((ψN X - X) * Real.log X) ((X : ℝ) - ∑ m ∈ range X, (m : ℝ) * Δ m)
    rw [abs_of_nonneg hdiff.1] at a1
    linarith [hdiff.2]

  have hl2sq : l2 ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have b1 : C * √(X : ℝ) * l2 ^ 2 * Real.log X ≤ 4 * C * √(X : ℝ) * L ^ 3 := by
    have : l2 ^ 2 * Real.log X ≤ 4 * L ^ 2 * L := mul_le_mul hl2sq hlogXL hlogX0 (by positivity)
    calc C * √(X : ℝ) * l2 ^ 2 * Real.log X = C * √(X : ℝ) * (l2 ^ 2 * Real.log X) := by ring
      _ ≤ C * √(X : ℝ) * (4 * L ^ 2 * L) := by gcongr
      _ = 4 * C * √(X : ℝ) * L ^ 3 := by ring
  have b2 : (1 + Real.log X) + 1 ≤ 3 * √(X : ℝ) * L ^ 3 := by
    have hL3 : L ≤ L ^ 3 := by nlinarith
    have : 2 + L ≤ 3 * L ^ 3 := by nlinarith
    nlinarith
  have b3 : C * l2 ^ 2 * (2 * √(X : ℝ)) ≤ 8 * C * √(X : ℝ) * L ^ 3 := by
    have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith
    calc C * l2 ^ 2 * (2 * √(X : ℝ)) ≤ C * (4 * L ^ 2) * (2 * √(X : ℝ)) := by gcongr
      _ ≤ C * (4 * L ^ 3) * (2 * √(X : ℝ)) := by gcongr
      _ = 8 * C * √(X : ℝ) * L ^ 3 := by ring
  have b4 : Real.log X * (2 * √(X : ℝ) * Real.log X) ≤ 3 * √(X : ℝ) * L ^ 3 := by
    have hlx2 : Real.log X * Real.log X ≤ L ^ 2 := by nlinarith
    have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith
    nlinarith
  calc |C0 - ((X : ℝ) * Real.log X - X)| ≤ _ := key
    _ ≤ (12 * C + 6) * √(X : ℝ) * L ^ 3 := by nlinarith

end RHSquare

theorem RHSquare.rh_psi_bound' (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      |(∑ k ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt k) - X| ≤
        C * √(X : ℝ) * Real.log (2 * (X : ℝ)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := RHSquare.rh_psi_bound hRH
  refine ⟨C, hC, fun X hX => ?_⟩
  have h1 := h X hX
  have hf : (Finset.range (X + 1)).filter (fun k => k % 1 = 0 % 1) = Finset.range (X + 1) :=
    Finset.filter_true_of_mem fun k _ => by simp [Nat.mod_one]
  rw [hf, Nat.totient_one, Nat.cast_one, div_one] at h1
  simpa using h1

end
end
end MmPsiBoundRef

theorem hc_moebius_aux_psi_bound (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      |(∑ k ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt k) - (X : ℝ)| ≤
        C * Real.sqrt X * Real.log (2 + (X : ℝ)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := MmPsiBoundRef.RHSquare.rh_psi_bound' hRH
  refine ⟨max (4 * C) 1, by positivity, fun X => ?_⟩
  rcases lt_or_ge X 2 with hX | hX
  ·
    have hX01 : X = 0 ∨ X = 1 := by omega
    rcases hX01 with rfl | rfl
    · have hsum : (∑ k ∈ Finset.range ((0:ℕ) + 1), ArithmeticFunction.vonMangoldt k) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        simp only [Finset.mem_range] at hk
        interval_cases k
        rw [ArithmeticFunction.vonMangoldt_apply]
        exact if_neg not_isPrimePow_zero
      rw [hsum]
      norm_num
    · have hsum : (∑ k ∈ Finset.range ((1:ℕ) + 1), ArithmeticFunction.vonMangoldt k) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        simp only [Finset.mem_range] at hk
        interval_cases k
        · rw [ArithmeticFunction.vonMangoldt_apply]
          exact if_neg not_isPrimePow_zero
        · exact ArithmeticFunction.vonMangoldt_apply_one
      have hlog3 : (1:ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have h := Real.exp_one_lt_d9
        norm_num at h ⊢
        linarith
      have hM : (1:ℝ) ≤ max (4 * C) 1 := le_max_right _ _
      have hL2 : (1:ℝ) ≤ Real.log 3 ^ 2 := by nlinarith
      have key : (1:ℝ) ≤ max (4 * C) 1 * Real.log 3 ^ 2 := by
        calc (1:ℝ) = max (4 * C) 1 * 1 - (max (4 * C) 1 - 1) := by ring
          _ ≤ max (4 * C) 1 * Real.log 3 ^ 2 := by
              have h1 : max (4 * C) 1 * 1 ≤ max (4 * C) 1 * Real.log 3 ^ 2 :=
                mul_le_mul_of_nonneg_left hL2 (by linarith)
              linarith
      rw [hsum]
      norm_num [Real.sqrt_one]
      linarith
  ·
    have hX2 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    have h2X : (0:ℝ) < 2 * X := by linarith
    have hkey : 2 * (X:ℝ) ≤ (2 + (X:ℝ))^2 := by nlinarith
    have hlog : Real.log (2 * (X:ℝ)) ≤ 2 * Real.log (2 + (X:ℝ)) := by
      have h1 := Real.log_le_log h2X hkey
      rw [Real.log_pow] at h1
      simpa using h1
    have hlog0 : 0 ≤ Real.log (2 * (X:ℝ)) := Real.log_nonneg (by nlinarith)
    have hlog2 : 0 ≤ Real.log (2 + (X:ℝ)) := Real.log_nonneg (by nlinarith)
    have hsq : Real.log (2 * (X:ℝ))^2 ≤ 4 * Real.log (2 + (X:ℝ))^2 := by
      have hprod : 0 ≤ (2 * Real.log (2 + (X:ℝ)) - Real.log (2 * (X:ℝ))) *
          (2 * Real.log (2 + (X:ℝ)) + Real.log (2 * (X:ℝ))) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    calc |(∑ k ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt k) - (X : ℝ)|
        ≤ C * Real.sqrt (X:ℝ) * Real.log (2 * (X:ℝ))^2 := h X hX
      _ ≤ C * Real.sqrt (X:ℝ) * (4 * Real.log (2 + (X:ℝ))^2) := by
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * C * Real.sqrt (X:ℝ) * Real.log (2 + (X:ℝ))^2 := by ring
      _ ≤ max (4 * C) 1 * Real.sqrt (X:ℝ) * Real.log (2 + (X:ℝ))^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (sq_nonneg _)

open Finset Filter

lemma hc_moebius_aux_mmB_power_tail (n : ℕ) (hn : 2 ≤ n) :
    |(∑' d : ℕ, (d : ℝ) ^ ((-5 : ℝ) / 4)) -
        ∑ d ∈ range n, (d : ℝ) ^ ((-5 : ℝ) / 4)| ≤
      8 * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hc : 0 < (n : ℝ) - 1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ ((-5 : ℝ) / 4))
      (Set.Ici ((n : ℝ) - 1)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
    intro x hx
    exact hc.trans_le hx
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ ((-5 : ℝ) / 4))
      (Set.Ioi ((n : ℝ) - 1)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hnonneg : ∀ x ∈ Set.Ioi ((n : ℝ) - 1), 0 ≤ x ^ ((-5 : ℝ) / 4) := by
    intro x hx
    exact Real.rpow_nonneg (hc.trans hx).le _
  have hbase := AntitoneOn.abs_tsum_sub_sum_range_le_integral
    (N := n) (f := fun x : ℝ => x ^ ((-5 : ℝ) / 4))
    (by omega) hanti hint hnonneg
  have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hroot : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc
      (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have htwo : (2 : ℝ) ^ ((-1 : ℝ) / 4) =
      ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [show ((-1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    |(∑' d : ℕ, (d : ℝ) ^ ((-5 : ℝ) / 4)) -
        ∑ d ∈ range n, (d : ℝ) ^ ((-5 : ℝ) / 4)| ≤
        ∫ x in Set.Ioi ((n : ℝ) - 1), x ^ ((-5 : ℝ) / 4) := hbase
    _ = 4 * ((n : ℝ) - 1) ^ ((-1 : ℝ) / 4) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hc]
      ring_nf
    _ ≤ 4 * ((n : ℝ) / 2) ^ ((-1 : ℝ) / 4) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by norm_num)) (by norm_num)
    _ = 4 * ((n : ℝ) ^ ((-1 : ℝ) / 4) * (2 : ℝ) ^ ((1 : ℝ) / 4)) := by
      rw [Real.div_rpow hnpos.le (by norm_num), htwo]
      simp only [div_eq_mul_inv, inv_inv]
    _ ≤ 8 * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
      have hp : 0 ≤ (n : ℝ) ^ ((-1 : ℝ) / 4) := Real.rpow_nonneg hnpos.le _
      nlinarith

lemma hc_moebius_aux_mmB_log_le_eight_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 8 * x ^ ((1 : ℝ) / 8) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < x ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hxpos _
  have hlog := Real.log_le_sub_one_of_pos hypos
  have hlog_eq : Real.log x = 8 * Real.log (x ^ ((1 : ℝ) / 8)) := by
    rw [Real.log_rpow hxpos]
    ring
  rw [hlog_eq]
  nlinarith

lemma hc_moebius_aux_mmB_log_sq_bound (d : ℕ) (hd : 1 ≤ d) :
    (Real.log (2 + (d : ℝ))) ^ 2 ≤ 192 * (d : ℝ) ^ ((1 : ℝ) / 4) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : (1 : ℝ) ≤ 2 + (d : ℝ) := by linarith
  have hlog := hc_moebius_aux_mmB_log_le_eight_rpow hx
  have hlog_nonneg : 0 ≤ Real.log (2 + (d : ℝ)) := Real.log_nonneg hx
  have hsquare := mul_self_le_mul_self hlog_nonneg hlog
  have hy_sq : ((2 + (d : ℝ)) ^ ((1 : ℝ) / 8)) ^ 2 =
      (2 + (d : ℝ)) ^ ((1 : ℝ) / 4) := by
    calc
      ((2 + (d : ℝ)) ^ ((1 : ℝ) / 8)) ^ 2 =
          (2 + (d : ℝ)) ^ ((1 : ℝ) / 8) *
            (2 + (d : ℝ)) ^ ((1 : ℝ) / 8) := by ring
      _ = (2 + (d : ℝ)) ^ (((1 : ℝ) / 8) + ((1 : ℝ) / 8)) :=
        (Real.rpow_add (by linarith : 0 < 2 + (d : ℝ)) _ _).symm
      _ = (2 + (d : ℝ)) ^ ((1 : ℝ) / 4) := by norm_num
  have hx_le : 2 + (d : ℝ) ≤ 3 * (d : ℝ) := by linarith
  have hquarter :
      (2 + (d : ℝ)) ^ ((1 : ℝ) / 4) ≤
        (3 * (d : ℝ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by linarith) hx_le (by norm_num)
  have hthree : (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ 3 := by
    calc
      (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have hdquarter_nonneg : 0 ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (by linarith) _
  calc
    (Real.log (2 + (d : ℝ))) ^ 2 ≤
      (8 * (2 + (d : ℝ)) ^ ((1 : ℝ) / 8)) ^ 2 := by nlinarith
    _ = 64 * (2 + (d : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [show (8 * (2 + (d : ℝ)) ^ ((1 : ℝ) / 8)) ^ 2 =
        64 * ((2 + (d : ℝ)) ^ ((1 : ℝ) / 8)) ^ 2 by ring, hy_sq]
    _ ≤ 64 * (3 * (d : ℝ)) ^ ((1 : ℝ) / 4) := by gcongr
    _ = 64 * ((3 : ℝ) ^ ((1 : ℝ) / 4) * (d : ℝ) ^ ((1 : ℝ) / 4)) := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
    _ ≤ 192 * (d : ℝ) ^ ((1 : ℝ) / 4) := by nlinarith

noncomputable def hc_moebius_aux_mmB_rho (d : ℕ) : ℝ :=
  (∑ k ∈ range (d + 1), ArithmeticFunction.vonMangoldt k) - (d : ℝ)

lemma hc_moebius_aux_mmB_rho_zero : hc_moebius_aux_mmB_rho 0 = 0 := by
  simp [hc_moebius_aux_mmB_rho, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]

lemma hc_moebius_aux_mmB_rho_step (d : ℕ) (hd : 1 ≤ d) :
    ArithmeticFunction.vonMangoldt d - 1 = hc_moebius_aux_mmB_rho d - hc_moebius_aux_mmB_rho (d - 1) := by
  simp only [hc_moebius_aux_mmB_rho, Nat.sub_add_cancel hd]
  rw [Finset.sum_range_succ, Nat.cast_sub hd]
  ring

lemma hc_moebius_aux_mmB_rho_power_bound (C : ℝ) (hC : 0 < C)
    (hψ : ∀ X : ℕ, |(∑ k ∈ range (X + 1), ArithmeticFunction.vonMangoldt k) - (X : ℝ)| ≤
      C * Real.sqrt X * Real.log (2 + (X : ℝ)) ^ 2) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ d : ℕ, |hc_moebius_aux_mmB_rho d| ≤ C₂ * (d : ℝ) ^ ((3 : ℝ) / 4) := by
  refine ⟨192 * C, by positivity, ?_⟩
  intro d
  by_cases hd : d = 0
  · subst d
    simp [hc_moebius_aux_mmB_rho_zero, Real.zero_rpow (by norm_num : ((3 : ℝ) / 4) ≠ 0)]
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd1
  have hlog := hc_moebius_aux_mmB_log_sq_bound d hd1
  have hpow : (d : ℝ) ^ ((1 : ℝ) / 2) * (d : ℝ) ^ ((1 : ℝ) / 4) =
      (d : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hdpos]
    congr 1
    norm_num
  calc
    |hc_moebius_aux_mmB_rho d| ≤ C * (d : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (2 + (d : ℝ)) ^ 2 := by
      simpa [hc_moebius_aux_mmB_rho, Real.sqrt_eq_rpow] using hψ d
    _ ≤ C * (d : ℝ) ^ ((1 : ℝ) / 2) *
        (192 * (d : ℝ) ^ ((1 : ℝ) / 4)) := by
      exact mul_le_mul_of_nonneg_left hlog
        (mul_nonneg hC.le (Real.rpow_nonneg hdpos.le _))
    _ = (192 * C) * (d : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← hpow]
      ring

lemma hc_moebius_aux_mmB_kernel_bound (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hrho : ∀ d : ℕ, |hc_moebius_aux_mmB_rho d| ≤ C₂ * (d : ℝ) ^ ((3 : ℝ) / 4))
    (d : ℕ) :
    ‖hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))‖ ≤
      C₂ * (d : ℝ) ^ ((-5 : ℝ) / 4) := by
  by_cases hd : d = 0
  · subst d
    simp [Real.zero_rpow (by norm_num : ((-5 : ℝ) / 4) ≠ 0)]
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd1
  have hdenpos : 0 < (d : ℝ) * ((d : ℝ) + 1) := by positivity
  have hpowratio : (d : ℝ) ^ ((3 : ℝ) / 4) /
      ((d : ℝ) * (d : ℝ)) = (d : ℝ) ^ ((-5 : ℝ) / 4) := by
    rw [show (d : ℝ) * (d : ℝ) = (d : ℝ) ^ (2 : ℕ) by ring,
      ← Real.rpow_natCast, ← Real.rpow_sub hdpos]
    congr 1
    norm_num
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
  calc
    |hc_moebius_aux_mmB_rho d| / ((d : ℝ) * ((d : ℝ) + 1)) ≤
        (C₂ * (d : ℝ) ^ ((3 : ℝ) / 4)) /
          ((d : ℝ) * ((d : ℝ) + 1)) := by
      gcongr
      exact hrho d
    _ ≤ (C₂ * (d : ℝ) ^ ((3 : ℝ) / 4)) /
        ((d : ℝ) * (d : ℝ)) := by
      gcongr
      nlinarith
    _ = C₂ * ((d : ℝ) ^ ((3 : ℝ) / 4) /
        ((d : ℝ) * (d : ℝ))) := by ring
    _ = C₂ * (d : ℝ) ^ ((-5 : ℝ) / 4) := by rw [hpowratio]

lemma hc_moebius_aux_mmB_kernel_summable (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hrho : ∀ d : ℕ, |hc_moebius_aux_mmB_rho d| ≤ C₂ * (d : ℝ) ^ ((3 : ℝ) / 4)) :
    Summable (fun d : ℕ => hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) := by
  have hp : Summable (fun d : ℕ => (d : ℝ) ^ ((-5 : ℝ) / 4)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact Summable.of_norm_bounded (hp.mul_left C₂)
    (hc_moebius_aux_mmB_kernel_bound C₂ hC₂ hrho)

lemma hc_moebius_aux_mmB_abel_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ)) =
      hc_moebius_aux_mmB_rho n / (n : ℝ) +
        ∑ d ∈ Icc 1 (n - 1),
          hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
      simp [hc_moebius_aux_mmB_rho, ArithmeticFunction.vonMangoldt_apply,
        not_isPrimePow_zero, not_isPrimePow_one, Finset.sum_range_succ]
  | succ n hn ih =>
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hstep := hc_moebius_aux_mmB_rho_step (n + 1) (by omega)
      have hkernel_sum :
          (∑ d ∈ Icc 1 n,
            hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) =
            (∑ d ∈ Icc 1 (n - 1),
              hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) +
              hc_moebius_aux_mmB_rho n / ((n : ℝ) * ((n : ℝ) + 1)) := by
        have h := Finset.sum_Icc_succ_top (a := 1) (b := n - 1) (by omega)
          (fun d => hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1)))
        rw [show n - 1 + 1 = n by omega] at h
        exact h
      rw [show n + 1 - 1 = n by omega]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [hkernel_sum]
      rw [ih, hstep]
      rw [show n + 1 - 1 = n by omega]
      push_cast
      field_simp
      ring

lemma hc_moebius_aux_mmB_kernel_Icc_range (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Icc 1 (n - 1),
      hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) =
      ∑ d ∈ range n, hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hsum := Finset.sum_Icc_succ_top (a := 1) (b := n - 1) (by omega)
        (fun d => hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1)))
      rw [show n - 1 + 1 = n by omega] at hsum
      rw [show n + 1 - 1 = n by omega, Finset.sum_range_succ, hsum, ih]

lemma hc_moebius_aux_mmB_endpoint_bound (C₂ : ℝ)
    (hrho : ∀ d : ℕ, |hc_moebius_aux_mmB_rho d| ≤ C₂ * (d : ℝ) ^ ((3 : ℝ) / 4))
    (n : ℕ) (hn : 1 ≤ n) :
    |hc_moebius_aux_mmB_rho n / (n : ℝ)| ≤ C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ ((3 : ℝ) / 4) / (n : ℝ) =
      (n : ℝ) ^ ((-1 : ℝ) / 4) := by
    calc
      (n : ℝ) ^ ((3 : ℝ) / 4) / (n : ℝ) =
          (n : ℝ) ^ ((3 : ℝ) / 4) / (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ (((3 : ℝ) / 4) - 1) :=
        (Real.rpow_sub hnpos _ _).symm
      _ = (n : ℝ) ^ ((-1 : ℝ) / 4) := by congr 1; norm_num
  rw [abs_div, abs_of_pos hnpos]
  calc
    |hc_moebius_aux_mmB_rho n| / (n : ℝ) ≤
        (C₂ * (n : ℝ) ^ ((3 : ℝ) / 4)) / (n : ℝ) := by
      gcongr
      exact hrho n
    _ = C₂ * ((n : ℝ) ^ ((3 : ℝ) / 4) / (n : ℝ)) := by ring
    _ = C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by rw [hpow]

lemma hc_moebius_aux_mmB_kernel_tail_bound (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hrho : ∀ d : ℕ, |hc_moebius_aux_mmB_rho d| ≤ C₂ * (d : ℝ) ^ ((3 : ℝ) / 4))
    (n : ℕ) (hn : 2 ≤ n) :
    ‖∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
      (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))‖ ≤
        8 * C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
  let b : ℕ → ℝ := fun d =>
    hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))
  let p : ℕ → ℝ := fun d => (d : ℝ) ^ ((-5 : ℝ) / 4)
  have hb : Summable b := hc_moebius_aux_mmB_kernel_summable C₂ hC₂ hrho
  have hp : Summable p := Real.summable_nat_rpow.mpr (by norm_num)
  have hb_shift : Summable (fun j => b (j + n)) :=
    (summable_nat_add_iff n).2 hb
  have hp_shift : Summable (fun j => p (j + n)) :=
    (summable_nat_add_iff n).2 hp
  have hb_norm : Summable (fun j => ‖b (j + n)‖) := hb_shift.norm
  have hscaled : Summable (fun j => C₂ * p (j + n)) := hp_shift.mul_left C₂
  have hpoint : ∀ j : ℕ, ‖b (j + n)‖ ≤ C₂ * p (j + n) := by
    intro j
    exact hc_moebius_aux_mmB_kernel_bound C₂ hC₂ hrho (j + n)
  have htsum_norm :
      (∑' j : ℕ, ‖b (j + n)‖) ≤ ∑' j : ℕ, C₂ * p (j + n) :=
    Summable.tsum_le_tsum hpoint hb_norm hscaled
  have hsplit := hp.sum_add_tsum_nat_add n
  have htail_eq :
      (∑' j : ℕ, p (j + n)) = (∑' d : ℕ, p d) - ∑ d ∈ range n, p d := by
    linarith
  have hptail := hc_moebius_aux_mmB_power_tail n hn
  change |(∑' d : ℕ, p d) - ∑ d ∈ range n, p d| ≤
    8 * (n : ℝ) ^ ((-1 : ℝ) / 4) at hptail
  have hptail' : (∑' j : ℕ, p (j + n)) ≤
      8 * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
    rw [htail_eq]
    exact (abs_le.mp hptail).2
  calc
    ‖∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
        (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))‖ =
        ‖∑' j : ℕ, b (j + n)‖ := by rfl
    _ ≤ ∑' j : ℕ, ‖b (j + n)‖ := norm_tsum_le_tsum_norm hb_norm
    _ ≤ ∑' j : ℕ, C₂ * p (j + n) := htsum_norm
    _ = C₂ * ∑' j : ℕ, p (j + n) := hp_shift.tsum_mul_left C₂
    _ ≤ C₂ * (8 * (n : ℝ) ^ ((-1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hptail' hC₂.le
    _ = 8 * C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by ring

theorem hc_moebius_aux_mertens_rate (C : ℝ) (hC : 0 < C)
    (hψ : ∀ X : ℕ, |(∑ k ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt k) - (X : ℝ)| ≤
      C * Real.sqrt X * Real.log (2 + (X : ℝ)) ^ 2) :
    ∃ c₀ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d - 1) / d) - c₀| ≤
        K / (n : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₂, hC₂, hrho⟩ := hc_moebius_aux_mmB_rho_power_bound C hC hψ
  have hb : Summable (fun d : ℕ =>
      hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) :=
    hc_moebius_aux_mmB_kernel_summable C₂ hC₂ hrho
  let c₀ : ℝ := ∑' d : ℕ,
    hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))
  let S₁ : ℝ :=
    ∑ d ∈ Icc 1 1, (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ)
  let K : ℝ := max (9 * C₂) |S₁ - c₀|
  refine ⟨c₀, K, ?_⟩
  intro n hn
  have hK_large : 9 * C₂ ≤ K := le_max_left _ _
  have hK_one : |S₁ - c₀| ≤ K := le_max_right _ _
  by_cases hn_one : n = 1
  · subst n
    simpa [S₁] using hK_one
  have hn_two : 2 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have habel := hc_moebius_aux_mmB_abel_identity n hn
  have hIcc := hc_moebius_aux_mmB_kernel_Icc_range n hn
  have hsplit :
      (∑ d ∈ range n, hc_moebius_aux_mmB_rho d / ((d : ℝ) * ((d : ℝ) + 1))) +
          (∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
            (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))) = c₀ := by
    simpa [c₀] using hb.sum_add_tsum_nat_add n
  have hdiff :
      (∑ d ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ)) - c₀ =
        hc_moebius_aux_mmB_rho n / (n : ℝ) -
          ∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
            (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1)) := by
    rw [habel, hIcc]
    linarith
  have hendpoint := hc_moebius_aux_mmB_endpoint_bound C₂ hrho n hn
  have htail := hc_moebius_aux_mmB_kernel_tail_bound C₂ hC₂ hrho n hn_two
  have htail_abs :
      |∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
        (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))| ≤
          8 * C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by
    simpa [Real.norm_eq_abs] using htail
  have hinv : (n : ℝ) ^ ((-1 : ℝ) / 4) =
      ((n : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [show ((-1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
      Real.rpow_neg hnpos.le]
  have hquarter_nonneg : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hnpos.le _
  calc
    |(∑ d ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ)) - c₀| =
        |hc_moebius_aux_mmB_rho n / (n : ℝ) -
          ∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
            (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))| := by rw [hdiff]
    _ ≤ |hc_moebius_aux_mmB_rho n / (n : ℝ)| +
        |∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
          (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1))| := by
      simpa using abs_sub_le
        (hc_moebius_aux_mmB_rho n / (n : ℝ))
        0
        (∑' j : ℕ, hc_moebius_aux_mmB_rho (j + n) /
          (((j + n : ℕ) : ℝ) * (((j + n : ℕ) : ℝ) + 1)))
    _ ≤ C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) +
        8 * C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := add_le_add hendpoint htail_abs
    _ = 9 * C₂ * (n : ℝ) ^ ((-1 : ℝ) / 4) := by ring
    _ ≤ K / (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hinv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hK_large
        (inv_nonneg.mpr hquarter_nonneg)

theorem hc_moebius_aux_identity (N : ℕ) (hN : 1 ≤ N) :
    (Finset.Icc 1 N).sum (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n/n) =
      1 + ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℝ) / k) *
        ∑ d ∈ Finset.Icc 1 (N / k), (ArithmeticFunction.vonMangoldt d - 1) / d := by

  have hPmul : ArithmeticFunction.pmul
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      = -ArithmeticFunction.vonMangoldt := by
    apply ArithmeticFunction.ext
    intro m
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := m)
    calc (∑ i ∈ m.divisors, (ArithmeticFunction.pmul
            ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            ArithmeticFunction.log) i)
        = ∑ i ∈ m.divisors, ((ArithmeticFunction.moebius i : ℤ) : ℝ) *
            ArithmeticFunction.log i := by
          apply Finset.sum_congr rfl
          intro i _
          rfl
      _ = -ArithmeticFunction.vonMangoldt m := h
      _ = (-ArithmeticFunction.vonMangoldt) m := rfl

  have hQ : (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      * ArithmeticFunction.vonMangoldt) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      = ArithmeticFunction.vonMangoldt := by
    rw [mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta,
      ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]

  have hPQ : ArithmeticFunction.pmul
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      ArithmeticFunction.log
      + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
          * ArithmeticFunction.vonMangoldt) = 0 := by
    calc ArithmeticFunction.pmul
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
          ArithmeticFunction.log
        + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            * ArithmeticFunction.vonMangoldt)
        = (ArithmeticFunction.pmul
            ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            ArithmeticFunction.log
          + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
              * ArithmeticFunction.vonMangoldt)) * 1 := (mul_one _).symm
      _ = (ArithmeticFunction.pmul
            ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            ArithmeticFunction.log
          + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
              * ArithmeticFunction.vonMangoldt)) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) := by
          rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
      _ = ((ArithmeticFunction.pmul
            ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            ArithmeticFunction.log
          + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
              * ArithmeticFunction.vonMangoldt)) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) :=
          (mul_assoc _ _ _).symm
      _ = 0 := by rw [add_mul, hPmul, hQ, neg_add_cancel, zero_mul]

  have key : ∀ n : ℕ, (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt) n
      = -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n := by
    intro n
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n) hPQ
    have h2 : ((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n
        + (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
            * ArithmeticFunction.vonMangoldt) n = 0 := h
    linarith

  let a : ArithmeticFunction ℝ :=
    ⟨fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ), by simp⟩
  let c : ArithmeticFunction ℝ :=
    ⟨fun d => (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ), by simp⟩
  have ha : ∀ k : ℕ, a k = ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ) := fun _ => rfl
  have hc : ∀ d : ℕ, c d = (ArithmeticFunction.vonMangoldt d - 1) / (d : ℝ) := fun _ => rfl

  have hpt : ∀ n : ℕ, 1 ≤ n →
      (a * c) n =
        (-((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n
          - (if n = 1 then (1 : ℝ) else 0)) / (n : ℝ) := by
    intro n hn
    have hmem : ∀ x : ℕ × ℕ, x ∈ n.divisorsAntidiagonal →
        x.1 * x.2 = n ∧ x.1 ≠ 0 ∧ x.2 ≠ 0 := by
      intro x hx
      obtain ⟨hprod, hne⟩ := (Nat.mem_divisorsAntidiagonal).1 hx
      refine ⟨hprod, ?_, ?_⟩
      · intro h1
        refine hne ?_
        rw [← hprod, h1, zero_mul]
      · intro h2
        refine hne ?_
        rw [← hprod, h2, mul_zero]
    have hstep : ∀ x ∈ n.divisorsAntidiagonal,
        a x.1 * c x.2 = (((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
          (ArithmeticFunction.vonMangoldt x.2 - 1)) / (n : ℝ) := by
      intro x hx
      obtain ⟨hprod, -, -⟩ := hmem x hx
      rw [ha, hc, div_mul_div_comm, ← Nat.cast_mul, hprod]
    have hz : ∀ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * 1 =
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
            ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) x.2) := by
      intro x hx
      obtain ⟨-, -, h2⟩ := hmem x hx
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne h2]
      simp
    have hsplit : ∀ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt x.2 - 1) =
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
              ArithmeticFunction.vonMangoldt x.2 -
            ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * 1 := by
      intro x _
      ring
    have e1 : (∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
        ArithmeticFunction.vonMangoldt x.2) =
        -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n := by
      have h := key n
      rwa [ArithmeticFunction.mul_apply] at h
    have e2 : (∑ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * 1) =
        (if n = 1 then (1 : ℝ) else 0) := by
      calc (∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * 1)
          = ∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
              ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) x.2) :=
            Finset.sum_congr rfl hz
        _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := rfl
        _ = (1 : ArithmeticFunction ℝ) n := by
            rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        _ = (if n = 1 then (1 : ℝ) else 0) := by
            rw [ArithmeticFunction.one_apply]
    have hnum : (∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
        (ArithmeticFunction.vonMangoldt x.2 - 1)) =
        -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n
          - (if n = 1 then (1 : ℝ) else 0) := by
      calc (∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt x.2 - 1))
          = (∑ x ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) *
              ArithmeticFunction.vonMangoldt x.2) -
            (∑ x ∈ n.divisorsAntidiagonal,
              ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * 1) := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl hsplit
        _ = -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n
              - (if n = 1 then (1 : ℝ) else 0) := by rw [e1, e2]
    rw [ArithmeticFunction.mul_apply, Finset.sum_congr rfl hstep, ← Finset.sum_div, hnum]

  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hRHS : (∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℝ) / k) *
        ∑ d ∈ Finset.Icc 1 (N / k), (ArithmeticFunction.vonMangoldt d - 1) / d)
      = ∑ n ∈ Finset.Icc 1 N, (a * c) n := by
    have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum a c N
    rw [← hIcc N] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hIcc (N / k)]
    simp only [ha, hc]

  have hsum : (∑ n ∈ Finset.Icc 1 N,
      -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n / (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (a * c) n) + 1 := by
    have hpt2 : ∀ n ∈ Finset.Icc 1 N,
        -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n / (n : ℝ)
          = (a * c) n + (if n = 1 then (1 : ℝ) else 0) := by
      intro n hn'
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn').1
      rw [hpt n hn1]
      by_cases h : n = 1
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl hpt2, Finset.sum_add_distrib]
    have hite : (∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0)) = 1 := by
      have hsplitIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 N := by simp [Finset.mem_Icc]
      rw [hsplitIcc, Finset.sum_insert hnotmem]
      have hz2 : (∑ n ∈ Finset.Icc 2 N, (if n = 1 then (1 : ℝ) else 0)) = 0 :=
        Finset.sum_eq_zero (fun n hn'' => by
          have h2 : 2 ≤ n := (Finset.mem_Icc.mp hn'').1
          exact ite_eq_right (by omega))
      rw [hz2]
      simp
    rw [hite]
  calc (Finset.Icc 1 N).sum (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n/n)
      = ∑ n ∈ Finset.Icc 1 N,
          -((ArithmeticFunction.moebius n : ℤ) : ℝ) * Real.log n / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = (∑ n ∈ Finset.Icc 1 N, (a * c) n) + 1 := hsum
    _ = 1 + ∑ n ∈ Finset.Icc 1 N, (a * c) n := by ring
    _ = 1 + ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℝ) / k) *
          ∑ d ∈ Finset.Icc 1 (N / k), (ArithmeticFunction.vonMangoldt d - 1) / d := by
        rw [hRHS]

lemma hc_moebius_aux_hyperbola_aux_algebra {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hd : a^4 - b^4 = 1) :
    1 / a^3 ≤ 4 * (a - b) := by
  have ha : 0 ≤ a := le_trans hb hab
  have hS : a^3 + a^2*b + a*b^2 + b^3 ≤ 4*a^3 := by
    have e1 : a^2*b ≤ a^3 := by
      nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg a)]
    have e2 : a*b^2 ≤ a^3 := by
      have hsq : b^2 ≤ a^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq ha]
    have e3 : b^3 ≤ a^3 := by
      have hsq : b^2 ≤ a^2 := by nlinarith
      have h := mul_le_mul hsq hab hb (sq_nonneg a)
      nlinarith [h]
    linarith
  have hprod : (1:ℝ) ≤ (a - b) * (4 * a^3) := by
    have hfac : a^4 - b^4 = (a - b) * (a^3 + a^2*b + a*b^2 + b^3) := by ring
    have hnn : (0:ℝ) ≤ a - b := by linarith
    calc (1:ℝ) = a^4 - b^4 := hd.symm
      _ = (a - b) * (a^3 + a^2*b + a*b^2 + b^3) := hfac
      _ ≤ (a - b) * (4 * a^3) := mul_le_mul_of_nonneg_left hS hnn
  have ha0 : 0 < a := by
    rcases lt_or_eq_of_le ha with h | h
    · exact h
    · exfalso
      have hb4 : (0:ℝ) ≤ b^4 := by positivity
      rw [← h] at hd
      linarith
  rw [div_le_iff₀ (by positivity : (0:ℝ) < a^3)]
  nlinarith [hprod]

lemma hc_moebius_aux_hyperbola_aux_key (k : ℕ) (hk : 1 ≤ k) :
    1 / ((k:ℝ))^((3:ℝ)/4) ≤ 4 * (((k:ℝ))^((1:ℝ)/4) - (((k-1:ℕ):ℝ))^((1:ℝ)/4)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hkm : (0:ℝ) ≤ ((k-1:ℕ):ℝ) := Nat.cast_nonneg _
  have hcast : (((k-1:ℕ):ℝ)) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub hk]; simp
  have hle : ((k-1:ℕ):ℝ) ≤ (k:ℝ) := by rw [hcast]; linarith
  have hb0 : (0:ℝ) ≤ (((k-1:ℕ):ℝ))^((1:ℝ)/4) := Real.rpow_nonneg hkm _
  have hab : (((k-1:ℕ):ℝ))^((1:ℝ)/4) ≤ ((k:ℝ))^((1:ℝ)/4) :=
    Real.rpow_le_rpow hkm hle (by norm_num)
  have ha4 : (((k:ℝ))^((1:ℝ)/4))^4 = (k:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hb4 : ((((k-1:ℕ):ℝ))^((1:ℝ)/4))^4 = ((k-1:ℕ):ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkm]; norm_num
  have ha3 : (((k:ℝ))^((1:ℝ)/4))^3 = ((k:ℝ))^((3:ℝ)/4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hd : (((k:ℝ))^((1:ℝ)/4))^4 - ((((k-1:ℕ):ℝ))^((1:ℝ)/4))^4 = 1 := by
    rw [ha4, hb4, hcast]; ring
  have h := hc_moebius_aux_hyperbola_aux_algebra hb0 hab hd
  rw [ha3] at h
  exact h

lemma hc_moebius_aux_hyperbola_aux_sum : ∀ M : ℕ,
    (∑ k ∈ Finset.Icc 1 M, (1:ℝ)/((k:ℝ))^((3:ℝ)/4)) ≤ 4 * ((M:ℝ))^((1:ℝ)/4) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    have hkey := hc_moebius_aux_hyperbola_aux_key (M+1) (by omega)
    have hcast : (((M+1-1:ℕ):ℝ)) = (M:ℝ) := by rw [show (M+1-1:ℕ) = M by omega]
    rw [hcast] at hkey
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    calc (∑ k ∈ Finset.Icc 1 M, (1:ℝ)/((k:ℝ))^((3:ℝ)/4)) + 1/((M+1:ℕ):ℝ)^((3:ℝ)/4)
        ≤ 4 * ((M:ℝ))^((1:ℝ)/4) + 1/((M+1:ℕ):ℝ)^((3:ℝ)/4) := by linarith [ih]
      _ ≤ 4 * ((M:ℝ))^((1:ℝ)/4)
          + 4 * (((M+1:ℕ):ℝ)^((1:ℝ)/4) - ((M:ℝ))^((1:ℝ)/4)) := by linarith [hkey]
      _ = 4 * (((M+1:ℕ):ℝ))^((1:ℝ)/4) := by push_cast; ring

theorem hc_moebius_aux_hyperbola (b Cf : ℕ → ℝ) (hb : ∀ k, |b k| ≤ 1 / (k : ℝ))
    (hB : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, b k) atTop (nhds 0))
    (c₀ K : ℝ) (hC : ∀ n : ℕ, 1 ≤ n → |Cf n - c₀| ≤ K / (n : ℝ) ^ ((1 : ℝ) / 4)) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, b k * Cf (N / k)) atTop (nhds 0) := by
  have hb0 : b 0 = 0 := by
    have h := hb 0
    rw [Nat.cast_zero, div_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hK : 0 ≤ K := by
    have h1 := hC 1 (by norm_num)
    rw [Nat.cast_one, Real.one_rpow, div_one] at h1
    linarith [abs_nonneg (Cf 1 - c₀)]

  have hset : ∀ (N j : ℕ), 1 ≤ j → ∀ k : ℕ,
      ((1 ≤ k ∧ k ≤ N) ∧ N / k = j) ↔ (N / (j+1) < k ∧ k ≤ N / j) := by
    intro N j hj k
    constructor
    · intro ⟨⟨hk1, hkN⟩, hkj⟩
      constructor
      · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < j + 1)]
        have hlt : N / k < j + 1 := by omega
        have h2 := (Nat.div_lt_iff_lt_mul hk1).mp hlt
        calc N < (j + 1) * k := h2
          _ = k * (j + 1) := by ring
      · rw [Nat.le_div_iff_mul_le hj]
        have hle : j ≤ N / k := by omega
        have h2 := (Nat.le_div_iff_mul_le hk1).mp hle
        calc k * j = j * k := by ring
          _ ≤ N := h2
    · intro ⟨h1, h2⟩
      have hkpos : 0 < k := by
        have hz : (0:ℕ) ≤ N / (j+1) := Nat.zero_le _
        omega
      have hkjmul : k * j ≤ N := (Nat.le_div_iff_mul_le hj).mp h2
      have hkN : k ≤ N := by
        calc k = k * 1 := (Nat.mul_one k).symm
          _ ≤ k * j := mul_le_mul (le_refl k) hj (Nat.zero_le _) (Nat.zero_le _)
          _ ≤ N := hkjmul
      have hNlt : N < (j+1) * k := by
        have h3 := (Nat.div_lt_iff_lt_mul (by omega : 0 < j+1)).mp h1
        calc N < k * (j+1) := h3
          _ = (j+1) * k := by ring
      refine ⟨⟨hkpos, hkN⟩, ?_⟩
      have hA' : j ≤ N / k := (Nat.le_div_iff_mul_le hkpos).mpr (by
        calc j * k = k * j := by ring
          _ ≤ N := hkjmul)
      have hB' : N / k < j + 1 := (Nat.div_lt_iff_lt_mul hkpos).mpr hNlt
      omega

  have hIcc : ∀ m : ℕ, (∑ k ∈ Finset.Icc 1 m, b k) = ∑ k ∈ Finset.range (m+1), b k := by
    intro m
    have h0 : (0:ℕ) ∈ Finset.range (m+1) := by simp
    have hset' : Finset.Icc 1 m = (Finset.range (m+1)).erase 0 := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hset']
    have h := Finset.sum_erase_add (Finset.range (m+1)) b h0
    rw [hb0, add_zero] at h
    exact h
  have hIoc : ∀ l m : ℕ, l ≤ m →
      (∑ k ∈ Finset.Ioc l m, b k)
        = (∑ k ∈ Finset.Icc 1 m, b k) - (∑ k ∈ Finset.Icc 1 l, b k) := by
    intro l m hlm
    have hset' : Finset.Ioc l m = (Finset.range (m+1)) \ (Finset.range (l+1)) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range]
      omega
    have hsub : Finset.range (l+1) ⊆ Finset.range (m+1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    rw [hset', hIcc m, hIcc l]
    have h := Finset.sum_sdiff hsub (f := b)
    linarith

  have hBpart : ∀ (Y N : ℕ), 1 ≤ Y →
      (∑ k ∈ (Finset.Icc 1 N).filter (fun k => N / k ≤ Y), b k * (Cf (N/k) - c₀))
        = ∑ j ∈ Finset.Icc 1 Y, (Cf j - c₀) *
            ((∑ k ∈ Finset.Icc 1 (N/j), b k) - (∑ k ∈ Finset.Icc 1 (N/(j+1)), b k)) := by
    intro Y N hY
    have hmaps : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => N / k ≤ Y),
        (N / k) ∈ Finset.Icc 1 Y := by
      intro k hk
      have hkI : k ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hk).1
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkI).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hkI).2
      have hkY : N / k ≤ Y := (Finset.mem_filter.mp hk).2
      have hq1 : 1 ≤ N / k := by
        rw [Nat.le_div_iff_mul_le hk1]; simpa using hkN
      exact Finset.mem_Icc.mpr ⟨hq1, hkY⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => b k * (Cf (N/k) - c₀))]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjY : j ≤ Y := (Finset.mem_Icc.mp hj).2
    have hfilt : ((Finset.Icc 1 N).filter (fun k => N / k ≤ Y)).filter (fun k => N / k = j)
        = Finset.Ioc (N/(j+1)) (N/j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · intro h
        exact (hset N j hj1 k).mp ⟨h.1.1, h.2⟩
      · intro h
        have hh := (hset N j hj1 k).mpr h
        exact ⟨⟨hh.1, by rw [hh.2]; exact hjY⟩, hh.2⟩
    rw [hfilt]
    have hinner : (∑ k ∈ Finset.Ioc (N/(j+1)) (N/j), b k * (Cf (N/k) - c₀))
        = ∑ k ∈ Finset.Ioc (N/(j+1)) (N/j), (Cf j - c₀) * b k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : N / k = j := ((hset N j hj1 k).mpr (Finset.mem_Ioc.mp hk)).2
      rw [hkj]; ring
    rw [hinner, ← Finset.mul_sum]
    have hdiv : N / (j+1) ≤ N / j := by
      rw [Nat.le_div_iff_mul_le hj1]
      calc (N/(j+1)) * j ≤ (N/(j+1)) * (j+1) :=
            mul_le_mul (le_refl _) (by omega) (Nat.zero_le _) (Nat.zero_le _)
        _ ≤ N := Nat.div_mul_le_self N (j+1)
    rw [hIoc (N/(j+1)) (N/j) hdiv]

  have hAbnd : ∀ (Y N : ℕ), 1 ≤ Y → 1 ≤ N →
      |∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)), b k * (Cf (N/k) - c₀)|
        ≤ 4 * K * (2:ℝ)^((1:ℝ)/4) / (((Y:ℝ)+1)^((1:ℝ)/4)) := by
    intro Y N hY hN
    have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hYr : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
    have hY1 : (0:ℝ) < ((Y:ℝ)+1) := by linarith
    have hN14 : (0:ℝ) < (N:ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos hN0 _
    have hY14 : (0:ℝ) < (((Y:ℝ)+1))^((1:ℝ)/4) := Real.rpow_pos_of_pos hY1 _
    have hc2 : (0:ℝ) < (2:ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
    have hsub : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)),
        k ∈ Finset.Icc 1 (N / (Y+1)) := by
      intro k hk
      have hkI : k ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hk).1
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkI).1
      have hkY : ¬ (N / k ≤ Y) := (Finset.mem_filter.mp hk).2
      have hkY' : Y + 1 ≤ N / k := by omega
      have hmul : (Y+1) * k ≤ N := (Nat.le_div_iff_mul_le hk1).mp hkY'
      have hkM : k ≤ N / (Y+1) := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < Y + 1)]
        calc k * (Y+1) = (Y+1) * k := by ring
          _ ≤ N := hmul
      exact Finset.mem_Icc.mpr ⟨hk1, hkM⟩
    have hterm : ∀ k ∈ Finset.Icc 1 (N / (Y+1)),
        |b k * (Cf (N/k) - c₀)|
          ≤ K * (2:ℝ)^((1:ℝ)/4) / ((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4)) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := le_trans (Finset.mem_Icc.mp hk).2 (Nat.div_le_self N (Y+1))
      have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
      have hq1 : 1 ≤ N / k := by
        rw [Nat.le_div_iff_mul_le hk1]; simpa using hkN
      have hq0 : (0:ℝ) < ((N/k:ℕ):ℝ) := by exact_mod_cast (show 0 < N / k by omega)
      have hNk : (N:ℝ) < (k:ℝ) * (((N/k:ℕ):ℝ) + 1) := by
        have h1 : N < k * (N/k) + k := by
          have hdm := Nat.div_add_mod N k
          have hml := Nat.mod_lt N (by omega : 0 < k)
          omega
        calc (N:ℝ) < ((k * (N/k) + k : ℕ):ℝ) := by exact_mod_cast h1
          _ = (k:ℝ) * (((N/k:ℕ):ℝ) + 1) := by push_cast; ring
      have hNk2 : (N:ℝ) < (k:ℝ) * (2 * ((N/k:ℕ):ℝ)) := by
        have hq1r : (1:ℝ) ≤ ((N/k:ℕ):ℝ) := by exact_mod_cast hq1
        have hprod : (0:ℝ) ≤ (k:ℝ) * (((N/k:ℕ):ℝ) - 1) :=
          mul_nonneg hk0.le (by linarith)
        nlinarith [hNk, hprod]
      have hdiv : (N:ℝ)/(k:ℝ) < 2 * ((N/k:ℕ):ℝ) := by
        rw [div_lt_iff₀ hk0]; linarith
      have hrpow : ((N:ℝ)/(k:ℝ))^((1:ℝ)/4) ≤ (2*((N/k:ℕ):ℝ))^((1:ℝ)/4) :=
        Real.rpow_le_rpow (div_nonneg hN0.le hk0.le) (le_of_lt hdiv) (by norm_num)
      rw [Real.div_rpow hN0.le hk0.le, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at hrpow
      have hk14 : (0:ℝ) < (k:ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos hk0 _
      have hk3 : (k:ℝ)^((3:ℝ)/4) = (k:ℝ)/(k:ℝ)^((1:ℝ)/4) := by
        rw [eq_div_iff (ne_of_gt hk14), mul_comm, ← Real.rpow_add hk0]
        norm_num
      have hcore : (N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4)
          ≤ (2:ℝ)^((1:ℝ)/4) * ((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4)) := by
        calc (N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4)
            = (N:ℝ)^((1:ℝ)/4) * ((k:ℝ)/(k:ℝ)^((1:ℝ)/4)) := by rw [hk3]
          _ = ((N:ℝ)^((1:ℝ)/4)/(k:ℝ)^((1:ℝ)/4)) * (k:ℝ) := by ring
          _ ≤ ((2:ℝ)^((1:ℝ)/4) * ((N/k:ℕ):ℝ)^((1:ℝ)/4)) * (k:ℝ) :=
              mul_le_mul_of_nonneg_right hrpow hk0.le
          _ = (2:ℝ)^((1:ℝ)/4) * ((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4)) := by ring
      have hbound : (1:ℝ)/((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4))
          ≤ (2:ℝ)^((1:ℝ)/4)/((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4)) := by
        rw [div_le_div_iff₀ (mul_pos hk0 (Real.rpow_pos_of_pos hq0 _))
          (mul_pos hN14 (Real.rpow_pos_of_pos hk0 _))]
        calc (1:ℝ) * ((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4))
            = (N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4) := one_mul _
          _ ≤ (2:ℝ)^((1:ℝ)/4) * ((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4)) := hcore
          _ = (2:ℝ)^((1:ℝ)/4) * ((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4)) := rfl
      calc |b k * (Cf (N/k) - c₀)| = |b k| * |Cf (N/k) - c₀| := abs_mul _ _
        _ ≤ (1/(k:ℝ)) * (K / ((N/k:ℕ):ℝ)^((1:ℝ)/4)) :=
            mul_le_mul (hb k) (hC (N/k) hq1) (abs_nonneg _)
              (div_nonneg zero_le_one hk0.le)
        _ = K * (1/((k:ℝ) * ((N/k:ℕ):ℝ)^((1:ℝ)/4))) := by ring
        _ ≤ K * ((2:ℝ)^((1:ℝ)/4)/((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4))) :=
            mul_le_mul_of_nonneg_left hbound hK
        _ = K * (2:ℝ)^((1:ℝ)/4) / ((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4)) := by ring
    calc |∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)), b k * (Cf (N/k) - c₀)|
        ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)),
            |b k * (Cf (N/k) - c₀)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)),
            (K * (2:ℝ)^((1:ℝ)/4) / ((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4))) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k (hsub k hk)
      _ ≤ ∑ k ∈ Finset.Icc 1 (N/(Y+1)),
            (K * (2:ℝ)^((1:ℝ)/4) / ((N:ℝ)^((1:ℝ)/4) * (k:ℝ)^((3:ℝ)/4))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; exact hsub k hk
          · intro k hk1 hk2
            have hk0 : (0:ℝ) < (k:ℝ) := by
              have : 1 ≤ k := (Finset.mem_Icc.mp hk1).1
              exact_mod_cast this
            exact div_nonneg (mul_nonneg hK hc2.le)
              (mul_nonneg hN14.le (Real.rpow_nonneg hk0.le _))
      _ = (K * (2:ℝ)^((1:ℝ)/4) / (N:ℝ)^((1:ℝ)/4)) *
            ∑ k ∈ Finset.Icc 1 (N/(Y+1)), (1/(k:ℝ)^((3:ℝ)/4)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
          have hk34 : (0:ℝ) < (k:ℝ)^((3:ℝ)/4) := Real.rpow_pos_of_pos hk0 _
          field_simp
      _ ≤ (K * (2:ℝ)^((1:ℝ)/4) / (N:ℝ)^((1:ℝ)/4)) *
            (4 * (((N/(Y+1):ℕ):ℝ))^((1:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left (hc_moebius_aux_hyperbola_aux_sum (N/(Y+1)))
          exact div_nonneg (mul_nonneg hK hc2.le) hN14.le
      _ ≤ 4 * K * (2:ℝ)^((1:ℝ)/4) / (((Y:ℝ)+1)^((1:ℝ)/4)) := by
          have hMmul : (((N/(Y+1):ℕ):ℝ)) * ((Y:ℝ)+1) ≤ (N:ℝ) := by
            have h := Nat.div_mul_le_self N (Y+1)
            calc (((N/(Y+1):ℕ):ℝ)) * ((Y:ℝ)+1) = (((N/(Y+1)) * (Y+1) : ℕ):ℝ) := by
                  push_cast; ring
              _ ≤ (N:ℝ) := by exact_mod_cast h
          have hMle : (((N/(Y+1):ℕ):ℝ)) ≤ (N:ℝ)/((Y:ℝ)+1) := by
            rw [le_div_iff₀ hY1]
            exact hMmul
          have hM14 : (((N/(Y+1):ℕ):ℝ))^((1:ℝ)/4) ≤ ((N:ℝ)/((Y:ℝ)+1))^((1:ℝ)/4) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hMle (by norm_num)
          rw [Real.div_rpow hN0.le hY1.le] at hM14
          have hcoef : (0:ℝ) ≤ K * (2:ℝ)^((1:ℝ)/4) / (N:ℝ)^((1:ℝ)/4) :=
            div_nonneg (mul_nonneg hK hc2.le) hN14.le
          calc (K * (2:ℝ)^((1:ℝ)/4) / (N:ℝ)^((1:ℝ)/4)) *
                (4 * (((N/(Y+1):ℕ):ℝ))^((1:ℝ)/4))
              ≤ (K * (2:ℝ)^((1:ℝ)/4) / (N:ℝ)^((1:ℝ)/4)) *
                (4 * ((N:ℝ)^((1:ℝ)/4)/(((Y:ℝ)+1))^((1:ℝ)/4))) := by
                apply mul_le_mul_of_nonneg_left _ hcoef
                linarith [hM14]
            _ = 4 * K * (2:ℝ)^((1:ℝ)/4) / (((Y:ℝ)+1)^((1:ℝ)/4)) := by
                field_simp

  have hS : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, b k * (Cf (N/k) - c₀))
      atTop (nhds 0) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hYexist : ∃ Y : ℕ, 1 ≤ Y ∧
        4 * K * (2:ℝ)^((1:ℝ)/4) / (((Y:ℝ)+1)^((1:ℝ)/4)) < ε / 2 := by
      have htend : Tendsto (fun Y : ℕ => ((Y:ℝ))^((1:ℝ)/4)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      have hev : ∀ᶠ Y : ℕ in atTop, 8 * K * (2:ℝ)^((1:ℝ)/4) / ε < ((Y:ℝ))^((1:ℝ)/4) := by
        filter_upwards [(Filter.tendsto_atTop.1 htend) (8 * K * (2:ℝ)^((1:ℝ)/4) / ε + 1)] with Y hY
        linarith
      rw [Filter.eventually_atTop] at hev
      obtain ⟨Y₀, hY₀⟩ := hev
      refine ⟨max Y₀ 1, le_max_right _ _, ?_⟩
      have h1 : 8 * K * (2:ℝ)^((1:ℝ)/4) / ε < ((max Y₀ 1 : ℕ):ℝ)^((1:ℝ)/4) :=
        hY₀ _ (le_max_left _ _)
      have h2 : (1:ℝ) ≤ ((max Y₀ 1 : ℕ):ℝ) := by
        have : (1:ℕ) ≤ max Y₀ 1 := le_max_right _ _
        exact_mod_cast this
      have h3 : (1:ℝ) ≤ ((max Y₀ 1 : ℕ):ℝ)^((1:ℝ)/4) := by
        calc (1:ℝ) = (1:ℝ)^((1:ℝ)/4) := (Real.one_rpow _).symm
          _ ≤ _ := Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
      have h4 : (0:ℝ) < ((max Y₀ 1 : ℕ):ℝ)^((1:ℝ)/4) := lt_of_lt_of_le (by norm_num) h3
      have h5 : ((max Y₀ 1 : ℕ):ℝ)^((1:ℝ)/4) ≤ (((max Y₀ 1 : ℕ):ℝ)+1)^((1:ℝ)/4) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have h6 : (0:ℝ) < (((max Y₀ 1 : ℕ):ℝ)+1)^((1:ℝ)/4) :=
        Real.rpow_pos_of_pos (by linarith) _
      rw [div_lt_iff₀ h6]
      have hkey : 4 * K * (2:ℝ)^((1:ℝ)/4) = (ε/2) * (8 * K * (2:ℝ)^((1:ℝ)/4) / ε) := by
        have hε0 : (ε:ℝ) ≠ 0 := ne_of_gt hε
        field_simp
        ring
      rw [hkey]
      apply mul_lt_mul_of_pos_left _ (by linarith)
      linarith
    obtain ⟨Y, hY1, hYbnd⟩ := hYexist
    have hBtend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc 1 Y, (Cf j - c₀) *
        ((∑ k ∈ Finset.Icc 1 (N/j), b k) - (∑ k ∈ Finset.Icc 1 (N/(j+1)), b k)))
        atTop (nhds 0) := by
      have hall : ∀ j ∈ Finset.Icc 1 Y, Tendsto (fun N : ℕ => (Cf j - c₀) *
          ((∑ k ∈ Finset.Icc 1 (N/j), b k) - (∑ k ∈ Finset.Icc 1 (N/(j+1)), b k)))
          atTop (nhds ((Cf j - c₀) * (0 - 0))) := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have t1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 (N/j), b k) atTop (nhds 0) :=
          hB.comp (Nat.tendsto_div_const_atTop (by omega))
        have t2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 (N/(j+1)), b k) atTop (nhds 0) :=
          hB.comp (Nat.tendsto_div_const_atTop (by omega))
        simpa using tendsto_const_nhds.mul (t1.sub t2)
      have hsum := tendsto_finsetSum (Finset.Icc 1 Y) hall
      simpa using hsum
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hBtend) (ε/2) (by linarith)
    refine ⟨max N₁ 1, fun N hN => ?_⟩
    have hNge : N₁ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hBsmall : |∑ k ∈ (Finset.Icc 1 N).filter (fun k => N / k ≤ Y),
        b k * (Cf (N/k) - c₀)| < ε/2 := by
      have h := hN₁ N hNge
      rw [Real.dist_eq, ← hBpart Y N hY1] at h
      simpa using h
    have hAbound := hAbnd Y N hY1 hN1
    have hsplit : (∑ k ∈ Finset.Icc 1 N, b k * (Cf (N/k) - c₀))
        = (∑ k ∈ (Finset.Icc 1 N).filter (fun k => N / k ≤ Y), b k * (Cf (N/k) - c₀))
          + (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)),
              b k * (Cf (N/k) - c₀)) :=
      (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun k => N / k ≤ Y)
        (fun k => b k * (Cf (N/k) - c₀))).symm
    have htotal : |∑ k ∈ Finset.Icc 1 N, b k * (Cf (N/k) - c₀)| < ε := by
      rw [hsplit]
      have htri := abs_add_le
        (∑ k ∈ (Finset.Icc 1 N).filter (fun k => N / k ≤ Y), b k * (Cf (N/k) - c₀))
        (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)), b k * (Cf (N/k) - c₀))
      have hAsmall : |∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ (N / k ≤ Y)),
          b k * (Cf (N/k) - c₀)| < ε/2 := by linarith [hAbound, hYbnd]
      linarith
    simpa [Real.dist_eq] using htotal
  have hmain : Tendsto (fun N : ℕ => c₀ * (∑ k ∈ Finset.Icc 1 N, b k)
      + ∑ k ∈ Finset.Icc 1 N, b k * (Cf (N/k) - c₀)) atTop (nhds (c₀ * 0 + 0)) :=
    (tendsto_const_nhds.mul hB).add hS
  rw [mul_zero, add_zero] at hmain
  refine hmain.congr' (Filter.Eventually.of_forall ?_)
  intro N
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hc_moebius (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (ArithmeticFunction.moebius n : ℝ)/n))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n/n))
      Filter.atTop (nhds 1) := by
  have h1 := hc_moebius_aux_axer hc_moebius_aux_mu_littleO
  refine ⟨h1, ?_⟩
  obtain ⟨C, hC, hψ⟩ := hc_moebius_aux_psi_bound hRH
  obtain ⟨c₀, K, hrate⟩ := hc_moebius_aux_mertens_rate C hC hψ
  have hb : ∀ k : ℕ, |(ArithmeticFunction.moebius k : ℝ) / k| ≤ 1 / (k : ℝ) := by
    intro k
    rw [abs_div, Nat.abs_cast]
    gcongr
    have h := ArithmeticFunction.abs_moebius_le_one (n := k)
    have h' : ((|ArithmeticFunction.moebius k| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    simpa [Int.cast_abs] using h'
  have h2 := hc_moebius_aux_hyperbola (fun k => (ArithmeticFunction.moebius k : ℝ) / k)
    (fun n => ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt d - 1) / d) hb h1 c₀ K hrate
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (hc_moebius_aux_identity N hN).symm

noncomputable def hc_odd_moments_aux_m (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / n

noncomputable def hc_odd_moments_aux_T (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, -(ArithmeticFunction.moebius n : ℝ) * Real.log n / n

theorem hc_odd_moments_aux_zero_m : hc_odd_moments_aux_m 0 = 0 := by
  simp [hc_odd_moments_aux_m]

theorem hc_odd_moments_aux_zero_T : hc_odd_moments_aux_T 0 = 0 := by
  simp [hc_odd_moments_aux_T]

theorem hc_odd_moments_aux_zero_mo : hcMo 0 = 0 := by
  simp [hcMo]

theorem hc_odd_moments_aux_zero_to : hcTo 0 = 0 := by
  simp [hcTo]

theorem hc_odd_moments_aux_mu (o : ℕ) :
    (ArithmeticFunction.moebius (2 * o) : ℝ) =
      if o % 2 = 1 then -(ArithmeticFunction.moebius o : ℝ) else 0 := by
  by_cases ho : o % 2 = 1
  · rw [if_pos ho]
    have hcop : Nat.Coprime 2 o := by
      have h1 : Nat.gcd 2 o ∣ 2 := Nat.gcd_dvd_left 2 o
      have h2 : Nat.gcd 2 o ∣ o := Nat.gcd_dvd_right 2 o
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · exfalso
        rw [h] at h2
        omega
    have h3 : ArithmeticFunction.moebius (2 * o)
        = ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius o :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    rw [h3, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    push_cast
    ring
  · rw [if_neg ho]
    have hns : ¬ Squarefree (2 * o) := by
      intro hsf
      have h4 := (Nat.squarefree_iff_prime_squarefree.mp hsf) 2 Nat.prime_two
      apply h4
      obtain ⟨k, hk⟩ : ∃ k, o = 2 * k := ⟨o / 2, by omega⟩
      exact ⟨k, by omega⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
    simp

def hc_odd_moments_aux_emb : ℕ ↪ ℕ :=
  ⟨fun o => 2 * o, by intro a b h; have h' : 2 * a = 2 * b := h; omega⟩

theorem hc_odd_moments_aux_emb_apply (o : ℕ) : hc_odd_moments_aux_emb o = 2 * o := rfl

theorem hc_odd_moments_aux_reindex (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = 0), f n
      = ∑ o ∈ Finset.Icc 1 (N / 2), f (2 * o) := by
  have hset : (Finset.Icc 1 (N / 2)).map hc_odd_moments_aux_emb
      = (Finset.Icc 1 N).filter (fun n => n % 2 = 0) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨o, ⟨ho1, ho2⟩, rfl⟩
      rw [hc_odd_moments_aux_emb_apply]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨⟨hn1, hn2⟩, hn3⟩
      refine ⟨n / 2, ⟨by omega, by omega⟩, ?_⟩
      rw [hc_odd_moments_aux_emb_apply]
      omega
  rw [← hset, Finset.sum_map]
  simp only [hc_odd_moments_aux_emb_apply]

theorem hc_odd_moments_aux_split (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ S, f n = ∑ n ∈ S.filter (fun n => n % 2 = 1), f n
      + ∑ n ∈ S.filter (fun n => n % 2 = 0), f n := by
  have h := Finset.sum_filter_add_sum_filter_not S (fun n => n % 2 = 1) f
  have hfilt : S.filter (fun n => ¬ (n % 2 = 1)) = S.filter (fun n => n % 2 = 0) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  rw [hfilt] at h
  exact h.symm

theorem hc_odd_moments_aux_mo_rec (N : ℕ) :
    hcMo N = hc_odd_moments_aux_m N + hcMo (N / 2) / 2 := by
  have hsplit := hc_odd_moments_aux_split (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.moebius n : ℝ) / n)
  have heven : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = 0),
      (ArithmeticFunction.moebius n : ℝ) / n = -(hcMo (N / 2)) / 2 := by
    rw [hc_odd_moments_aux_reindex]
    have hterm : ∀ o ∈ Finset.Icc 1 (N / 2),
        (ArithmeticFunction.moebius (2 * o) : ℝ) / ((2 * o : ℕ) : ℝ)
          = if o % 2 = 1 then -((ArithmeticFunction.moebius o : ℝ) / (o : ℝ)) / 2 else 0 := by
      intro o ho
      have ho1 : 1 ≤ o := (Finset.mem_Icc.mp ho).1
      have ho0 : ((o : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (o : ℕ) ≠ 0 by omega)
      rw [hc_odd_moments_aux_mu]
      split_ifs with hodd
      · push_cast
        field_simp
      · simp
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter]
    have hsum : ∑ o ∈ (Finset.Icc 1 (N / 2)).filter (fun o => o % 2 = 1),
        (-((ArithmeticFunction.moebius o : ℝ) / (o : ℝ)) / 2)
          = -((1:ℝ)/2) * ∑ o ∈ (Finset.Icc 1 (N / 2)).filter (fun o => o % 2 = 1),
              ((ArithmeticFunction.moebius o : ℝ) / (o : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o ho
      ring
    rw [hsum]
    simp only [hcMo]
    ring
  have h1 : hc_odd_moments_aux_m N = hcMo N
      + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = 0),
        (ArithmeticFunction.moebius n : ℝ) / n := by
    rw [hc_odd_moments_aux_m]
    exact hsplit
  rw [heven] at h1
  linarith

theorem hc_odd_moments_aux_to_rec (N : ℕ) :
    hcTo N = hc_odd_moments_aux_T N - Real.log 2 / 2 * hcMo (N / 2) + hcTo (N / 2) / 2 := by
  have hsplit := hc_odd_moments_aux_split (Finset.Icc 1 N)
    (fun n => -(ArithmeticFunction.moebius n : ℝ) * Real.log n / n)
  have heven : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = 0),
      -(ArithmeticFunction.moebius n : ℝ) * Real.log n / n
        = Real.log 2 / 2 * hcMo (N / 2) - hcTo (N / 2) / 2 := by
    rw [hc_odd_moments_aux_reindex]
    have hterm : ∀ o ∈ Finset.Icc 1 (N / 2),
        -(ArithmeticFunction.moebius (2 * o) : ℝ) * Real.log ((2 * o : ℕ) : ℝ)
            / ((2 * o : ℕ) : ℝ)
          = if o % 2 = 1 then
              Real.log 2 / 2 * ((ArithmeticFunction.moebius o : ℝ) / (o : ℝ))
                - (-(ArithmeticFunction.moebius o : ℝ) * Real.log o / (o : ℝ)) / 2
            else 0 := by
      intro o ho
      have ho1 : 1 ≤ o := (Finset.mem_Icc.mp ho).1
      have ho0 : ((o : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (o : ℕ) ≠ 0 by omega)
      rw [hc_odd_moments_aux_mu]
      split_ifs with hodd
      · rw [show ((2 * o : ℕ) : ℝ) = 2 * ((o : ℕ) : ℝ) by push_cast; ring]
        rw [Real.log_mul (by norm_num) ho0]
        field_simp
        ring
      · simp
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    simp only [hcMo, hcTo]
  have h1 : hc_odd_moments_aux_T N = hcTo N
      + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = 0),
        -(ArithmeticFunction.moebius n : ℝ) * Real.log n / n := by
    rw [hc_odd_moments_aux_T]
    exact hsplit
  rw [heven] at h1
  linarith

theorem hc_odd_moments_aux_mo_iter : ∀ K N : ℕ,
    hcMo N = (∑ j ∈ Finset.range K, (1/2:ℝ)^j * hc_odd_moments_aux_m (N / 2^j))
      + (1/2:ℝ)^K * hcMo (N / 2^K) := by
  intro K
  induction K with
  | zero => intro N; simp
  | succ K ih =>
      intro N
      have h1 := ih N
      have h2 := hc_odd_moments_aux_mo_rec (N / 2^K)
      have hdiv : N / 2^K / 2 = N / 2^(K+1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      rw [hdiv] at h2
      rw [Finset.sum_range_succ, h1, h2]
      ring

theorem hc_odd_moments_aux_to_iter : ∀ K N : ℕ,
    hcTo N = (∑ j ∈ Finset.range K, (1/2:ℝ)^j *
        (hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1))))
      + (1/2:ℝ)^K * hcTo (N / 2^K) := by
  intro K
  induction K with
  | zero => intro N; simp
  | succ K ih =>
      intro N
      have h1 := ih N
      have h2 := hc_odd_moments_aux_to_rec (N / 2^K)
      have hdiv : N / 2^K / 2 = N / 2^(K+1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ]
      rw [hdiv] at h2
      rw [Finset.sum_range_succ, h1, h2]
      ring

theorem hc_odd_moments_aux_pow_gt (N : ℕ) : N < 2^(N+1) := by
  calc N < 2^N := Nat.lt_two_pow_self (n := N)
    _ ≤ 2^(N+1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hc_odd_moments_aux_div_zero (N j : ℕ) (hj : N + 1 ≤ j) : N / 2^j = 0 := by
  refine (Nat.div_eq_zero_iff_lt (by positivity)).mpr ?_
  calc N < 2^(N+1) := hc_odd_moments_aux_pow_gt N
    _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj

theorem hc_odd_moments_aux_mo_tsum (N : ℕ) :
    hcMo N = ∑' j, (1/2:ℝ)^j * hc_odd_moments_aux_m (N / 2^j) := by
  have hiter := hc_odd_moments_aux_mo_iter (N+1) N
  rw [hc_odd_moments_aux_div_zero N (N+1) (by omega), hc_odd_moments_aux_zero_mo,
    mul_zero, add_zero] at hiter
  rw [hiter, tsum_eq_sum (s := Finset.range (N+1))]
  intro b hb
  rw [hc_odd_moments_aux_div_zero N b (by simp only [Finset.mem_range, not_lt] at hb; omega),
    hc_odd_moments_aux_zero_m, mul_zero]

theorem hc_odd_moments_aux_to_tsum (N : ℕ) :
    hcTo N = ∑' j, (1/2:ℝ)^j *
      (hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1))) := by
  have hiter := hc_odd_moments_aux_to_iter (N+1) N
  rw [hc_odd_moments_aux_div_zero N (N+1) (by omega), hc_odd_moments_aux_zero_to,
    mul_zero, add_zero] at hiter
  rw [hiter, tsum_eq_sum (s := Finset.range (N+1))]
  intro b hb
  have hb' : N + 1 ≤ b := by simp only [Finset.mem_range, not_lt] at hb; omega
  rw [hc_odd_moments_aux_div_zero N b hb', hc_odd_moments_aux_div_zero N (b+1) (by omega),
    hc_odd_moments_aux_zero_T, hc_odd_moments_aux_zero_mo]
  simp

theorem hc_odd_moments_aux_mo_tendsto
    (hm : Tendsto hc_odd_moments_aux_m atTop (nhds 0)) :
    Tendsto hcMo atTop (nhds 0) := by
  obtain ⟨B, hBpos, hB⟩ := (Metric.isBounded_range_of_tendsto _ hm).exists_pos_norm_le
  have hsumm : Summable (fun j => B * (1/2:ℝ)^j) :=
    (summable_geometric_of_norm_lt_one (x := (1/2:ℝ)) (by norm_num)).mul_left B
  have hpt : ∀ j : ℕ, Tendsto (fun N => (1/2:ℝ)^j * hc_odd_moments_aux_m (N / 2^j))
      atTop (nhds 0) := by
    intro j
    have h1 : Tendsto (fun N : ℕ => hc_odd_moments_aux_m (N / 2^j)) atTop (nhds 0) :=
      hm.comp (Nat.tendsto_div_const_atTop (by positivity))
    simpa using h1.const_mul ((1/2:ℝ)^j)
  have hbd : ∀ N j : ℕ, ‖(1/2:ℝ)^j * hc_odd_moments_aux_m (N / 2^j)‖ ≤ B * (1/2:ℝ)^j := by
    intro N j
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) j)]
    have e1 := hB _ ⟨N / 2^j, rfl⟩
    calc (1/2:ℝ)^j * ‖hc_odd_moments_aux_m (N / 2^j)‖ ≤ (1/2:ℝ)^j * B := by
          exact mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = B * (1/2:ℝ)^j := by ring
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun N j => (1/2:ℝ)^j * hc_odd_moments_aux_m (N / 2^j))
    (g := fun _ => (0:ℝ)) (bound := fun j => B * (1/2:ℝ)^j)
    hsumm hpt (Filter.Eventually.of_forall (fun N j => hbd N j))
  rw [tsum_zero] at h
  refine h.congr' ?_
  filter_upwards with N
  exact (hc_odd_moments_aux_mo_tsum N).symm

theorem hc_odd_moments_aux_to_tendsto
    (hT : Tendsto hc_odd_moments_aux_T atTop (nhds 1))
    (hmo : Tendsto hcMo atTop (nhds 0)) :
    Tendsto hcTo atTop (nhds 2) := by
  obtain ⟨B1, hB1pos, hB1⟩ := (Metric.isBounded_range_of_tendsto _ hT).exists_pos_norm_le
  obtain ⟨B2, hB2pos, hB2⟩ := (Metric.isBounded_range_of_tendsto _ hmo).exists_pos_norm_le
  have hsumm : Summable (fun j => (B1 + |Real.log 2 / 2| * B2) * (1/2:ℝ)^j) :=
    (summable_geometric_of_norm_lt_one (x := (1/2:ℝ)) (by norm_num)).mul_left _
  have hpt : ∀ j : ℕ, Tendsto (fun N => (1/2:ℝ)^j *
      (hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1))))
      atTop (nhds ((1/2:ℝ)^j)) := by
    intro j
    have h1 : Tendsto (fun N : ℕ => hc_odd_moments_aux_T (N / 2^j)) atTop (nhds 1) :=
      hT.comp (Nat.tendsto_div_const_atTop (by positivity))
    have h2 : Tendsto (fun N : ℕ => hcMo (N / 2^(j+1))) atTop (nhds 0) :=
      hmo.comp (Nat.tendsto_div_const_atTop (by positivity))
    have h3 : Tendsto (fun N : ℕ =>
        hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1)))
        atTop (nhds (1 - Real.log 2 / 2 * 0)) := h1.sub (h2.const_mul (Real.log 2 / 2))
    have h4 := h3.const_mul ((1/2:ℝ)^j)
    simpa using h4
  have hbd : ∀ N j : ℕ, ‖(1/2:ℝ)^j *
      (hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1)))‖
        ≤ (B1 + |Real.log 2 / 2| * B2) * (1/2:ℝ)^j := by
    intro N j
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) j)]
    have e1 := hB1 _ ⟨N / 2^j, rfl⟩
    have e2 := hB2 _ ⟨N / 2^(j+1), rfl⟩
    have hinner : ‖hc_odd_moments_aux_T (N / 2^j)
        - Real.log 2 / 2 * hcMo (N / 2^(j+1))‖ ≤ B1 + |Real.log 2 / 2| * B2 := by
      calc ‖hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1))‖
            ≤ ‖hc_odd_moments_aux_T (N / 2^j)‖
              + ‖Real.log 2 / 2 * hcMo (N / 2^(j+1))‖ := norm_sub_le _ _
        _ = ‖hc_odd_moments_aux_T (N / 2^j)‖
              + |Real.log 2 / 2| * ‖hcMo (N / 2^(j+1))‖ := by
            simp only [norm_mul, Real.norm_eq_abs]
        _ ≤ B1 + |Real.log 2 / 2| * B2 := by gcongr
    calc (1/2:ℝ)^j * ‖hc_odd_moments_aux_T (N / 2^j)
            - Real.log 2 / 2 * hcMo (N / 2^(j+1))‖
          ≤ (1/2:ℝ)^j * (B1 + |Real.log 2 / 2| * B2) := by
            exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (B1 + |Real.log 2 / 2| * B2) * (1/2:ℝ)^j := by ring
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun N j => (1/2:ℝ)^j *
      (hc_odd_moments_aux_T (N / 2^j) - Real.log 2 / 2 * hcMo (N / 2^(j+1))))
    (g := fun j => (1/2:ℝ)^j)
    (bound := fun j => (B1 + |Real.log 2 / 2| * B2) * (1/2:ℝ)^j)
    hsumm hpt (Filter.Eventually.of_forall (fun N j => hbd N j))
  have hsum2 : (∑' j, (1/2:ℝ)^j) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
    norm_num
  rw [hsum2] at h
  refine h.congr' ?_
  filter_upwards with N
  exact (hc_odd_moments_aux_to_tsum N).symm

theorem hc_odd_moments
    (h0 : Filter.Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (ArithmeticFunction.moebius n : ℝ)/n))
      Filter.atTop (nhds 0))
    (h1 : Filter.Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n/n))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto hcMo Filter.atTop (nhds 0) ∧ Filter.Tendsto hcTo Filter.atTop (nhds 2) := by
  have hm : Tendsto hc_odd_moments_aux_m atTop (nhds 0) := h0
  have hT : Tendsto hc_odd_moments_aux_T atTop (nhds 1) := h1
  have hmo := hc_odd_moments_aux_mo_tendsto hm
  exact ⟨hmo, hc_odd_moments_aux_to_tendsto hT hmo⟩

noncomputable def hc_factor_aux_hh : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (-1 : ℝ) / ((p : ℝ) - 1))

noncomputable def hc_factor_aux_tgt : ArithmeticFunction ℝ :=
  ⟨fun m => (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) / (Nat.totient m : ℝ),
    by simp [ArithmeticFunction.map_zero]⟩

theorem hc_factor_aux_tgt_apply (m : ℕ) :
    hc_factor_aux_tgt m
      = (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) / (Nat.totient m : ℝ) := rfl

theorem hc_factor_aux_hh_mult : hc_factor_aux_hh.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem hc_factor_aux_hh_apply {m : ℕ} (hm : m ≠ 0) :
    hc_factor_aux_hh m = ∏ p ∈ m.primeFactors, (-1 : ℝ) / ((p : ℝ) - 1) := by
  simp [hc_factor_aux_hh, ArithmeticFunction.prodPrimeFactors_apply hm]

theorem hc_factor_aux_hh_one : hc_factor_aux_hh 1 = 1 := hc_factor_aux_hh_mult.1

theorem hc_factor_aux_hh_ppow {p i : ℕ} (hp : p.Prime) (hi : i ≠ 0) :
    hc_factor_aux_hh (p ^ i) = (-1 : ℝ) / ((p : ℝ) - 1) := by
  rw [hc_factor_aux_hh_apply (pow_ne_zero i hp.ne_zero), Nat.primeFactors_prime_pow hi hp]
  simp

theorem hc_factor_aux_tgt_mult : hc_factor_aux_tgt.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [hc_factor_aux_tgt_apply]
    simp
  · intro m n h
    have h1 : ArithmeticFunction.moebius (m * n)
        = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
      ArithmeticFunction.isMultiplicative_moebius.2 h
    have h2 : Nat.totient (m * n) = Nat.totient m * Nat.totient n := Nat.totient_mul h
    simp only [hc_factor_aux_tgt_apply, h1, h2]
    push_cast
    ring

theorem hc_factor_aux_sum_eval (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i) :
    ∑ x ∈ Finset.range (i + 1),
        hc_factor_aux_hh (p ^ x) * ((ArithmeticFunction.moebius (p ^ (i - x)) : ℝ))
      = hc_factor_aux_hh (p ^ (i - 1)) * ((ArithmeticFunction.moebius p : ℝ))
        + hc_factor_aux_hh (p ^ i) * ((ArithmeticFunction.moebius 1 : ℝ)) := by
  have hz : ∀ x ∈ Finset.range (i + 1), x ∉ ({i - 1, i} : Finset ℕ) →
      hc_factor_aux_hh (p ^ x) * ((ArithmeticFunction.moebius (p ^ (i - x)) : ℝ)) = 0 := by
    intro x hx hxnot
    have hlt : x < i - 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
      simp only [Finset.mem_range] at hx
      omega
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i - x ≠ 0)]
    simp [show i - x ≠ 1 by omega]
  have hsub : ({i - 1, i} : Finset ℕ) ⊆ Finset.range (i + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    omega
  rw [(Finset.sum_subset hsub hz).symm, Finset.sum_pair (by omega : i - 1 ≠ i)]
  rw [show i - (i - 1) = 1 by omega, show i - i = 0 by omega]
  simp only [pow_one, pow_zero]

theorem hc_factor_aux_conv_ppow_aux (p i : ℕ) (hp : p.Prime) :
    (hc_factor_aux_hh * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (p ^ i)
      = ∑ x ∈ Finset.range (i + 1),
          hc_factor_aux_hh (p ^ x) * ((ArithmeticFunction.moebius (p ^ (i - x)) : ℝ)) := by
  have h1 : (hc_factor_aux_hh * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (p ^ i)
      = ∑ d ∈ (p ^ i).divisors,
          hc_factor_aux_hh d * ((ArithmeticFunction.moebius ((p ^ i) / d) : ℝ)) := by
    rw [ArithmeticFunction.mul_apply]
    exact (Nat.sum_divisorsAntidiagonal
      (fun a b : ℕ => hc_factor_aux_hh a * ((ArithmeticFunction.moebius b : ℝ)))
      (n := p ^ i))
  rw [h1, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hx' : x ≤ i := by
    simp only [Finset.mem_range] at hx
    omega
  rw [Nat.pow_div hx' hp.pos]

theorem hc_factor_aux_conv_ppow (p i : ℕ) (hp : p.Prime) :
    (hc_factor_aux_hh * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (p ^ i)
      = hc_factor_aux_tgt (p ^ i) := by
  rw [hc_factor_aux_conv_ppow_aux p i hp, hc_factor_aux_tgt_apply]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hμp : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  have hμ1 : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hc_factor_aux_hh_one]
  · rw [hc_factor_aux_sum_eval p i hp hi, hμp, hμ1]
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi2
    · have hA : hc_factor_aux_hh (p ^ (1 - 1)) = 1 := by
        rw [show (1 : ℕ) - 1 = 0 by rfl, pow_zero]
        exact hc_factor_aux_hh_one
      have hB : hc_factor_aux_hh (p ^ (1 : ℕ)) = (-1 : ℝ) / ((p : ℝ) - 1) :=
        hc_factor_aux_hh_ppow hp (by norm_num)
      have hC : (ArithmeticFunction.moebius (p ^ (1 : ℕ)) : ℝ) = -1 := by
        rw [pow_one, ArithmeticFunction.moebius_apply_prime hp]; norm_num
      have hD : (Nat.totient (p ^ (1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
        rw [pow_one, Nat.totient_prime hp, Nat.cast_sub (by have := hp.two_le; omega)]
        norm_num
      rw [hA, hB, hC, hD]
      push_cast
      field_simp <;> ring
    · have hA : hc_factor_aux_hh (p ^ (i - 1)) = (-1 : ℝ) / ((p : ℝ) - 1) :=
        hc_factor_aux_hh_ppow hp (by omega)
      have hB : hc_factor_aux_hh (p ^ i) = (-1 : ℝ) / ((p : ℝ) - 1) :=
        hc_factor_aux_hh_ppow hp (by omega)
      have hC : (ArithmeticFunction.moebius (p ^ i) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show i ≠ 1 by omega]
      rw [hA, hB, hC]
      ring

theorem hc_factor_aux_conv :
    hc_factor_aux_hh * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      = hc_factor_aux_tgt :=
  (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (hc_factor_aux_hh_mult.mul ArithmeticFunction.isMultiplicative_moebius.intCast) _
    hc_factor_aux_tgt_mult).2 fun p i hp => hc_factor_aux_conv_ppow p i hp

theorem hc_factor (n : ℕ) (hn : n % 2 = 1) :
    (ArithmeticFunction.moebius n : ℝ) / Nat.totient n =
      ∑ d ∈ n.divisors, hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hφn : (Nat.totient n : ℝ) ≠ 0 := by
    have h := Nat.totient_pos.mpr (by omega : 0 < n)
    exact_mod_cast (ne_of_gt h)
  have hodd : Odd n := ⟨n / 2, by omega⟩
  have hG : ∀ d ∈ n.divisors, hcG d = hc_factor_aux_hh d / (d : ℝ) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := Nat.pos_of_mem_divisors hd; omega
    have hdodd : d % 2 = 1 := by
      obtain ⟨k, hk⟩ := Odd.of_dvd_nat hodd (Nat.dvd_of_mem_divisors hd)
      omega
    have hG' : hcG d = (∏ p ∈ d.primeFactors, (-1 : ℝ) / ((p : ℝ) - 1)) / (d : ℝ) := by
      simp [hcG, hdodd]
    rw [hG', hc_factor_aux_hh_apply hd0]
  have hterm : ∀ d ∈ n.divisors,
      hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))
        = hc_factor_aux_hh d * (ArithmeticFunction.moebius (n / d) : ℝ) / (n : ℝ) := by
    intro d hd
    have hd0 : d ≠ 0 := by have := Nat.pos_of_mem_divisors hd; omega
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hdd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
      rw [eq_div_iff hdR, ← Nat.cast_mul, Nat.div_mul_cancel hdd]
    have hnd : (n : ℝ) / (d : ℝ) ≠ 0 := div_ne_zero hnR hdR
    rw [hG d hd, hcast]
    field_simp <;> ring
  have hsum : ∑ d ∈ n.divisors,
      hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))
      = ∑ d ∈ n.divisors,
        hc_factor_aux_hh d * (ArithmeticFunction.moebius (n / d) : ℝ) / (n : ℝ) :=
    Finset.sum_congr rfl hterm
  have hsum2 : ∑ d ∈ n.divisors,
      hc_factor_aux_hh d * (ArithmeticFunction.moebius (n / d) : ℝ) / (n : ℝ)
      = (∑ d ∈ n.divisors,
          hc_factor_aux_hh d * (ArithmeticFunction.moebius (n / d) : ℝ)) / (n : ℝ) := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  have hconv : (∑ d ∈ n.divisors,
      hc_factor_aux_hh d * (ArithmeticFunction.moebius (n / d) : ℝ))
      = (hc_factor_aux_hh * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) n := by
    rw [ArithmeticFunction.mul_apply]
    exact (Nat.sum_divisorsAntidiagonal
      (fun a b : ℕ => hc_factor_aux_hh a * ((ArithmeticFunction.moebius b : ℝ)))
      (n := n)).symm
  rw [hsum, hsum2, hconv, hc_factor_aux_conv, hc_factor_aux_tgt_apply]
  field_simp <;> ring

lemma hc_split_aux_reindex (D : ℕ) (Ψ : ℕ → ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1), ∑ d ∈ n.divisors, Ψ d (n / d) =
      ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1), Ψ d e := by
  have memS : ∀ n : ℕ, n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1) ↔
      (1 ≤ n ∧ n ≤ D ∧ n % 2 = 1) := by
    intro n; simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have memT : ∀ d e : ℕ, e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1) ↔
      (1 ≤ e ∧ e ≤ D / d ∧ e % 2 = 1) := by
    intro d e; simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have oddmul : ∀ a b : ℕ, (a * b) % 2 = 1 → a % 2 = 1 ∧ b % 2 = 1 := by
    intro a b h
    have h' : Odd (a * b) := Nat.odd_iff.2 h
    rw [Nat.odd_mul] at h'
    exact ⟨Nat.odd_iff.1 h'.1, Nat.odd_iff.1 h'.2⟩
  calc ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1), ∑ d ∈ n.divisors, Ψ d (n / d)
      = ∑ p ∈ ((Finset.Icc 1 D).filter (fun n => n % 2 = 1)).sigma (fun n => n.divisors),
          Ψ p.2 (p.1 / p.2) := by
        rw [Finset.sum_sigma']
    _ = ∑ p ∈ ((Finset.Icc 1 D).filter (fun n => n % 2 = 1)).sigma
          (fun d => (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1)), Ψ p.1 p.2 := by
        refine Finset.sum_nbij' (f := fun p : Sigma (fun _ : ℕ => ℕ) => Ψ p.2 (p.1 / p.2))
          (g := fun q : Sigma (fun _ : ℕ => ℕ) => Ψ q.1 q.2)
          (fun p : Sigma (fun _ : ℕ => ℕ) => ⟨p.2, p.1 / p.2⟩)
          (fun q : Sigma (fun _ : ℕ => ℕ) => ⟨q.1 * q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨n, d⟩ hd
          simp only [Finset.mem_sigma] at hd
          obtain ⟨hn, hdd⟩ := hd
          obtain ⟨hn1, hnD, hnodd⟩ := (memS n).1 hn
          have hdpos : 0 < d := Nat.pos_of_mem_divisors hdd
          have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdd
          have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
          have hodd := oddmul d (n / d) (by rw [hmul]; exact hnodd)
          refine Finset.mem_sigma.2 ⟨(memS d).2 ⟨hdpos, ?_, hodd.1⟩,
            (memT d (n / d)).2 ⟨?_, ?_, hodd.2⟩⟩
          · exact le_trans (Nat.le_of_dvd (by omega) hdvd) hnD
          · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
          · exact Nat.div_le_div_right hnD
        · rintro ⟨d, e⟩ he
          simp only [Finset.mem_sigma] at he
          obtain ⟨hd, heT⟩ := he
          obtain ⟨hd1, hdD, hdodd⟩ := (memS d).1 hd
          obtain ⟨he1, heD, heodd⟩ := (memT d e).1 heT
          refine Finset.mem_sigma.2 ⟨(memS (d * e)).2 ⟨?_, ?_, ?_⟩, ?_⟩
          · have := Nat.mul_pos (by omega : 0 < d) (by omega : 0 < e); omega
          · calc d * e ≤ d * (D / d) := Nat.mul_le_mul_left d heD
                 _ = D / d * d := by ring
                 _ ≤ D := Nat.div_mul_le_self D d
          · rw [Nat.mul_mod, hdodd, heodd]
          · have hpos : 0 < d * e := Nat.mul_pos (by omega) (by omega)
            refine Nat.mem_divisors.2 ⟨⟨e, rfl⟩, ?_⟩
            exact Nat.ne_of_gt hpos
        · rintro ⟨n, d⟩ hd
          simp only [Finset.mem_sigma] at hd
          have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd.2
          have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
          simp [hmul]
        · rintro ⟨d, e⟩ he
          simp only [Finset.mem_sigma] at he
          have hd1 : 1 ≤ d := ((memS d).1 he.1).1
          have hdm : d * e / d = e := Nat.mul_div_cancel_left e (by omega)
          simp [hdm]
        · rintro ⟨n, d⟩ _
          rfl
    _ = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1), Ψ d e := by
        rw [Finset.sum_sigma']

theorem hc_split
    (hfac : ∀ n : ℕ, n % 2 = 1 → (ArithmeticFunction.moebius n : ℝ) / Nat.totient n =
      ∑ d ∈ n.divisors, hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)))
    (D : ℕ) :
    ((Finset.Icc 1 D).filter (fun n => n %2=1)).sum
        (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n / Nat.totient n) =
      ∑ d ∈ Finset.Icc 1 D, hcG d * (-(Real.log d) * hcMo (D / d) + hcTo (D / d)) := by
  have memS : ∀ n : ℕ, n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1) ↔
      (1 ≤ n ∧ n ≤ D ∧ n % 2 = 1) := by
    intro n; simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have memT : ∀ d e : ℕ, e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1) ↔
      (1 ≤ e ∧ e ≤ D / d ∧ e % 2 = 1) := by
    intro d e; simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hstep1 : ∀ n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1),
      -(ArithmeticFunction.moebius n : ℝ) * Real.log n / Nat.totient n =
      ∑ d ∈ n.divisors, (-(hcG d) * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))
        * Real.log ((d * (n / d) : ℕ) : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hnD, hodd⟩ := (memS n).1 hn
    calc -(ArithmeticFunction.moebius n : ℝ) * Real.log n / Nat.totient n
        = -(Real.log n) * ((ArithmeticFunction.moebius n : ℝ) / Nat.totient n) := by ring
      _ = -(Real.log n) * ∑ d ∈ n.divisors,
            hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)) := by
          rw [hfac n hodd]
      _ = ∑ d ∈ n.divisors, -(Real.log n) *
            (hcG d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
      _ = ∑ d ∈ n.divisors, (-(hcG d) * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))
            * Real.log ((d * (n / d) : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hmul : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
          rw [hmul]
          ring
  have hstep3 : ∀ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
      ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
        (-(hcG d) * ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ))
          * Real.log ((d * e : ℕ) : ℝ)) =
      hcG d * (-(Real.log d) * hcMo (D / d) + hcTo (D / d)) := by
    intro d hd
    obtain ⟨hd1, hdD, hdodd⟩ := (memS d).1 hd
    have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast (show (0 : ℕ) < d by omega)
      exact ne_of_gt h
    have hlog : ∀ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
        Real.log ((d * e : ℕ) : ℝ) = Real.log ((d : ℕ) : ℝ) + Real.log ((e : ℕ) : ℝ) := by
      intro e he
      have he1 : 1 ≤ e := (memT d e).1 he |>.1
      have he0 : ((e : ℕ) : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < ((e : ℕ) : ℝ) := by exact_mod_cast (show (0 : ℕ) < e by omega)
        exact ne_of_gt h
      rw [Nat.cast_mul, Real.log_mul hd0 he0]
    have hMo : hcMo (D / d) =
        ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
          ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ)) := by
      simp only [hcMo]
    have hTo : hcTo (D / d) =
        ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
          ((-(ArithmeticFunction.moebius e : ℝ)) * Real.log e / ((e : ℕ) : ℝ)) := by
      simp only [hcTo]
    calc ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
          (-(hcG d) * ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ))
            * Real.log ((d * e : ℕ) : ℝ))
        = ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
            (hcG d * (-(Real.log d) * ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ)))
              + hcG d * ((-(ArithmeticFunction.moebius e : ℝ)) * Real.log e / ((e : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hlog e he]
          ring
      _ = (∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
              hcG d * (-(Real.log d) * ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ))))
            + ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
              hcG d * ((-(ArithmeticFunction.moebius e : ℝ)) * Real.log e / ((e : ℕ) : ℝ)) :=
          by rw [Finset.sum_add_distrib]
      _ = hcG d * (-(Real.log d) * ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
              ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ)))
            + hcG d * ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
              ((-(ArithmeticFunction.moebius e : ℝ)) * Real.log e / ((e : ℕ) : ℝ)) := by
          simp only [Finset.mul_sum]
      _ = hcG d * (-(Real.log d) * hcMo (D / d) + hcTo (D / d)) := by
          rw [hMo, hTo]
          ring
  calc ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1),
        (-(ArithmeticFunction.moebius n : ℝ) * Real.log n / Nat.totient n)
      = ∑ n ∈ (Finset.Icc 1 D).filter (fun n => n % 2 = 1),
          ∑ d ∈ n.divisors, (-(hcG d) * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ))
            * Real.log ((d * (n / d) : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hstep1 n hn
    _ = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ e ∈ (Finset.Icc 1 (D / d)).filter (fun e => e % 2 = 1),
            (-(hcG d) * ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ))
              * Real.log ((d * e : ℕ) : ℝ)) :=
        hc_split_aux_reindex D (fun d e => -(hcG d) *
          ((ArithmeticFunction.moebius e : ℝ) / ((e : ℕ) : ℝ)) * Real.log ((d * e : ℕ) : ℝ))
    _ = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          hcG d * (-(Real.log d) * hcMo (D / d) + hcTo (D / d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hstep3 d hd
    _ = ∑ d ∈ Finset.Icc 1 D, hcG d * (-(Real.log d) * hcMo (D / d) + hcTo (D / d)) := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro d hd hdn
        have hne : ¬ (d % 2 = 1) := by
          intro hcon
          exact hdn ((memS d).2 ⟨(Finset.mem_Icc.1 hd).1, (Finset.mem_Icc.1 hd).2, hcon⟩)
        have hg : hcG d = 0 := by simp [hcG, hne]
        rw [hg]
        ring

noncomputable def hc_g_summable_aux_odd : ArithmeticFunction ℝ :=
  ⟨fun n => if n % 2 = 1 then 1 else 0, by simp⟩

theorem hc_g_summable_aux_odd_mult : hc_g_summable_aux_odd.IsMultiplicative := by
  constructor
  · simp [hc_g_summable_aux_odd]
  · intro m n hcop
    by_cases hm : m % 2 = 1 <;> by_cases hn : n % 2 = 1
    · have hmn : (m * n) % 2 = 1 := by
        rw [Nat.mul_mod, hm, hn] <;> norm_num
      simp [hc_g_summable_aux_odd, hm, hn, hmn]
    · have hn0 : n % 2 = 0 := by omega
      have hmn : (m * n) % 2 = 0 := by
        rw [Nat.mul_mod, hn0] <;> norm_num
      simp [hc_g_summable_aux_odd, hm, hn, hmn]
    · have hm0 : m % 2 = 0 := by omega
      have hmn : (m * n) % 2 = 0 := by
        rw [Nat.mul_mod, hm0] <;> norm_num
      simp [hc_g_summable_aux_odd, hm, hn, hmn]
    · have hm0 : m % 2 = 0 := by omega
      have hn0 : n % 2 = 0 := by omega
      have hmn : (m * n) % 2 = 0 := by
        rw [Nat.mul_mod, hm0, hn0] <;> norm_num
      simp [hc_g_summable_aux_odd, hm, hn, hmn]

noncomputable def hc_g_summable_aux_sqrtInv : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹, by simp⟩

theorem hc_g_summable_aux_sqrtInv_mult : hc_g_summable_aux_sqrtInv.IsMultiplicative := by
  constructor
  · simp [hc_g_summable_aux_sqrtInv]
  · intro m n hcop
    by_cases hm : m = 0 <;> by_cases hn : n = 0
    · subst m; subst n; simp [hc_g_summable_aux_sqrtInv]
    · subst m; simp [hc_g_summable_aux_sqrtInv]
    · subst n; simp [hc_g_summable_aux_sqrtInv]
    · change (if m * n = 0 then (0 : ℝ) else (Real.sqrt ((m * n : ℕ) : ℝ))⁻¹) =
        (if m = 0 then 0 else (Real.sqrt (m : ℝ))⁻¹) *
          (if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹)
      rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg m) (n : ℝ)]
      ring

noncomputable def hc_g_summable_aux_k : ArithmeticFunction ℝ :=
  hc_g_summable_aux_odd.pmul
    (hc_g_summable_aux_sqrtInv.pmul
      (ArithmeticFunction.prodPrimeFactors (fun p => (1 : ℝ) / ((p : ℝ) - 1))))

theorem hc_g_summable_aux_k_mult : hc_g_summable_aux_k.IsMultiplicative :=
  hc_g_summable_aux_odd_mult.pmul
    (hc_g_summable_aux_sqrtInv_mult.pmul (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _))

theorem hc_g_summable_aux_k_apply {n : ℕ} (hn : n ≠ 0) :
    hc_g_summable_aux_k n = (if n % 2 = 1 then 1 else 0) *
      ((Real.sqrt (n : ℝ))⁻¹ * ∏ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) := by
  change (if n % 2 = 1 then (1 : ℝ) else 0) *
      ((if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹) *
        (if n = 0 then 0 else ∏ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) - 1))) = _
  rw [if_neg hn, if_neg hn]

theorem hc_g_summable_aux_sqrt_nat_pow (p e : ℕ) :
    Real.sqrt ((p ^ e : ℕ) : ℝ) = Real.sqrt (p : ℝ) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, pow_succ, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg (p ^ e)) (p : ℝ), ih]

theorem hc_g_summable_aux_k_ppow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    hc_g_summable_aux_k (p ^ e) =
      if p = 2 then 0 else
        ((Real.sqrt (p : ℝ) ^ e)⁻¹ * (1 / ((p : ℝ) - 1))) := by
  have hpow : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  rw [hc_g_summable_aux_k_apply hpow, Nat.primeFactors_prime_pow (by omega) hp]
  simp only [Finset.prod_singleton]
  rw [hc_g_summable_aux_sqrt_nat_pow]
  by_cases h2 : p = 2
  · subst p
    have he0 : e ≠ 0 := by omega
    have hmod : (2 ^ e) % 2 = 0 := by
      simp [Nat.pow_mod, he0]
    simp [hmod]
  · have hpodd : p % 2 = 1 := by
      have hp2 : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases hp2 with h0 | h1
      · have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have := hp.eq_one_or_self_of_dvd 2 hdvd
        omega
      · exact h1
    have hmod : (p ^ e) % 2 = 1 := by
      rw [Nat.pow_mod, hpodd]
      norm_num
    simp [h2, hmod]

theorem hc_g_summable_aux_k_nonneg (n : ℕ) : 0 ≤ hc_g_summable_aux_k n := by
  by_cases hn : n = 0
  · subst n
    simp [hc_g_summable_aux_k]
  · rw [hc_g_summable_aux_k_apply hn]
    split_ifs with hodd
    · apply mul_nonneg (by norm_num)
      apply mul_nonneg (by positivity)
      apply Finset.prod_nonneg
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      exact div_nonneg zero_le_one (by linarith)
    · simp

theorem hc_g_summable_aux_k_ppow_le_geom {p e : ℕ} (hp : p.Prime) :
    hc_g_summable_aux_k (p ^ e) ≤ ((Real.sqrt (p : ℝ))⁻¹) ^ e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simpa using le_of_eq hc_g_summable_aux_k_mult.1
  · rw [hc_g_summable_aux_k_ppow hp he]
    by_cases h2 : p = 2
    · subst p
      simp
    · simp only [h2, if_false]
      rw [inv_pow]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have hc : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).2 hp1
      exact mul_le_of_le_one_right (by positivity) hc

theorem hc_g_summable_aux_k_ppow_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖hc_g_summable_aux_k (p ^ e)‖) := by
  let q : ℝ := (Real.sqrt (p : ℝ))⁻¹
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsqrt : (1 : ℝ) < Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by norm_num)]
    exact hpR
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    exact (inv_lt_one₀ (lt_trans zero_lt_one hsqrt)).2 hsqrt
  have hgeom : Summable (fun e : ℕ => q ^ e) :=
    summable_geometric_of_lt_one hq0 hq1
  apply hgeom.of_nonneg_of_le (fun e => norm_nonneg _)
  intro e
  simpa [q, Real.norm_eq_abs, abs_of_nonneg (hc_g_summable_aux_k_nonneg (p ^ e))] using
    hc_g_summable_aux_k_ppow_le_geom hp (e := e)

theorem hc_g_summable_aux_k_tail_eq {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) =
      1 / (((p : ℝ) - 1) * (Real.sqrt (p : ℝ) - 1)) := by
  let q : ℝ := (Real.sqrt (p : ℝ))⁻¹
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsqrt : (1 : ℝ) < Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by norm_num)]
    exact hpR
  have hqabs : |q| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hsqrt)).2 hsqrt
  have hterm : ∀ e : ℕ,
      hc_g_summable_aux_k (p ^ (e + 1)) = (1 / ((p : ℝ) - 1)) * q ^ (e + 1) := by
    intro e
    rw [hc_g_summable_aux_k_ppow hp (by omega), if_neg h2]
    dsimp [q]
    rw [inv_pow]
    ring
  calc
    (∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) =
        ∑' e : ℕ, (1 / ((p : ℝ) - 1)) * q ^ (e + 1) := tsum_congr hterm
    _ = (1 / ((p : ℝ) - 1)) * ∑' e : ℕ, q ^ (e + 1) := tsum_mul_left
    _ = (1 / ((p : ℝ) - 1)) * (q * ∑' e : ℕ, q ^ e) := by
      rw [show (fun e : ℕ => q ^ (e + 1)) = (fun e => q * q ^ e) by
        funext e; rw [pow_succ]; ring]
      rw [tsum_mul_left]
    _ = (1 / ((p : ℝ) - 1)) * q * ∑' e : ℕ, q ^ e := by ring
    _ = (1 / ((p : ℝ) - 1)) * q / (1 - q) := by
      rw [tsum_geometric_of_abs_lt_one hqabs]
      ring
    _ = 1 / (((p : ℝ) - 1) * (Real.sqrt (p : ℝ) - 1)) := by
      dsimp [q]
      have hs0 : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hsqrt)
      have hs1 : Real.sqrt (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.2 hsqrt)
      have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.2 hpR)
      field_simp

theorem hc_g_summable_aux_k_tail_le {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) ≤
      8 * (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  by_cases h2 : p = 2
  · subst p
    have hzero : ∀ e : ℕ, hc_g_summable_aux_k (2 ^ (e + 1)) = 0 := by
      intro e
      rw [hc_g_summable_aux_k_ppow (by norm_num) (by omega)]
      simp
    rw [tsum_congr hzero, tsum_zero]
    positivity
  · rw [hc_g_summable_aux_k_tail_eq hp h2]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have hp3nat : 3 ≤ p := by
        have hp2 := hp.two_le
        omega
      exact_mod_cast hp3nat
    let s : ℝ := Real.sqrt (p : ℝ)
    have hs0 : 0 ≤ s := by positivity
    have hs_sq : s * s = (p : ℝ) := by
      dsimp [s]
      exact Real.mul_self_sqrt (Nat.cast_nonneg p)
    have hs_ge : (4 : ℝ) / 3 ≤ s := by nlinarith
    have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by nlinarith
    have hs_quarter : s / 4 ≤ s - 1 := by nlinarith
    have hden : (p : ℝ) * s / 8 ≤ ((p : ℝ) - 1) * (s - 1) := by
      have := mul_le_mul hp_half hs_quarter (by positivity) (by nlinarith [hp3])
      nlinarith
    have hbase : (0 : ℝ) < (p : ℝ) * s / 8 := by
      have : (0 : ℝ) < (p : ℝ) := by linarith
      have : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs_ge
      positivity
    have hpow : (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) * s := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by linarith)]
      norm_num
    rw [hpow]
    calc
      1 / (((p : ℝ) - 1) * (s - 1)) ≤ 1 / ((p : ℝ) * s / 8) :=
        one_div_le_one_div_of_le hbase hden
      _ = 8 * ((p : ℝ) * s)⁻¹ := by ring

theorem hc_g_summable_aux_k_summable : Summable (fun n : ℕ => hc_g_summable_aux_k n) := by
  let w : ℕ → ℝ := fun n => 8 * (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)
  have hw : Summable w := by
    exact (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8
  have hw_nonneg : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    dsimp [w]
    positivity
  let B : ℝ := Real.exp (∑' n : ℕ, w n)
  apply summable_of_sum_range_le (c := B) hc_g_summable_aux_k_nonneg
  intro N
  let S : Finset N.smoothNumbers :=
    (Finset.range N).subtype (fun d => d ∈ N.smoothNumbers)
  have hSmap : S.map (Function.Embedding.subtype (fun d => d ∈ N.smoothNumbers)) =
      (Finset.range N).filter (fun d => d ∈ N.smoothNumbers) := by
    simpa [S] using (Finset.subtype_map (fun d => d ∈ N.smoothNumbers)
      (s := Finset.range N))
  have hsumS : (∑ d ∈ Finset.range N, hc_g_summable_aux_k d) = ∑ d ∈ S, hc_g_summable_aux_k d := by
    calc
      (∑ d ∈ Finset.range N, hc_g_summable_aux_k d) =
          ∑ d ∈ (Finset.range N).filter (fun d => d ∈ N.smoothNumbers), hc_g_summable_aux_k d := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro d hd hds
            have hd0 : d = 0 := by
              by_contra hd0
              apply hds
              exact Finset.mem_filter.mpr ⟨hd,
                Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hd0)
                  (Finset.mem_range.mp hd)⟩
            subst d
            simp [hc_g_summable_aux_k]
      _ = ∑ d ∈ S, hc_g_summable_aux_k d := by
        rw [← hSmap]
        simp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := (hc_g_summable_aux_k : ℕ → ℝ)) hc_g_summable_aux_k_mult.1 hc_g_summable_aux_k_mult.2 hc_g_summable_aux_k_ppow_summable N
  have hlocal : ∀ p ∈ N.primesBelow,
      (∑' e : ℕ, hc_g_summable_aux_k (p ^ e)) =
        1 + ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1)) := by
    intro p hp
    have hkp : Summable (fun e : ℕ => hc_g_summable_aux_k (p ^ e)) :=
      (hc_g_summable_aux_k_ppow_summable (Nat.prime_of_mem_primesBelow hp)).of_norm
    rw [hkp.tsum_eq_zero_add]
    simp only [pow_zero, hc_g_summable_aux_k_mult.1]
  have hprod_tail :
      (∏ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ e)) =
        ∏ p ∈ N.primesBelow, (1 + ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact hlocal p hp
  have htail_nonneg : ∀ p : ℕ, 0 ≤ ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1)) := by
    intro p
    exact tsum_nonneg (fun e => hc_g_summable_aux_k_nonneg (p ^ (e + 1)))
  have htail_sum_le :
      (∑ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) ≤ ∑' n : ℕ, w n := by
    calc
      (∑ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) ≤
          ∑ p ∈ N.primesBelow, w p := by
            apply Finset.sum_le_sum
            intro p hp
            exact hc_g_summable_aux_k_tail_le (Nat.prime_of_mem_primesBelow hp)
      _ ≤ ∑ p ∈ Finset.range N, w p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
        · intro p hpN hpnot
          exact hw_nonneg p
      _ ≤ ∑' n : ℕ, w n := hw.sum_le_tsum (Finset.range N)
        (fun p hp => hw_nonneg p)
  have hprod_le :
      (∏ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ e)) ≤ B := by
    calc
      (∏ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ e)) =
          ∏ p ∈ N.primesBelow, (1 + ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) := hprod_tail
      _ ≤ Real.exp (∑ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ (e + 1))) :=
        Real.prod_one_add_le_exp_sum _ htail_nonneg
      _ ≤ Real.exp (∑' n : ℕ, w n) := Real.exp_le_exp.mpr htail_sum_le
      _ = B := by rfl
  calc
    (∑ d ∈ Finset.range N, hc_g_summable_aux_k d) = ∑ d ∈ S, hc_g_summable_aux_k d := hsumS
    _ ≤ ∑' d : N.smoothNumbers, hc_g_summable_aux_k d :=
      hEuler.2.summable.sum_le_tsum S (fun d hd => hc_g_summable_aux_k_nonneg d)
    _ = ∏ p ∈ N.primesBelow, ∑' e : ℕ, hc_g_summable_aux_k (p ^ e) := hEuler.2.tsum_eq
    _ ≤ B := hprod_le

theorem hc_g_summable_aux_abs_mul_sqrt (d : ℕ) :
    |hcG d| * Real.sqrt (d : ℝ) = hc_g_summable_aux_k d := by
  by_cases hodd : d % 2 = 1
  · have hd0 : d ≠ 0 := by omega
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero hd0)))
    rw [hcG, if_pos hodd, hc_g_summable_aux_k_apply hd0]
    simp only [if_pos hodd, one_mul]
    have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
    rw [abs_div, hdabs, abs_prod]
    have hprod :
        (∏ p ∈ d.primeFactors, |(-1 : ℝ) / ((p : ℝ) - 1)|) =
          ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      rw [abs_div, abs_neg, abs_one, abs_of_nonneg (by linarith)]
    rw [hprod]
    calc
      ((∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) / (d : ℝ)) *
          Real.sqrt (d : ℝ) =
          (∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) *
            (Real.sqrt (d : ℝ) / (d : ℝ)) := by ring
      _ = (∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) *
          (Real.sqrt (d : ℝ))⁻¹ := by
        congr 1
        field_simp [hdR, hsqrt]
        nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg d)]
      _ = (Real.sqrt (d : ℝ))⁻¹ *
          ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by ring
  · have hk0 : hc_g_summable_aux_k d = 0 := by
      by_cases hd0 : d = 0
      · subst d
        exact hc_g_summable_aux_k.map_zero
      · rw [hc_g_summable_aux_k_apply hd0]
        simp [hodd]
    simp [hcG, hodd, hk0]

theorem hc_g_summable_aux_log_weight_le {d : ℕ} (hd : 0 < d) :
    1 + Real.log (d : ℝ) ≤ 3 * Real.sqrt (d : ℝ) := by
  have hlog := Real.log_natCast_le_rpow_div d (ε := (1 / 2 : ℝ)) (by norm_num)
  have hlog' : Real.log (d : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hlog
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  linarith

theorem hc_g_summable_aux_term_le (d : ℕ) :
    |hcG d| * (1 + Real.log (d : ℝ)) ≤ 3 * hc_g_summable_aux_k d := by
  by_cases hd0 : d = 0
  · subst d
    simp [hcG, hc_g_summable_aux_k]
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    calc
      |hcG d| * (1 + Real.log (d : ℝ)) ≤
          |hcG d| * (3 * Real.sqrt (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (hc_g_summable_aux_log_weight_le hd) (abs_nonneg _)
      _ = 3 * (|hcG d| * Real.sqrt (d : ℝ)) := by ring
      _ = 3 * hc_g_summable_aux_k d := by rw [hc_g_summable_aux_abs_mul_sqrt]

theorem hc_g_summable : Summable (fun d : ℕ => |hcG d| * (1 + Real.log d)) := by
  apply hc_g_summable_aux_k_summable.mul_left 3 |>.of_nonneg_of_le
  · intro d
    exact mul_nonneg (abs_nonneg _) (by linarith [Real.log_natCast_nonneg d])
  · exact hc_g_summable_aux_term_le

theorem hc_g_tsum_aux_of_odd {d : ℕ} (hd : d % 2 = 1) :
    hcG d = (∏ p ∈ d.primeFactors, (-1 / ((p : ℝ) - 1))) / (d : ℝ) := by
  simp [hcG, hd]

theorem hc_g_tsum_aux_of_even {d : ℕ} (hd : d % 2 ≠ 1) : hcG d = 0 := by
  simp [hcG, hd]

theorem hc_g_tsum_aux_zero : hcG 0 = 0 := hc_g_tsum_aux_of_even (by norm_num)

theorem hc_g_tsum_aux_one : hcG 1 = 1 := by
  rw [hc_g_tsum_aux_of_odd (by norm_num), Nat.primeFactors_one]
  norm_num

theorem hc_g_tsum_aux_mul {m n : ℕ} (h : Nat.Coprime m n) :
    hcG (m * n) = hcG m * hcG n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hc_g_tsum_aux_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hc_g_tsum_aux_zero]
  by_cases hmo : m % 2 = 1
  · by_cases hno : n % 2 = 1
    · have hmn : (m * n) % 2 = 1 := by
        rw [Nat.mul_mod, hmo, hno]
      rw [hc_g_tsum_aux_of_odd hmn, hc_g_tsum_aux_of_odd hmo, hc_g_tsum_aux_of_odd hno,
        h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors, div_mul_div_comm,
        Nat.cast_mul]
    · have hn0 : n % 2 = 0 := by
        have := Nat.mod_lt n (by norm_num : 0 < 2); omega
      have hmn : (m * n) % 2 = 0 := by rw [Nat.mul_mod, hn0, mul_zero, Nat.zero_mod]
      rw [hc_g_tsum_aux_of_even (by omega : (m * n) % 2 ≠ 1), hc_g_tsum_aux_of_even hno, mul_zero]
  · have hm0 : m % 2 = 0 := by
      have := Nat.mod_lt m (by norm_num : 0 < 2); omega
    have hmn : (m * n) % 2 = 0 := by rw [Nat.mul_mod, hm0, zero_mul, Nat.zero_mod]
    rw [hc_g_tsum_aux_of_even (by omega : (m * n) % 2 ≠ 1), hc_g_tsum_aux_of_even hmo, zero_mul]

theorem hc_g_tsum_aux_ppow {p e : ℕ} (hp : Nat.Prime p) (he : e ≠ 0) :
    hcG (p ^ e) = if p % 2 = 1 then (-1 / ((p : ℝ) - 1)) / ((p ^ e : ℕ) : ℝ) else 0 := by
  by_cases hpo : p % 2 = 1
  · have hpe : (p ^ e) % 2 = 1 := by
      rw [Nat.pow_mod, hpo, one_pow]; norm_num
    rw [if_pos hpo, hc_g_tsum_aux_of_odd hpe, Nat.primeFactors_prime_pow he hp]
    simp
  · rw [if_neg hpo]
    refine hc_g_tsum_aux_of_even ?_
    rw [Nat.pow_mod]
    have hp0 : p % 2 = 0 := by
      have := Nat.mod_lt p (by norm_num : 0 < 2); omega
    rw [hp0, zero_pow he]
    norm_num

theorem hc_g_tsum_aux_ppow_val {p : ℕ} (hp : Nat.Prime p) (hpo : p % 2 = 1) (e : ℕ) :
    hcG (p ^ (e + 1)) = (-1 / ((p : ℝ) - 1)) * ((p : ℝ) ^ (e + 1))⁻¹ := by
  rw [hc_g_tsum_aux_ppow hp (by omega : e + 1 ≠ 0), if_pos hpo, Nat.cast_pow, div_eq_mul_inv]

theorem hc_g_tsum_aux_ppow_succ {p : ℕ} (hp : Nat.Prime p) (hpo : p % 2 = 1) (e : ℕ) :
    hcG (p ^ (e + 1)) = (-1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e := by
  rw [hc_g_tsum_aux_ppow_val hp hpo e, pow_succ, mul_inv_rev, ← inv_pow]
  ring

theorem hc_g_tsum_aux_local_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => hcG (p ^ e)) := by
  have h : Summable (fun e : ℕ => hcG (p ^ (e + 1))) := by
    by_cases hpo : p % 2 = 1
    · have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
      have hr : ‖((p : ℝ))⁻¹‖ < 1 := by
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp0]
        exact (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
      have hs : Summable (fun e : ℕ => ((p : ℝ))⁻¹ ^ e) := summable_geometric_of_norm_lt_one hr
      have h2 : Summable (fun e : ℕ => (-1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) :=
        hs.mul_left _
      rwa [show (fun e : ℕ => hcG (p ^ (e + 1)))
            = (fun e : ℕ => (-1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) from
          funext (fun e => hc_g_tsum_aux_ppow_succ hp hpo e)]
    · have h0 : ∀ e : ℕ, hcG (p ^ (e + 1)) = 0 := by
        intro e
        rw [hc_g_tsum_aux_ppow hp (by omega : e + 1 ≠ 0), if_neg hpo]
      rw [show (fun e : ℕ => hcG (p ^ (e + 1))) = (fun _ : ℕ => (0:ℝ)) from funext h0]
      exact summable_zero
  exact (summable_nat_add_iff (f := fun e : ℕ => hcG (p ^ e)) 1).mp h

theorem hc_g_tsum_aux_local {p : ℕ} (hp : Nat.Prime p) :
    ∑' e : ℕ, hcG ((p : ℕ) ^ e) = if 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  have hsum : Summable (fun e : ℕ => hcG (p ^ e)) := hc_g_tsum_aux_local_summable hp
  rw [hsum.tsum_eq_zero_add]
  have h0 : hcG (p ^ 0) = 1 := by rw [pow_zero]; exact hc_g_tsum_aux_one
  rw [h0]
  rcases hp.eq_two_or_odd with rfl | hpo
  · have hz : ∀ e : ℕ, hcG (2 ^ (e + 1)) = 0 := by
      intro e
      rw [hc_g_tsum_aux_ppow Nat.prime_two (by omega : e + 1 ≠ 0), if_neg (by norm_num)]
    rw [show (fun e : ℕ => hcG (2 ^ (e + 1))) = (fun _ : ℕ => (0:ℝ)) from funext hz, tsum_zero]
    norm_num
  · have hp2 : 2 < p := by
      have h1 := hp.two_le
      have h2 : p ≠ 2 := by intro h; rw [h] at hpo; norm_num at hpo
      omega
    rw [if_pos hp2]
    have hval : ∀ e : ℕ, hcG (p ^ (e + 1))
        = (-1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e :=
      fun e => hc_g_tsum_aux_ppow_succ hp hpo e
    rw [show (fun e : ℕ => hcG (p ^ (e + 1)))
          = (fun e : ℕ => (-1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) from funext hval,
        tsum_mul_left]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have hr0 : (0:ℝ) ≤ ((p : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hp0)
    have hr1 : ((p : ℝ))⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
    rw [tsum_geometric_of_lt_one hr0 hr1]
    have hp1 : ((p:ℝ) - 1) ≠ 0 := by
      have h1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
      linarith
    field_simp <;> ring

theorem hc_g_tsum_aux_norm_one : ‖hcG 1‖ = 1 := by rw [hc_g_tsum_aux_one, norm_one]

theorem hc_g_tsum_aux_norm_mul {m n : ℕ} (h : Nat.Coprime m n) :
    ‖hcG (m * n)‖ = ‖hcG m‖ * ‖hcG n‖ := by rw [hc_g_tsum_aux_mul h, norm_mul]

theorem hc_g_tsum_aux_norm_norm {d : ℕ} : ‖‖hcG d‖‖ = ‖hcG d‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem hc_g_tsum_aux_norm_ppow_val {p : ℕ} (hp : Nat.Prime p) (hpo : p % 2 = 1) (e : ℕ) :
    ‖hcG (p ^ (e + 1))‖ = (1 / ((p : ℝ) - 1)) * ((p : ℝ) ^ (e + 1))⁻¹ := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have h1 : (0:ℝ) < (p:ℝ) - 1 := by
    have h : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hpow : (0:ℝ) < (p:ℝ) ^ (e + 1) := pow_pos hp0 _
  rw [hc_g_tsum_aux_ppow hp (by omega : e + 1 ≠ 0), if_pos hpo, Real.norm_eq_abs, abs_div,
    Nat.cast_pow, abs_of_pos hpow, abs_div, abs_neg, abs_one, abs_of_pos h1, div_eq_mul_inv]

theorem hc_g_tsum_aux_norm_ppow_succ {p : ℕ} (hp : Nat.Prime p) (hpo : p % 2 = 1) (e : ℕ) :
    ‖hcG (p ^ (e + 1))‖ = (1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e := by
  rw [hc_g_tsum_aux_norm_ppow_val hp hpo e, pow_succ, mul_inv_rev, ← inv_pow]
  ring

theorem hc_g_tsum_aux_norm_local_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖hcG (p ^ (e + 1))‖) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hr : ‖((p : ℝ))⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp0]
    exact (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hs : Summable (fun e : ℕ => ((p : ℝ))⁻¹ ^ e) := summable_geometric_of_norm_lt_one hr
  by_cases hpo : p % 2 = 1
  · have h2 : Summable (fun e : ℕ => (1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) :=
      hs.mul_left _
    rwa [show (fun e : ℕ => ‖hcG (p ^ (e + 1))‖)
          = (fun e : ℕ => (1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) from
        funext (fun e => hc_g_tsum_aux_norm_ppow_succ hp hpo e)]
  · have h0 : ∀ e : ℕ, ‖hcG (p ^ (e + 1))‖ = 0 := by
      intro e
      rw [hc_g_tsum_aux_ppow hp (by omega : e + 1 ≠ 0), if_neg hpo, norm_zero]
    rw [show (fun e : ℕ => ‖hcG (p ^ (e + 1))‖) = (fun _ : ℕ => (0:ℝ)) from funext h0]
    exact summable_zero

theorem hc_g_tsum_aux_norm_pow_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun n : ℕ => ‖hcG (p ^ n)‖) :=
  (summable_nat_add_iff (f := fun n : ℕ => ‖hcG (p ^ n)‖) 1).mp
    (hc_g_tsum_aux_norm_local_summable hp)

theorem hc_g_tsum_aux_norm_norm_pow_summable {p : ℕ} (hp : Nat.Prime p) :
    Summable (fun n : ℕ => ‖‖hcG (p ^ n)‖‖) := by
  rw [show (fun n : ℕ => ‖‖hcG (p ^ n)‖‖) = (fun n : ℕ => ‖hcG (p ^ n)‖) from
    funext (fun n => hc_g_tsum_aux_norm_norm)]
  exact hc_g_tsum_aux_norm_pow_summable hp

theorem hc_g_tsum_aux_norm_local {p : ℕ} (hp : Nat.Prime p) :
    ∑' e : ℕ, ‖hcG (p ^ (e + 1))‖ = if p % 2 = 1 then 1 / ((p : ℝ) - 1) ^ 2 else 0 := by
  by_cases hpo : p % 2 = 1
  · rw [if_pos hpo]
    have hval : ∀ e : ℕ, ‖hcG (p ^ (e + 1))‖
        = (1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e :=
      fun e => hc_g_tsum_aux_norm_ppow_succ hp hpo e
    rw [show (fun e : ℕ => ‖hcG (p ^ (e + 1))‖)
          = (fun e : ℕ => (1 / ((p : ℝ) - 1) * ((p : ℝ))⁻¹) * ((p : ℝ))⁻¹ ^ e) from funext hval,
        tsum_mul_left]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have hr0 : (0:ℝ) ≤ ((p : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hp0)
    have hr1 : ((p : ℝ))⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
    rw [tsum_geometric_of_lt_one hr0 hr1]
    have hp1 : ((p:ℝ) - 1) ≠ 0 := by
      have h1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
      linarith
    field_simp <;> ring
  · rw [if_neg hpo]
    have h0 : ∀ e : ℕ, ‖hcG (p ^ (e + 1))‖ = 0 := by
      intro e
      rw [hc_g_tsum_aux_ppow hp (by omega : e + 1 ≠ 0), if_neg hpo, norm_zero]
    rw [show (fun e : ℕ => ‖hcG (p ^ (e + 1))‖) = (fun _ : ℕ => (0:ℝ)) from funext h0, tsum_zero]

theorem hc_g_tsum_aux_norm_local_le {p : ℕ} (hp : Nat.Prime p) :
    ∑' e : ℕ, ‖hcG (p ^ (e + 1))‖ ≤ 4 / (p : ℝ) ^ 2 := by
  rw [hc_g_tsum_aux_norm_local hp]
  by_cases hpo : p % 2 = 1
  · rw [if_pos hpo]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by
      have h : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
      linarith
    have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    rw [div_le_div_iff₀ (sq_pos_of_pos h1) (sq_pos_of_pos hp0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ 3 * (p:ℝ) - 2)]
  · rw [if_neg hpo]
    exact div_nonneg (by norm_num) (sq_nonneg _)

theorem hc_g_tsum_aux_norm_local_bound {p : ℕ} (hp : Nat.Prime p) :
    ∑' e : ℕ, ‖hcG (p ^ e)‖ ≤ 1 + 4 / (p : ℝ) ^ 2 := by
  have hsum : Summable (fun e : ℕ => ‖hcG (p ^ e)‖) := hc_g_tsum_aux_norm_pow_summable hp
  have h0 : ‖hcG (p ^ 0)‖ = 1 := by rw [pow_zero, hc_g_tsum_aux_one, norm_one]
  have hle := hc_g_tsum_aux_norm_local_le hp
  calc ∑' e : ℕ, ‖hcG (p ^ e)‖
      = ‖hcG (p ^ 0)‖ + ∑' e : ℕ, ‖hcG (p ^ (e + 1))‖ := hsum.tsum_eq_zero_add
    _ = 1 + ∑' e : ℕ, ‖hcG (p ^ (e + 1))‖ := by rw [h0]
    _ ≤ 1 + 4 / (p : ℝ) ^ 2 := by linarith

theorem hc_g_tsum_aux_summable : Summable (fun d : ℕ => ‖hcG d‖) := by
  apply summable_of_sum_range_le (fun d => norm_nonneg _)
    (c := Real.exp (4 * ∑' m : ℕ, 1 / (m : ℝ) ^ 2))
  intro N
  have hmem : ∀ d ∈ Finset.range N, d ≠ 0 → d ∈ Nat.factoredNumbers (Finset.range N) := by
    intro d hd hdn
    rw [Nat.mem_factoredNumbers']
    intro q _ hqd
    have hqle : q ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hdn) hqd
    exact Finset.mem_range.mpr (lt_of_le_of_lt hqle (Finset.mem_range.mp hd))
  obtain ⟨hsum_sub, hHasSum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (f := fun d : ℕ => ‖hcG d‖) hc_g_tsum_aux_norm_one hc_g_tsum_aux_norm_mul
      (fun {p} hp => hc_g_tsum_aux_norm_norm_pow_summable hp) (Finset.range N)
  have hsum_sub' : Summable (fun m : Nat.factoredNumbers (Finset.range N) => ‖hcG (m : ℕ)‖) := by
    rwa [show (fun m : Nat.factoredNumbers (Finset.range N) => ‖‖hcG (m : ℕ)‖‖)
        = (fun m : Nat.factoredNumbers (Finset.range N) => ‖hcG (m : ℕ)‖) from
      funext (fun m => hc_g_tsum_aux_norm_norm)] at hsum_sub
  have hind : Summable ((Nat.factoredNumbers (Finset.range N)).indicator (fun d => ‖hcG d‖)) :=
    summable_subtype_iff_indicator.mp hsum_sub'
  have hstep1 : ∑ d ∈ Finset.range N, ‖hcG d‖
      ≤ ∑ d ∈ Finset.range N, (Nat.factoredNumbers (Finset.range N)).indicator
          (fun d => ‖hcG d‖) d := by
    apply Finset.sum_le_sum
    intro d hd
    by_cases hd0 : d = 0
    · subst hd0
      rw [hc_g_tsum_aux_zero, norm_zero]
      exact Set.indicator_nonneg (fun a _ => norm_nonneg _) 0
    · rw [Set.indicator_of_mem (hmem d hd hd0)]
  have hstep2 : ∑ d ∈ Finset.range N, (Nat.factoredNumbers (Finset.range N)).indicator
        (fun d => ‖hcG d‖) d
      ≤ ∑' d : ℕ, (Nat.factoredNumbers (Finset.range N)).indicator (fun d => ‖hcG d‖) d :=
    hind.sum_le_tsum _ (fun i _ => Set.indicator_nonneg (fun a _ => norm_nonneg _) i)
  have hstep3 : ∑' d : ℕ, (Nat.factoredNumbers (Finset.range N)).indicator (fun d => ‖hcG d‖) d
      = ∑' m : Nat.factoredNumbers (Finset.range N), ‖hcG (m : ℕ)‖ :=
    (tsum_subtype (Nat.factoredNumbers (Finset.range N)) (fun d => ‖hcG d‖)).symm
  have hstep4 : ∑' m : Nat.factoredNumbers (Finset.range N), ‖hcG (m : ℕ)‖
      = ∏ p ∈ Finset.range N with Nat.Prime p, ∑' n : ℕ, ‖hcG (p ^ n)‖ := hHasSum.tsum_eq
  have hstep5 : ∏ p ∈ Finset.range N with Nat.Prime p, ∑' n : ℕ, ‖hcG (p ^ n)‖
      ≤ ∏ p ∈ Finset.range N with Nat.Prime p, (1 + 4 / (p : ℝ) ^ 2) := by
    refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg (fun n => norm_nonneg _)) ?_
    intro p hp
    exact hc_g_tsum_aux_norm_local_bound (Finset.mem_filter.mp hp).2
  have hstep6 : ∏ p ∈ Finset.range N with Nat.Prime p, (1 + 4 / (p : ℝ) ^ 2)
      ≤ Real.exp (4 * ∑' m : ℕ, 1 / (m : ℝ) ^ 2) := by
    have hsum4 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h1 : ∑ p ∈ Finset.range N with Nat.Prime p, (4 : ℝ) / (p : ℝ) ^ 2
        = 4 * ∑ p ∈ Finset.range N with Nat.Prime p, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    have h2 : ∑ p ∈ Finset.range N with Nat.Prime p, 1 / (p : ℝ) ^ 2
        ≤ ∑' m : ℕ, 1 / (m : ℝ) ^ 2 :=
      hsum4.sum_le_tsum _ (fun i _ => div_nonneg (by norm_num) (sq_nonneg _))
    calc ∏ p ∈ Finset.range N with Nat.Prime p, (1 + 4 / (p : ℝ) ^ 2)
        ≤ ∏ p ∈ Finset.range N with Nat.Prime p, Real.exp (4 / (p : ℝ) ^ 2) := by
          refine Finset.prod_le_prod₀
            (fun p _ => add_nonneg (by norm_num) (div_nonneg (by norm_num) (sq_nonneg _))) ?_
          intro p _
          have := Real.add_one_le_exp (4 / (p : ℝ) ^ 2)
          linarith
      _ = Real.exp (∑ p ∈ Finset.range N with Nat.Prime p, 4 / (p : ℝ) ^ 2) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (4 * ∑' m : ℕ, 1 / (m : ℝ) ^ 2) := by
          rw [Real.exp_le_exp]
          rw [h1]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  calc ∑ d ∈ Finset.range N, ‖hcG d‖
      ≤ ∑ d ∈ Finset.range N, (Nat.factoredNumbers (Finset.range N)).indicator
          (fun d => ‖hcG d‖) d := hstep1
    _ ≤ ∑' d : ℕ, (Nat.factoredNumbers (Finset.range N)).indicator (fun d => ‖hcG d‖) d := hstep2
    _ = ∑' m : Nat.factoredNumbers (Finset.range N), ‖hcG (m : ℕ)‖ := hstep3
    _ = ∏ p ∈ Finset.range N with Nat.Prime p, ∑' n : ℕ, ‖hcG (p ^ n)‖ := hstep4
    _ ≤ ∏ p ∈ Finset.range N with Nat.Prime p, (1 + 4 / (p : ℝ) ^ 2) := hstep5
    _ ≤ Real.exp (4 * ∑' m : ℕ, 1 / (m : ℝ) ^ 2) := hstep6

theorem hc_g_tsum :
    ∑' d : ℕ, hcG d = ∏' p : ℕ, (if p.Prime ∧ 2 < p then 1 - 1/((p:ℝ)-1)^2 else 1) := by
  have hE : ∏' q : {q : ℕ // q.Prime}, ∑' e : ℕ, hcG ((q : ℕ) ^ e) = ∑' n : ℕ, hcG n :=
    EulerProduct.eulerProduct_tprod hc_g_tsum_aux_one hc_g_tsum_aux_mul
      hc_g_tsum_aux_summable hc_g_tsum_aux_zero
  have hF : Function.mulSupport
      (fun p : ℕ => if p.Prime ∧ 2 < p then 1 - 1/((p:ℝ)-1)^2 else 1) ⊆ {p : ℕ | p.Prime} := by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    by_contra hcon
    simp only [Set.mem_setOf_eq] at hcon
    simp [hcon] at hp
  calc ∑' d : ℕ, hcG d
      = ∏' q : {q : ℕ // q.Prime}, ∑' e : ℕ, hcG ((q : ℕ) ^ e) := hE.symm
    _ = ∏' q : {q : ℕ // q.Prime},
          (if (q : ℕ).Prime ∧ 2 < (q : ℕ) then 1 - 1/((q:ℝ)-1)^2 else 1) := by
        apply tprod_congr
        intro q
        rw [hc_g_tsum_aux_local q.prop]
        simp [q.prop]
    _ = ∏' p : ℕ, (if p.Prime ∧ 2 < p then 1 - 1/((p:ℝ)-1)^2 else 1) :=
        tprod_subtype_eq_of_mulSupport_subset hF

theorem hc_tannery (g : ℕ → ℝ) (hg : Summable (fun d : ℕ => |g d| * (1 + Real.log d))) (hg0 : g 0 = 0)
    (u v : ℕ → ℝ) (L : ℝ) (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hv : Filter.Tendsto v Filter.atTop (nhds L)) :
    Filter.Tendsto (fun D : ℕ => ∑ d ∈ Finset.Icc 1 D, g d * (-(Real.log d) * u (D / d) + v (D / d)))
      Filter.atTop (nhds (L * ∑' d : ℕ, g d)) := by
  let f : ℕ → ℕ → ℝ := fun D d =>
    if d ∈ Finset.Icc 1 D then
      g d * (-(Real.log d) * u (D / d) + v (D / d))
    else 0
  have huB : Bornology.IsBounded (Set.range u) :=
    Metric.isBounded_range_of_tendsto u hu
  have hvB : Bornology.IsBounded (Set.range v) :=
    Metric.isBounded_range_of_tendsto v hv
  obtain ⟨U, hUpos, hU⟩ := huB.exists_pos_norm_le
  obtain ⟨V, hVpos, hV⟩ := hvB.exists_pos_norm_le
  let C : ℝ := U + V
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hf_mem (D d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      f D d = g d * (-(Real.log d) * u (D / d) + v (D / d)) := by
    simp only [f, if_pos hd]
  have hf_not_mem (D d : ℕ) (hd : d ∉ Finset.Icc 1 D) : f D d = 0 := by
    simp only [f, if_neg hd]
  have h_bound : ∀ D d : ℕ, ‖f D d‖ ≤ C * (|g d| * (1 + Real.log d)) := by
    intro D d
    by_cases hd : d ∈ Finset.Icc 1 D
    · have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hlog : 0 ≤ Real.log d := by
        exact_mod_cast Real.log_natCast_nonneg d
      have huD : ‖u (D / d)‖ ≤ U := hU _ ⟨_, rfl⟩
      have hvD : ‖v (D / d)‖ ≤ V := hV _ ⟨_, rfl⟩
      rw [hf_mem D d hd]
      rw [norm_mul]
      have hinner :
          ‖-(Real.log d) * u (D / d) + v (D / d)‖ ≤
            Real.log d * U + V := by
        calc
          ‖-(Real.log d) * u (D / d) + v (D / d)‖ ≤
              ‖-(Real.log d) * u (D / d)‖ + ‖v (D / d)‖ := norm_add_le _ _
          _ = Real.log d * ‖u (D / d)‖ + ‖v (D / d)‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hlog]
          _ ≤ Real.log d * U + V := by gcongr
      have hweight : 0 ≤ |g d| := abs_nonneg _
      have hbase : Real.log d * U + V ≤ (1 + Real.log d) * C := by
        dsimp [C]
        nlinarith [hlog, hUpos, hVpos]
      calc
        ‖g d‖ * ‖-(Real.log d) * u (D / d) + v (D / d)‖ ≤
            ‖g d‖ * (Real.log d * U + V) := by gcongr
        _ ≤ ‖g d‖ * ((1 + Real.log d) * C) := by
          exact mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
        _ = C * (|g d| * (1 + Real.log d)) := by
          rw [Real.norm_eq_abs]
          ring
    · have hweight : 0 ≤ |g d| * (1 + Real.log d) := by
        positivity
      have hC : 0 ≤ C := hCpos.le
      rw [hf_not_mem D d hd, norm_zero]
      positivity
  have h_sum : Summable (fun d : ℕ => C * (|g d| * (1 + Real.log d))) :=
    hg.mul_left C
  have hab : ∀ d : ℕ, Tendsto (fun D : ℕ => f D d) atTop (nhds (L * g d)) := by
    intro d
    by_cases hd0 : d = 0
    · subst d
      simpa [f, hg0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdiv : Tendsto (fun D : ℕ => D / d) atTop atTop :=
        Nat.tendsto_div_const_atTop hd0
      have hu' : Tendsto (fun D : ℕ => u (D / d)) atTop (nhds 0) := hu.comp hdiv
      have hv' : Tendsto (fun D : ℕ => v (D / d)) atTop (nhds L) := hv.comp hdiv
      have hzero : Tendsto (fun D : ℕ => -(Real.log d) * u (D / d)) atTop (nhds 0) := by
        simpa using hu'.const_mul (-(Real.log d))
      have hinner : Tendsto (fun D : ℕ =>
          -(Real.log d) * u (D / d) + v (D / d)) atTop (nhds L) := by
        simpa using hzero.add hv'
      have hwhole : Tendsto (fun D : ℕ =>
          g d * (-(Real.log d) * u (D / d) + v (D / d))) atTop (nhds (L * g d)) := by
        simpa [mul_comm] using hinner.const_mul (g d)
      apply hwhole.congr'
      filter_upwards [eventually_ge_atTop d] with D hD
      have hmem : d ∈ Finset.Icc 1 D := by
        exact Finset.mem_Icc.mpr ⟨hdpos, hD⟩
      rw [hf_mem D d hmem]
  have hT := tendsto_tsum_of_dominated_convergence
    (f := f) (g := fun d : ℕ => L * g d)
    (bound := fun d : ℕ => C * (|g d| * (1 + Real.log d)))
    h_sum hab (Filter.Eventually.of_forall h_bound)
  have hfinite (D : ℕ) : (∑' d : ℕ, f D d) =
      ∑ d ∈ Finset.Icc 1 D, g d * (-(Real.log d) * u (D / d) + v (D / d)) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 D)]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [hf_mem D d hd]
    · intro d hd
      exact hf_not_mem D d hd
  have hT' : Tendsto (fun D : ℕ =>
      ∑ d ∈ Finset.Icc 1 D, g d * (-(Real.log d) * u (D / d) + v (D / d)))
      atTop (nhds (∑' d : ℕ, L * g d)) := by
    simpa only [hfinite] using hT
  simpa only [tsum_mul_left] using hT'

theorem PEqualNP.Outside.L_twin_primes_hard_cutoff : let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1; let twinC := ∏' p : ℕ, f p; RiemannHypothesis → Filter.Tendsto (fun D : ℕ => ((Finset.Icc 1 D).filter (fun n => n %2=1)).sum (fun n => -(ArithmeticFunction.moebius n : ℝ)*Real.log n / Nat.totient n)) Filter.atTop (nhds (2*twinC)) := by
  intro f twinC hRH
  obtain ⟨h0, h1⟩ := hc_moebius hRH
  obtain ⟨ho0, ho1⟩ := hc_odd_moments h0 h1
  have ht : twinC = ∑' d : ℕ, hcG d := hc_g_tsum.symm
  have hT := hc_tannery hcG hc_g_summable (by simp [hcG]) hcMo hcTo 2 ho0 ho1
  rw [ht]
  refine hT.congr' ?_
  filter_upwards with D
  exact (hc_split hc_factor D).symm
