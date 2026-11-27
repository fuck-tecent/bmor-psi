import Mathlib

namespace PEqualNP.Outside.MellinWindowDecayAux

noncomputable section

private def eulerOp (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * deriv g x

private theorem zero_outside {g : ℝ → ℂ} (hsupp : Function.support g ⊆ Set.Icc 1 2)
    {x : ℝ} (hx : x ∉ Set.Icc (1 : ℝ) 2) : g x = 0 := by
  by_contra hne
  exact hx (hsupp hne)

private theorem vanish_one {g : ℝ → ℂ} (hc : Continuous g)
    (hsupp : Function.support g ⊆ Set.Icc 1 2) : g 1 = 0 := by
  have hclosed : IsClosed {x : ℝ | g x = 0} := isClosed_singleton.preimage hc
  have hsub : Set.Iio (1 : ℝ) ⊆ {x : ℝ | g x = 0} := fun x hx =>
    zero_outside hsupp (fun h => by linarith [h.1, Set.mem_Iio.mp hx])
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Iio] at hcl
  exact hcl (Set.mem_Iic.mpr le_rfl)

private theorem vanish_two {g : ℝ → ℂ} (hc : Continuous g)
    (hsupp : Function.support g ⊆ Set.Icc 1 2) : g 2 = 0 := by
  have hclosed : IsClosed {x : ℝ | g x = 0} := isClosed_singleton.preimage hc
  have hsub : Set.Ioi (2 : ℝ) ⊆ {x : ℝ | g x = 0} := fun x hx =>
    zero_outside hsupp (fun h => by linarith [h.2, Set.mem_Ioi.mp hx])
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioi] at hcl
  exact hcl (Set.mem_Ici.mpr le_rfl)

private theorem eulerOp_smooth {g : ℝ → ℂ} (hg : ∀ j : ℕ, ContDiff ℝ j g) :
    ∀ j : ℕ, ContDiff ℝ j (eulerOp g) := by
  intro j
  have hsucc := hg (j + 1)
  rw [Nat.cast_add, Nat.cast_one] at hsucc
  have hd : ContDiff ℝ j (deriv g) := (contDiff_succ_iff_deriv.mp hsucc).2.2
  exact Complex.ofRealCLM.contDiff.mul hd

private theorem eulerOp_support {g : ℝ → ℂ} (hsupp : Function.support g ⊆ Set.Icc 1 2) :
    Function.support (eulerOp g) ⊆ Set.Icc 1 2 := by
  intro x hx
  by_contra hnot
  apply hx
  have hd0 : deriv g x = 0 := by
    by_cases h1 : x < 1
    · have heq : g =ᶠ[nhds x] (fun _ : ℝ => (0 : ℂ)) :=
        Filter.eventually_of_mem (Iio_mem_nhds h1) fun y hy =>
          zero_outside hsupp (fun h => by linarith [h.1, Set.mem_Iio.mp hy])
      rw [heq.deriv_eq, deriv_const]
    · have h2 : 2 < x := by
        by_contra hle
        exact hnot ⟨by linarith, by linarith⟩
      have heq : g =ᶠ[nhds x] (fun _ : ℝ => (0 : ℂ)) :=
        Filter.eventually_of_mem (Ioi_mem_nhds h2) fun y hy =>
          zero_outside hsupp (fun h => by linarith [h.2, Set.mem_Ioi.mp hy])
      rw [heq.deriv_eq, deriv_const]
  simp [eulerOp, hd0]

private theorem mellin_eq_interval {g : ℝ → ℂ} (hc : Continuous g)
    (hsupp : Function.support g ⊆ Set.Icc 1 2) (s : ℂ) :
    mellin g s = ∫ x in (1 : ℝ)..2, (x : ℂ) ^ (s - 1) * g x := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  funext x
  have hg1 : g 1 = 0 := vanish_one hc hsupp
  by_cases hIoc : x ∈ Set.Ioc (1 : ℝ) 2
  · have hIoi : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith [hIoc.1])
    rw [Set.indicator_of_mem hIoi, Set.indicator_of_mem hIoc]
  · rw [Set.indicator_of_notMem hIoc]
    by_cases hIoi : x ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hIoi]
      by_cases hx1 : x = 1
      · simp [hx1, hg1]
      · have hnot : x ∉ Set.Icc (1 : ℝ) 2 := fun h =>
          hIoc ⟨lt_of_le_of_ne h.1 (Ne.symm hx1), h.2⟩
        simp [zero_outside hsupp hnot]
    · rw [Set.indicator_of_notMem hIoi]

private theorem cpow_mul_integrable {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ z * u x) MeasureTheory.volume (1 : ℝ) 2 := by
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Set.uIcc (1 : ℝ) 2) := by
    by_cases hz : z = 0
    · subst hz
      simp only [Complex.cpow_zero]
      exact continuousOn_const
    · refine continuousOn_of_forall_continuousAt fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      exact (hasDerivAt_ofReal_cpow_const (by linarith [hx.1]) hz).continuousAt
  exact (hcont.mul hu.continuousOn).intervalIntegrable

private theorem mellin_ibp_norm {g : ℝ → ℂ} (hg : ∀ j : ℕ, ContDiff ℝ j g)
    (hsupp : Function.support g ⊆ Set.Icc 1 2) {s : ℂ} (hs : s ≠ 0) :
    ‖s‖ * ‖mellin g s‖ = ‖mellin (eulerOp g) s‖ := by
  have hc : Continuous g := (hg 0).continuous
  have hce : Continuous (eulerOp g) := ((eulerOp_smooth hg) 0).continuous
  let f1 := fun x : ℝ => (x : ℂ) ^ (s - 1) * g x
  let f2 := fun x : ℝ => (x : ℂ) ^ (s - 1) * eulerOp g x
  have hint1 : IntervalIntegrable f1 MeasureTheory.volume (1 : ℝ) 2 := cpow_mul_integrable hc (s - 1)
  have hint2 : IntervalIntegrable f2 MeasureTheory.volume (1 : ℝ) 2 := cpow_mul_integrable hce (s - 1)
  have h1 := hg 1
  rw [Nat.cast_one] at h1
  have hdiff : Differentiable ℝ g := (contDiff_one_iff_deriv.mp h1).1
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s * g y) (s * f1 x + f2 x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    have hd1 := hasDerivAt_ofReal_cpow_const hx0 hs
    have hd2 := (hdiff x).hasDerivAt
    have hpow : (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * (x : ℂ) := by
      calc
        (x : ℂ) ^ s = (x : ℂ) ^ ((s - 1) + 1) := by ring_nf
        _ = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := Complex.cpow_add (s - 1) 1 hxc
        _ = (x : ℂ) ^ (s - 1) * (x : ℂ) := by rw [Complex.cpow_one]
    convert hd1.mul hd2 using 1
    dsimp [f1, f2, eulerOp]
    rw [hpow]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((hint1.const_mul s).add hint2)
  rw [vanish_one hc hsupp, vanish_two hc hsupp, mul_zero, mul_zero, sub_self] at hftc
  rw [intervalIntegral.integral_add (hint1.const_mul s) hint2,
    intervalIntegral.integral_const_mul] at hftc
  have hm1 : mellin g s = ∫ x in (1 : ℝ)..2, f1 x := mellin_eq_interval hc hsupp s
  have hm2 : mellin (eulerOp g) s = ∫ x in (1 : ℝ)..2, f2 x :=
    mellin_eq_interval hce (eulerOp_support hsupp) s
  rw [← hm1, ← hm2] at hftc
  have heq : s * mellin g s = -mellin (eulerOp g) s := eq_neg_of_add_eq_zero_left hftc
  rw [← norm_mul, heq, norm_neg]

private def iterEuler : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, g => g
  | k + 1, g => iterEuler k (eulerOp g)

private theorem iterEuler_smooth (k : ℕ) {g : ℝ → ℂ} (hg : ∀ j : ℕ, ContDiff ℝ j g) :
    ∀ j : ℕ, ContDiff ℝ j (iterEuler k g) := by
  induction k generalizing g with
  | zero => exact hg
  | succ k ih => exact ih (eulerOp_smooth hg)

private theorem iterEuler_support (k : ℕ) {g : ℝ → ℂ} (hsupp : Function.support g ⊆ Set.Icc 1 2) :
    Function.support (iterEuler k g) ⊆ Set.Icc 1 2 := by
  induction k generalizing g with
  | zero => exact hsupp
  | succ k ih => exact ih (eulerOp_support hsupp)

private theorem iterEuler_mellin_norm (k : ℕ) {g : ℝ → ℂ} (hg : ∀ j : ℕ, ContDiff ℝ j g)
    (hsupp : Function.support g ⊆ Set.Icc 1 2) {s : ℂ} (hs : s ≠ 0) :
    ‖s‖ ^ k * ‖mellin g s‖ = ‖mellin (iterEuler k g) s‖ := by
  induction k generalizing g with
  | zero => simp [iterEuler]
  | succ k ih =>
    calc
      ‖s‖ ^ (k + 1) * ‖mellin g s‖ = ‖s‖ ^ k * (‖s‖ * ‖mellin g s‖) := by rw [pow_succ]; ring
      _ = ‖s‖ ^ k * ‖mellin (eulerOp g) s‖ := by rw [mellin_ibp_norm hg hsupp hs]
      _ = ‖mellin (iterEuler k (eulerOp g)) s‖ := ih (eulerOp_smooth hg) (eulerOp_support hsupp)
      _ = ‖mellin (iterEuler (k + 1) g) s‖ := rfl

private theorem mellin_window_decay (f : ℝ → ℂ) (hf : ∀ j : ℕ, ContDiff ℝ j f)
    (hsupp : Function.support f ⊆ Set.Icc 1 2) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖mellin f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ A := by
  let g := iterEuler A f
  have hg_smooth : ∀ j : ℕ, ContDiff ℝ j g := iterEuler_smooth A hf
  have hg_supp : Function.support g ⊆ Set.Icc 1 2 := iterEuler_support A hsupp
  have hc : Continuous g := (hg_smooth 0).continuous
  have hne : (Set.Icc (1 : ℝ) 2).Nonempty := ⟨1, by norm_num⟩
  obtain ⟨x₀, _, hx₀⟩ := isCompact_Icc.exists_isMaxOn hne hc.norm.continuousOn
  let M : ℝ := max 1 ‖g x₀‖
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖g x₀‖)
  let C : ℝ := (3 : ℝ) ^ A * M
  refine ⟨C, by positivity, ?_⟩
  intro t
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs_re
    norm_num at hs_re
  have hre := Complex.abs_re_le_norm s
  have him := Complex.abs_im_le_norm s
  rw [hs_re, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hre
  rw [hs_im] at him
  have h1t : 1 + |t| ≤ 3 * ‖s‖ := by linarith
  have hm_bound : ‖mellin g s‖ ≤ M := by
    rw [mellin_eq_interval hc hg_supp s]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := 2) (C := M)
      (f := fun x : ℝ => (x : ℂ) ^ (s - 1) * g x) fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
        have hx_pos : 0 < x := by linarith [hx.1]
        have hx_Icc : x ∈ Set.Icc (1 : ℝ) 2 := ⟨hx.1.le, hx.2⟩
        have hgx : ‖g x‖ ≤ M := (isMaxOn_iff.mp hx₀ x hx_Icc).trans (le_max_right 1 ‖g x₀‖)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        have hexp : (s - 1).re ≤ 0 := by simp [hs_re]; norm_num
        have hrpow : x ^ (s - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1.le hexp
        calc
          x ^ (s - 1).re * ‖g x‖ ≤ 1 * M :=
            mul_le_mul hrpow hgx (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    have habs : |(2 : ℝ) - 1| = 1 := by norm_num
    rw [habs, mul_one] at hb
    exact hb
  have hpow : (1 + |t|) ^ A ≤ (3 : ℝ) ^ A * ‖s‖ ^ A := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1t A
  have hpos_t : 0 < (1 + |t|) ^ A := by positivity
  rw [le_div_iff₀ hpos_t, mul_comm]
  calc
    (1 + |t|) ^ A * ‖mellin f s‖
      ≤ ((3 : ℝ) ^ A * ‖s‖ ^ A) * ‖mellin f s‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (3 : ℝ) ^ A * (‖s‖ ^ A * ‖mellin f s‖) := by ring
    _ = (3 : ℝ) ^ A * ‖mellin g s‖ := by rw [iterEuler_mellin_norm A hf hsupp hs0]
    _ ≤ (3 : ℝ) ^ A * M := mul_le_mul_of_nonneg_left hm_bound (by positivity)
    _ = C := rfl

end

end PEqualNP.Outside.MellinWindowDecayAux

theorem PEqualNP.Outside.L_quadratic_primes_levent_mellin_window_decay :
    ∀ f : ℝ → ℂ, (∀ j : ℕ, ContDiff ℝ j f) → Function.support f ⊆ Set.Icc 1 2 → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∀ t : ℝ, ‖mellin f ((1/2 : ℂ) + (t : ℂ)*Complex.I)‖ ≤ C/(1+|t|)^A :=
  PEqualNP.Outside.MellinWindowDecayAux.mellin_window_decay
