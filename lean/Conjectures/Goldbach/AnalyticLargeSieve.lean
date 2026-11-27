import Mathlib

open MeasureTheory

namespace Conjectures.Goldbach.AnalyticLargeSieve_aux

noncomputable def Ex (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma Ex_add (x y : ℝ) : Ex (x + y) = Ex x * Ex y := by
  unfold Ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma Ex_int (m : ℤ) : Ex (m : ℝ) = 1 := by
  unfold Ex
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    ring
  rw [h, h2, Complex.exp_int_mul_two_pi_mul_I]

lemma Ex_conj (x : ℝ) : (starRingEnd ℂ) (Ex x) = Ex (-x) := by
  unfold Ex
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma norm_Ex (x : ℝ) : ‖Ex x‖ = 1 := by
  unfold Ex
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_Ex : Continuous Ex := by
  unfold Ex
  fun_prop

lemma orth (m : ℤ) (a : ℝ) :
    ∫ t in a..(a + 1), Ex ((m : ℝ) * t) = if m = 0 then 1 else 0 := by
  have hrewrite : (∫ t in a..(a + 1), Ex ((m : ℝ) * t)) =
      ∫ t in a..(a + 1), Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    unfold Ex
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
    rw [integral_exp_mul_complex hc]
    have hval : Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      have h := Ex_int m
      unfold Ex at h
      exact h
    have hexp : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (a : ℂ)) := by
      have hcast : ((a + 1 : ℝ) : ℂ) = (a : ℂ) + 1 := by
        push_cast
        ring
      rw [hcast, mul_add, Complex.exp_add, mul_one, hval, mul_one]
    rw [hexp, sub_self, zero_div]
    simp [hm]

lemma parseval (s : Finset ℕ) (z : ℕ → ℂ) (a : ℝ) :
    ∫ t in a..(a + 1), ‖∑ k ∈ s, z k * Ex ((k : ℝ) * t)‖ ^ 2 = ∑ k ∈ s, ‖z k‖ ^ 2 := by
  classical
  set S : ℝ → ℂ := fun t => ∑ k ∈ s, z k * Ex ((k : ℝ) * t) with hSdef
  set W : ℝ → ℂ := fun t => ∑ k ∈ s, ∑ j ∈ s,
    ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t) with hWdef
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = W t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [hSdef, hWdef]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Ex_conj]
    have hmul : Ex (-((k : ℝ) * t)) * Ex ((j : ℝ) * t) = Ex (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← Ex_add]
      congr 1
      ring
    calc
      ((starRingEnd ℂ) (z k) * Ex (-((k : ℝ) * t))) * (z j * Ex ((j : ℝ) * t)) =
          ((starRingEnd ℂ) (z k) * z j) * (Ex (-((k : ℝ) * t)) * Ex ((j : ℝ) * t)) := by ring
      _ = ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t) := by rw [hmul]
  have hint_single : ∀ (c : ℂ) (b : ℝ),
      IntervalIntegrable (fun t : ℝ => c * Ex (b * t)) volume a (a + 1) := by
    intro c b
    exact (continuous_const.mul (continuous_Ex.comp (by fun_prop))).intervalIntegrable _ _
  have hint_W : IntervalIntegrable W volume a (a + 1) := by
    simp only [hWdef]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (continuous_Ex.comp (by fun_prop))))).intervalIntegrable _ _
  have hmain : (∫ t in a..(a + 1), W t) = ((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hWdef]
    have houter (k : ℕ) (hk : k ∈ s) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) volume a (a + 1) := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (continuous_Ex.comp (by fun_prop)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ s, (∫ t in a..(a + 1), ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) = ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      have hii : ∀ j ∈ s, IntervalIntegrable
          (fun t : ℝ => ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t))
          volume a (a + 1) := fun j hj => hint_single _ _
      rw [intervalIntegral.integral_finsetSum hii]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      have ho : (∫ t in a..(a + 1), Ex (((j : ℝ) - (k : ℝ)) * t))
          = (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
        rw [hm]
        exact orth _ a
      rw [ho]
    calc
      (∑ k ∈ s, ∫ t in a..(a + 1), ∑ j ∈ s,
          ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) =
          ∑ k ∈ s, ∑ j ∈ s, ((starRingEnd ℂ) (z k) * z j) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ∑ k ∈ s, (starRingEnd ℂ) (z k) * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hdiag : ∀ j ∈ s, ((starRingEnd ℂ) (z k) * z j) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) =
            (if j = k then (starRingEnd ℂ) (z k) * z j else 0) := by
          intro j hj
          by_cases hjk : j = k
          · subst hjk
            simp
          · have hne : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
              intro hz
              exact hjk (by omega)
            simp [hne, hjk]
        rw [Finset.sum_congr rfl hdiag,
          Finset.sum_eq_single k (fun b hb hbk => by simp [hbk]) (fun hk' => absurd hk hk')]
        simp
      _ = ((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro k hk
        have hz : (starRingEnd ℂ) (z k) * z k = ((‖z k‖ ^ 2 : ℝ) : ℂ) := by
          have h := Complex.normSq_eq_conj_mul_self (z := z k)
          rw [Complex.normSq_eq_norm_sq] at h
          exact h.symm
        rw [hz]
        push_cast
        ring
  have hre : (∫ t in a..(a + 1), (W t).re) = (∫ t in a..(a + 1), W t).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show a ≤ a + 1 by linarith, ite_true, one_smul]
    exact integral_re hint_W.def'
  calc
    (∫ t in a..(a + 1), ‖S t‖ ^ 2) = ∫ t in a..(a + 1), (W t).re := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (∫ t in a..(a + 1), W t).re := hre
    _ = ∑ k ∈ s, ‖z k‖ ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

lemma hasDerivAt_Ex (lam t : ℝ) :
    HasDerivAt (fun s : ℝ => Ex (lam * s))
      (Ex (lam * t) * (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I)) t := by
  have hreal : HasDerivAt (fun s : ℝ => 2 * Real.pi * (lam * s)) (2 * Real.pi * lam) t := by
    have h1 : HasDerivAt (fun s : ℝ => lam * s) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    have h2 : HasDerivAt (fun s : ℝ => Real.pi * (lam * s)) (Real.pi * lam) t := by
      simpa using h1.const_mul Real.pi
    simpa [mul_assoc] using h2.const_mul 2
  have h1 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * (lam * s) : ℝ) : ℂ))
      ((2 * Real.pi * lam : ℝ) : ℂ) t := hreal.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * (lam * s) : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I) t := h1.mul_const Complex.I
  have h3 := h2.cexp
  simpa only [Ex] using h3

lemma sum_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {G : Type*}
    [AddCommMonoid G] (f : α → β) (g : β → G) :
    ∀ (A : Finset α), Set.InjOn f ↑A → (∑ a ∈ A, g (f a)) = ∑ b ∈ A.image f, g b := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | insert a A' ha ih =>
    intro hf
    have hne : f a ∉ A'.image f := by
      intro hmem
      obtain ⟨b, hbA, hbeq⟩ := Finset.mem_image.mp hmem
      have hba : b = a :=
        hf (Finset.mem_insert_of_mem hbA) (Finset.mem_insert_self a A') hbeq
      exact ha (hba ▸ hbA)
    have hf' : Set.InjOn f ↑A' :=
      hf.mono (fun x hx => Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.image_insert, Finset.sum_insert hne, ih hf']

lemma gallagher_midpoint {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hcont : Continuous f') (x r : ℝ) (hr : 0 < r) :
    ‖f x‖ ^ 2 ≤ (1 / (2 * r)) * (∫ t in (x - r)..(x + r), ‖f t‖ ^ 2)
      + ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
  let g : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let gd : ℝ → ℝ := fun t => 2 * inner ℝ (f t) (f' t)
  have hg : ∀ t, HasDerivAt g (gd t) t := by
    intro t
    simpa [g, gd] using (hf t).norm_sq
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hgc : Continuous g := by
    change Continuous (fun t : ℝ => ‖f t‖ ^ 2)
    exact (continuous_norm.comp hfc).pow 2
  have hgdc : Continuous gd := by
    change Continuous (fun t : ℝ => (2 : ℝ) * inner ℝ (f t) (f' t))
    exact continuous_const.mul (hfc.inner hcont)
  have hleftWeightC : Continuous (fun t => (t - (x - r)) * gd t) :=
    (continuous_id.sub continuous_const).mul hgdc
  have hrightWeightC : Continuous (fun t => ((x + r) - t) * gd t) :=
    (continuous_const.sub continuous_id).mul hgdc
  have hprodC : Continuous (fun t => ‖f t‖ * ‖f' t‖) :=
    (continuous_norm.comp hfc).mul (continuous_norm.comp hcont)
  have h2prodC : Continuous (fun t : ℝ => (2 : ℝ) * (‖f t‖ * ‖f' t‖)) :=
    continuous_const.mul hprodC
  have hab : x - r ≤ x := by linarith
  have hbc : x ≤ x + r := by linarith
  have hFleft : ∀ t, HasDerivAt (fun t => (t - (x - r)) * g t)
      (g t + (t - (x - r)) * gd t) t := by
    intro t
    convert ((hasDerivAt_id t).sub_const (x - r)).mul (hg t) using 1
    · funext s
      simp
    · simp
  have hFright : ∀ t, HasDerivAt (fun t => ((x + r) - t) * g t)
      (-g t + ((x + r) - t) * gd t) t := by
    intro t
    convert ((hasDerivAt_id t).const_sub (x + r)).mul (hg t) using 1
    · funext s
      simp
    · simp
  have hleftDerivC : Continuous (fun t => g t + (t - (x - r)) * gd t) :=
    hgc.add hleftWeightC
  have hrightDerivC : Continuous (fun t => -g t + ((x + r) - t) * gd t) :=
    hgc.neg.add hrightWeightC
  have h1 : (∫ t in (x - r)..x, g t + (t - (x - r)) * gd t) = r * g x := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hFleft t)
      (hleftDerivC.intervalIntegrable (x - r) x) using 1
    ring
  have h2 : (∫ t in x..(x + r), -g t + ((x + r) - t) * gd t) = -(r * g x) := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hFright t)
      (hrightDerivC.intervalIntegrable x (x + r)) using 1
    ring
  have h1split :
      (∫ t in (x - r)..x, g t + (t - (x - r)) * gd t) =
        (∫ t in (x - r)..x, g t) +
          ∫ t in (x - r)..x, (t - (x - r)) * gd t :=
    intervalIntegral.integral_add
      (hgc.intervalIntegrable (x - r) x)
      (hleftWeightC.intervalIntegrable (x - r) x)
  have h2split :
      (∫ t in x..(x + r), -g t + ((x + r) - t) * gd t) =
        -(∫ t in x..(x + r), g t) +
          ∫ t in x..(x + r), ((x + r) - t) * gd t := by
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
      intervalIntegral.integral_add
        (hgc.neg.intervalIntegrable x (x + r))
        (hrightWeightC.intervalIntegrable x (x + r))
  rw [h1split] at h1
  rw [h2split] at h2
  have hleft_point : ∀ t ∈ Set.Icc (x - r) x,
      |(t - (x - r)) * gd t| ≤ r * |gd t| := by
    intro t ht
    have ht0 : 0 ≤ t - (x - r) := by linarith [ht.1]
    have htr : t - (x - r) ≤ r := by linarith [ht.2]
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right htr (abs_nonneg _)
  have hright_point : ∀ t ∈ Set.Icc x (x + r),
      |((x + r) - t) * gd t| ≤ r * |gd t| := by
    intro t ht
    have ht0 : 0 ≤ (x + r) - t := by linarith [ht.2]
    have htr : (x + r) - t ≤ r := by linarith [ht.1]
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right htr (abs_nonneg _)
  have hrGdAbsC : Continuous (fun t => r * |gd t|) :=
    continuous_const.mul hgdc.abs
  have hleft_bound :
      |∫ t in (x - r)..x, (t - (x - r)) * gd t| ≤
        r * ∫ t in (x - r)..x, |gd t| := by
    calc
      |∫ t in (x - r)..x, (t - (x - r)) * gd t| ≤
          ∫ t in (x - r)..x, |(t - (x - r)) * gd t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in (x - r)..x, r * |gd t| :=
        intervalIntegral.integral_mono_on hab
          (hleftWeightC.abs.intervalIntegrable (x - r) x)
          (hrGdAbsC.intervalIntegrable (x - r) x) hleft_point
      _ = r * ∫ t in (x - r)..x, |gd t| :=
        intervalIntegral.integral_const_mul r (fun t => |gd t|)
  have hright_bound :
      |∫ t in x..(x + r), ((x + r) - t) * gd t| ≤
        r * ∫ t in x..(x + r), |gd t| := by
    calc
      |∫ t in x..(x + r), ((x + r) - t) * gd t| ≤
          ∫ t in x..(x + r), |((x + r) - t) * gd t| :=
        intervalIntegral.abs_integral_le_integral_abs hbc
      _ ≤ ∫ t in x..(x + r), r * |gd t| :=
        intervalIntegral.integral_mono_on hbc
          (hrightWeightC.abs.intervalIntegrable x (x + r))
          (hrGdAbsC.intervalIntegrable x (x + r)) hright_point
      _ = r * ∫ t in x..(x + r), |gd t| :=
        intervalIntegral.integral_const_mul r (fun t => |gd t|)
  have hgd_bound : ∀ t, |gd t| ≤ 2 * (‖f t‖ * ‖f' t‖) := by
    intro t
    dsimp [gd]
    calc
      |2 * inner ℝ (f t) (f' t)| = 2 * |inner ℝ (f t) (f' t)| := by
        rw [abs_mul]; norm_num
      _ ≤ 2 * (‖f t‖ * ‖f' t‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  have hJleft :
      (∫ t in (x - r)..x, |gd t|) ≤
        2 * ∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖ := by
    calc
      (∫ t in (x - r)..x, |gd t|) ≤
          ∫ t in (x - r)..x, 2 * (‖f t‖ * ‖f' t‖) :=
        intervalIntegral.integral_mono hab
          (hgdc.abs.intervalIntegrable (x - r) x)
          (h2prodC.intervalIntegrable (x - r) x)
          (fun t => hgd_bound t)
      _ = 2 * ∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖ :=
        intervalIntegral.integral_const_mul 2 (fun t => ‖f t‖ * ‖f' t‖)
  have hJright :
      (∫ t in x..(x + r), |gd t|) ≤
        2 * ∫ t in x..(x + r), ‖f t‖ * ‖f' t‖ := by
    calc
      (∫ t in x..(x + r), |gd t|) ≤
          ∫ t in x..(x + r), 2 * (‖f t‖ * ‖f' t‖) :=
        intervalIntegral.integral_mono hbc
          (hgdc.abs.intervalIntegrable x (x + r))
          (h2prodC.intervalIntegrable x (x + r))
          (fun t => hgd_bound t)
      _ = 2 * ∫ t in x..(x + r), ‖f t‖ * ‖f' t‖ :=
        intervalIntegral.integral_const_mul 2 (fun t => ‖f t‖ * ‖f' t‖)
  have hleft_main :
      r * g x ≤ (∫ t in (x - r)..x, g t) +
        r * ∫ t in (x - r)..x, |gd t| := by
    have hupper : (∫ t in (x - r)..x, (t - (x - r)) * gd t) ≤
        r * ∫ t in (x - r)..x, |gd t| := (le_abs_self _).trans hleft_bound
    linarith
  have hright_main :
      r * g x ≤ (∫ t in x..(x + r), g t) +
        r * ∫ t in x..(x + r), |gd t| := by
    have hneg := neg_le_of_abs_le hright_bound
    linarith
  have hGadj :
      (∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t) =
        ∫ t in (x - r)..(x + r), g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (x - r) x)
      (hgc.intervalIntegrable x (x + r))
  have hJadj :
      (∫ t in (x - r)..x, |gd t|) + (∫ t in x..(x + r), |gd t|) =
        ∫ t in (x - r)..(x + r), |gd t| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hgdc.abs.intervalIntegrable (x - r) x)
      (hgdc.abs.intervalIntegrable x (x + r))
  have hHadj :
      (∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖) +
          (∫ t in x..(x + r), ‖f t‖ * ‖f' t‖) =
        ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hprodC.intervalIntegrable (x - r) x)
      (hprodC.intervalIntegrable x (x + r))
  have hsum :
      2 * r * g x ≤
        ((∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t)) +
          ((r * ∫ t in (x - r)..x, |gd t|) +
            r * ∫ t in x..(x + r), |gd t|) := by
    linarith
  have hJtotal :
      (∫ t in (x - r)..(x + r), |gd t|) ≤
        2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    rw [← hJadj, ← hHadj]
    linarith
  have hJmul :
      r * (∫ t in (x - r)..(x + r), |gd t|) ≤
        r * (2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) :=
    mul_le_mul_of_nonneg_left hJtotal (le_of_lt hr)
  have hmain :
      2 * r * g x ≤ (∫ t in (x - r)..(x + r), g t) +
        2 * r * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    calc
      2 * r * g x ≤
          ((∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t)) +
            ((r * ∫ t in (x - r)..x, |gd t|) +
              r * ∫ t in x..(x + r), |gd t|) := hsum
      _ = (∫ t in (x - r)..(x + r), g t) +
          r * ((∫ t in (x - r)..x, |gd t|) +
            ∫ t in x..(x + r), |gd t|) := by
        rw [hGadj]
        ring
      _ = (∫ t in (x - r)..(x + r), g t) +
          r * (∫ t in (x - r)..(x + r), |gd t|) := by rw [hJadj]
      _ ≤ (∫ t in (x - r)..(x + r), g t) +
          r * (2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) :=
        by linarith
      _ = (∫ t in (x - r)..(x + r), g t) +
          2 * r * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by ring
  have hden : 0 < 2 * r := mul_pos (by norm_num) hr
  have hsub :
      2 * r * (g x - ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) ≤
        ∫ t in (x - r)..(x + r), g t := by
    nlinarith
  have hquot :
      g x - ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ ≤
        (∫ t in (x - r)..(x + r), g t) / (2 * r) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hsub)
  have hfinish :
      g x ≤ (∫ t in (x - r)..(x + r), g t) / (2 * r) +
        ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    linarith
  simpa [g, div_eq_mul_inv, one_div, mul_comm] using hfinish

lemma sum_windows_le (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    (δ : ℝ) (_hδ : 0 < δ) :
    ∀ (X : Finset ℝ) (α β : ℝ),
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → δ ≤ |u - v|) →
      (∀ u ∈ X, α + δ / 2 ≤ u ∧ u ≤ β - δ / 2) →
      α ≤ β →
      (∑ u ∈ X, ∫ t in (u - δ / 2)..(u + δ / 2), F t) ≤ ∫ t in α..β, F t := by
  classical
  intro X
  induction X using Finset.induction_on_max with
  | empty =>
      intro α β _ _ hαβ
      simpa using intervalIntegral.integral_nonneg hαβ (fun u _ => hF0 u)
  | insert a s hlt ih =>
      intro α β hsep hbd _hαβ
      have ha : a ∉ s := fun ha => lt_irrefl a (hlt a ha)
      have hmem : ∀ u ∈ s, u ∈ insert a s := fun u hu => Finset.mem_insert_of_mem hu
      have hle : ∀ u ∈ s, u ≤ a - δ := by
        intro u hu
        have h1 : δ ≤ |u - a| :=
          hsep u (hmem u hu) a (Finset.mem_insert_self a s) (ne_of_lt (hlt u hu))
        have h2 : u - a ≤ 0 := by linarith [hlt u hu]
        rw [abs_of_nonpos h2] at h1
        linarith
      have ih' : (∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          ≤ ∫ t in α..(a - δ / 2), F t :=
        ih α (a - δ / 2)
          (fun u hu v hv huv => hsep u (hmem u hu) v (hmem v hv) huv)
          (fun u hu => ⟨(hbd u (hmem u hu)).1, by have := hle u hu; linarith⟩)
          (by have := (hbd a (Finset.mem_insert_self a s)).1; linarith)
      have hsum : (∑ u ∈ insert a s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          = (∫ t in (a - δ / 2)..(a + δ / 2), F t)
            + ∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t := Finset.sum_insert ha
      have hadd : (∫ t in α..(a - δ / 2), F t) + (∫ t in (a - δ / 2)..(a + δ / 2), F t)
          = ∫ t in α..(a + δ / 2), F t :=
        intervalIntegral.integral_add_adjacent_intervals
          (hF.intervalIntegrable α (a - δ / 2)) (hF.intervalIntegrable (a - δ / 2) (a + δ / 2))
      have hfin : ∫ t in α..(a + δ / 2), F t ≤ ∫ t in α..β, F t := by
        have hb : a + δ / 2 ≤ β := by
          have := (hbd a (Finset.mem_insert_self a s)).2; linarith
        have h2 : (∫ t in α..(a + δ / 2), F t) + (∫ t in (a + δ / 2)..β, F t)
            = ∫ t in α..β, F t :=
          intervalIntegral.integral_add_adjacent_intervals
            (hF.intervalIntegrable α (a + δ / 2)) (hF.intervalIntegrable (a + δ / 2) β)
        have h3 : 0 ≤ ∫ t in (a + δ / 2)..β, F t :=
          intervalIntegral.integral_nonneg hb (fun u _ => hF0 u)
        linarith
      calc (∑ u ∈ insert a s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          = (∫ t in (a - δ / 2)..(a + δ / 2), F t)
              + ∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t := hsum
        _ ≤ (∫ t in (a - δ / 2)..(a + δ / 2), F t) + ∫ t in α..(a - δ / 2), F t :=
            by linarith [ih']
        _ = (∫ t in α..(a - δ / 2), F t) + (∫ t in (a - δ / 2)..(a + δ / 2), F t) := by ring
        _ = ∫ t in α..(a + δ / 2), F t := hadd
        _ ≤ ∫ t in α..β, F t := hfin

lemma frac_sep (Q q r a b : ℕ) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hca : Nat.Coprime a q) (hcb : Nat.Coprime b r) (hne : q ≠ r ∨ a ≠ b) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hcross_ne : a * r ≠ b * q := by
    intro hcross
    have hqr : q ∣ a * r := by
      rw [hcross]
      exact dvd_mul_left q b
    have hrq : r ∣ b * q := by
      rw [← hcross]
      exact dvd_mul_left r a
    have hqdr : q ∣ r := hca.symm.dvd_of_dvd_mul_left hqr
    have hrdq : r ∣ q := hcb.symm.dvd_of_dvd_mul_left hrq
    have hqreq : q = r := Nat.dvd_antisymm hqdr hrdq
    have hab : a = b := by
      apply Nat.mul_right_cancel (show 0 < r by omega)
      calc
        a * r = b * q := hcross
        _ = b * r := by rw [hqreq]
    rcases hne with hqne | hane
    · exact hqne hqreq
    · exact hane hab
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hcross : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
    rcases lt_or_gt_of_ne hcross_ne with h | h
    · have hstep : (a : ℝ) * r + 1 ≤ (b : ℝ) * q := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (neg_le_abs _)
    · have hstep : (b : ℝ) * q + 1 ≤ (a : ℝ) * r := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (le_abs_self _)
  have hquot : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by
    field_simp
  have hsep : (1 : ℝ) / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
    rw [hquot, abs_div, abs_of_pos (mul_pos hqR hrR)]
    exact div_le_div_of_nonneg_right hcross (mul_pos hqR hrR).le
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    calc
      (q : ℝ) * r ≤ (Q : ℝ) * Q := by exact_mod_cast Nat.mul_le_mul hqQ hrQ
      _ = (Q : ℝ) ^ 2 := by ring
  exact (one_div_le_one_div_of_le (mul_pos hqR hrR) hden).trans hsep

lemma frac_inj (q r a b : ℕ) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (ha : a < q) (hb : b < r)
    (hca : Nat.Coprime a q) (hcb : Nat.Coprime b r)
    (heq : (a : ℝ) / q = (b : ℝ) / r) : q = r ∧ a = b := by
  have hqfacts : 0 < q ∧ 1 ≤ q := ⟨Nat.zero_lt_of_lt ha, hq1⟩
  have hrfacts : 0 < r ∧ 1 ≤ r := ⟨Nat.zero_lt_of_lt hb, hr1⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqfacts.1.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hrfacts.1.ne'
  have hcross : a * r = b * q := by
    field_simp [hqR, hrR] at heq
    have hcross' : a * r = q * b := by exact_mod_cast heq
    simpa [Nat.mul_comm] using hcross'
  have hqr : q ∣ a * r := by
    rw [hcross]
    exact dvd_mul_left q b
  have hrq : r ∣ b * q := by
    rw [← hcross]
    exact dvd_mul_left r a
  have hqdr : q ∣ r := hca.symm.dvd_of_dvd_mul_left hqr
  have hrdq : r ∣ q := hcb.symm.dvd_of_dvd_mul_left hrq
  have hqreq : q = r := Nat.dvd_antisymm hqdr hrdq
  have hab : a = b := by
    apply Nat.mul_right_cancel (show 0 < r by omega)
    calc
      a * r = b * q := hcross
      _ = b * r := by rw [hqreq]
  exact ⟨hqreq, hab⟩

lemma frac_bounds (Q q a : ℕ) (hQ : 1 ≤ Q) (hq1 : 1 ≤ q) (hqQ : q ≤ Q) (ha : a < q) :
    (0 : ℝ) ≤ (a : ℝ) / q ∧ (a : ℝ) / q ≤ 1 - 1 / (Q : ℝ) ^ 2 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have haR : (a : ℝ) + 1 ≤ q := by
    exact_mod_cast Nat.succ_le_of_lt ha
  have hfrac : (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := by
    calc
      (a : ℝ) / q ≤ ((q : ℝ) - 1) / q :=
        div_le_div_of_nonneg_right (by linarith) hqR.le
      _ = (q : ℝ) / q - 1 / (q : ℝ) := by ring
      _ = 1 - 1 / (q : ℝ) := by rw [div_self hqR.ne']
  have hinvQ_le_one : 1 / (Q : ℝ) ≤ 1 := div_le_self zero_le_one hQone
  have hinvQ_sq : 1 / (Q : ℝ) ^ 2 ≤ 1 / (Q : ℝ) := by
    calc
      1 / (Q : ℝ) ^ 2 = (1 / (Q : ℝ)) * (1 / (Q : ℝ)) := by ring
      _ ≤ 1 / (Q : ℝ) :=
        mul_le_of_le_one_right (one_div_nonneg.mpr hQR.le) hinvQ_le_one
  have hinvQq : 1 / (Q : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqR hqQ'
  have hsmall : 1 / (Q : ℝ) ^ 2 ≤ 1 / (q : ℝ) := hinvQ_sq.trans hinvQq
  constructor
  · exact div_nonneg (Nat.cast_nonneg a) hqR.le
  · calc
      (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := hfrac
      _ ≤ 1 - 1 / (Q : ℝ) ^ 2 := by linarith

theorem large_sieve (M N Q : ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖(∑ k ∈ Finset.Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / q)))‖ ^ 2)
      ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    have h1 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [h1, Finset.sum_empty]
    refine mul_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg Real.pi_pos.le (Nat.cast_nonneg N)
    · positivity
    · exact Finset.sum_nonneg (fun k hk => sq_nonneg _)
  by_cases hN : N = 0
  · subst hN
    have h1 : Finset.Ico M (M + 0) = (∅ : Finset ℕ) := by
      rw [Nat.add_zero, Finset.Ico_self]
    simp
  have hQ1 : 1 ≤ Q := by omega
  have hN1 : 1 ≤ N := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQ0 : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  set s : Finset ℕ := Finset.Ico M (M + N) with hs
  set L : ℝ := (M : ℝ) + (N : ℝ) / 2 with hL
  set δ : ℝ := 1 / (Q : ℝ) ^ 2 with hδ
  have hδpos : (0 : ℝ) < δ := by
    simp only [hδ]
    positivity
  set S : ℝ → ℂ := fun t => ∑ k ∈ s, c k * Ex ((k : ℝ) * t) with hSdef
  set T : ℝ → ℂ := fun t => Ex (-(L * t)) * S t with hTdef
  set V : ℝ → ℂ := fun t => ∑ k ∈ s,
    ((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k) * Ex ((k : ℝ) * t) with hVdef
  set Td : ℝ → ℂ := fun t => Ex (-(L * t)) * V t with hTddef
  have hTS : ∀ t, ‖T t‖ = ‖S t‖ := by
    intro t
    rw [hTdef, norm_mul, norm_Ex, one_mul]
  have hTdV : ∀ t, ‖Td t‖ = ‖V t‖ := by
    intro t
    rw [hTddef, norm_mul, norm_Ex, one_mul]
  have hmulwin : ∀ (k : ℕ) (t : ℝ),
      Ex (-(L * t)) * Ex ((k : ℝ) * t) = Ex (((k : ℝ) - L) * t) := by
    intro k t
    rw [← Ex_add]
    congr 1
    ring
  have hTsum : ∀ t, T t = ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * t) := by
    intro t
    simp only [hTdef, hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc Ex (-(L * t)) * (c k * Ex ((k : ℝ) * t))
        = c k * (Ex (-(L * t)) * Ex ((k : ℝ) * t)) := by ring
      _ = c k * Ex (((k : ℝ) - L) * t) := by rw [hmulwin k t]
  have hderivT : ∀ t, HasDerivAt T (Td t) t := by
    intro t
    have hpiece : ∀ k ∈ s, HasDerivAt
        (fun u : ℝ => c k * Ex (((k : ℝ) - L) * u))
        (c k * (Ex (((k : ℝ) - L) * t) *
          (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t :=
      fun k hk => (hasDerivAt_Ex ((k : ℝ) - L) t).const_mul (c k)
    have h1 : HasDerivAt (fun u : ℝ => ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * u))
        (∑ k ∈ s, c k * (Ex (((k : ℝ) - L) * t) *
          (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t := by
      have key : ∀ (u : Finset ℕ),
          HasDerivAt (fun v : ℝ => ∑ k ∈ u, c k * Ex (((k : ℝ) - L) * v))
            (∑ k ∈ u, c k * (Ex (((k : ℝ) - L) * t) *
              (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t := by
        intro u
        induction u using Finset.induction_on with
        | empty => simpa using (hasDerivAt_const t (0 : ℂ))
        | insert a u' ha ih =>
            have hA : HasDerivAt (fun v : ℝ => c a * Ex (((a : ℝ) - L) * v))
                (c a * (Ex (((a : ℝ) - L) * t) *
                  (((2 * Real.pi * ((a : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t :=
              (hasDerivAt_Ex ((a : ℝ) - L) t).const_mul (c a)
            have hsum := hA.add ih
            have hfun : ((fun v : ℝ => c a * Ex (((a : ℝ) - L) * v))
                  + fun v : ℝ => ∑ k ∈ u', c k * Ex (((k : ℝ) - L) * v))
                = (fun v : ℝ => ∑ k ∈ insert a u', c k * Ex (((k : ℝ) - L) * v)) := by
              funext v
              rw [Finset.sum_insert ha]
              simp
            have hder : (c a * (Ex (((a : ℝ) - L) * t) *
                  (((2 * Real.pi * ((a : ℝ) - L) : ℝ) : ℂ) * Complex.I)))
                + (∑ k ∈ u', c k * (Ex (((k : ℝ) - L) * t) *
                  (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I)))
                = ∑ k ∈ insert a u', c k * (Ex (((k : ℝ) - L) * t) *
                  (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I)) := by
              rw [Finset.sum_insert ha]
            rw [hfun] at hsum
            rw [hder] at hsum
            exact hsum
      exact key s
    have h3 : (fun u : ℝ => ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * u)) = T := by
      funext u
      exact (hTsum u).symm
    rw [h3] at h1
    have h4 : (∑ k ∈ s, c k * (Ex (((k : ℝ) - L) * t) *
        (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) = Td t := by
      simp only [hTddef, hVdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc c k * (Ex (((k : ℝ) - L) * t) *
            (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))
          = (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k *
              (Ex (-(L * t)) * Ex ((k : ℝ) * t)) := by rw [hmulwin k t]; ring
        _ = Ex (-(L * t)) * (((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k) *
            Ex ((k : ℝ) * t)) := by ring
    rw [h4] at h1
    exact h1
  have hcontT : Continuous T :=
    continuous_iff_continuousAt.mpr (fun t => (hderivT t).continuousAt)
  have hcontTd : Continuous Td := by
    simp only [hTddef]
    refine (continuous_Ex.comp (by fun_prop)).mul ?_
    simp only [hVdef]
    exact continuous_finsetSum _ (fun k _ =>
      continuous_const.mul (continuous_Ex.comp (by fun_prop)))
  have hab : -(δ / 2) ≤ 1 - δ / 2 := by linarith
  have hpar1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2) = ∑ k ∈ s, ‖c k‖ ^ 2 := by
    have h1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
        = ∫ t in (-(δ / 2))..(1 - δ / 2), ‖S t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hTS t]
    rw [h1]
    have h2 : (1 - δ / 2) = (-(δ / 2)) + 1 := by ring
    rw [h2]
    simpa only [hSdef] using (parseval s c (-(δ / 2)))
  have hpar2 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2)
      = ∑ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2 := by
    have h1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2)
        = ∫ t in (-(δ / 2))..(1 - δ / 2), ‖V t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hTdV t]
    rw [h1]
    have h2 : (1 - δ / 2) = (-(δ / 2)) + 1 := by ring
    rw [h2]
    simpa only [hVdef] using
      (parseval s (fun k => ((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k))
        (-(δ / 2)))
  have hcoef : ∀ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2
      ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖c k‖ ^ 2 := by
    intro k hk
    have hk1 : M ≤ k := (Finset.mem_Ico.mp (hs ▸ hk)).1
    have hk2 : k < M + N := (Finset.mem_Ico.mp (hs ▸ hk)).2
    have hk1' : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hk2' : (k : ℝ) < (M : ℝ) + (N : ℝ) := by exact_mod_cast hk2
    have hkl : |(k : ℝ) - L| ≤ (N : ℝ) / 2 := by
      rw [abs_le]
      simp only [hL]
      constructor <;> linarith
    have hsq : ((k : ℝ) - L) ^ 2 ≤ ((N : ℝ) / 2) ^ 2 := by
      nlinarith [abs_nonneg ((k : ℝ) - L)]
    have hpi : (2 * Real.pi * ((k : ℝ) - L)) ^ 2 ≤ (Real.pi * (N : ℝ)) ^ 2 := by
      have h4 : 4 * Real.pi ^ 2 * ((k : ℝ) - L) ^ 2 ≤ 4 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      calc (2 * Real.pi * ((k : ℝ) - L)) ^ 2 = 4 * Real.pi ^ 2 * ((k : ℝ) - L) ^ 2 := by ring
        _ ≤ 4 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 := h4
        _ = (Real.pi * (N : ℝ)) ^ 2 := by ring
    have hI : ‖(Complex.I : ℂ)‖ = 1 := by simp
    have hreal : ‖((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ)‖ ^ 2
        = (2 * Real.pi * ((k : ℝ) - L)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    calc ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2
        = (‖((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ * ‖c k‖) ^ 2 := by
          rw [norm_mul, norm_mul]
      _ = (2 * Real.pi * ((k : ℝ) - L)) ^ 2 * ‖c k‖ ^ 2 := by
          rw [hI, mul_one, mul_pow, hreal]
      _ ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖c k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hpi (by positivity)
  have hYoung : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖)
      ≤ Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2 := by
    have hπN : (0 : ℝ) < Real.pi * (N : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      positivity
    have hpt : ∀ t, 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖)
        ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2 := by
      intro t
      nlinarith [sq_nonneg ((Real.pi * (N : ℝ)) * ‖T t‖ - ‖Td t‖)]
    have hintL : IntervalIntegrable (fun t => ‖T t‖ * ‖Td t‖) volume (-(δ / 2)) (1 - δ / 2) :=
      (hcontT.norm.mul hcontTd.norm).intervalIntegrable _ _
    have hintL' : IntervalIntegrable (fun t => 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
        volume (-(δ / 2)) (1 - δ / 2) :=
      (continuous_const.mul (hcontT.norm.mul hcontTd.norm)).intervalIntegrable _ _
    have hintR1 : IntervalIntegrable (fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2)
        volume (-(δ / 2)) (1 - δ / 2) :=
      (continuous_const.mul (hcontT.norm.pow 2)).intervalIntegrable _ _
    have hintR2 : IntervalIntegrable (fun t => ‖Td t‖ ^ 2) volume (-(δ / 2)) (1 - δ / 2) :=
      (hcontTd.norm.pow 2).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono
      (f := fun t => 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
      (g := fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2)
      (a := -(δ / 2)) (b := 1 - δ / 2) (μ := volume) hab hintL' (hintR1.add hintR2) hpt
    have hL : (∫ t in (-(δ / 2))..(1 - δ / 2), 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
        = 2 * (Real.pi * (N : ℝ)) * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖) :=
      intervalIntegral.integral_const_mul (r := 2 * (Real.pi * (N : ℝ)))
        (f := fun t => ‖T t‖ * ‖Td t‖)
    have hR : (∫ t in (-(δ / 2))..(1 - δ / 2),
        (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2)
        = (Real.pi * (N : ℝ)) ^ 2 * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
          + (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2) := by
      rw [intervalIntegral.integral_add
        (f := fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2) (g := fun t => ‖Td t‖ ^ 2)
        hintR1 hintR2,
        intervalIntegral.integral_const_mul (r := (Real.pi * (N : ℝ)) ^ 2)
          (f := fun t => ‖T t‖ ^ 2)]
    rw [hL, hR, hpar1, hpar2] at hmono
    have hsumcoef : (∑ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2)
        ≤ (Real.pi * (N : ℝ)) ^ 2 * ∑ k ∈ s, ‖c k‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k hk => hcoef k hk)
    have hkey : 2 * (Real.pi * (N : ℝ)) * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖)
        ≤ 2 * (Real.pi * (N : ℝ)) * (Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2) := by
      nlinarith [hmono, hsumcoef]
    exact le_of_mul_le_mul_left hkey (by positivity : (0 : ℝ) < 2 * (Real.pi * (N : ℝ)))
  set P : Finset (Σ q : ℕ, ℕ) := (Finset.Icc 1 Q).sigma
    (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hP
  set X : Finset ℝ := P.image (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ)) with hX
  have hfrac_inj : Set.InjOn (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ)) ↑P := by
    intro p hp p' hp' heq
    have hmem := Finset.mem_sigma.mp hp
    have hmem' := Finset.mem_sigma.mp hp'
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hq1' : 1 ≤ p'.1 := (Finset.mem_Icc.mp hmem'.1).1
    have ha : p.2 < p.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem.2).1
    have ha' : p'.2 < p'.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem'.2).1
    have hcop : Nat.Coprime p.2 p.1 := (Finset.mem_filter.mp hmem.2).2
    have hcop' : Nat.Coprime p'.2 p'.1 := (Finset.mem_filter.mp hmem'.2).2
    obtain ⟨hqq, haa⟩ := frac_inj p.1 p'.1 p.2 p'.2 hq1 hq1' ha ha' hcop hcop' heq
    exact Sigma.ext hqq (heq_of_eq haa)
  have hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hne
    rw [hX] at hx hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨p', hp', hpy⟩ := Finset.mem_image.mp hy
    have hmem := Finset.mem_sigma.mp hp
    have hmem' := Finset.mem_sigma.mp hp'
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hq1' : 1 ≤ p'.1 := (Finset.mem_Icc.mp hmem'.1).1
    have hqQ : p.1 ≤ Q := (Finset.mem_Icc.mp hmem.1).2
    have hqQ' : p'.1 ≤ Q := (Finset.mem_Icc.mp hmem'.1).2
    have hcop : Nat.Coprime p.2 p.1 := (Finset.mem_filter.mp hmem.2).2
    have hcop' : Nat.Coprime p'.2 p'.1 := (Finset.mem_filter.mp hmem'.2).2
    have hpair : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
      by_contra hc
      have hqeq : p.1 = p'.1 := by
        by_contra h
        exact hc (Or.inl h)
      have haeq : p.2 = p'.2 := by
        by_contra h
        exact hc (Or.inr h)
      apply hne
      rw [← hpx, ← hpy, Sigma.ext hqeq (heq_of_eq haeq)]
    have hfs := frac_sep Q p.1 p'.1 p.2 p'.2 hq1 hq1' hqQ hqQ' hcop hcop' hpair
    rw [hδ, ← hpx, ← hpy]
    exact hfs
  have hbounds : ∀ x ∈ X, (-(δ / 2)) + δ / 2 ≤ x ∧ x ≤ (1 - δ / 2) - δ / 2 := by
    intro x hx
    rw [hX] at hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    have hmem := Finset.mem_sigma.mp hp
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hqQ : p.1 ≤ Q := (Finset.mem_Icc.mp hmem.1).2
    have ha : p.2 < p.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem.2).1
    have hfb := frac_bounds Q p.1 p.2 hQ1 hq1 hqQ ha
    have hx0 : (0 : ℝ) ≤ x := by rw [← hpx]; exact hfb.1
    have hx1 : x ≤ 1 - δ := by rw [← hpx, hδ]; exact hfb.2
    constructor <;> linarith
  have hmain : (∑ q ∈ Finset.Icc 1 Q,
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
      = ∑ x ∈ X, ‖S x‖ ^ 2 := by
    have h1 : (∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
        = ∑ p ∈ P, ‖S ((p.2 : ℝ) / (p.1 : ℝ))‖ ^ 2 := by
      rw [Finset.sum_sigma']
    rw [h1, hX]
    exact (sum_image_of_inj (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ))
      (fun x : ℝ => ‖S x‖ ^ 2) P hfrac_inj)
  have hstep : ∀ x ∈ X, ‖S x‖ ^ 2 ≤ (Q : ℝ) ^ 2 *
      (∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
      + ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖ := by
    intro x hx
    have hg := gallagher_midpoint hderivT hcontTd x (δ / 2) (by linarith)
    rw [hTS x] at hg
    have h2r : (1 : ℝ) / (2 * (δ / 2)) = (Q : ℝ) ^ 2 := by
      have he : (2 : ℝ) * (δ / 2) = δ := by ring
      rw [he, hδ]
      field_simp
    rw [h2r] at hg
    exact hg
  have hsum1 : (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
      ≤ ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2 :=
    sum_windows_le (fun t => ‖T t‖ ^ 2) (hcontT.norm.pow 2) (fun t => sq_nonneg _) δ hδpos X
      (-(δ / 2)) (1 - δ / 2) hsep hbounds hab
  have hsum2 : (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖)
      ≤ ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖ :=
    sum_windows_le (fun t => ‖T t‖ * ‖Td t‖) (hcontT.norm.mul hcontTd.norm)
      (fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)) δ hδpos X
      (-(δ / 2)) (1 - δ / 2) hsep hbounds hab
  have hQsq : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  calc (∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
      = ∑ x ∈ X, ‖S x‖ ^ 2 := hmain
    _ ≤ ∑ x ∈ X, ((Q : ℝ) ^ 2 * (∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
        + ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖) :=
      Finset.sum_le_sum (fun x hx => hstep x hx)
    _ = (Q : ℝ) ^ 2 * (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
        + ∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (Q : ℝ) ^ 2 * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
        + ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖ :=
      by exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hQsq) hsum2
    _ ≤ (Q : ℝ) ^ 2 * (∑ k ∈ s, ‖c k‖ ^ 2) + Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2 := by
      rw [hpar1]
      exact add_le_add (le_refl _) hYoung
    _ = (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ s, ‖c k‖ ^ 2 := by ring

end Conjectures.Goldbach.AnalyticLargeSieve_aux

open Conjectures.Goldbach.AnalyticLargeSieve_aux

theorem Conjectures.Goldbach.AnalyticLargeSieve :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N Q : ℕ) (c : ℕ → ℂ), let S (t : ℝ) := ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t); (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2) ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  dsimp only
  intro M N Q c
  exact large_sieve M N Q c
