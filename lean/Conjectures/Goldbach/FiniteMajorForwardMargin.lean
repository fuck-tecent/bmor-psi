import Mathlib

private theorem cs_interval (a b : ℝ) (f g : ℝ → ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in a..b, f x * g x) ≤ Real.sqrt ((∫ x in a..b, (f x)^2) * (∫ x in a..b, (g x)^2)) := by
  let A := ∫ x in a..b, (f x)^2
  let B := ∫ x in a..b, f x * g x
  let C := ∫ x in a..b, (g x)^2
  have h_f_sq : IntervalIntegrable (fun x => (f x)^2) MeasureTheory.volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have h_fg : IntervalIntegrable (fun x => f x * g x) MeasureTheory.volume a b :=
    (hf.mul hg).intervalIntegrable a b
  have h_g_sq : IntervalIntegrable (fun x => (g x)^2) MeasureTheory.volume a b :=
    (hg.pow 2).intervalIntegrable a b
  have h_expand (t : ℝ) :
      (∫ x in a..b, (t * f x - g x)^2) = t^2 * A - 2 * t * B + C := by
    have h_left : IntervalIntegrable
        (fun x => t^2 * (f x)^2 - 2 * t * (f x * g x)) MeasureTheory.volume a b :=
      (h_f_sq.const_mul _).sub (h_fg.const_mul _)
    calc
      (∫ x in a..b, (t * f x - g x)^2) =
          ∫ x in a..b, (t^2 * (f x)^2 - 2 * t * (f x * g x) + (g x)^2) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (∫ x in a..b, t^2 * (f x)^2 - 2 * t * (f x * g x)) +
          ∫ x in a..b, (g x)^2 := by
            rw [intervalIntegral.integral_add h_left h_g_sq]
      _ = ((∫ x in a..b, t^2 * (f x)^2) -
          ∫ x in a..b, 2 * t * (f x * g x)) +
          ∫ x in a..b, (g x)^2 := by
            rw [intervalIntegral.integral_sub (h_f_sq.const_mul _) (h_fg.const_mul _)]
      _ = t^2 * A - 2 * t * B + C := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h_quad (t : ℝ) : 0 ≤ t^2 * A - 2 * t * B + C := by
    rw [← h_expand t]
    exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hA : 0 ≤ A := by
    exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg (f x))
  have hC : 0 ≤ C := by
    exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg (g x))
  have hAC : B^2 ≤ A * C := by
    rcases lt_or_eq_of_le hA with hApos | hAz
    · have hzero := h_quad (B / A)
      have hid : (B / A)^2 * A - 2 * (B / A) * B + C = C - B^2 / A := by
        field_simp [ne_of_gt hApos]
        ring
      rw [hid] at hzero
      have hdiv : B^2 / A ≤ C := by linarith
      have hmul : B^2 ≤ C * A := (div_le_iff₀ hApos).mp hdiv
      nlinarith
    · by_cases hB : B = 0
      · simp [hAz.symm, hB]
      · have hzero := h_quad ((C + 1) / (2 * B))
        rw [hAz.symm] at hzero
        have hid : ((C + 1) / (2 * B))^2 * 0 -
            2 * ((C + 1) / (2 * B)) * B + C = -1 := by
          field_simp [hB]
          ring
        rw [hid] at hzero
        norm_num at hzero
  change B ≤ Real.sqrt (A * C)
  exact Real.le_sqrt_of_sq_le hAC

private theorem arc_transfer (h : ℝ) (f m p : ℝ → ℂ) (hh : 0 ≤ h)
    (hf : Continuous f) (hm : Continuous m) (hp : Continuous p) (hp1 : ∀ x, ‖p x‖ = 1)
    (hcs : ∀ (u v : ℝ → ℝ), Continuous u → Continuous v →
        (∫ x in (-h)..h, u x * v x) ≤
          Real.sqrt ((∫ x in (-h)..h, (u x)^2) * (∫ x in (-h)..h, (v x)^2))) :
    (∫ x in (-h)..h, (f x)^2 * p x).re ≥ (∫ x in (-h)..h, (m x)^2 * p x).re
      - 2 * Real.sqrt ((∫ x in (-h)..h, ‖f x - m x‖^2) * (∫ x in (-h)..h, ‖m x‖^2))
      - (∫ x in (-h)..h, ‖f x - m x‖^2) := by
  have hab : -h ≤ h := by linarith
  have hd : Continuous (fun x => f x - m x) := hf.sub hm
  have h1 : IntervalIntegrable (fun x => (m x)^2 * p x) MeasureTheory.volume (-h) h :=
    ((hm.pow 2).mul hp).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => 2 * (m x * (f x - m x)) * p x)
      MeasureTheory.volume (-h) h :=
    ((continuous_const.mul (hm.mul hd)).mul hp).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x => (f x - m x)^2 * p x) MeasureTheory.volume (-h) h :=
    ((hd.pow 2).mul hp).intervalIntegrable _ _
  have hsplit : (∫ x in (-h)..h, (f x)^2 * p x)
      = (∫ x in (-h)..h, (m x)^2 * p x) + (∫ x in (-h)..h, 2 * (m x * (f x - m x)) * p x)
        + (∫ x in (-h)..h, (f x - m x)^2 * p x) := by
    have hc : (∫ x in (-h)..h, (f x)^2 * p x)
        = ∫ x in (-h)..h, ((m x)^2 * p x + 2 * (m x * (f x - m x)) * p x
            + (f x - m x)^2 * p x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [hc, intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  have hI2 : (∫ x in (-h)..h, 2 * (m x * (f x - m x)) * p x).re
      ≥ -(2 * Real.sqrt ((∫ x in (-h)..h, ‖f x - m x‖^2) * (∫ x in (-h)..h, ‖m x‖^2))) := by
    have ha : -(‖∫ x in (-h)..h, 2 * (m x * (f x - m x)) * p x‖)
        ≤ (∫ x in (-h)..h, 2 * (m x * (f x - m x)) * p x).re :=
      le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
    have hb : ‖∫ x in (-h)..h, 2 * (m x * (f x - m x)) * p x‖
        ≤ ∫ x in (-h)..h, ‖2 * (m x * (f x - m x)) * p x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have hc : (∫ x in (-h)..h, ‖2 * (m x * (f x - m x)) * p x‖)
        = 2 * ∫ x in (-h)..h, ‖f x - m x‖ * ‖m x‖ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      have h2n : ‖(2 : ℂ)‖ = 2 := by simp
      simp only [norm_mul, h2n, hp1, mul_one]
      ring
    rw [hc] at hb
    have hd2 := hcs (fun x => ‖f x - m x‖) (fun x => ‖m x‖) hd.norm hm.norm
    linarith
  have hI3 : (∫ x in (-h)..h, (f x - m x)^2 * p x).re
      ≥ -((∫ x in (-h)..h, ‖f x - m x‖^2)) := by
    have ha : -(‖∫ x in (-h)..h, (f x - m x)^2 * p x‖)
        ≤ (∫ x in (-h)..h, (f x - m x)^2 * p x).re :=
      le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
    have hb : ‖∫ x in (-h)..h, (f x - m x)^2 * p x‖
        ≤ ∫ x in (-h)..h, ‖(f x - m x)^2 * p x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have hc : (∫ x in (-h)..h, ‖(f x - m x)^2 * p x‖) = ∫ x in (-h)..h, ‖f x - m x‖^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [norm_mul, hp1, mul_one, norm_pow]
    rw [hc] at hb
    linarith
  rw [hsplit, Complex.add_re, Complex.add_re]
  linarith

private theorem sums_assembly (n : ℝ) (Q : Finset ℕ) (Aq : ℕ → Finset ℕ)
    (e : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (cm cs : ℕ → ℕ → ℝ)
    (hn : 0 < n)
    (he : ∀ q ∈ Q, ∀ a ∈ Aq q, 0 ≤ e q a)
    (hm : ∀ q ∈ Q, 0 ≤ m q)
    (harc : ∀ q ∈ Q, ∀ a ∈ Aq q, cm q a - 2 * Real.sqrt (e q a * m q) - e q a ≤ cs q a)
    (hC : (7/2) * n < ∑ q ∈ Q, ∑ a ∈ Aq q, cm q a)
    (hB : (∑ q ∈ Q, ((Aq q).card:ℝ) * m q) < 6 * n)
    (hU : (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) ≤ n / 10) :
    (∑ q ∈ Q, ∑ a ∈ Aq q, cm q a) - 2 * Real.sqrt ((∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q)) - (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) ≤ ∑ q ∈ Q, ∑ a ∈ Aq q, cs q a
      ∧ (37/20) * n < ∑ q ∈ Q, ∑ a ∈ Aq q, cs q a := by
  have hP : ∀ q ∈ Q, 0 ≤ ∑ a ∈ Aq q, e q a := fun q hq =>
    Finset.sum_nonneg (fun a ha => he q hq a ha)
  have hR : ∀ q ∈ Q, 0 ≤ ((Aq q).card:ℝ) * m q := fun q hq =>
    mul_nonneg (Nat.cast_nonneg _) (hm q hq)
  have hU0 : 0 ≤ ∑ q ∈ Q, ∑ a ∈ Aq q, e q a := Finset.sum_nonneg (fun q hq => hP q hq)
  have hB0 : 0 ≤ ∑ q ∈ Q, ((Aq q).card:ℝ) * m q := Finset.sum_nonneg (fun q hq => hR q hq)
  have hstep1 : (∑ q ∈ Q, ∑ a ∈ Aq q, cm q a)
      - 2 * (∑ q ∈ Q, ∑ a ∈ Aq q, Real.sqrt (e q a * m q))
      - (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) ≤ ∑ q ∈ Q, ∑ a ∈ Aq q, cs q a := by
    have inner : ∀ q ∈ Q, (∑ a ∈ Aq q, (cm q a - 2 * Real.sqrt (e q a * m q) - e q a))
        ≤ ∑ a ∈ Aq q, cs q a := by
      intro q hq
      exact Finset.sum_le_sum (fun a ha => harc q hq a ha)
    have outer := Finset.sum_le_sum inner
    have eq1 : ∀ q ∈ Q, (∑ a ∈ Aq q, (cm q a - 2 * Real.sqrt (e q a * m q) - e q a))
        = (∑ a ∈ Aq q, cm q a) - 2 * (∑ a ∈ Aq q, Real.sqrt (e q a * m q))
          - (∑ a ∈ Aq q, e q a) := by
      intro q hq
      have e1 : (∑ a ∈ Aq q, (cm q a - 2 * Real.sqrt (e q a * m q) - e q a))
          = (∑ a ∈ Aq q, cm q a) - (∑ a ∈ Aq q, 2 * Real.sqrt (e q a * m q))
            - (∑ a ∈ Aq q, e q a) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      rw [e1, Finset.mul_sum]
    have eq2 : (∑ q ∈ Q, ∑ a ∈ Aq q, (cm q a - 2 * Real.sqrt (e q a * m q) - e q a))
        = (∑ q ∈ Q, ∑ a ∈ Aq q, cm q a)
          - 2 * (∑ q ∈ Q, ∑ a ∈ Aq q, Real.sqrt (e q a * m q))
          - (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) := by
      have e1 : (∑ q ∈ Q, ∑ a ∈ Aq q, (cm q a - 2 * Real.sqrt (e q a * m q) - e q a))
          = ∑ q ∈ Q, ((∑ a ∈ Aq q, cm q a) - 2 * (∑ a ∈ Aq q, Real.sqrt (e q a * m q))
            - (∑ a ∈ Aq q, e q a)) :=
        Finset.sum_congr rfl (fun q hq => eq1 q hq)
      rw [e1, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [eq2] at outer
    exact outer
  have hstep2 : (∑ q ∈ Q, ∑ a ∈ Aq q, Real.sqrt (e q a * m q))
      ≤ Real.sqrt ((∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q)) := by
    have inner : ∀ q ∈ Q, (∑ a ∈ Aq q, Real.sqrt (e q a * m q))
        ≤ Real.sqrt ((∑ a ∈ Aq q, e q a) * (((Aq q).card:ℝ) * m q)) := by
      intro q hq
      have hrw : (∑ a ∈ Aq q, Real.sqrt (e q a * m q))
          = ∑ a ∈ Aq q, Real.sqrt (e q a) * Real.sqrt (m q) :=
        Finset.sum_congr rfl (fun a ha => Real.sqrt_mul (he q hq a ha) (m q))
      rw [hrw]
      apply Real.le_sqrt_of_sq_le
      have hkey := Finset.sum_mul_sq_le_sq_mul_sq (Aq q) (fun a => Real.sqrt (e q a))
        (fun _ => Real.sqrt (m q))
      have e1 : (∑ a ∈ Aq q, (Real.sqrt (e q a))^2) = ∑ a ∈ Aq q, e q a :=
        Finset.sum_congr rfl (fun a ha => Real.sq_sqrt (he q hq a ha))
      have e2 : (∑ a ∈ Aq q, (Real.sqrt (m q))^2) = ((Aq q).card:ℝ) * m q := by
        have h3 : ∀ a ∈ Aq q, (Real.sqrt (m q))^2 = m q := fun a _ => Real.sq_sqrt (hm q hq)
        have h4 : (∑ a ∈ Aq q, m q) = ((Aq q).card:ℝ) * m q := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_congr rfl h3, h4]
      rw [e1, e2] at hkey
      exact hkey
    have outer := Finset.sum_le_sum inner
    refine le_trans outer ?_
    apply Real.le_sqrt_of_sq_le
    have hrw : (∑ q ∈ Q, Real.sqrt ((∑ a ∈ Aq q, e q a) * (((Aq q).card:ℝ) * m q)))
        = ∑ q ∈ Q, Real.sqrt (∑ a ∈ Aq q, e q a) * Real.sqrt (((Aq q).card:ℝ) * m q) :=
      Finset.sum_congr rfl (fun q hq => Real.sqrt_mul (hP q hq) (((Aq q).card:ℝ) * m q))
    rw [hrw]
    have hkey := Finset.sum_mul_sq_le_sq_mul_sq Q (fun q => Real.sqrt (∑ a ∈ Aq q, e q a))
      (fun q => Real.sqrt (((Aq q).card:ℝ) * m q))
    have e1 : (∑ q ∈ Q, (Real.sqrt (∑ a ∈ Aq q, e q a))^2) = ∑ q ∈ Q, ∑ a ∈ Aq q, e q a :=
      Finset.sum_congr rfl (fun q hq => Real.sq_sqrt (hP q hq))
    have e2 : (∑ q ∈ Q, (Real.sqrt (((Aq q).card:ℝ) * m q))^2)
        = ∑ q ∈ Q, ((Aq q).card:ℝ) * m q :=
      Finset.sum_congr rfl (fun q hq => Real.sq_sqrt (hR q hq))
    rw [e1, e2] at hkey
    exact hkey
  have hmain : (∑ q ∈ Q, ∑ a ∈ Aq q, cm q a)
      - 2 * Real.sqrt ((∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q))
      - (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) ≤ ∑ q ∈ Q, ∑ a ∈ Aq q, cs q a := by
    linarith [hstep1, hstep2]
  refine ⟨hmain, ?_⟩
  have h1 : (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q) < (3/5) * n^2 := by
    calc (∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q)
        ≤ (n/10) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q) := mul_le_mul_of_nonneg_right hU hB0
      _ < (n/10) * (6*n) := mul_lt_mul_of_pos_left hB (by positivity)
      _ = (3/5) * n^2 := by ring
  have hsq : Real.sqrt ((∑ q ∈ Q, ∑ a ∈ Aq q, e q a) * (∑ q ∈ Q, ((Aq q).card:ℝ) * m q))
      < Real.sqrt (3/5) * n := by
    have hx := Real.sqrt_lt_sqrt (mul_nonneg hU0 hB0) h1
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/5), Real.sqrt_sq (le_of_lt hn)] at hx
  have hbound : 2 * (Real.sqrt (3/5) * n) < (31/20) * n := by
    have hs : Real.sqrt (3/5) < 31/40 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (3/5:ℝ)), Real.sqrt_nonneg (3/5:ℝ)]
    nlinarith
  linarith

set_option maxRecDepth 4000 in
theorem Conjectures.Goldbach.FiniteMajorForwardMargin :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); let S := fun (n : ℕ) (α : ℝ) => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*α); let M := fun (n q : ℕ) (β : ℝ) => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*V n β; let H := fun (n q : ℕ) => (105:ℝ)/((q:ℝ)*(n:ℝ)); let Q := Finset.Icc (1:ℕ) 105; let A := fun (q : ℕ) => (Finset.range q).filter (fun a => Nat.Coprime a q); let B := fun (n : ℕ) => ∑ q ∈ Q, ((A q).card:ℝ) * Jr (H n q) (fun β => ‖M n q β‖^2); let C := fun (n : ℕ) => ∑ q ∈ Q, ∑ a ∈ A q, (_J (H n q) (fun β => (M n q β)^2*E (-(n:ℝ)*((a:ℝ)/q+β)))).re; let U := fun (n : ℕ) => ∑ q ∈ Q, ∑ a ∈ A q, Jr (H n q) (fun β => ‖S n ((a:ℝ)/q+β)-M n q β‖^2); ∀ n : ℕ, 0<n → (7/2:ℝ)*(n:ℝ)<C n → B n<6*(n:ℝ) → U n≤(n:ℝ)/10 → let actual := ∑ q ∈ Q, ∑ a ∈ A q, (_J (H n q) (fun β => (S n ((a:ℝ)/q+β))^2*E (-(n:ℝ)*((a:ℝ)/q+β)))).re; C n-2*Real.sqrt (U n*B n)-U n≤actual ∧ (37/20:ℝ)*(n:ℝ)<actual := by
  intro E J Jr V S M H Q A B C U n hn hC hB hU actual
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hE : Continuous E := by
    show Continuous (fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))
    fun_prop
  have hEn : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    show ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ = 1
    rw [Complex.norm_exp]
    have hx : (((2*Real.pi*x:ℝ):ℂ)*Complex.I).re = 0 := by simp
    rw [hx, Real.exp_zero]
  have hS : Continuous (S n) := by
    show Continuous (fun α : ℝ => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k:ℂ)*E ((k:ℝ)*α))
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (hE.comp (continuous_const.mul continuous_id)))
  have hV : Continuous (V n) := by
    show Continuous (fun β : ℝ => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β))
    exact continuous_finsetSum _ (fun k _ => hE.comp (continuous_const.mul continuous_id))
  have hM : ∀ q : ℕ, Continuous (M n q) := by
    intro q
    show Continuous (fun β : ℝ => ((ArithmeticFunction.moebius q:ℤ):ℂ)/(Nat.totient q:ℂ)*V n β)
    exact continuous_const.mul hV
  have hH : ∀ q ∈ Q, 0 < H n q := by
    intro q hq
    have hq2 : q ∈ Finset.Icc (1:ℕ) 105 := hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq2).1
    have hqp : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
    show (0:ℝ) < 105/((q:ℝ)*(n:ℝ))
    positivity
  have he : ∀ q ∈ Q, ∀ a ∈ A q, (0:ℝ) ≤ ∫ β in (-(H n q))..(H n q), ‖S n ((a:ℝ)/q+β)-M n q β‖^2 := by
    intro q hq a ha
    exact intervalIntegral.integral_nonneg_of_forall (by linarith [hH q hq]) (fun β => sq_nonneg _)
  have hm : ∀ q ∈ Q, (0:ℝ) ≤ ∫ β in (-(H n q))..(H n q), ‖M n q β‖^2 := by
    intro q hq
    exact intervalIntegral.integral_nonneg_of_forall (by linarith [hH q hq]) (fun β => sq_nonneg _)
  have harc : ∀ q ∈ Q, ∀ a ∈ A q,
      (∫ β in (-(H n q))..(H n q), (M n q β)^2 * E (-(n:ℝ)*((a:ℝ)/q+β))).re
        - 2 * Real.sqrt ((∫ β in (-(H n q))..(H n q), ‖S n ((a:ℝ)/q+β)-M n q β‖^2) * (∫ β in (-(H n q))..(H n q), ‖M n q β‖^2))
        - (∫ β in (-(H n q))..(H n q), ‖S n ((a:ℝ)/q+β)-M n q β‖^2)
      ≤ (∫ β in (-(H n q))..(H n q), (S n ((a:ℝ)/q+β))^2 * E (-(n:ℝ)*((a:ℝ)/q+β))).re := by
    intro q hq a ha
    refine arc_transfer (H n q) (fun β => S n ((a:ℝ)/q+β)) (fun β => M n q β)
      (fun β => E (-(n:ℝ)*((a:ℝ)/q+β))) (le_of_lt (hH q hq)) ?_ ?_ ?_ ?_ ?_
    · exact hS.comp (continuous_const.add continuous_id)
    · exact hM q
    · exact hE.comp (continuous_const.mul (continuous_const.add continuous_id))
    · intro x
      exact hEn _
    · intro u v hu hv
      exact cs_interval (-(H n q)) (H n q) u v (by linarith [hH q hq]) hu hv
  have hmain := sums_assembly (n:ℝ) Q A
    (fun q a => ∫ β in (-(H n q))..(H n q), ‖S n ((a:ℝ)/q+β)-M n q β‖^2)
    (fun q => ∫ β in (-(H n q))..(H n q), ‖M n q β‖^2)
    (fun q a => (∫ β in (-(H n q))..(H n q), (M n q β)^2 * E (-(n:ℝ)*((a:ℝ)/q+β))).re)
    (fun q a => (∫ β in (-(H n q))..(H n q), (S n ((a:ℝ)/q+β))^2 * E (-(n:ℝ)*((a:ℝ)/q+β))).re)
    hnR he hm harc hC hB hU
  exact hmain
