import Mathlib
import Conjectures.Goldbach.MajorFixed144

open Finset MeasureTheory Filter
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc

namespace MajorDilationRefute

noncomputable section

open scoped Classical

private theorem phase_add' (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

def Wh (q a : ℕ) (h : ℝ) : Set ℝ := Set.Icc (center q a - h) (center q a + h)

private theorem mem_Wh (q a : ℕ) (h t : ℝ) : t ∈ Wh q a h ↔ |t - center q a| ≤ h := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem Wh_sub {n q a : ℕ} {h : ℝ} (h0 : 0 ≤ h) (hw : h ≤ width n q) :
    Wh q a h ⊆ window n q a :=
  Set.Icc_subset_Icc (by linarith) (by linarith)

private theorem cross_eq_of_overlap' {n q r a b : ℕ} {t : ℝ} (hn : 2 * (cutoff n)^2 < n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : t ∈ window n q a) (hb : t ∈ window n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let Q := cutoff n
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window n q a t).mp ha
  have h₂ := (mem_window n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique' {n q r a b : ℕ} {t : ℝ} (hn : 2*(cutoff n)^2<n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window n q a) (htb : t ∈ window n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap' hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

private theorem arc_indicator_sum_h {n : ℕ} (hn : 2*(cutoff n)^2<n) (h : ℕ → ℕ → ℝ)
    (h0 : ∀ q a, 0 ≤ h q a) (hw : ∀ q a, h q a ≤ width n q) (F : ℝ → ℂ) (t : ℝ) :
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ h q a}.indicator F t =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (Wh q a (h q a)).indicator F t := by
  classical
  by_cases ht : t ∈ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ h q a}
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hwh : t ∈ Wh q a (h q a) := (mem_Wh _ _ _ _).mpr habs
    have hw' : t ∈ window n q a := Wh_sub (h0 q a) (hw q a) hwh
    symm
    calc
      _ = ∑ b ∈ numerators q, (Wh q b (h q b)).indicator F t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique' hn hr hq hb ha' (Wh_sub (h0 r b) (hw r b) ht') hw').1) _
      _ = (Wh q a (h q a)).indicator F t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique' hn hq hq hb ha' (Wh_sub (h0 q b) (hw q b) ht') hw').2) _
      _ = _ := Set.indicator_of_mem hwh _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw' => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_Wh _ _ _ _).mp hw'⟩) _


private theorem cont_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

private theorem cont_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

def Pint (n q a : ℕ) (h : ℝ) : ℂ := ∫ β in -h..h, integrand n (center q a + β)

def Mint (n q a : ℕ) (h : ℝ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n:ℝ) * center q a)) * (kernelMass n h : ℂ)

private theorem int_window {q a : ℕ} {h : ℝ} (hh : 0 ≤ h) (hl : 0 ≤ center q a - h)
    (hr : center q a + h ≤ 1) (F : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, (Wh q a h).indicator F t) = ∫ β in -h..h, F (center q a + β) := by
  rw [intervalIntegral.integral_comp_add_left]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    Wh, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : center q a + -h ≤ center q a + h),
    ← integral_Icc_eq_integral_Ioc]
  rw [max_eq_left (by linarith), min_eq_left (by linarith), show center q a + -h = center q a - h by ring]

private theorem model_int (n q a : ℕ) (h : ℝ) :
    (∫ β in -h..h, modelPoint n q a β) = Mint n q a h := by
  have hh (β : ℝ) : modelPoint n q a β =
      (unitMean q a ^2 * phase (-(n:ℝ)*center q a)) * ((‖kernel n β‖^2 : ℝ) : ℂ) := by
    rw [modelPoint, ← kernel_square_twist, mul_add, phase_add']
    ring
  simp_rw [hh]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rfl

private theorem error_cont' (n q a : ℕ) :
    Continuous (fun β => integrand n (center q a+β) - modelPoint n q a β) := by
  unfold integrand modelPoint primeSum kernel phase
  fun_prop

private theorem Pint_sub_Mint {n q a : ℕ} {h : ℝ} (h0 : 0 ≤ h) (hw : h ≤ width n q) :
    ‖Pint n q a h - Mint n q a h‖ ≤ ∫ β in -(width n q)..width n q, modelError n q a β := by
  have hi : Continuous (fun β => integrand n (center q a+β)) := by
    unfold integrand primeSum phase; fun_prop
  have hm : Continuous (modelPoint n q a) := by unfold modelPoint kernel phase; fun_prop
  rw [Pint, ← model_int, ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hw (Eventually.of_forall fun _ => norm_nonneg _)
    ((error_cont' n q a).norm.intervalIntegrable _ _)


private theorem split_int (n : ℕ) (hh : ℕ → ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q,
      (Wh q a (hh q a)).indicator (integrand n) t) =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q,
      ∫ t in (0:ℝ)..1, (Wh q a (hh q a)).indicator (integrand n) t := by
  have hcont := cont_integrand n
  have hInt (q a : ℕ) : IntervalIntegrable ((Wh q a (hh q a)).indicator (integrand n)) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩

private theorem interior_order' {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut' {n q a : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    width n q ≤ center q a ∧ center q a + width n q ≤ 1 := by
  obtain ⟨ha₁,haq⟩ := interior_order' hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  constructor <;> linarith

theorem diff_formula {n : ℕ} (hn : 2*(cutoff n)^2<n) (sel : ℕ → ℕ → Prop)
    (hsel : ∀ q a, sel q a → 2 ≤ q) :
    ‖((∫ t in (0:ℝ)..1, (arcs n).indicator (integrand n) t) -
      ∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (if sel q a then (1/2:ℝ) else 1) * (cutoff n:ℝ)/((q:ℝ)*(n:ℝ))}).indicator
          (integrand n) t) -
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q,
        (if sel q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0)‖
      ≤ 2 * totalArcError n := by
  classical
  set hh : ℕ → ℕ → ℝ := fun q a => (if sel q a then (1/2:ℝ) else 1) * width n q with hhdef
  have hh0 : ∀ q a, 0 ≤ hh q a := fun q a => by
    have := width_nonneg n q
    simp only [hhdef]; split_ifs <;> positivity
  have hhw : ∀ q a, hh q a ≤ width n q := fun q a => by
    have := width_nonneg n q
    simp only [hhdef]; split_ifs <;> linarith
  have hset : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (if sel q a then (1/2:ℝ) else 1) * (cutoff n:ℝ)/((q:ℝ)*(n:ℝ))} =
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ hh q a} := by
    ext t
    simp only [Set.mem_setOf_eq, hhdef, width, mul_div_assoc]
  rw [hset]
  have e2 : ∀ t, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ hh q a}).indicator (integrand n) t =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (Wh q a (hh q a)).indicator (integrand n) t :=
    fun t => arc_indicator_sum_h hn hh hh0 hhw (integrand n) t
  have e1 : ∀ t, (arcs n).indicator (integrand n) t =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (Wh q a (width n q)).indicator (integrand n) t :=
    fun t => arc_indicator_sum hn t
  simp_rw [e1, e2]
  rw [split_int n (fun q _ => width n q), split_int n hh, ← sum_sub_distrib, ← sum_sub_distrib]
  have hterm : ∀ q ∈ Icc 1 (cutoff n),
      ‖((∑ a ∈ numerators q, ∫ t in (0:ℝ)..1, (Wh q a (width n q)).indicator (integrand n) t) -
          ∑ a ∈ numerators q, ∫ t in (0:ℝ)..1, (Wh q a (hh q a)).indicator (integrand n) t) -
        ∑ a ∈ numerators q,
          (if sel q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0)‖ ≤
        2 * ∑ a ∈ range (q+1), ∫ β in -(width n q)..width n q, modelError n q a β := by
    intro q hq
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    have hE : ∀ a, 0 ≤ ∫ β in -(width n q)..width n q, modelError n q a β := fun a =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) fun _ _ => norm_nonneg _
    calc
      _ ≤ ∑ a ∈ numerators q, 2 * ∫ β in -(width n q)..width n q, modelError n q a β := by
        refine sum_le_sum fun a ha => ?_
        by_cases hs : sel q a
        · have hq2 := hsel q a hs
          obtain ⟨hl, hr⟩ := uncut' hn (by omega) ha
          have hw0 := width_nonneg n q
          have hhs : hh q a = width n q / 2 := by simp only [hhdef, hs, if_true]; ring
          rw [hhs, if_pos hs]
          have i1 := int_window (q := q) (a := a) (h := width n q) hw0 (by linarith) hr (integrand n)
          have i2 := int_window (q := q) (a := a) (h := width n q / 2) (by linarith) (by linarith) (by linarith) (integrand n)
          have b1 := Pint_sub_Mint (n := n) (q := q) (a := a) (h := width n q) hw0 le_rfl
          have b2 := Pint_sub_Mint (n := n) (q := q) (a := a) (h := width n q / 2) (by linarith) (by linarith)
          rw [i1, i2]
          show ‖(Pint n q a (width n q) - Pint n q a (width n q / 2)) -
            (Mint n q a (width n q) - Mint n q a (width n q / 2))‖ ≤ _
          have e : (Pint n q a (width n q) - Pint n q a (width n q / 2)) -
            (Mint n q a (width n q) - Mint n q a (width n q / 2)) =
            (Pint n q a (width n q) - Mint n q a (width n q)) -
            (Pint n q a (width n q / 2) - Mint n q a (width n q / 2)) := by ring
          rw [e]
          linarith [norm_sub_le (Pint n q a (width n q) - Mint n q a (width n q))
            (Pint n q a (width n q / 2) - Mint n q a (width n q / 2))]
        · have hhs : hh q a = width n q := by simp only [hhdef, hs, if_false]; ring
          rw [hhs, if_neg hs]
          simp only [sub_self, sub_zero, norm_zero]
          linarith [hE a]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => by linarith [hE a]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ q ∈ Icc 1 (cutoff n), 2 * ∑ a ∈ range (q+1), ∫ β in -(width n q)..width n q, modelError n q a β :=
      sum_le_sum hterm
    _ = _ := by rw [totalArcError, mul_sum]



private theorem phase_pow (k : ℕ) (β : ℝ) : phase ((k:ℝ) * β) = (phase β)^k := by
  induction k with
  | zero => simp [phase]
  | succ k ih =>
    rw [pow_succ, ← ih, ← phase_add']
    congr 1
    push_cast; ring

private theorem sq_norm_phase_sub_one (x : ℝ) : ‖phase x - 1‖^2 = 2 - 2 * Real.cos (2 * Real.pi * x) := by
  have h1 : (phase x - 1).re = Real.cos (2 * Real.pi * x) - 1 := by
    simp only [Complex.sub_re, Complex.one_re, phase, Complex.exp_ofReal_mul_I_re]
  have h2 : (phase x - 1).im = Real.sin (2 * Real.pi * x) := by
    simp only [Complex.sub_im, Complex.one_im, phase, Complex.exp_ofReal_mul_I_im, sub_zero]
  rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * x)]

private theorem kernel_lower (n : ℕ) (β : ℝ) :
    2 - 2 * Real.cos (2 * Real.pi * ((n+1:ℕ) * β)) ≤ ‖kernel n β‖^2 * (2 * Real.pi * β)^2 := by
  have hk : kernel n β * (phase β - 1) = phase (((n+1:ℕ):ℝ) * β) - 1 := by
    unfold kernel
    simp_rw [phase_pow]
    rw [geom_sum_mul]
  have h1 : ‖phase β - 1‖ ≤ 2 * Real.pi * |β| := by
    unfold phase
    rw [mul_comm _ Complex.I]
    calc
      _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  rw [← sq_norm_phase_sub_one, ← hk, norm_mul, mul_pow]
  have : (2 * Real.pi * β)^2 = (2 * Real.pi * |β|)^2 := by rw [show (2*Real.pi*|β|)^2 = (2*Real.pi)^2*|β|^2 by ring, sq_abs]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)


private theorem cos_integral (c a b : ℝ) (hc : c ≠ 0) :
    ∫ x in a..b, (2 - 2 * Real.cos (c * x)) = 2 * (b - a) - 2 * (Real.sin (c * b) - Real.sin (c * a)) / c := by
  have h1 : ∫ x in a..b, (2 - 2 * Real.cos (c * x)) =
      (∫ x in a..b, (2:ℝ)) - 2 * ∫ x in a..b, Real.cos (c * x) := by
    rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul]
  rw [h1, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
  simp only [intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  field_simp

theorem delta_lower {n : ℕ} (hn : 0 < n) {w : ℝ} (hw : 1 / (n:ℝ) ≤ w) :
    1 / (12 * Real.pi ^ 2 * w) ≤ kernelMass n w - kernelMass n (w / 2) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hf : Continuous (fun β => ‖kernel n β‖ ^ 2) := (cont_kernel n).norm.pow 2
  set c : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) with hc
  have hcpos : 0 < c := by positivity
  have hsplit : kernelMass n w = (∫ β in -w..(w/2), ‖kernel n β‖ ^ 2) + ∫ β in (w/2)..w, ‖kernel n β‖ ^ 2 := by
    unfold kernelMass
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have hmid : kernelMass n (w/2) ≤ ∫ β in -w..(w/2), ‖kernel n β‖ ^ 2 := by
    unfold kernelMass
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Eventually.of_forall fun _ => sq_nonneg _) (hf.intervalIntegrable _ _)
  have hlow : ∫ β in (w/2)..w, (2 - 2 * Real.cos (c * β)) / (2 * Real.pi * w)^2 ≤
      ∫ β in (w/2)..w, ‖kernel n β‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · apply Continuous.intervalIntegrable; fun_prop
    · exact hf.intervalIntegrable _ _
    · intro β hβ
      have hk := kernel_lower n β
      have hpos : 0 < (2 * Real.pi * w)^2 := by positivity
      rw [div_le_iff₀ hpos]
      have hβ2 : (2 * Real.pi * β)^2 ≤ (2 * Real.pi * w)^2 := by
        have hb : 0 ≤ β := by linarith [hβ.1]
        apply pow_le_pow_left₀ (by positivity)
        have := Real.pi_pos
        nlinarith [hβ.2]
      calc
        _ ≤ ‖kernel n β‖^2 * (2 * Real.pi * β)^2 := by
          have : (n:ℝ) + 1 = ((n+1:ℕ):ℝ) := by push_cast; ring
          have e : c * β = 2 * Real.pi * (((n+1:ℕ):ℝ) * β) := by rw [hc]; ring
          rw [e]; exact hk
        _ ≤ _ := mul_le_mul_of_nonneg_left hβ2 (sq_nonneg _)
  have hval : ∫ β in (w/2)..w, (2 - 2 * Real.cos (c * β)) / (2 * Real.pi * w)^2 =
      (2 * (w - w/2) - 2 * (Real.sin (c * w) - Real.sin (c * (w/2))) / c) / (2 * Real.pi * w)^2 := by
    rw [intervalIntegral.integral_div, cos_integral c _ _ hcpos.ne']
  have hsin : Real.sin (c * w) - Real.sin (c * (w/2)) ≤ 2 := by
    linarith [Real.sin_le_one (c*w), Real.neg_one_le_sin (c * (w/2))]
  have hcw : 4 / c ≤ w * (2/3) := by
    rw [div_le_iff₀ hcpos, hc]
    have hnn : (1:ℝ) ≤ w * n := by
      have := (div_le_iff₀ hn').mp hw
      rw [div_le_iff₀ hn'] at hw; linarith
    have hpi := Real.pi_gt_three
    push_cast
    nlinarith [mul_pos hw0 hn', Real.pi_pos]
  have hnum : w / 3 ≤ 2 * (w - w/2) - 2 * (Real.sin (c * w) - Real.sin (c * (w/2))) / c := by
    have : 2 * (Real.sin (c * w) - Real.sin (c * (w/2))) / c ≤ 4 / c := by
      rw [div_le_div_iff_of_pos_right hcpos]; linarith
    linarith
  have hpos : 0 < (2 * Real.pi * w)^2 := by positivity
  calc
    1 / (12 * Real.pi ^ 2 * w) = (w/3) / (2 * Real.pi * w)^2 := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hpos.le
    _ = _ := hval.symm
    _ ≤ _ := hlow
    _ ≤ _ := by linarith



private theorem sqfree_prime_pow {p j : ℕ} (hp : p.Prime) (h : Squarefree (p ^ j)) : j ≤ 1 := by
  by_contra hj
  have hj : 2 ≤ j := by omega
  have h2 : p * p ∣ p ^ j := by
    rw [← pow_two]; exact pow_dvd_pow p (by omega)
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (h p h2))

theorem ram_one_sign {q : ℕ} (hq : Squarefree q) : ram q 1 = 1 ∨ ram q 1 = -1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => exact absurd hq not_squarefree_zero
  | prime_pow p j hp =>
    have hj := sqfree_prime_pow hp hq
    interval_cases j
    · left; simp [ram_one]
    · right
      have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
      simp [ram_prime hp, h1]
  | coprime q r hq' hr' hqr iq ir =>
    have hsq := Nat.squarefree_mul_iff.mp hq
    rw [ram_mul (by omega) (by omega) hqr]
    rcases iq hsq.2.1 with h | h <;> rcases ir hsq.2.2 with h' | h' <;> simp [h, h']

theorem totient_sq_ge {q : ℕ} (hq : Squarefree q) (ho : Odd q) : q ≤ q.totient ^ 2 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => exact absurd hq not_squarefree_zero
  | prime_pow p j hp =>
    have hj := sqfree_prime_pow hp hq
    interval_cases j
    · simp
    · have hp3 : 3 ≤ p := by
        have h2 := hp.two_le
        rcases Nat.lt_or_ge p 3 with h | h
        · have : p = 2 := by omega
          subst this
          exact absurd ho (by decide)
        · exact h
      rw [pow_one, Nat.totient_prime hp]
      have : p - 1 + 1 = p := by omega
      zify [hp.one_le]
      nlinarith
  | coprime q r hq' hr' hqr iq ir =>
    have hsq := Nat.squarefree_mul_iff.mp hq
    have hoq := Nat.odd_mul.mp ho
    rw [Nat.totient_mul hqr, mul_pow]
    exact Nat.mul_le_mul (iq hsq.2.1 hoq.1) (ir hsq.2.2 hoq.2)

private theorem re_phase (x : ℝ) : (phase x).re = Real.cos (2 * Real.pi * x) := by
  simp only [phase, Complex.exp_ofReal_mul_I_re]

theorem cos_sum_units {q m : ℕ} (hq : Squarefree q) (hm : m.Coprime q) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), Real.cos (2 * Real.pi * ((m:ℝ) * a / q)) =
      (ram q 1).re := by
  have : (ram q m).re = ∑ a ∈ (range q).filter (fun a => a.Coprime q), Real.cos (2 * Real.pi * ((m:ℝ) * a / q)) := by
    unfold ram
    rw [Complex.re_sum]
    exact sum_congr rfl fun a _ => re_phase _
  rw [← this, ram_unit q m hm]

theorem cosplus_lower {q n : ℕ} (hq : Squarefree q) (h1 : n.Coprime q) (h2 : (2*n).Coprime q) :
    ((q.totient:ℝ) - 3) / 4 ≤ ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      max (Real.cos (2 * Real.pi * ((n:ℝ) * a / q))) 0 := by
  set U := (range q).filter (fun a => a.Coprime q) with hU
  have hcard : (U.card : ℝ) = q.totient := by
    have : U.card = q.totient := by
      rw [Nat.totient_eq_card_coprime]
      congr 1
      ext a
      simp [hU, Nat.coprime_comm]
    exact_mod_cast this
  have hS1 := cos_sum_units hq h1
  have hS2 := cos_sum_units hq h2
  have hR : -1 ≤ (ram q 1).re ∧ (ram q 1).re ≤ 1 := by
    rcases ram_one_sign hq with h | h <;> simp [h]
  have hpt : ∀ a ∈ U, (Real.cos (2 * Real.pi * ((n:ℝ) * a / q)) +
      (1 + Real.cos (2 * Real.pi * (((2*n:ℕ):ℝ) * a / q))) / 2) / 2 ≤
      max (Real.cos (2 * Real.pi * ((n:ℝ) * a / q))) 0 := by
    intro a _
    set c := Real.cos (2 * Real.pi * ((n:ℝ) * a / q)) with hc
    have h2c : Real.cos (2 * Real.pi * (((2*n:ℕ):ℝ) * a / q)) = 2 * c^2 - 1 := by
      rw [hc, ← Real.cos_two_mul]
      congr 1
      push_cast; ring
    rw [h2c]
    have hc1 : -1 ≤ c := Real.neg_one_le_cos _
    have hc2 : c ≤ 1 := Real.cos_le_one _
    rcases le_total 0 c with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  calc
    _ ≤ ∑ a ∈ U, (Real.cos (2 * Real.pi * ((n:ℝ) * a / q)) +
      (1 + Real.cos (2 * Real.pi * (((2*n:ℕ):ℝ) * a / q))) / 2) / 2 := by
      rw [← sum_div, sum_add_distrib, ← sum_div, sum_add_distrib, hS1, hS2]
      simp only [sum_const, nsmul_eq_mul, mul_one, hcard]
      linarith [hR.1, hR.2]
    _ ≤ _ := sum_le_sum hpt



private theorem tele (J : ℕ) :
    ∑ j ∈ Icc 1 J, 1 / ((2 * (j:ℝ) + 1) ^ 2) ≤ 1 / 4 - 1 / (4 * ((J:ℝ) + 1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have key : 1 / ((2 * ((J+1:ℕ):ℝ) + 1) ^ 2) ≤ 1 / (4 * ((J:ℝ) + 1)) - 1 / (4 * (((J+1:ℕ):ℝ) + 1)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private theorem card_odd_mult (Q m : ℕ) (hm : 0 < m) :
    (((Icc 1 Q).filter (fun q => Odd q ∧ m * m ∣ q)).card : ℝ) ≤ ((Q:ℝ) / ((m:ℝ)^2) + 1) / 2 := by
  have hsub : (Icc 1 Q).filter (fun q => Odd q ∧ m * m ∣ q) ⊆
      (range ((Q / (m*m) + 1) / 2)).image (fun j => m * m * (2 * j + 1)) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨hq1, ho, ⟨c, hc⟩⟩ := hq
    have hc_odd : Odd c := by
      rw [hc] at ho
      exact (Nat.odd_mul.mp ho).2
    obtain ⟨j, hj⟩ := hc_odd
    simp only [mem_image, mem_range]
    refine ⟨j, ?_, by rw [hc, hj]⟩
    have hle : m * m * (2 * j + 1) ≤ Q := by rw [← hj, ← hc]; exact hq1.2
    have : 2 * j + 1 ≤ Q / (m*m) := (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith [mul_comm (2*j+1) (m*m)])
    omega
  have h1 := (card_le_card hsub).trans card_image_le
  rw [card_range] at h1
  have h2 : (((Q / (m*m) + 1) / 2 : ℕ) : ℝ) ≤ (((Q / (m*m) : ℕ) : ℝ) + 1) / 2 := by
    have : ((Q / (m*m) + 1) / 2 : ℕ) * 2 ≤ Q / (m*m) + 1 := Nat.div_mul_le_self _ _
    have : (((Q / (m*m) + 1) / 2 : ℕ) : ℝ) * 2 ≤ ((Q / (m*m) : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have h3 : ((Q / (m*m) : ℕ) : ℝ) ≤ (Q:ℝ) / ((m:ℝ)^2) := by
    rw [sq, ← Nat.cast_mul]
    exact Nat.cast_div_le
  calc _ ≤ (((Q / (m*m) + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2.trans (by linarith)


theorem count_S (s : ℕ) (hs : 40 ≤ s) :
    ((s*s : ℕ) : ℝ) / 5 ≤
      (((Icc 36 (s*s)).filter (fun q => Odd q ∧ Squarefree q)).card : ℝ) := by
  classical
  set Q := s * s with hQ
  set O := (Icc 1 Q).filter Odd with hO
  -- lower bound for odd numbers
  have hOcard : (Q + 1) / 2 ≤ O.card := by
    have : (range ((Q+1)/2)).card ≤ O.card := by
      apply card_le_card_of_injOn (fun j => 2 * j + 1)
      · intro j hj
        simp only [coe_range, Set.mem_Iio] at hj
        simp only [hO, coe_filter, mem_Icc, Set.mem_setOf_eq]
        refine ⟨⟨by omega, by omega⟩, ⟨j, rfl⟩⟩
      · intro i _ j _ h
        simp only at h
        omega
    simpa using this
  have hsplit : O.card = (O.filter Squarefree).card + (O.filter (fun q => ¬ Squarefree q)).card :=
    (card_filter_add_card_filter_not _).symm
  -- bound the non squarefree odd numbers
  have hB : (O.filter (fun q => ¬ Squarefree q)) ⊆
      (Icc 1 s).biUnion (fun j => (Icc 1 Q).filter (fun q => Odd q ∧ (2*j+1) * (2*j+1) ∣ q)) := by
    intro q hq
    simp only [mem_filter, hO, mem_Icc] at hq
    obtain ⟨⟨hq1, hqo⟩, hns⟩ := hq
    have : ∃ x, x * x ∣ q ∧ ¬ IsUnit x := by
      by_contra hcon
      push_neg at hcon
      exact hns hcon
    obtain ⟨x, hx, hxu⟩ := this
    have hxq : x ∣ q := (Dvd.intro x rfl).trans hx
    have hxo : Odd x := Odd.of_dvd_nat hqo hxq
    have hx1 : x ≠ 1 := fun h => hxu (by simp [h])
    have hx3 : 3 ≤ x := by
      obtain ⟨t, ht⟩ := hxo
      omega
    have hxq' : x * x ≤ q := Nat.le_of_dvd (by omega) hx
    have hxs : x ≤ s := by
      by_contra hh
      push_neg at hh
      have : s * s < x * x := Nat.mul_self_lt_mul_self hh
      omega
    obtain ⟨t, ht⟩ := hxo
    simp only [mem_biUnion, mem_Icc, mem_filter]
    refine ⟨t, ⟨by omega, by omega⟩, ⟨hq1, hqo, ?_⟩⟩
    rw [← ht]; exact hx
  have hBcard : ((O.filter (fun q => ¬ Squarefree q)).card : ℝ) ≤ (Q:ℝ) / 8 + (s:ℝ) / 2 := by
    have h1 := (card_le_card hB).trans card_biUnion_le
    have h2 : ((∑ j ∈ Icc 1 s, ((Icc 1 Q).filter (fun q => Odd q ∧ (2*j+1) * (2*j+1) ∣ q)).card : ℕ) : ℝ) ≤
        ∑ j ∈ Icc 1 s, (((Q:ℝ) / (((2*j+1 : ℕ):ℝ)^2) + 1) / 2) := by
      push_cast
      refine sum_le_sum fun j hj => ?_
      have := card_odd_mult Q (2*j+1) (by omega)
      push_cast at this
      exact this
    have h3 : ∑ j ∈ Icc 1 s, (((Q:ℝ) / (((2*j+1 : ℕ):ℝ)^2) + 1) / 2) =
        (Q:ℝ) / 2 * ∑ j ∈ Icc 1 s, 1 / ((2 * (j:ℝ) + 1) ^ 2) + (s:ℝ) / 2 := by
      rw [mul_sum]
      have : ∀ j ∈ Icc 1 s, (((Q:ℝ) / (((2*j+1 : ℕ):ℝ)^2) + 1) / 2) =
          (Q:ℝ) / 2 * (1 / ((2 * (j:ℝ) + 1) ^ 2)) + 1 / 2 := by
        intro j _
        push_cast
        field_simp
      rw [sum_congr rfl this, sum_add_distrib]
      simp
      ring
    have h4 := tele s
    have hQ0 : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
    have h5 : (Q:ℝ) / 2 * ∑ j ∈ Icc 1 s, 1 / ((2 * (j:ℝ) + 1) ^ 2) ≤ (Q:ℝ) / 2 * (1/4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (0:ℝ) ≤ 1 / (4 * ((s:ℝ) + 1)) := by positivity
      linarith
    have h6 : ((O.filter (fun q => ¬ Squarefree q)).card : ℝ) ≤
        ((∑ j ∈ Icc 1 s, ((Icc 1 Q).filter (fun q => Odd q ∧ (2*j+1) * (2*j+1) ∣ q)).card : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hS : (O.filter Squarefree).card ≤
      ((Icc 36 Q).filter (fun q => Odd q ∧ Squarefree q)).card + 35 := by
    have : O.filter Squarefree ⊆ ((Icc 36 Q).filter (fun q => Odd q ∧ Squarefree q)) ∪ Icc 1 35 := by
      intro q hq
      simp only [mem_filter, hO, mem_Icc, mem_union] at hq ⊢
      by_cases h36 : 36 ≤ q
      · left; exact ⟨⟨h36, hq.1.1.2⟩, hq.1.2, hq.2⟩
      · right; exact ⟨hq.1.1.1, by omega⟩
    refine (card_le_card this).trans ((card_union_le _ _).trans ?_)
    simp
  have hOr : (Q:ℝ) / 2 ≤ (O.card : ℝ) := by
    have : Q ≤ 2 * ((Q+1)/2) := by omega
    have h' : (Q:ℝ) ≤ 2 * (((Q+1)/2 : ℕ) : ℝ) := by exact_mod_cast this
    have h'' : (((Q+1)/2 : ℕ) : ℝ) ≤ (O.card : ℝ) := by exact_mod_cast hOcard
    linarith
  have hsplitR : (O.card : ℝ) = ((O.filter Squarefree).card : ℝ) + ((O.filter (fun q => ¬ Squarefree q)).card : ℝ) := by
    exact_mod_cast hsplit
  have hSR : ((O.filter Squarefree).card : ℝ) ≤
      (((Icc 36 Q).filter (fun q => Odd q ∧ Squarefree q)).card : ℝ) + 35 := by exact_mod_cast hS
  have hs' : (40:ℝ) ≤ s := by exact_mod_cast hs
  have hQs : (Q:ℝ) = (s:ℝ) * s := by rw [hQ]; push_cast; ring
  have : (Q:ℝ) / 5 ≤ (Q:ℝ) / 2 - ((Q:ℝ) / 8 + (s:ℝ) / 2) - 35 := by
    rw [hQs]; nlinarith
  linarith



def Sset (n : ℕ) : Finset ℕ := (Icc 36 (cutoff n)).filter (fun q => Odd q ∧ Squarefree q)

def selP (n q a : ℕ) : Prop := q ∈ Sset n ∧ 0 < Real.cos (2 * Real.pi * ((n:ℝ) * a / q))

theorem selP_two {n q a : ℕ} (h : selP n q a) : 2 ≤ q := by
  have h1 := (mem_Icc.mp (mem_filter.mp h.1).1).1
  omega

theorem re_Mint {n q a : ℕ} (hsq : Squarefree q) (ha : a.Coprime q) (h : ℝ) :
    (Mint n q a h).re = (1 / (q.totient:ℝ)^2) * Real.cos (2 * Real.pi * ((n:ℝ) * a / q)) * kernelMass n h := by
  unfold Mint
  have hU : unitMean q a ^ 2 = (((1 / (q.totient:ℝ)^2 : ℝ)) : ℂ) := by
    rw [unitMean_eq_ram ha]
    rcases ram_one_sign hsq with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
  rw [hU]
  have e : ((((1 / (q.totient:ℝ)^2 : ℝ)) : ℂ) * phase (-(n:ℝ) * center q a)) * (kernelMass n h : ℂ) =
      (((1 / (q.totient:ℝ)^2) * kernelMass n h : ℝ) : ℂ) * phase (-(n:ℝ) * center q a) := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul, re_phase]
  have : 2 * Real.pi * (-(n:ℝ) * center q a) = -(2 * Real.pi * ((n:ℝ) * a / q)) := by
    unfold center; ring
  rw [this, Real.cos_neg]
  ring

theorem per_q {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : q ∈ Sset n) (h1 : n.Coprime q)
    (h2 : (2*n).Coprime q) :
    (n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ)) ≤ (∑ a ∈ numerators q,
      (if selP n q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0)).re := by
  have hq' := mem_filter.mp hq
  obtain ⟨hqI, hqo, hsq⟩ := hq'
  obtain ⟨h36, hqQ⟩ := mem_Icc.mp hqI
  have hn0 : 0 < n := by omega
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hQ0 : (0:ℝ) < cutoff n := by exact_mod_cast (by omega : 0 < cutoff n)
  have hqQ' : (q:ℝ) ≤ cutoff n := by exact_mod_cast hqQ
  have hnum : numerators q = (range q).filter (fun a => a.Coprime q) := by
    ext a
    constructor
    · intro ha
      exact mem_filter.mpr ⟨mem_range.mpr (interior_order' (by omega) ha).2, (mem_filter.mp ha).2⟩
    · intro ha
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
  set w := width n q with hw
  have hw1 : 1 / (n:ℝ) ≤ w := by
    rw [hw, width, div_le_div_iff₀ hn' (by positivity)]
    nlinarith
  have hδ := delta_lower hn0 hw1
  set δ := kernelMass n w - kernelMass n (w/2) with hδdef
  have hφ : (6:ℝ) ≤ q.totient := by
    have := totient_sq_ge hsq hqo
    have h6 : 6 ≤ q.totient := by nlinarith
    exact_mod_cast h6
  have hφq : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ0 : (0:ℝ) < q.totient := by linarith
  have hterm : ∀ a ∈ numerators q,
      ((if selP n q a then Mint n q a w - Mint n q a (w / 2) else 0 : ℂ)).re =
        δ / (q.totient:ℝ)^2 * max (Real.cos (2 * Real.pi * ((n:ℝ) * a / q))) 0 := by
    intro a ha
    have hac : a.Coprime q := (mem_filter.mp ha).2
    by_cases hc : 0 < Real.cos (2 * Real.pi * ((n:ℝ) * a / q))
    · have hs : selP n q a := ⟨hq, hc⟩
      rw [if_pos hs, Complex.sub_re, re_Mint hsq hac, re_Mint hsq hac, max_eq_left hc.le, hδdef]
      ring
    · have hs : ¬ selP n q a := fun h => hc h.2
      rw [if_neg hs, max_eq_right (not_lt.mp hc)]
      simp
  rw [Complex.re_sum, sum_congr rfl hterm, ← mul_sum, hnum]
  have hcp := cosplus_lower (n := n) hsq h1 h2
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw1
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have hS : (q.totient:ℝ) / 8 ≤ ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      max (Real.cos (2 * Real.pi * ((n:ℝ) * a / q))) 0 := by linarith
  have hfin : 1 / (96 * Real.pi ^ 2 * (cutoff n:ℝ)) * n ≤ δ / (q.totient:ℝ)^2 * ((q.totient:ℝ) / 8) := by
    have hpi := Real.pi_pos
    have e1 : 1 / (12 * Real.pi ^ 2 * w) = (q:ℝ) * n / (12 * Real.pi^2 * cutoff n) := by
      rw [hw, width]; field_simp
    rw [e1] at hδ
    calc 1 / (96 * Real.pi ^ 2 * (cutoff n:ℝ)) * n = (q * n / (12 * Real.pi^2 * cutoff n)) / (8 * q) := by
          field_simp; ring
      _ ≤ (q * n / (12 * Real.pi^2 * cutoff n)) / (8 * q.totient) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ δ / (8 * q.totient) := div_le_div_of_nonneg_right hδ (by positivity)
      _ = _ := by field_simp
  calc
    (n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ)) = 1 / (96 * Real.pi ^ 2 * (cutoff n:ℝ)) * n := by ring
    _ ≤ _ := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)


theorem main_lower {n : ℕ} (hn : 2*(cutoff n)^2<n)
    (hcop : ∀ q, Odd q → n.Coprime q ∧ (2*n).Coprime q) (hlg : 40 ≤ Nat.log 2 (n+2)) :
    (n:ℝ) / (480 * Real.pi^2) - 2 * totalArcError n ≤
      ((∫ t in (0:ℝ)..1, (arcs n).indicator (integrand n) t) -
      ∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (if selP n q a then (1/2:ℝ) else 1) * (cutoff n:ℝ)/((q:ℝ)*(n:ℝ))}).indicator
          (integrand n) t).re := by
  have hd := diff_formula hn (selP n) (fun q a h => selP_two h)
  set X := ((∫ t in (0:ℝ)..1, (arcs n).indicator (integrand n) t) -
      ∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (if selP n q a then (1/2:ℝ) else 1) * (cutoff n:ℝ)/((q:ℝ)*(n:ℝ))}).indicator
          (integrand n) t) with hX
  set T : ℂ := ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q,
        (if selP n q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0) with hT
  have h1 : T.re - 2 * totalArcError n ≤ X.re := by
    have := Complex.abs_re_le_norm (X - T)
    rw [Complex.sub_re] at this
    have h2 := (abs_le.mp this).1
    linarith
  have hsub : Sset n ⊆ Icc 1 (cutoff n) := by
    intro q hq
    have := mem_Icc.mp (mem_filter.mp hq).1
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hTre : T.re = ∑ q ∈ Sset n, (∑ a ∈ numerators q,
        (if selP n q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0)).re := by
    rw [hT, Complex.re_sum]
    symm
    apply sum_subset hsub
    intro q hq hqS
    have : ∀ a, ¬ selP n q a := fun a h => hqS h.1
    simp [this]
  have hQ : cutoff n = Nat.log 2 (n+2) * Nat.log 2 (n+2) := by unfold cutoff; ring
  have hcnt := count_S (Nat.log 2 (n+2)) hlg
  rw [← hQ] at hcnt
  have hQpos : (0:ℝ) < cutoff n := by
    have : 1 ≤ cutoff n := cutoff_positive n
    exact_mod_cast this
  have hSum : ((Sset n).card : ℝ) * ((n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ))) ≤ T.re := by
    rw [hTre]
    have := card_nsmul_le_sum (Sset n) (fun q => (∑ a ∈ numerators q,
        (if selP n q a then Mint n q a (width n q) - Mint n q a (width n q / 2) else 0)).re)
      ((n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ))) (fun q hq => per_q hn hq (hcop q (mem_filter.mp hq).2.1).1 (hcop q (mem_filter.mp hq).2.1).2)
    simpa [nsmul_eq_mul] using this
  have hpi := Real.pi_pos
  have hfin : (n:ℝ) / (480 * Real.pi^2) ≤ ((Sset n).card : ℝ) * ((n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ))) := by
    have hc : (cutoff n : ℝ) / 5 ≤ (Sset n).card := hcnt
    calc (n:ℝ) / (480 * Real.pi^2) = ((cutoff n : ℝ) / 5) * ((n:ℝ) / (96 * Real.pi^2 * (cutoff n:ℝ))) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  linarith


theorem final_lower : ∃ N : ℕ, ∀ k ≥ N, ∃ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) ∧
    (1:ℝ) / (960 * Real.pi^2) * ((2^k : ℕ) : ℝ) ≤
      ((∫ t in (0:ℝ)..1, (arcs (2^k)).indicator (integrand (2^k)) t) -
      ∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff (2^k) ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ r q a * (cutoff (2^k):ℝ)/((q:ℝ)*((2^k : ℕ):ℝ))}).indicator
          (integrand (2^k)) t).re := by
  have hpi := Real.pi_pos
  have hsmall := totalArcError_sublinear.eventually_lt_const
    (show (0:ℝ) < 1 / (1920 * Real.pi^2) by positivity)
  have hev : ∀ᶠ n : ℕ in atTop, (2 * (cutoff n)^2 < n ∧ totalArcError n / n < 1 / (1920 * Real.pi^2)) ∧
      40 ≤ Nat.log 2 (n+2) := by
    refine (cutoff_separated.and hsmall).and ?_
    filter_upwards [eventually_ge_atTop (2^40)] with n hn
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hk : ∀ᶠ k : ℕ in atTop, (2 * (cutoff (2^k))^2 < 2^k ∧ totalArcError (2^k) / ((2^k : ℕ):ℝ) < 1 / (1920 * Real.pi^2)) ∧
      40 ≤ Nat.log 2 (2^k+2) :=
    (tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id).eventually hev
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hk
  refine ⟨max N0 1, fun k hk' => ?_⟩
  obtain ⟨⟨hsep, herr⟩, hlg⟩ := hN0 k (le_trans (le_max_left _ _) hk')
  have hcop : ∀ q, Odd q → (2^k).Coprime q ∧ (2*2^k).Coprime q := by
    intro q hq
    have h2 : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
    exact ⟨Nat.Coprime.pow_left k h2, Nat.Coprime.mul_left h2 (Nat.Coprime.pow_left k h2)⟩
  refine ⟨fun q a => if selP (2^k) q a then (1/2:ℝ) else 1, fun q a => ?_, ?_⟩
  · show (1/2:ℝ) ≤ (if selP (2^k) q a then (1/2:ℝ) else 1) ∧ (if selP (2^k) q a then (1/2:ℝ) else 1) ≤ 2
    split_ifs <;> constructor <;> norm_num
  · have hm := main_lower hsep hcop hlg
    have hnpos : (0:ℝ) < ((2^k : ℕ):ℝ) := by positivity
    have := (div_lt_iff₀ hnpos).mp herr
    have h3 : (1:ℝ) / (960 * Real.pi^2) * ((2^k : ℕ) : ℝ) =
        ((2^k : ℕ):ℝ) / (480 * Real.pi^2) - ((2^k : ℕ):ℝ) / (960 * Real.pi^2) := by
      field_simp; ring
    have h4 : 2 * totalArcError (2^k) ≤ ((2^k : ℕ):ℝ) / (960 * Real.pi^2) := by
      have : totalArcError (2^k) < 1 / (1920 * Real.pi^2) * ((2^k : ℕ):ℝ) := this
      have e : 1 / (1920 * Real.pi^2) * ((2^k : ℕ):ℝ) = ((2^k : ℕ):ℝ) / (960 * Real.pi^2) / 2 := by
        field_simp; ring
      linarith
    exact le_trans (by linarith) hm


theorem arcs_eq (n : ℕ) : arcs n = {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ 1 * (cutoff n:ℝ)/((q:ℝ)*(n:ℝ))} := by
  ext t
  simp [arcs]

end
end MajorDilationRefute

theorem Conjectures.Goldbach.MajorDilationOscillationRefute :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let A := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let M := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => (intervalIntegral (fun t => (A n r).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) → |M n r - M n (fun _ _ => 1)| ≤ ε*(n:ℝ)) := by
  intro h
  obtain ⟨N0, hN0⟩ := MajorDilationRefute.final_lower
  have hpi := Real.pi_pos
  obtain ⟨N, hN⟩ := h (1 / (1920 * Real.pi^2)) (by positivity)
  set k := max (max N0 N) 1 with hk
  have hk1 : N0 ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk2 : N ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk3 : 1 ≤ k := le_max_right _ _
  obtain ⟨r, hr, hlow⟩ := hN0 k hk1
  have hge : 2^k ≥ N := le_trans hk2 (Nat.lt_two_pow_self (n := k)).le
  have heven : Even (2^k) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hmain := hN (2^k) hge heven r hr
  have hmain' : |(∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff (2^k) ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ r q a * (cutoff (2^k):ℝ)/((q:ℝ)*((2^k : ℕ):ℝ))}).indicator
          (integrand (2^k)) t).re -
      (∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff (2^k) ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ 1 * (cutoff (2^k):ℝ)/((q:ℝ)*((2^k : ℕ):ℝ))}).indicator
          (integrand (2^k)) t).re| ≤ 1 / (1920 * Real.pi^2) * ((2^k : ℕ):ℝ) := hmain
  rw [← MajorDilationRefute.arcs_eq] at hmain'
  rw [Complex.sub_re] at hlow
  have hnpos : (0:ℝ) < ((2^k : ℕ):ℝ) := by positivity
  have h1 := (abs_le.mp hmain').1
  have h2 : (1:ℝ) / (1920 * Real.pi^2) * ((2^k : ℕ):ℝ) < 1 / (960 * Real.pi^2) * ((2^k : ℕ):ℝ) := by
    apply mul_lt_mul_of_pos_right _ hnpos
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  linarith
