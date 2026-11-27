import Mathlib
import Conjectures.Goldbach.MajorFixed144

/-! The arc separation and model approximation adapt the Apache-2.0 proofs
`MajorFixed144` (#3120) and `MajorDenominatorDilation` (7b62fec45f0b516900d568fbdf819753cf17373a).
The radius here varies independently at each reduced fraction. -/
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc
open Finset Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section

namespace GoldbachNumeratorDilation

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

def width (r : ℕ → ℕ → ℝ) (n q a : ℕ) : ℝ :=
  r q a * (cutoff n : ℝ) / ((q : ℝ) * n)

theorem width_eq (r : ℕ → ℕ → ℝ) (n q a : ℕ) :
    width r n q a = r q a * Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width n q := by
  unfold width Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width
  ring

theorem width_nonneg (r : ℕ → ℕ → ℝ) (hr : ∀ q a, 0 ≤ r q a) (n q a : ℕ) : 0 ≤ width r n q a := by
  rw [width_eq]; exact mul_nonneg (hr q a) (by unfold Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width; positivity)

theorem width_le_twice (r : ℕ → ℕ → ℝ) (hr : ∀ q a, r q a ≤ 2) (n q a : ℕ) :
    width r n q a ≤ 2 * (cutoff n : ℝ) / ((q : ℝ) * n) := by
  unfold width
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hr q a) (by positivity)) (by positivity)

def arcs (r : ℕ → ℕ → ℝ) (n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - center q a| ≤ width r n q a}

def wideWidth (n q : ℕ) : ℝ := 2 * (cutoff n : ℝ) / ((q : ℝ) * n)

theorem wideWidth_nonneg (n q : ℕ) : 0 ≤ wideWidth n q := by
  unfold wideWidth; positivity

def totalWideError (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ range (q+1),
     ∫ β in -(wideWidth n q)..wideWidth n q, modelError n q a β

def window (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width ρ n q a) (center q a + width ρ n q a)
def leftEnd (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) : ℝ := max (center q a - width ρ n q a) 0 - center q a
def rightEnd (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) : ℝ := min (center q a + width ρ n q a) 1 - center q a

theorem cutoff_separated : ∀ᶠ n : ℕ in atTop, 4 * (cutoff n)^2 < n := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^4 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop (2 : ℕ), h.eventually_lt_const (by norm_num : (0:ℝ) < 1/1024)] with n hn hl
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl' := (div_lt_iff₀ hn').mp hl
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 2
  have h' : 4 * (cutoff n : ℝ)^2 < n := by nlinarith only [hb, hl']
  exact_mod_cast h'

theorem mem_window (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) (t : ℝ) : t ∈ window ρ n q a ↔ |t - center q a| ≤ width ρ n q a := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n q r a b : ℕ} {t : ℝ} (hn : 4 * (cutoff n)^2 < n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : t ∈ window ρ n q a) (hb : t ∈ window ρ n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let Q := cutoff n
  have hsmall : 2 * Q * r + 2 * Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left (2 * Q) hrQ, Nat.mul_le_mul_left (2 * Q) hqQ]
  have hradii : 2 * (Q : ℝ) / (q*n) + 2 * Q/(r*n) < 1/(q*r) := calc
    _ = (2*(Q : ℝ)*r+2*Q*q)/(q*r*n) := by field_simp
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
  have h₁ := (mem_window ρ n q a t).mp ha
  have h₂ := (mem_window ρ n r b t).mp hb
  have h₁' := h₁.trans (width_le_twice ρ hρ₂ n q a)
  have h₂' := h₂.trans (width_le_twice ρ hρ₂ n r b)
  change |t-(a:ℝ)/q| ≤ 2*(Q:ℝ)/(q*n) at h₁'
  change |t-(b:ℝ)/r| ≤ 2*(Q:ℝ)/(r*n) at h₂'
  linarith

private theorem center_unique (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n q r a b : ℕ} {t : ℝ} (hn : 4*(cutoff n)^2<n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window ρ n q a) (htb : t ∈ window ρ n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap ρ hρ₂ hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) (t : ℝ) :
    (arcs ρ n).indicator (integrand n) t =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (window ρ n q a).indicator (integrand n) t := by
  classical
  by_cases ht : t ∈ arcs ρ n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window ρ n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window ρ n q b).indicator (integrand n) t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique ρ hρ₂ hn hr hq hb ha' ht' hw).1) _
      _ = (window ρ n q a).indicator (integrand n) t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique ρ hρ₂ hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window ρ n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width ρ n q a ≤ leftEnd ρ n q a ∧ leftEnd ρ n q a ≤ rightEnd ρ n q a ∧ rightEnd ρ n q a ≤ width ρ n q a := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg ρ hρ₀ n q a
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width ρ n q a) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width ρ n q a) 1]

theorem indicator_clipped (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window ρ n q a).indicator F t) =
    ∫ β in leftEnd ρ n q a..rightEnd ρ n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order ρ hρ₀ (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width ρ n q a) 0 ≤ min (center q a+width ρ n q a) 1),
    ← integral_Icc_eq_integral_Ioc]

def majorContribution (ρ : ℕ → ℕ → ℝ) (n : ℕ) : ℂ := ∫ t in (0:ℝ)..1, (arcs ρ n).indicator (integrand n) t
def actualPiece (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) : ℂ := ∫ β in leftEnd ρ n q a..rightEnd ρ n q a, integrand n (center q a+β)

theorem major_split (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) : majorContribution ρ n =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, actualPiece ρ n q a := by
  have hcont := continuous_integrand n
  have hInt (q a : ℕ) : IntervalIntegrable ((window ρ n q a).indicator (integrand n)) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold majorContribution
  simp_rw [arc_indicator_sum ρ hρ₂ hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped ρ hρ₀ (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩
def modelPoint (n q a : ℕ) (β : ℝ) : ℂ :=
  (unitMean q a * kernel n β)^2 * phase (-(n:ℝ) * (center q a + β))

def modelPiece (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n:ℝ)*center q a)) *
    ((∫ β in leftEnd ρ n q a..rightEnd ρ n q a, ‖kernel n β‖^2 : ℝ) : ℂ)

theorem model_piece_eq (ρ : ℕ → ℕ → ℝ) (n q a : ℕ) :
    (∫ β in leftEnd ρ n q a..rightEnd ρ n q a, modelPoint n q a β) = modelPiece ρ n q a := by
  have h (β : ℝ) : modelPoint n q a β =
      (unitMean q a ^2 * phase (-(n:ℝ)*center q a)) * ((‖kernel n β‖^2 : ℝ) : ℂ) := by
    rw [modelPoint, ← kernel_square_twist, mul_add, phase_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rfl

private theorem error_cont (n q a : ℕ) :
    Continuous (fun β => integrand n (center q a+β) - modelPoint n q a β) := by
  unfold integrand modelPoint primeSum kernel phase
  fun_prop

theorem piece_error_le (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    ‖actualPiece ρ n q a - modelPiece ρ n q a‖ ≤ ∫ β in -(width ρ n q a)..width ρ n q a, modelError n q a β := by
  have hi : Continuous (fun β => integrand n (center q a+β)) := by unfold integrand primeSum phase; fun_prop
  have hm : Continuous (modelPoint n q a) := by unfold modelPoint kernel phase; fun_prop
  have ⟨hl,hord,hr⟩ := clipped_order ρ hρ₀ (n := n) hq ha
  rw [actualPiece, ← model_piece_eq ρ, ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm hord).trans
  exact intervalIntegral.integral_mono_interval hl hord hr (Eventually.of_forall fun _ => norm_nonneg _)
    ((error_cont n q a).norm.intervalIntegrable _ _)

theorem width_le_unit (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n q a : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 0<q) :
    width ρ n q a ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : 2 * cutoff n ≤ n := by nlinarith [cutoff_positive n]
  calc
    width ρ n q a ≤ 2 * (cutoff n:ℝ) / ((q:ℝ)*n) := width_le_twice ρ hρ₂ n q a
    _ = ((2 * (cutoff n:ℝ))/n)/q := by ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2) {n q a : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd ρ n q a = -(width ρ n q a) ∧ rightEnd ρ n q a = width ρ n q a := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit ρ hρ₂ (a := a) hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem denom_one_phase (n : ℕ) : phase (-(n:ℝ)) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
  push_cast
  ring

private theorem norm_kernel_neg (n : ℕ) (t : ℝ) : ‖kernel n (-t)‖ = ‖kernel n t‖ := by
  have hphase (x : ℝ) : phase (-x) = conj (phase x) := by
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have h : kernel n (-t) = conj (kernel n t) := by
    unfold kernel
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_neg, hphase])
  rw [h, Complex.norm_conj]

theorem kernel_half_mass (n : ℕ) (b : ℝ) :
    (∫ t in (0 : ℝ)..b, ‖kernel n t‖ ^ 2) = kernelMass n b / 2 := by
  have hneg : (∫ t in -b..(0 : ℝ), ‖kernel n t‖ ^ 2) = ∫ t in (0 : ℝ)..b, ‖kernel n t‖ ^ 2 := by
    simpa only [neg_zero, norm_kernel_neg] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := b) (fun t => ‖kernel n t‖ ^ 2)).symm
  have hcont : Continuous (fun t => ‖kernel n t‖ ^ 2) := (continuous_kernel n).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-b) 0) (hcont.intervalIntegrable 0 b)
  unfold kernelMass
  linarith

/-- The boundary fractions at 0 and 1 contribute one half of their own symmetric kernel masses. -/
theorem endpoint_models (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) (hρ₂ : ∀ q a, ρ q a ≤ 2)
    {n : ℕ} (hn : 4*(cutoff n)^2<n) :
    (∑ a ∈ numerators 1, modelPiece ρ n 1 a) =
      ((kernelMass n (width ρ n 1 0) + kernelMass n (width ρ n 1 1)) / 2 : ℝ) := by
  let w₀ := width ρ n 1 0
  let w₁ := width ρ n 1 1
  have hw₀ : 0 ≤ w₀ := width_nonneg ρ hρ₀ _ _ _
  have hw₁ : 0 ≤ w₁ := width_nonneg ρ hρ₀ _ _ _
  have hw₀' : w₀ ≤ 1 := by simpa [w₀] using width_le_unit ρ hρ₂ (a := 0) hn (by decide : 0<1)
  have hw₁' : w₁ ≤ 1 := by simpa [w₁] using width_le_unit ρ hρ₂ (a := 1) hn (by decide : 0<1)
  have h0 : leftEnd ρ n 1 0 = 0 ∧ rightEnd ρ n 1 0 = w₀ := by
    change max (0/(1:ℝ)-w₀) 0 - 0/1 = 0 ∧ min (0/1+w₀) 1 - 0/1 = w₀
    simp [hw₀,hw₀']
  have h1 : leftEnd ρ n 1 1 = -w₁ ∧ rightEnd ρ n 1 1 = 0 := by
    change max (1/(1:ℝ)-w₁) 0 - 1/1 = -w₁ ∧ min (1/1+w₁) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp), ram_one]; simp
  have hneg : (∫ t in -w₁..(0 : ℝ), ‖kernel n t‖ ^ 2) = kernelMass n w₁ / 2 := by
    calc
      _ = (∫ t in (0 : ℝ)..w₁, ‖kernel n t‖ ^ 2) := by
        simpa only [neg_zero, norm_kernel_neg] using
          (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := w₁) (fun t => ‖kernel n t‖ ^ 2)).symm
      _ = _ := kernel_half_mass n w₁
  have hnSet : numerators 1 = {0,1} := by decide
  rw [hnSet]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2,hu,
    center, Nat.cast_zero,Nat.cast_one,div_one,mul_zero,mul_one,one_pow,one_mul,denom_one_phase,
    kernel_half_mass, hneg]
  have hz : phase 0=1 := by simp [phase]
  rw [hz,one_mul,← Complex.ofReal_add]
  change ((kernelMass n w₀ / 2 + kernelMass n w₁ / 2 : ℝ) : ℂ) =
    ((kernelMass n w₀ + kernelMass n w₁) / 2 : ℝ)
  norm_cast
  ring

theorem modelPiece_interior (ρ : ℕ → ℕ → ℝ) (hρ₂ : ∀ q a, ρ q a ≤ 2)
    {n q a : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 1<q) (ha : a ∈ numerators q) :
    modelPiece ρ n q a = (unitMean q a ^ 2 * phase (-(n:ℝ)*center q a)) *
      (kernelMass n (width ρ n q a) : ℂ) := by
  obtain ⟨hl,hr⟩ := uncut ρ hρ₂ hn hq ha
  simp only [modelPiece,hl,hr,kernelMass]

def modeledContribution (ρ : ℕ → ℕ → ℝ) (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, modelPiece ρ n q a

/-- The indicator integral differs from the sum of the clipped rational models by at most
the aggregate error on the widest allowed arcs. -/
theorem major_error (ρ : ℕ → ℕ → ℝ) (hρ₀ : ∀ q a, 0 ≤ ρ q a) (hρ₂ : ∀ q a, ρ q a ≤ 2)
    {n : ℕ} (hn : 4*(cutoff n)^2<n) :
    ‖majorContribution ρ n - modeledContribution ρ n‖ ≤ totalWideError n := by
  rw [major_split ρ hρ₀ hρ₂ hn, modeledContribution, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold totalWideError
  apply sum_le_sum
  intro q hq
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ numerators q, ∫ β in -(width ρ n q a)..width ρ n q a, modelError n q a β :=
      sum_le_sum fun a ha => piece_error_le ρ hρ₀ (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
    _ ≤ ∑ a ∈ numerators q,
          ∫ β in -(wideWidth n q)..wideWidth n q, modelError n q a β := by
      refine sum_le_sum fun a _ => ?_
      have hle := width_le_twice ρ hρ₂ n q a
      exact intervalIntegral.integral_mono_interval (neg_le_neg hle)
        (by linarith [width_nonneg ρ hρ₀ n q a]) hle
        (Eventually.of_forall fun _ => norm_nonneg _)
        ((error_cont n q a).norm.intervalIntegrable _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [wideWidth_nonneg n q]) fun _ _ => norm_nonneg _


end GoldbachNumeratorDilation

namespace GoldbachNumeratorDilation

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight (n : ℕ) :
    ∑ k ∈ range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
  rfl

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem wide_rational_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ 2 * (cutoff n : ℝ) / ((q : ℝ) * n)) :
    ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((2 * (cutoff n : ℝ)) / q)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ (2 * (cutoff n : ℝ)) / q := by
    apply (le_div_iff₀ hq').mpr
    calc
      _ = |β| * ((q : ℝ) * n) := by ring
      _ ≤ _ := (le_div_iff₀ (mul_pos hq' hn')).mp hβ
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) :=
    (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) _ _)
  refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply add_le_add_right
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem wide_squared_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ 2 * (cutoff n : ℝ) / ((q : ℝ) * n)) :
    let r : ℝ := (a : ℝ) / q
    let A := unitMean q a
    ‖integrand n (r + β) - (A * kernel n β) ^ 2 * phase (-(n : ℝ) * (r + β))‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * ((2 * (cutoff n : ℝ)) / q)) *
        (Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ)) := by
  intro r A
  have hsum : ‖primeSum n (r + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase]
  have hplus : ‖primeSum n (r + β) + A * kernel n β‖ ≤ Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ) := by
    refine (norm_add_le _ _).trans (add_le_add hsum ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  unfold integrand
  rw [← sub_mul, norm_mul, norm_phase, mul_one,
    show (primeSum n (r + β)) ^ 2 - (A * kernel n β) ^ 2 =
      (primeSum n (r + β) - A * kernel n β) * (primeSum n (r + β) + A * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul (wide_rational_arc_error (a := a) hn hq hβ) hplus (norm_nonneg _)
    ((norm_nonneg _).trans (wide_rational_arc_error (a := a) hn hq hβ))

private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

private theorem integral_error_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ cutoff n)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(wideWidth n q)..(wideWidth n q), modelError n q a β) ≤
      4 * (cutoff n : ℝ) ^ 2 * E * ((1 + 4 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ wideWidth n q := by unfold wideWidth; positivity
  have hlength : wideWidth n q ≤ (2 * (cutoff n : ℝ)) / n := by
    unfold wideWidth
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(wideWidth n q)) (wideWidth n q)) :
      modelError n q a β ≤ B := by
    have hp' := wide_squared_arc_error (a := a) hn hq (abs_le.mpr hβ)
    rw [show 1 + 2 * Real.pi * ((2 * (cutoff n : ℝ)) / q) =
      1 + 4 * Real.pi * ((cutoff n : ℝ) / q) by ring] at hp'
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) ≤
        E * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 4 * Real.pi * cutoff n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a) := by
    unfold modelError integrand primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(wideWidth n q)..(wideWidth n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * wideWidth n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((2 * (cutoff n : ℝ)) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp; ring

private theorem totalWideError_nonneg (n : ℕ) : 0 ≤ totalWideError n := by
  refine sum_nonneg fun q _ => sum_nonneg fun a _ => ?_
  have hw : 0 ≤ wideWidth n q := by unfold wideWidth; positivity
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _

/-- The aggregate integral error made by the rational models is o(n) for the exact
logarithmic cutoff, with their denominators, widths and both endpoints retained. -/
theorem totalWideError_sublinear : Tendsto (fun n : ℕ => totalWideError n / n) atTop (𝓝 0) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error
  let C : ℝ := 8 * ((1 + 4 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving M).const_mul (C * 16 ^ 4)
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (totalWideError_nonneg n) (Nat.cast_nonneg n)) _ hlimit
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ), hl.eventually_ge_atTop 1] with n hp hn hL
  change (1 : ℝ) ≤ Real.log n at hL
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff n := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)).ne')
  have hQ' : (1 : ℝ) ≤ cutoff n := by exact_mod_cast hQ1
  have hE : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  let B : ℝ := 4 * (cutoff n : ℝ) ^ 2 * errorEnvelope M n * ((1 + 4 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalWideError n ≤ C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by
    unfold totalWideError
    calc
      _ ≤ ∑ _q ∈ Icc 1 (cutoff n), (((cutoff n : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C]; ring
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 4
  have hlpow : (Real.log n) ^ 8 ≤ (Real.log n) ^ 10 :=
    pow_le_pow_right₀ hL (by decide)
  have hcomp : (cutoff n : ℝ) ^ 4 ≤ 16 ^ 4 * (Real.log n) ^ 10 := by
    calc
      _ ≤ _ := hpow
      _ = 16 ^ 4 * (Real.log n) ^ 8 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlpow (by norm_num)
  calc
    _ ≤ (C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n) / n :=
      div_le_div_of_nonneg_right htot (Nat.cast_nonneg _)
    _ ≤ (C * (16 ^ 4 * (Real.log n) ^ 10) * errorEnvelope M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) hE) (Nat.cast_nonneg _)
    _ = _ := by ring

end GoldbachNumeratorDilation

/-!
Kernel mass estimates adapted from the Apache-2.0 proof of
`L-goldbach-major-denominator-dilation` in goldbach-proofs PR #3678. The Parseval argument
there adapts `L-goldbach-continuous-parseval`.
-/

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

namespace NumeratorDilationKernelHalfMass

noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def kernel (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * t)

def mass (n : ℕ) (b : ℝ) : ℝ := ∫ t in -b..b, ‖kernel n t‖ ^ 2

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private theorem kernel_centered_cos {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : |t| ≤ 1 / (2 * (n : ℝ))) :
    ((n : ℝ) + 1) * Real.cos (Real.pi * (n : ℝ) * t) ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht' : 0 ≤ |t| := abs_nonneg _
  have hpi' : 0 ≤ Real.pi := Real.pi_pos.le
  have hcut : |Real.pi * (n : ℝ) * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hpi' hn'.le)]
    have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg hpi' hn'.le)
    convert hh using 1
    field_simp
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      Real.cos (Real.pi * (n : ℝ) * t) ≤ (phase (((k : ℝ) - (n : ℝ)/2) * t)).re := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp (mem_range.mp hk))
    have hb : |(k : ℝ) - (n : ℝ)/2| ≤ (n : ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have harg : |2 * Real.pi * (((k : ℝ) - (n : ℝ)/2) * t)| ≤ |Real.pi * (n : ℝ) * t| := by
      simp only [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num),
        abs_of_nonneg hpi', abs_of_nonneg hn'.le]
      calc
        _ ≤ (2 * Real.pi) * ((n : ℝ)/2 * |t|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb ht') (by positivity)
        _ = _ := by ring
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs (Real.pi * (n : ℝ) * t),
      ← Real.cos_abs (2 * Real.pi * (((k : ℝ) - (n : ℝ)/2) * t))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hrotate (k : ℕ) : phase (((k : ℝ) - (n : ℝ)/2) * t) =
      phase (-(n : ℝ)/2 * t) * phase ((k : ℝ) * t) := by
    rw [← phase_add]
    congr 1
    ring
  calc
    _ = ∑ _k ∈ range (n + 1), Real.cos (Real.pi * (n : ℝ) * t) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (n + 1), (phase (((k : ℝ) - (n : ℝ)/2) * t)).re := sum_le_sum hterm
    _ = (phase (-(n : ℝ)/2 * t) * kernel n t).re := by
      simp only [hrotate, kernel, mul_sum, Complex.re_sum]
    _ ≤ ‖phase (-(n : ℝ)/2 * t) * kernel n t‖ := Complex.re_le_norm _
    _ = _ := by rw [norm_mul, phase_norm, one_mul]

private theorem cos_mass {n : ℕ} (hn : 0 < n) :
    (∫ t in -(1 / (2 * (n : ℝ)))..(1 / (2 * (n : ℝ))), Real.cos (Real.pi * (n : ℝ) * t) ^ 2) =
      1 / (2 * (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let c : ℝ := Real.pi * (n : ℝ)
  let b : ℝ := 1 / (2 * (n : ℝ))
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hcb : c * b = Real.pi/2 := by dsimp [c,b]; field_simp
  have hcb' : c * -b = -(Real.pi/2) := by rw [mul_neg, hcb]
  have h := intervalIntegral.integral_comp_mul_left (a := -b) (b := b)
    (fun x : ℝ => Real.cos x ^ 2) hc
  change (∫ t in -b..b, Real.cos (c*t)^2) = b
  refine h.trans ?_
  rw [hcb, hcb', integral_cos_sq]
  simp only [Real.cos_pi_div_two, Real.cos_neg, zero_mul, sub_zero, sub_neg_eq_add, smul_eq_mul]
  dsimp [c,b]
  field_simp
  ring

theorem half_mass {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (2 * (n : ℝ)) ≤ b) :
    ((n : ℝ) + 1)/2 ≤ mass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let r : ℝ := 1 / (2 * (n : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hF : Continuous (fun t : ℝ => ‖kernel n t‖ ^ 2) := by
    unfold kernel phase
    fun_prop
  have hG : Continuous (fun t : ℝ => (((n : ℝ) + 1) * Real.cos (Real.pi * (n : ℝ) * t)) ^ 2) := by
    fun_prop
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-r) r) :
      (((n : ℝ) + 1) * Real.cos (Real.pi * (n : ℝ) * t)) ^ 2 ≤ ‖kernel n t‖ ^ 2 := by
    have ht' : |t| ≤ r := abs_le.mpr ht
    have hcut : |Real.pi * (n : ℝ) * t| ≤ Real.pi/2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg Real.pi_pos.le hn'.le)]
      calc
        _ ≤ (Real.pi * (n : ℝ)) * r := mul_le_mul_of_nonneg_left ht' (by positivity)
        _ = _ := by dsimp [r]; field_simp
    have hc : 0 ≤ Real.cos (Real.pi * (n : ℝ) * t) :=
      Real.cos_nonneg_of_mem_Icc (abs_le.mp hcut)
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) hc) (kernel_centered_cos hn ht') 2
  calc
    _ ≤ ((n : ℝ) + 1)^2 * r := by dsimp [r]; field_simp; nlinarith only [hn']
    _ = ∫ t in -r..r, (((n : ℝ) + 1) * Real.cos (Real.pi * (n : ℝ) * t)) ^ 2 := by
      simp_rw [mul_pow]
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (((n : ℝ) + 1)^2 * ·) (cos_mass hn).symm
    _ ≤ ∫ t in -r..r, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) (hG.intervalIntegrable _ _)
        (hF.intervalIntegrable _ _) hpoint
    _ ≤ mass n b :=
      intervalIntegral.integral_mono_interval (neg_le_neg hb) (by linarith) hb
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hF.intervalIntegrable _ _)

end
end NumeratorDilationKernelHalfMass

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

/- Parseval argument adapted from PEqualNP.Outside.L_goldbach_continuous_parseval in this repository. -/
namespace NumeratorDilationKernel

private theorem parseval_unit_interval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w (a : ℝ), intervalIntegral (fun t => ‖S n w t‖^2) a (a + 1) MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w a
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) a (a + 1) MeasureTheory.volume = _
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
      a (a + 1) MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        a (a + 1) MeasureTheory.volume =
        ∫ t in a..(a+1), Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
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
      have he : Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I *
          ((a + 1 : ℝ) : ℂ)) =
          Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I * (a : ℂ)) := by
        push_cast
        rw [mul_add, mul_one, Complex.exp_add, hphase_exp m, mul_one]
      rw [he, sub_self, zero_div, ite_eq_right hm]
  have hint_single : ∀ (c : ℂ) (u : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (u * t)) MeasureTheory.volume a (a + 1) := by
    intro c u
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable a (a + 1)
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
  have hint_z : IntervalIntegrable z MeasureTheory.volume a (a + 1) := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable a (a + 1)
  have hmain : intervalIntegral z a (a + 1) MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume a (a + 1) := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable a (a + 1)
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        a (a + 1) MeasureTheory.volume = ∑ j ∈ T,
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
          a (a + 1) MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) a (a + 1) MeasureTheory.volume =
      (intervalIntegral z a (a + 1) MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show a ≤ a + 1 by linarith, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) a (a + 1) MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) a (a + 1) MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z a (a + 1) MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _



private noncomputable def packet (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), parsevalPhase ((k : ℝ) * t)

private noncomputable def mass (n : ℕ) (b : ℝ) : ℝ :=
  ∫ t in -b..b, ‖packet n t‖^2

private theorem continuous_packet (n : ℕ) : Continuous (packet n) := by
  unfold packet parsevalPhase
  fun_prop

private theorem mass_half (n : ℕ) : mass n (1/2) = (n : ℝ) + 1 := by
  have h := parseval_unit_interval n (fun _ => 1) (-(1/2))
  norm_num only [Complex.ofReal_one, one_mul, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.card_range, Nat.cast_add, Nat.cast_one] at h
  exact h

private theorem norm_packet_neg (n : ℕ) (t : ℝ) : ‖packet n (-t)‖ = ‖packet n t‖ := by
  have h (x : ℝ) : parsevalPhase (-x) = conj (parsevalPhase x) := by
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hh : packet n (-t) = conj (packet n t) := by
    unfold packet
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_neg, h])
  rw [hh, Complex.norm_conj]

private theorem norm_packet_le_inv_of_chord (n : ℕ) {α t : ℝ}
    (hα : 0 < α * t) (hs : α * t ≤ Real.sin (Real.pi * t)) :
    ‖packet n t‖ ≤ 1 / (α * t) := by
  let z := parsevalPhase t
  have hnorm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  have hp (k : ℕ) : parsevalPhase ((k : ℝ) * t) = z ^ k := by
    dsimp [z, parsevalPhase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgeom : packet n t * (z - 1) = z ^ (n+1) - 1 := by
    unfold packet
    simp_rw [hp]
    exact geom_sum_mul z (n+1)
  have hz' : ‖z - 1‖ = ‖2 * Real.sin (Real.pi * t)‖ := by
    dsimp [z, parsevalPhase]
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    congr 3
    ring
  have hz : 2 * (α * t) ≤ ‖z - 1‖ := by
    rw [hz', Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hprod : ‖packet n t‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖z ^ (n+1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [hnorm, one_add_one_eq_two]
  have h := (mul_le_mul_of_nonneg_left hz (norm_nonneg (packet n t))).trans hprod
  apply (le_div_iff₀ hα).mpr
  have h' : 2 * (‖packet n t‖ * (α * t)) ≤ 2 := by
    convert h using 1
    ring
  linarith

private theorem norm_packet_le_inv (n : ℕ) {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1/2) :
    ‖packet n t‖ ≤ 1 / (2 * t) := by
  apply norm_packet_le_inv_of_chord n (by positivity)
  have hh := Real.mul_le_sin (mul_nonneg Real.pi_pos.le ht.le)
    (show Real.pi * t ≤ Real.pi / 2 by nlinarith [mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le])
  calc
    2 * t = 2 / Real.pi * (Real.pi * t) := by field_simp
    _ ≤ _ := hh

private theorem three_mul_le_sin_pi_mul {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/6) :
    3 * t ≤ Real.sin (Real.pi * t) := by
  have h := (StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc).2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show Real.pi/6 ∈ Set.Icc 0 Real.pi from
      ⟨by positivity, by linarith [Real.pi_pos]⟩)
    (show 0 ≤ 1 - 6*t by linarith) (show 0 ≤ 6*t by positivity)
    (show 1 - 6*t + 6*t = 1 by ring)
  have harg : (1 - 6*t) • (0 : ℝ) + (6*t) • (Real.pi/6) = Real.pi*t := by
    simp only [smul_eq_mul]
    ring
  rw [harg, Real.sin_zero, Real.sin_pi_div_six] at h
  calc
    3 * t = (1 - 6*t) • (0 : ℝ) + (6*t) • (1/2 : ℝ) := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      ring
    _ ≤ _ := h

private theorem packet_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
    (∫ t in b..(1/2 : ℝ), ‖packet n t‖^2) ≤ 1/(4*b) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc b (1/2) := by
    rw [Set.uIcc_of_le hhalf]
    exact fun h => (not_le_of_gt hb) h.1
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) MeasureTheory.volume b (1/2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hmono :
      (∫ t in b..(1/2 : ℝ), ‖packet n t‖^2) ≤ ∫ t in b..(1/2 : ℝ), (1/4 : ℝ) * t^(-2 : ℤ) := by
    apply intervalIntegral.integral_mono_on hhalf ((continuous_packet n).norm.pow 2 |>.intervalIntegrable _ _)
      (hint.const_mul _)
    intro t ht
    have ht0 := hb.trans_le ht.1
    calc
      _ ≤ (1/(2*t))^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_packet_le_inv n ht0 ht.2) 2
      _ = _ := by rw [zpow_neg]; field_simp; norm_num
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by decide, hzero⟩)]
  norm_num [zpow_neg]
  have hh : 0 < b⁻¹ := inv_pos.mpr hb
  ring_nf
  linarith

theorem mass_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
    ((n : ℝ) + 1) - 1/(2*b) ≤ mass n b := by
  have hint (x y : ℝ) : IntervalIntegrable (fun t => ‖packet n t‖^2) MeasureTheory.volume x y :=
    ((continuous_packet n).norm.pow 2).intervalIntegrable x y
  have hneg : (∫ t in (-(1/2) : ℝ)..-b, ‖packet n t‖^2) =
      ∫ t in b..(1/2 : ℝ), ‖packet n t‖^2 := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => ‖packet n t‖^2) (a := b) (b := (1/2 : ℝ))
    rw [← h]
    exact intervalIntegral.integral_congr (fun t _ => by rw [norm_packet_neg])
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hint (-(1/2)) (-b)) (hint (-b) b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hint (-(1/2)) b) (hint b (1/2))
  have h3 := mass_half n
  unfold mass at h3 ⊢
  rw [hneg] at h1
  have ht := packet_tail n hb hhalf
  have hc : (1 : ℝ) / (2*b) = 2 * (1/(4*b)) := by ring
  linarith

/-- The one-sided integral is half of the symmetric mass. -/
theorem mass_eq_two_integral (n : ℕ) (b : ℝ) :
    mass n b = 2 * ∫ t in 0..b, ‖packet n t‖^2 := by
  have hint (x y : ℝ) : IntervalIntegrable (fun t => ‖packet n t‖^2) volume x y :=
    ((continuous_packet n).norm.pow 2).intervalIntegrable x y
  have hneg : (∫ t in -b..0, ‖packet n t‖^2) = ∫ t in 0..b, ‖packet n t‖^2 := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => ‖packet n t‖^2) (a := 0) (b := b)
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun t _ => by rw [norm_packet_neg])
  unfold mass
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-b) 0) (hint 0 b), hneg]
  ring

/-- On a short annulus, bound the kernel by the chord from 0 to π/6. -/
theorem mass_variation (n : ℕ) {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) (hc : c ≤ 1/6) :
    mass n c - mass n b ≤ (2/9 : ℝ) * (1/b - 1/c) := by
  have hint (x y : ℝ) : IntervalIntegrable (fun t => ‖packet n t‖^2) volume x y :=
    ((continuous_packet n).norm.pow 2).intervalIntegrable x y
  have hzero : (0 : ℝ) ∉ Set.uIcc b c := by
    rw [Set.uIcc_of_le hbc]
    exact fun h => (not_le_of_gt hb) h.1
  have hinv : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) volume b c :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hmono : (∫ t in b..c, ‖packet n t‖^2) ≤ ∫ t in b..c, (1/9 : ℝ) * t^(-2 : ℤ) := by
    apply intervalIntegral.integral_mono_on hbc (hint b c) (hinv.const_mul _)
    intro t ht
    have ht0 := hb.trans_le ht.1
    have hsin := three_mul_le_sin_pi_mul ht0.le (ht.2.trans hc)
    calc
      _ ≤ (1/(3*t))^2 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_packet_le_inv_of_chord n (by positivity) hsin) 2
      _ = _ := by rw [zpow_neg]; field_simp; norm_num
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by decide, hzero⟩)] at hmono
  norm_num [zpow_neg] at hmono
  rw [mass_eq_two_integral, mass_eq_two_integral,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 b) (hint b c)]
  simp only [one_div, div_neg, div_one] at hmono ⊢
  linarith only [hmono]

/-- Uniform cap from the mass of the full symmetric fundamental interval. -/
theorem mass_upper (n : ℕ) {b : ℝ} (hb : 0 ≤ b) (hhalf : b ≤ 1/2) :
    mass n b ≤ (n : ℝ) + 1 := by
  rw [← mass_half]
  unfold mass
  exact intervalIntegral.integral_mono_interval (neg_le_neg hhalf) (by linarith) hhalf
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (((continuous_packet n).norm.pow 2).intervalIntegrable _ _)

end NumeratorDilationKernel

open Conjectures.Goldbach.MajorFixed144_aux

theorem NumeratorDilationKernel.kernelMass_upper (n : ℕ) {b : ℝ} (hb : 0 ≤ b) (hhalf : b ≤ 1/2) :
    GoldbachMajorArc.kernelMass n b ≤ (n : ℝ) + 1 :=
  NumeratorDilationKernel.mass_upper n hb hhalf

theorem NumeratorDilationKernel.kernelMass_half_mass {n : ℕ} (hn : 0 < n) {b : ℝ}
    (hb : 1 / (2 * (n : ℝ)) ≤ b) :
    ((n : ℝ) + 1)/2 ≤ GoldbachMajorArc.kernelMass n b :=
  NumeratorDilationKernelHalfMass.half_mass hn hb

theorem NumeratorDilationKernel.kernelMass_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
    ((n : ℝ) + 1) - 1/(2*b) ≤ GoldbachMajorArc.kernelMass n b :=
  NumeratorDilationKernel.mass_tail n hb hhalf

theorem NumeratorDilationKernel.kernelMass_variation (n : ℕ) {b c : ℝ}
    (hb : 0 < b) (hbc : b ≤ c) (hc : c ≤ 1/6) :
    GoldbachMajorArc.kernelMass n c - GoldbachMajorArc.kernelMass n b ≤
      (2/9 : ℝ) * (1/b - 1/c) :=
  NumeratorDilationKernel.mass_variation n hb hbc hc

namespace GoldbachNumeratorArithmetic

open Finset
open scoped BigOperators

noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by
  unfold badFactor
  positivity

private lemma product_sum_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1 + f i)) * (1 - ∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hs' : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hs
    have hp : 0 ≤ ∏ i ∈ s, (1 + f i) := prod_nonneg fun i hi => by linarith [hs i hi]
    rw [prod_insert has, sum_insert has, mul_comm (1 + f a), mul_assoc]
    apply le_trans (mul_le_mul_of_nonneg_left ?_ hp) (ih hs)
    nlinarith only [sq_nonneg (f a), mul_nonneg ha hs']

private def tailWeight (k : ℕ) : ℝ := 1 / (4 * ((k : ℝ) + 5) ^ 2)

private lemma tailWeight_nonneg (k : ℕ) : 0 ≤ tailWeight k := by
  unfold tailWeight
  positivity

private lemma tail_sum (m : ℕ) :
    (∑ k ∈ range m, tailWeight k) ≤ 1/16 - 1/(4*((m:ℝ)+4)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ]
    apply (add_le_add_left ih (tailWeight m)).trans
    unfold tailWeight
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have h₄ : 0 < (m : ℝ) + 4 := by linarith
    have h₅ : 0 < (m : ℝ) + 5 := by linarith
    have hstep : 1 / (4 * ((m : ℝ) + 5) ^ 2) ≤
        1 / (4 * ((m : ℝ) + 4) * ((m : ℝ) + 5)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [hm]
    have htel : 1 / (4 * ((m : ℝ) + 4) * ((m : ℝ) + 5)) =
        1 / (4 * ((m : ℝ) + 4)) - 1 / (4 * ((m : ℝ) + 5)) := by
      field_simp
      ring
    have he : (m : ℝ) + 1 + 4 = (m : ℝ) + 5 := by ring
    rw [htel] at hstep
    rw [he]
    linarith

private lemma tail_prod (m : ℕ) :
    (∏ k ∈ range m, (1 + tailWeight k)) ≤ (16/15 : ℝ) := by
  have hs : (∑ k ∈ range m, tailWeight k) ≤ 1/16 :=
    (tail_sum m).trans (sub_le_self _ (by positivity))
  have hp : 0 ≤ ∏ k ∈ range m, (1 + tailWeight k) :=
    prod_nonneg fun k _ => by linarith [tailWeight_nonneg k]
  have h := (mul_le_mul_of_nonneg_left (show (15/16:ℝ) ≤ 1 - ∑ k ∈ range m, tailWeight k by
    linarith) hp).trans (product_sum_bound (range m) tailWeight (fun k _ => tailWeight_nonneg k))
  linarith

private def tailPrime (k : ℕ) : ℕ := 2 * (k + 5) + 1

private lemma tailPrime_weight (k : ℕ) : badFactor (tailPrime k) = tailWeight k := by
  unfold badFactor tailPrime tailWeight
  push_cast
  congr 2
  ring

theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    (∏ p ∈ s, (1 + badFactor p)) ≤ (73/50 : ℝ) := by
  classical
  let base : Finset ℕ := {3, 5, 7}
  let m := s.sup id
  let U := (range m).image tailPrime
  have hinj : Function.Injective tailPrime := by
    intro a b hab
    unfold tailPrime at hab
    omega
  have hd : Disjoint base U := by
    rw [disjoint_left]
    intro p hp hp'
    obtain ⟨k, _, hk⟩ := mem_image.mp hp'
    have hk' : 11 ≤ tailPrime k := by unfold tailPrime; omega
    have hsmall : p = 3 ∨ p = 5 ∨ p = 7 := by simpa [base] using hp
    omega
  have hsub : s ⊆ base ∪ U := by
    intro p hp
    by_cases hb : p ∈ base
    · exact mem_union_left _ hb
    · apply mem_union_right
      have hpm : p ≤ m := Finset.le_sup (f := id) hp
      have hprime := (hs p hp).1
      have hgt := (hs p hp).2
      have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
      rcases (Nat.odd_iff.mpr hodd) with ⟨j, hj⟩
      have hp9 : p ≠ 9 := fun h => (show ¬ Nat.Prime 9 by decide) (h ▸ hprime)
      have hsmall : p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 := by simpa [base] using hb
      refine mem_image.mpr ⟨j-5, mem_range.mpr (by omega), ?_⟩
      unfold tailPrime
      omega
  calc
    _ ≤ ∏ p ∈ base ∪ U, (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (3145/2304 : ℝ) * ∏ p ∈ U, (1 + badFactor p) := by
      rw [prod_union hd]
      congr 1
      change (∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 + badFactor p)) = _
      rw [prod_insert (by decide), prod_insert (by decide), prod_singleton]
      norm_num [badFactor]
    _ = (3145/2304 : ℝ) * ∏ k ∈ range m, (1 + tailWeight k) := by
      rw [show U = (range m).image tailPrime by rfl, prod_image hinj.injOn]
      simp only [tailPrime_weight]
    _ ≤ (3145/2304 : ℝ) * (16/15) := mul_le_mul_of_nonneg_left (tail_prod m) (by norm_num)
    _ ≤ _ := by norm_num

theorem negative_block_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (M : ℝ) (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M) (d : ℕ) :
    W d - (23/50)*M ≤ ∑ t ∈ s.powerset,
      (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  classical
  let P := s.powerset.erase ∅
  have hM := (hW0 0).trans (hWM 0)
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have htotal : (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 23/50 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    have hprod := product_bad_factors hs
    change (∏ p ∈ s, (1 + badFactor p)) = (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 at h
    linarith
  have ht (t : Finset ℕ) (h : t ∈ P) :
      -(M * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hW0 _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hWM _) (prod_nonneg fun p _ => badFactor_nonneg p)
  have hsum := sum_le_sum ht
  simp only [sum_neg_distrib, ← mul_sum] at hsum
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  have hcap := mul_le_mul_of_nonneg_left htotal hM
  linarith

private def signedBlock (a W : ℕ → ℝ) (s : Finset ℕ) (d : ℕ) : ℝ :=
  ∑ t ∈ s.powerset, (∏ p ∈ t, a p) * W (d * ∏ p ∈ t, p)

private theorem signedBlock_vanish (a W : ℕ → ℝ) (s : Finset ℕ) {d Q : ℕ}
    (hs : ∀ p ∈ s, p.Prime) (hcut : ∀ q, Q < q → W q = 0) (hd : Q < d) :
    signedBlock a W s d = 0 := by
  unfold signedBlock
  apply sum_eq_zero
  intro t ht
  have hpos : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (mem_powerset.mp ht hp)).pos
  rw [hcut _ (hd.trans_le (Nat.le_mul_of_pos_right _ hpos)), mul_zero]

private theorem signedBlock_insert (a W : ℕ → ℝ) (s : Finset ℕ) {p d : ℕ} (hp : p ∉ s) :
    signedBlock a W (insert p s) d = signedBlock a W s d + a p * signedBlock a W s (d * p) := by
  unfold signedBlock
  rw [sum_powerset_insert hp, mul_sum]
  congr 1
  apply sum_congr rfl
  intro t ht
  have hpt : p ∉ t := fun h => hp (mem_powerset.mp ht h)
  rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (a p)]

private theorem signedBlock_lower (a W : ℕ → ℝ) (M : ℝ) (Q : ℕ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q)
    (G B : Finset ℕ) (hdj : Disjoint G B)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ a p = -badFactor p)
    (hG : ∀ p ∈ G, p.Prime ∧ 0 ≤ a p) (d : ℕ) (hd : 0 < d) :
    W d - (23/50)*M ≤ signedBlock a W (G ∪ B) d := by
  classical
  have hM := (hW0 0).trans (hWM 0)
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_block_lower (fun p hp => (hB p hp).1) W M hW0 hWM d).trans
    apply le_of_eq
    unfold signedBlock
    apply sum_congr rfl
    intro t ht
    congr 1
    exact prod_congr rfl fun p hp => (hB p (mem_powerset.mp ht hp)).2.symm
  | @insert p G hp ih =>
    have hpr := hG p (mem_insert_self _ _)
    have hGs : ∀ r ∈ G, r.Prime ∧ 0 ≤ a r := fun r hr => hG r (mem_insert_of_mem hr)
    have hdj' : Disjoint G B := hdj.mono_left (subset_insert ..)
    have hpB : p ∉ B := fun h => (Finset.disjoint_left.mp hdj) (mem_insert_self _ _) h
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hdp : 0 < d * p := Nat.mul_pos hd hpr.1.pos
    have hfirst := ih hdj' hGs d hd
    have hsecond : 0 ≤ signedBlock a W (G ∪ B) (d * p) := by
      by_cases hq : d * p ≤ Q
      · have hM' := hWmid (d*p) hdp hq
        linarith [ih hdj' hGs (d*p) hdp]
      · rw [signedBlock_vanish a W (G ∪ B) (fun r hr => by
          rcases mem_union.mp hr with hr | hr
          · exact (hGs r hr).1
          · exact (hB r hr).1.1) hcut (lt_of_not_ge hq)]
    rw [insert_union, signedBlock_insert a W (G ∪ B) hpGB]
    linarith [mul_nonneg hpr.2 hsecond]

private theorem badFactor_le_one {p : ℕ} (hp : 2 < p) : badFactor p ≤ 1 := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_of_lt hp)
  unfold badFactor
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  apply (div_le_iff₀ (pow_pos hp1 2)).2
  nlinarith only [hpr, sq_nonneg ((p : ℝ) - 3)]

private theorem shifted_tail_sum (K m : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ range m, 1 / (4 * ((k : ℝ) + K)^2)) ≤
      1 / (4 * ((K : ℝ) - 1)) - 1 / (4 * ((m : ℝ) + K - 1)) := by
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ]
    apply (add_le_add_left ih _).trans
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have h₁ : 0 < (m : ℝ) + K - 1 := by linarith
    have h₂ : 0 < (m : ℝ) + K := by linarith
    have hstep : 1 / (4 * ((m : ℝ) + K)^2) ≤
        1 / (4 * (((m : ℝ) + K) - 1) * ((m : ℝ) + K)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [h₂]
    have htel : 1 / (4 * (((m : ℝ) + K) - 1) * ((m : ℝ) + K)) =
        1 / (4 * ((m : ℝ) + K - 1)) - 1 / (4 * ((m : ℝ) + K)) := by
      field_simp
      ring
    rw [htel] at hstep
    rw [show (m : ℝ) + 1 + K - 1 = (m : ℝ) + K by ring]
    linarith

private theorem bad_tail_sum {s : Finset ℕ} (K : ℕ) (hK : 2 ≤ K)
    (hs : ∀ p ∈ s, Odd p ∧ 2*K+1 ≤ p) :
    (∑ p ∈ s, badFactor p) ≤ 1 / (4 * ((K : ℝ) - 1)) := by
  let f (k : ℕ) := 2 * (k + K) + 1
  let m := s.sup id
  have hf : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    omega
  have hsub : s ⊆ (range m).image f := by
    intro p hp
    obtain ⟨hod, hmin⟩ := hs p hp
    obtain ⟨j, hj⟩ := hod
    have hmax : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_image.mpr ⟨j-K, mem_range.mpr (by omega), by dsimp [f]; omega⟩
  have heq (k : ℕ) : badFactor (f k) = 1 / (4 * ((k : ℝ) + K)^2) := by
    unfold badFactor f
    push_cast
    congr 2
    ring
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (m : ℝ) + K - 1 := by linarith
  calc
    _ ≤ ∑ p ∈ (range m).image f, badFactor p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => badFactor_nonneg p)
    _ = ∑ k ∈ range m, 1 / (4 * ((k : ℝ) + K)^2) := by
      rw [sum_image hf.injOn]
      exact sum_congr rfl fun k _ => heq k
    _ ≤ _ := (shifted_tail_sum K m hK).trans (sub_le_self _ (by positivity))

private theorem signed_product_lower {s : Finset ℕ} (f : ℕ → ℝ)
    (hf : ∀ p ∈ s, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1-f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [sum_insert hp, prod_insert hp]
    have hp' := hf p (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    calc
      _ ≤ (1-f p) * (1 - ∑ i ∈ s, f i) := by
        nlinarith only [mul_nonneg hp'.1 (sum_nonneg fun i hi => (hs i hi).1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr hp'.2)

private theorem prime_product_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    (653/1000 : ℝ) ≤ ∏ p ∈ s, (1-badFactor p) := by
  let A : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
  let T := s \ A
  have hA (p : ℕ) (hp : p ∈ A) : 2 < p := by
    simp [A] at hp
    omega
  have hT (p : ℕ) (hp : p ∈ T) : 2 < p := (hs p (mem_sdiff.mp hp).1).2
  have hdis : Disjoint T A := sdiff_disjoint
  have hsub : s ⊆ T ∪ A := by
    intro p hp
    by_cases h : p ∈ A
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hp,h⟩)
  have htail (p : ℕ) (hp : p ∈ T) : Odd p ∧ 2*16+1 ≤ p := by
    obtain ⟨hps, hpA⟩ := mem_sdiff.mp hp
    obtain ⟨hprime, hpge⟩ := hs p hps
    have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
    have hn9 : p ≠ 9 := fun h => (show ¬ Nat.Prime 9 by decide) (h ▸ hprime)
    have hn15 : p ≠ 15 := fun h => (show ¬ Nat.Prime 15 by decide) (h ▸ hprime)
    have hn21 : p ≠ 21 := fun h => (show ¬ Nat.Prime 21 by decide) (h ▸ hprime)
    have hn25 : p ≠ 25 := fun h => (show ¬ Nat.Prime 25 by decide) (h ▸ hprime)
    have hn27 : p ≠ 27 := fun h => (show ¬ Nat.Prime 27 by decide) (h ▸ hprime)
    simp only [A, mem_insert, mem_singleton, not_or] at hpA
    exact ⟨Nat.odd_iff.mpr hodd, by omega⟩
  have hb := bad_tail_sum 16 (by decide) htail
  norm_num at hb
  have ht : (59/60 : ℝ) ≤ ∏ p ∈ T, (1-badFactor p) := by
    have h := signed_product_lower badFactor
      (fun p hp => ⟨badFactor_nonneg p, badFactor_le_one (hT p hp)⟩)
    linarith only [h, hb]
  have ha : ∏ p ∈ A, (1-badFactor p) = (42803602439 : ℝ)/64424509440 := by
    change (∏ p ∈ ({3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), (1-badFactor p)) = _
    rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton]
    norm_num [badFactor]
  calc
    _ ≤ (59/60 : ℝ) * ((42803602439 : ℝ)/64424509440) := by norm_num
    _ ≤ (∏ p ∈ T, (1-badFactor p)) * ∏ p ∈ A, (1-badFactor p) := by
      rw [ha]
      exact mul_le_mul_of_nonneg_right ht (by norm_num)
    _ = ∏ p ∈ T ∪ A, (1-badFactor p) := (prod_union hdis).symm
    _ ≤ _ := prod_le_prod_of_subset_of_le_one₀ hsub
      (fun p hp => sub_nonneg.mpr (badFactor_le_one (mem_union.mp hp |>.elim (hT p) (hA p))))
      (fun p _ _ => sub_le_self _ (badFactor_nonneg p))

/-- A fixed cutoff containing both 1 and 2 times every product of distinct
primes at most 1024. -/
def smallDenominatorCutoff : ℕ := 2 * 1025 ^ (Nat.succ 1024)

private theorem small_denominator_bound {s : Finset ℕ} (hs : ∀ p ∈ s, p ≤ 1024)
    {d : ℕ} (hd : d ≤ 2) : d * ∏ p ∈ s, p ≤ smallDenominatorCutoff := by
  have hsc : s.card ≤ 1025 := by
    have hsub : s ⊆ range 1025 := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hs p hp))
    simpa using card_le_card hsub
  have hp : ∏ p ∈ s, p ≤ 1025 ^ s.card :=
    prod_le_pow_card s id 1025 (fun p hp => (hs p hp).trans (by decide))
  unfold smallDenominatorCutoff
  have hpow : 1025 ^ s.card ≤ (1025 : ℕ) ^ (Nat.succ 1024) := Nat.pow_le_pow_right (by decide) hsc
  exact Nat.mul_le_mul hd (hp.trans hpow)

private theorem prime_tail_mass {s t : Finset ℕ} (hts : t ⊆ s)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (ht : ∀ p ∈ s, p ∉ t → 1024 < p) :
    (∑ u ∈ s.powerset \ t.powerset, ∏ p ∈ u, badFactor p) ≤ 1/1000 := by
  let U := s \ t
  have hU (p : ℕ) (hp : p ∈ U) : p.Prime ∧ 2 < p := hs p (mem_sdiff.mp hp).1
  have htail (p : ℕ) (hp : p ∈ U) : Odd p ∧ 2*512+1 ≤ p := by
    have hbig := ht p (mem_sdiff.mp hp).1 (mem_sdiff.mp hp).2
    exact ⟨Nat.odd_iff.mpr ((hU p hp).1.eq_two_or_odd.resolve_left (by omega)), by omega⟩
  have hsum := bad_tail_sum 512 (by decide) htail
  norm_num at hsum
  have hpU : 0 ≤ ∏ p ∈ U, (1+badFactor p) :=
    prod_nonneg (fun p _ => by linarith [badFactor_nonneg p])
  have hcap : (∏ p ∈ U, (1+badFactor p)) ≤ 2044/2043 := by
    have hb := product_sum_bound U badFactor (fun p _ => badFactor_nonneg p)
    have hm := (mul_le_mul_of_nonneg_left
      (show (2043/2044 : ℝ) ≤ 1 - ∑ p ∈ U, badFactor p by linarith only [hsum]) hpU).trans hb
    linarith only [hm]
  have hprod := product_bad_factors (fun p hp => hs p (hts hp))
  have hprod0 : 0 ≤ ∏ p ∈ t, (1+badFactor p) :=
    prod_nonneg (fun p _ => by linarith [badFactor_nonneg p])
  have heq : (∏ p ∈ U, (1+badFactor p)) * (∏ p ∈ t, (1+badFactor p)) =
      ∏ p ∈ s, (1+badFactor p) := prod_sdiff hts
  have hsub : t.powerset ⊆ s.powerset := fun u hu =>
    mem_powerset.mpr ((mem_powerset.mp hu).trans hts)
  have hspl := sum_sdiff (f := fun u => ∏ p ∈ u, badFactor p) hsub
  rw [← prod_one_add, ← prod_one_add, ← heq] at hspl
  have hmul := mul_le_mul_of_nonneg_right hcap hprod0
  nlinarith only [hspl, hprod, hmul]

private theorem signedBlock_small_lower (a W : ℕ → ℝ) (M : ℝ) (B : Finset ℕ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hsmall : ∀ q, 0 < q → q ≤ smallDenominatorCutoff → (999/1000 : ℝ)*M ≤ W q)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ a p = -badFactor p)
    {d : ℕ} (hd : 0 < d) (hd' : d ≤ 2) :
    (13/20 : ℝ) * M ≤ signedBlock a W B d := by
  let S := B.filter (fun p => p ≤ 1024)
  let v (t : Finset ℕ) := ∏ p ∈ t, a p
  let b (t : Finset ℕ) := ∏ p ∈ t, badFactor p
  let q (t : Finset ℕ) := d * ∏ p ∈ t, p
  have hM := (hW0 0).trans (hWM 0)
  have hS : S ⊆ B := filter_subset _ _
  have hPS : S.powerset ⊆ B.powerset := fun t ht =>
    mem_powerset.mpr ((mem_powerset.mp ht).trans hS)
  have habs (t : Finset ℕ) (ht : t ∈ B.powerset) : |v t| = b t := by
    unfold v b
    rw [Finset.abs_prod]
    apply prod_congr rfl
    intro p hp
    rw [(hB p (mem_powerset.mp ht hp)).2, abs_neg, abs_of_nonneg (badFactor_nonneg p)]
  have hsubdiff (t : Finset ℕ) (ht : t ∈ B.powerset) :
      -(b t * (M - W (q t))) ≤ v t * (W (q t) - M) := by
    apply (abs_le.mp ?_).1
    rw [abs_mul, habs t ht, abs_of_nonpos (sub_nonpos.mpr (hWM _)), neg_sub]
  have hb0 (t : Finset ℕ) : 0 ≤ b t := prod_nonneg (fun p _ => badFactor_nonneg p)
  have hlocal (t : Finset ℕ) (ht : t ∈ S.powerset) :
      -(b t * ((1/1000 : ℝ)*M)) ≤ v t * (W (q t) - M) := by
    have hpos : 0 < q t :=
      Nat.mul_pos hd (prod_pos fun p hp => (hB p (hS (mem_powerset.mp ht hp))).1.1.pos)
    have hqle : q t ≤ smallDenominatorCutoff :=
      small_denominator_bound (fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2) hd'
    have hw := hsmall (q t) hpos hqle
    refine le_trans (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (hb0 t))) (hsubdiff t (hPS ht))
    linarith only [hw]
  have hfar (t : Finset ℕ) (ht : t ∈ B.powerset \ S.powerset) :
      -(b t * M) ≤ v t * (W (q t) - M) := by
    refine le_trans (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (hb0 t)))
      (hsubdiff t (mem_sdiff.mp ht).1)
    linarith only [hW0 (q t)]
  have hlocalSum := sum_le_sum hlocal
  have hfarSum := sum_le_sum hfar
  simp only [sum_neg_distrib, ← sum_mul] at hlocalSum hfarSum
  have hlocalCap : (∑ t ∈ S.powerset, b t) ≤ 73/50 := by
    have h := product_bad_factors (fun p hp => (hB p (hS hp)).1)
    rwa [prod_one_add] at h
  have hfarCap : (∑ t ∈ B.powerset \ S.powerset, b t) ≤ 1/1000 :=
    prime_tail_mass hS (fun p hp => (hB p hp).1) (fun p hp h => by
      by_contra! hn
      exact h (mem_filter.mpr ⟨hp, hn⟩))
  have hsplit := sum_sdiff (f := fun t => v t * (W (q t) - M)) hPS
  have hp : (653/1000 : ℝ) ≤ ∑ t ∈ B.powerset, v t := by
    have hb := prime_product_lower (fun p hp => (hB p hp).1)
    have hf : (∏ p ∈ B, (1-badFactor p)) = ∏ p ∈ B, (1+a p) := by
      exact prod_congr rfl fun p hp => by rw [(hB p hp).2, sub_eq_add_neg]
    rw [hf, prod_one_add] at hb
    exact hb
  have hdiff : (∑ t ∈ B.powerset, v t * (W (q t) - M)) =
      signedBlock a W B d - (∑ t ∈ B.powerset, v t) * M := by
    simp only [mul_sub, sum_sub_distrib, sum_mul, signedBlock, v, q]
  rw [hdiff] at hsplit
  have hmul := mul_le_mul_of_nonneg_right hp hM
  have hl := mul_le_mul_of_nonneg_right hlocalCap (show 0 ≤ (1/1000 : ℝ)*M by positivity)
  have hf := mul_le_mul_of_nonneg_right hfarCap hM
  linarith only [hsplit, hlocalSum, hfarSum, hmul, hl, hf, hM]

private theorem signedBlock_remove_good (a W : ℕ → ℝ) (M : ℝ) (Q : ℕ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q)
    (G B : Finset ℕ) (hdj : Disjoint G B)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ a p = -badFactor p)
    (hG : ∀ p ∈ G, p.Prime ∧ 0 ≤ a p) (d : ℕ) (hd : 0 < d) :
    signedBlock a W B d ≤ signedBlock a W (G ∪ B) d := by
  have hM := (hW0 0).trans (hWM 0)
  induction G using Finset.induction_on with
  | empty => simp
  | @insert p G hp ih =>
    have hpr := hG p (mem_insert_self _ _)
    have hGs : ∀ r ∈ G, r.Prime ∧ 0 ≤ a r := fun r hr => hG r (mem_insert_of_mem hr)
    have hdj' : Disjoint G B := hdj.mono_left (subset_insert ..)
    have hpB : p ∉ B := fun h => (Finset.disjoint_left.mp hdj) (mem_insert_self _ _) h
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hfirst := ih hdj' hGs
    have hdp : 0 < d*p := Nat.mul_pos hd hpr.1.pos
    have hsecond : 0 ≤ signedBlock a W (G ∪ B) (d*p) := by
      by_cases hq : d*p ≤ Q
      · have hmid := hWmid (d*p) hdp hq
        linarith [signedBlock_lower a W M Q hW0 hWM hcut hWmid G B hdj' hB hGs (d*p) hdp]
      · rw [signedBlock_vanish a W (G ∪ B) (fun r hr => by
          rcases mem_union.mp hr with hr | hr
          · exact (hGs r hr).1
          · exact (hB r hr).1.1) hcut (lt_of_not_ge hq)]
    rw [insert_union, signedBlock_insert a W (G ∪ B) hpGB]
    linarith [mul_nonneg hpr.2 hsecond]

/-- Retain the blocks belonging to 1 and 2 among the prime divisors of the
even target, and bound the signed Euler factors for each of those blocks. -/
theorem signed_powerset_two_floor (a W : ℕ → ℝ) (M : ℝ) (Q : ℕ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q)
    (hsmall : ∀ q, 0 < q → q ≤ smallDenominatorCutoff → (999/1000 : ℝ)*M ≤ W q)
    (G B : Finset ℕ) (hdj : Disjoint G B) (h2G : 2 ∈ G) (h2a : a 2 = 1)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ a p = -badFactor p)
    (hG : ∀ p ∈ G, p.Prime ∧ 0 ≤ a p) :
    (13/10 : ℝ)*M ≤ ∑ t ∈ (G ∪ B).powerset, (∏ p ∈ t, a p) * W (∏ p ∈ t, p) := by
  classical
  let G' := G.erase 2
  have hdj' : Disjoint G' B := hdj.mono_left (erase_subset _ _)
  have hG' : ∀ p ∈ G', p.Prime ∧ 0 ≤ a p := fun p hp => hG _ (mem_of_mem_erase hp)
  have h2B : 2 ∉ B := fun h => (Finset.disjoint_left.mp hdj) h2G h
  have h2 : 2 ∉ G' ∪ B := by simp [G', h2B]
  have heq : G ∪ B = insert 2 (G' ∪ B) := by rw [← insert_union, insert_erase h2G]
  have hsum (d : ℕ) (hd : 0 < d) (hd' : d ≤ 2) :
      (13/20 : ℝ)*M ≤ signedBlock a W (G' ∪ B) d :=
    (signedBlock_small_lower a W M B hW0 hWM hsmall hB hd hd').trans
      (signedBlock_remove_good a W M Q hW0 hWM hcut hWmid G' B hdj' hB hG' d hd)
  have hre : (∑ t ∈ (G ∪ B).powerset, (∏ p ∈ t, a p) * W (∏ p ∈ t, p)) =
      signedBlock a W (G ∪ B) 1 := by simp [signedBlock]
  rw [hre, heq, signedBlock_insert a W (G' ∪ B) h2, h2a, one_mul, one_mul]
  linarith only [hsum 1 (by decide) (by decide), hsum 2 (by decide) (by decide)]

def localCoeff (p n : ℕ) : ℝ := if p ∣ n then 1 / ((p : ℝ) - 1) else -badFactor p

-- Arithmetic reindexing adapted from Conjectures.Goldbach.MajorFixed144 in
-- goldbach-proofs (file blob 3fb16e16c798e5389494343c78ce9b1b6a95adcd,
-- Apache-2.0), abstracted over its coefficient interface for independent checking.
section

variable (c : ℕ → ℕ → ℂ)
variable (c_one : ∀ n, c 1 n = 1)
variable (c_mul : ∀ {q r}, 0 < q → 0 < r → q.Coprime r → ∀ n, c (q*r) n = c q n * c r n)
variable (c_prime : ∀ {p}, p.Prime → ∀ n, c p n = (localCoeff p n : ℂ))
variable (c_high : ∀ {p}, p.Prime → ∀ k n, c (p^(k+2)) n = 0)

include c_mul c_high in
private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : c q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact c_high hp j n
  | coprime a b ha hb hab ia ib =>
    rw [c_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

include c_one c_mul c_prime in
private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    c (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoeff p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [c_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, c_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      c_prime hprime, ih hs', Complex.ofReal_mul]

include c_one c_mul c_prime c_high in
private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (c q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoeff p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree c c_mul c_high n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product c c_one c_mul c_prime n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product c c_one c_mul c_prime n t (hprime ht), Complex.ofReal_re]

include c_one c_mul c_prime c_high in
theorem reweighted_floor {Q n : ℕ} (hQ : 2 ≤ Q) (hn : Even n) (W : ℕ → ℝ) (M : ℝ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q)
    (hsmall : ∀ q, 0 < q → q ≤ smallDenominatorCutoff → (999/1000 : ℝ) * M ≤ W q) :
    (13/10 : ℝ) * M ≤ ∑ q ∈ Icc 1 Q, (c q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hdj : Disjoint G B := by
    refine Finset.disjoint_left.mpr fun p hp hp' => ?_
    exact (mem_filter.mp hp').2 (mem_filter.mp hp).2
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have h2n := even_iff_two_dvd.mp hn
  have h2G : 2 ∈ G := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩,h2n⟩
  have h2a : localCoeff 2 n = 1 := by norm_num [localCoeff,h2n]
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ localCoeff p n = -badFactor p := by
    obtain ⟨hp', hnd⟩ := mem_filter.mp hp
    have hpr := (mem_filter.mp hp').2
    have hne : p ≠ 2 := fun e => hnd (e ▸ h2n)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, by simp [localCoeff,hnd]⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ 0 ≤ localCoeff p n := by
    obtain ⟨hp', hd⟩ := mem_filter.mp hp
    have hpr := (mem_filter.mp hp').2
    have hp1 : (1:ℝ) < p := by exact_mod_cast hpr.one_lt
    exact ⟨hpr, by simp only [localCoeff, ite_eq_left hd]; positivity⟩
  rw [reindex_denominators c c_one c_mul c_prime c_high Q n W hcut]
  change _ ≤ ∑ t ∈ P.powerset, (∏ p ∈ t, localCoeff p n) * W (∏ p ∈ t, p)
  rw [← hGB]
  exact signed_powerset_two_floor _ _ _ _ hW0 hWM hcut hWmid hsmall G B hdj h2G h2a hB hG

end

end
end GoldbachNumeratorArithmetic

open Finset

namespace NumeratorDilationMean

noncomputable section

private def twoWeight (q : ℕ) : ℝ :=
  if 4 ∣ q then 0 else if 2 ∣ q then 2 else 1

private lemma twoWeight_nonneg (q : ℕ) : 0 ≤ twoWeight q := by
  unfold twoWeight
  split_ifs <;> norm_num

private lemma twoWeight_formula (q : ℕ) :
    twoWeight q = 1 + (if 2 ∣ q then (1 : ℝ) else 0) -
      2 * (if 4 ∣ q then (1 : ℝ) else 0) := by
  unfold twoWeight
  have h : 4 ∣ q → 2 ∣ q := fun hq => dvd_trans (by decide : 2 ∣ 4) hq
  split_ifs <;> norm_num <;> tauto

private def primeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
private def inverseFactors (s : Finset ℕ) : ℝ := ∏ p ∈ s, 1 / ((p : ℝ) - 1)
private def oddPrimes (Q : ℕ) : Finset ℕ := (Ioc 2 Q).filter Nat.Prime
private def primeWeight (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 1))

private lemma oddPrimes_spec {Q p : ℕ} (hp : p ∈ oddPrimes Q) :
    p.Prime ∧ 2 < p ∧ p ≤ Q := by
  obtain ⟨h, hp⟩ := mem_filter.mp hp
  exact ⟨hp, (mem_Ioc.mp h).1, (mem_Ioc.mp h).2⟩

private lemma primeWeight_nonneg (p : ℕ) : 0 ≤ primeWeight p := by
  by_cases hp : p = 0
  · simp [primeWeight, hp]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp)
  unfold primeWeight
  positivity

private lemma tail_bound (m : ℕ) :
    (∑ k ∈ range m, primeWeight (2 * k + 5))
      ≤ (1 : ℝ) / 6 - 1 / (2 * (2 * (m : ℝ) + 3)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hb : primeWeight (2 * m + 5) ≤
        1 / (2 * (2 * (m : ℝ) + 3)) - 1 / (2 * (2 * (m : ℝ) + 5)) := by
      unfold primeWeight
      push_cast
      calc
        _ ≤ 1 / ((2 * (m : ℝ) + 5) * (2 * (m : ℝ) + 3)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith only [hm]
        _ = _ := by
          field_simp
          <;> ring
    rw [show 2 * ((m : ℝ) + 1) + 3 = 2 * (m : ℝ) + 5 by ring]
    linarith

private lemma primeWeight_sum (Q : ℕ) : ∑ p ∈ oddPrimes Q, primeWeight p ≤ 1/3 := by
  classical
  let tail : ℕ → ℕ := fun k => 2 * k + 5
  let U := (range Q).image tail
  have htail : Function.Injective tail := by intro a b hab; dsimp [tail] at hab; omega
  have h3 : 3 ∉ U := by simp [U, tail]
  have hsub : oddPrimes Q ⊆ insert 3 U := by
    intro p hp
    obtain ⟨hp, h2, hQ⟩ := oddPrimes_spec hp
    by_cases h : p = 3
    · simp [h]
    · apply mem_insert_of_mem
      obtain ⟨k, hk⟩ := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
      exact mem_image.mpr ⟨k - 2, mem_range.mpr (by omega), by dsimp [tail]; omega⟩
  calc
    _ ≤ ∑ p ∈ insert 3 U, primeWeight p :=
      sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => primeWeight_nonneg p
    _ = primeWeight 3 + ∑ k ∈ range Q, primeWeight (2*k+5) := by
      rw [sum_insert h3, sum_image htail.injOn]
    _ ≤ 1/3 := by
      have h := tail_bound Q
      have hz : (0 : ℝ) ≤ 1 / (2 * (2 * (Q : ℝ) + 3)) := by positivity
      have hp3 : primeWeight 3 = (1 : ℝ)/6 := by norm_num [primeWeight]
      rw [hp3]
      linarith

private lemma product_sum_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1 + f i)) * (1 - ∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hs' : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hs
    have hp : 0 ≤ ∏ i ∈ s, (1 + f i) := prod_nonneg fun i hi => by linarith [hs i hi]
    rw [prod_insert has, sum_insert has, mul_comm (1 + f a), mul_assoc]
    apply (mul_le_mul_of_nonneg_left ?_ hp).trans (ih hs)
    nlinarith only [sq_nonneg (f a), mul_nonneg ha hs']

private lemma product_pos_nat {Q : ℕ} {s : Finset ℕ} (hs : s ⊆ oddPrimes Q) :
    0 < primeProduct s :=
  prod_pos fun p hp => (oddPrimes_spec (hs hp)).1.pos

private lemma product_odd {Q : ℕ} {s : Finset ℕ} (hs : s ⊆ oddPrimes Q) :
    Odd (primeProduct s) := by
  rw [← Nat.coprime_two_right]
  apply Nat.Coprime.prod_left
  intro p hp
  obtain ⟨hp, h2, _⟩ := oddPrimes_spec (hs hp)
  exact (Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))).coprime_two_right

private lemma inverseFactors_nonneg {Q : ℕ} {s : Finset ℕ} (hs : s ⊆ oddPrimes Q) :
    0 ≤ inverseFactors s := by
  apply prod_nonneg
  intro p hp
  have hp' : (2 : ℝ) < p := by exact_mod_cast (oddPrimes_spec (hs hp)).2.1
  exact div_nonneg zero_le_one (by linarith)

private lemma inverseFactors_le_one {Q : ℕ} {s : Finset ℕ} (hs : s ⊆ oddPrimes Q) :
    inverseFactors s ≤ 1 := by
  apply prod_le_one₀
  · intro p hp
    have hp' : (2 : ℝ) < p := by exact_mod_cast (oddPrimes_spec (hs hp)).2.1
    exact div_nonneg zero_le_one (by linarith)
  · intro p hp
    have hp' : (2 : ℝ) < p := by exact_mod_cast (oddPrimes_spec (hs hp)).2.1
    exact div_le_one_of_le₀ (by linarith) (by linarith)

private lemma inverseFactors_square {Q : ℕ} {s : Finset ℕ} (hs : s ⊆ oddPrimes Q) :
    (inverseFactors s)^2 * (primeProduct s : ℝ) ≤ 1 := by
  unfold inverseFactors primeProduct
  push_cast
  rw [← prod_pow, ← prod_mul_distrib]
  apply prod_le_one₀
  · intro p _
    positivity
  · intro p hp
    have hp' : (3 : ℝ) ≤ p := by exact_mod_cast (oddPrimes_spec (hs hp)).2.1
    have hz : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
    apply div_le_one_of_le₀ _ (by positivity)
    nlinarith only [sq_nonneg ((p : ℝ) - 3), hp']

private lemma primeProduct_inj {Q : ℕ} :
    ((oddPrimes Q).powerset : Set (Finset ℕ)).InjOn primeProduct := by
  intro s hs t ht h
  have hx (u : Finset ℕ) (hu : u ∈ (oddPrimes Q).powerset) :
      (primeProduct u).primeFactors = u :=
    Nat.primeFactors_prod fun p hp => (oddPrimes_spec (mem_powerset.mp hu hp)).1
  exact (hx s hs).symm.trans ((congrArg Nat.primeFactors h).trans (hx t ht))

private lemma count_multiples (Q d : ℕ) :
    ((Icc 1 Q).filter (fun q => d ∣ q)).card = Q / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

private lemma sum_twoWeight {Q d : ℕ} (hd : 0 < d) (ho : Odd d) :
    (∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), twoWeight q) ≤ (Q : ℝ) / d + 1 := by
  have hd2 := ho.coprime_two_right
  have hd4 : d.Coprime 4 := by simpa using hd2.pow_right 2
  have hf (a : ℕ) (ha : d.Coprime a) :
      ((Icc 1 Q).filter (fun q => d ∣ q)).filter (fun q => a ∣ q) =
        (Icc 1 Q).filter (fun q => d*a ∣ q) := by
    ext q
    simp only [mem_filter, and_assoc]
    exact and_congr_right fun _ =>
      ⟨fun h => ha.mul_dvd_of_dvd_of_dvd h.1 h.2,
        fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩⟩
  simp_rw [twoWeight_formula]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul, mul_one, ← sum_filter]
  rw [hf 2 hd2, hf 4 hd4]
  simp only [count_multiples]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have hi : Q / d / 2 ≤ 2 * (Q / d / 4) + 1 := by omega
  have hi' : ((Q / d / 2 : ℕ) : ℝ) ≤ 2 * ((Q / d / 4 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hi
  have hfloor : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / d := by
    apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self Q d
  linarith

private lemma sum_twoWeight_zero {Q d : ℕ} (hd : Q < d) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => d ∣ q), twoWeight q = 0 := by
  apply sum_eq_zero
  intro q hq
  obtain ⟨hq, hqd⟩ := mem_filter.mp hq
  have h : d ≤ q := Nat.le_of_dvd (mem_Icc.mp hq).1 hqd
  have hqQ := (mem_Icc.mp hq).2
  omega

private lemma totient_ratio {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / q.totient = ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  have h : ((q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h' := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at h'
    convert h' using 2
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  calc
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) / ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
      have hp : 0 < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
        apply prod_pos
        intro p hp
        have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        linarith
      have ht : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
      exact (div_eq_div_iff ht.ne' hp.ne').mpr (by linarith)
    _ = _ := by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro p hp
      have hp' : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      field_simp
      ring

/-- The squarefree totient cost of one denominator after summing over its numerators. -/
def cost (q : ℕ) : ℝ := if Squarefree q then (q : ℝ) / q.totient else 0

private lemma pointwise {Q q : ℕ} (hq : q ∈ Icc 1 Q) :
    cost q ≤ twoWeight q *
      ∑ s ∈ (oddPrimes Q).powerset, if primeProduct s ∣ q then inverseFactors s else 0 := by
  classical
  let A := q.primeFactors.erase 2
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hsub : A ⊆ oddPrimes Q := by
    intro p hp
    obtain ⟨hne, hpq⟩ := mem_erase.mp hp
    have hpr := Nat.prime_of_mem_primeFactors hpq
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := hpr.two_le; omega,
      (Nat.le_of_mem_primeFactors hpq).trans (mem_Icc.mp hq).2⟩, hpr⟩
  have hpos : ∀ s ∈ (oddPrimes Q).powerset,
      0 ≤ (if primeProduct s ∣ q then inverseFactors s else 0) := by
    intro s hs
    split_ifs
    · exact inverseFactors_nonneg (mem_powerset.mp hs)
    · rfl
  by_cases hs : Squarefree q
  · rw [cost, ite_eq_left hs, totient_ratio hq0]
    have hd4 : ¬ 4 ∣ q := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
    have hprod : (∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) - 1))) =
        twoWeight q * ∏ p ∈ A, (1 + 1 / ((p : ℝ) - 1)) := by
      by_cases h2 : 2 ∣ q
      · have hm : 2 ∈ q.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hq0.ne'⟩
        have hAe : q.primeFactors = insert 2 A := (insert_erase hm).symm
        have h2A : 2 ∉ A := by simp [A]
        conv_lhs => rw [hAe, prod_insert h2A]
        norm_num [twoWeight, hd4, h2]
      · have hm : 2 ∉ q.primeFactors := fun hh => h2 (Nat.dvd_of_mem_primeFactors hh)
        simp [twoWeight, hd4, h2, A, hm]
    rw [hprod, prod_one_add]
    apply mul_le_mul_of_nonneg_left _ (twoWeight_nonneg q)
    calc
      _ = ∑ s ∈ A.powerset, if primeProduct s ∣ q then inverseFactors s else 0 := by
        apply sum_congr rfl
        intro s hs
        have hs' : s ⊆ q.primeFactors := (mem_powerset.mp hs).trans (erase_subset _ _)
        have hdvd : primeProduct s ∣ q :=
          (prod_dvd_prod_of_subset _ _ _ hs').trans (Nat.prod_primeFactors_dvd q)
        simp [hdvd, inverseFactors]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (powerset_mono.mpr hsub) fun s ss _ => hpos s ss
  · rw [cost, ite_eq_right hs]
    exact mul_nonneg (twoWeight_nonneg _) (sum_nonneg hpos)

private lemma weighted_sum (Q : ℕ) :
    ∑ s ∈ (oddPrimes Q).powerset, inverseFactors s / (primeProduct s : ℝ) ≤ 3/2 := by
  have hfactor : (∑ s ∈ (oddPrimes Q).powerset, inverseFactors s / (primeProduct s : ℝ)) =
      ∏ p ∈ oddPrimes Q, (1 + primeWeight p) := by
    rw [prod_one_add]
    apply sum_congr rfl
    intro s hs
    unfold inverseFactors primeProduct primeWeight
    push_cast
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    have hp' : (2 : ℝ) < p := by
      exact_mod_cast (oddPrimes_spec (mem_powerset.mp hs hp)).2.1
    field_simp
    <;> ring
  rw [hfactor]
  have hp := product_sum_bound (oddPrimes Q) primeWeight fun p _ => primeWeight_nonneg p
  have h := primeWeight_sum Q
  have hnonneg : 0 ≤ ∏ p ∈ oddPrimes Q, (1 + primeWeight p) :=
    prod_nonneg fun p _ => by linarith [primeWeight_nonneg p]
  have hh := (mul_le_mul_of_nonneg_left
    (show (2/3 : ℝ) ≤ 1 - ∑ p ∈ oddPrimes Q, primeWeight p by linarith) hnonneg).trans hp
  linarith

private lemma lower_order (Q : ℕ) :
    ∑ s ∈ (oddPrimes Q).powerset.filter (fun s => primeProduct s ≤ Q), inverseFactors s
      ≤ 400 + (Q : ℝ)/20 := by
  classical
  let U := (oddPrimes Q).powerset.filter (fun s => primeProduct s ≤ Q)
  let V := U.filter (fun s => primeProduct s < 400)
  let W := U.filter (fun s => ¬ primeProduct s < 400)
  have hcard (X : Finset (Finset ℕ)) (H : ℕ)
      (hX : X ⊆ (oddPrimes Q).powerset)
      (hbound : ∀ s ∈ X, primeProduct s ≤ H) : X.card ≤ H := by
    have h := card_le_card_of_injOn (t := Icc 1 H) primeProduct
      (fun s hs => mem_Icc.mpr ⟨product_pos_nat (mem_powerset.mp (hX hs)), hbound s hs⟩)
      ((primeProduct_inj (Q := Q)).mono hX)
    simpa using h
  have hU : U ⊆ (oddPrimes Q).powerset := filter_subset _ _
  have hV : V ⊆ (oddPrimes Q).powerset := (filter_subset _ _).trans hU
  have hW : W ⊆ (oddPrimes Q).powerset := (filter_subset _ _).trans hU
  have hcV : (V.card : ℝ) ≤ 400 := by
    exact_mod_cast hcard V 400 hV fun s hs => (mem_filter.mp hs).2.le
  have hcW : (W.card : ℝ) ≤ Q := by
    exact_mod_cast hcard W Q hW fun s hs => (mem_filter.mp (mem_filter.mp hs).1).2
  have hl (s : Finset ℕ) (hs : s ∈ W) : inverseFactors s ≤ 1/20 := by
    have hP : (400 : ℝ) ≤ primeProduct s := by
      exact_mod_cast Nat.le_of_not_gt (mem_filter.mp hs).2
    have hs' := mem_powerset.mp (hW hs)
    have hsq := inverseFactors_square hs'
    have hh := mul_le_mul_of_nonneg_left hP (sq_nonneg (inverseFactors s))
    nlinarith only [hh, hsq, sq_nonneg (inverseFactors s - 1/20)]
  change ∑ s ∈ U, inverseFactors s ≤ _
  rw [← sum_filter_add_sum_filter_not U (fun s => primeProduct s < 400)]
  change (∑ s ∈ V, inverseFactors s) + (∑ s ∈ W, inverseFactors s) ≤ _
  have ha := sum_le_sum (fun s hs => inverseFactors_le_one (mem_powerset.mp (hV hs)))
  have hb := sum_le_sum hl
  simp only [sum_const, nsmul_eq_mul, mul_one] at ha hb
  linarith

/-- Pair the odd denominators and the denominators with 2-adic valuation one.
Each odd divisor then sees density one, with a bounded endpoint error. -/
theorem cost_sum {Q : ℕ} (hQ : 8000 ≤ Q) : ∑ q ∈ Icc 1 Q, cost q ≤ (8/5) * (Q : ℝ) := by
  classical
  have h1 := sum_le_sum (fun q (hq : q ∈ Icc 1 Q) => pointwise hq)
  simp_rw [mul_sum] at h1
  rw [sum_comm] at h1
  simp_rw [mul_ite, mul_zero, ← sum_filter] at h1
  simp_rw [← sum_mul] at h1
  have hbound (s : Finset ℕ) (hs : s ∈ (oddPrimes Q).powerset) :
      (∑ q ∈ (Icc 1 Q).filter (fun q => primeProduct s ∣ q), twoWeight q) * inverseFactors s
      ≤ (Q : ℝ) * (inverseFactors s / (primeProduct s : ℝ)) +
        (if primeProduct s ≤ Q then inverseFactors s else 0) := by
    have hs' := mem_powerset.mp hs
    have hnonneg := inverseFactors_nonneg hs'
    by_cases hd : primeProduct s ≤ Q
    · rw [ite_eq_left hd]
      have h := mul_le_mul_of_nonneg_right (sum_twoWeight (Q := Q) (product_pos_nat hs') (product_odd hs')) hnonneg
      convert h using 1 <;> ring
    · rw [ite_eq_right hd, sum_twoWeight_zero (lt_of_not_ge hd), zero_mul]
      positivity
  apply h1.trans ((sum_le_sum hbound).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← sum_filter]
  have h := mul_le_mul_of_nonneg_left (weighted_sum Q) (Nat.cast_nonneg Q)
  have h' := lower_order Q
  have hQ' : (8000 : ℝ) ≤ Q := by exact_mod_cast hQ
  linarith

end
end NumeratorDilationMean

namespace GoldbachNumeratorDilation

open scoped ArithmeticFunction.Moebius in
private lemma ram_one_is_moebius (q : ℕ) : ram q 1 = (μ q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p k hp =>
    cases k with
    | zero => simp [ram_one]
    | succ j =>
      rw [ram_primePower p j 1 hp, ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero j)]
      have hn (l : ℕ) : ¬ p ^ (l + 1) ∣ 1 :=
        fun h => hp.ne_one (Nat.dvd_one.mp ((dvd_pow_self p (Nat.succ_ne_zero l)).trans h))
      cases j <;> simp [hn, hp.ne_one]
  | coprime a b ha hb hab ia ib =>
    rw [ram_mul (by omega) (by omega) hab, ia, ib,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab, Int.cast_mul]

private lemma scalar_norm {q a n : ℕ} (ha : a.Coprime q) :
    ‖unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)‖ =
      if Squarefree q then 1 / (q.totient : ℝ)^2 else 0 := by
  have hphase : ‖phase (-(n : ℝ) * center q a)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, hphase, mul_one, norm_pow, unitMean_eq_ram ha,
    ram_one_is_moebius, norm_div, Complex.norm_natCast, Complex.norm_intCast,
    ← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split_ifs <;> simp [div_pow]

private def minimumRadius (n q : ℕ) : ℝ :=
  (1/2 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * n)

private def meanMass (n q : ℕ) : ℝ :=
  (kernelMass n (minimumRadius n q) + kernelMass n (wideWidth n q)) / 2

private def baseWeight (n q : ℕ) : ℝ :=
  if q ∈ Icc 1 (cutoff n) then meanMass n q else 0

private lemma minimumRadius_pos {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    0 < minimumRadius n q := by
  have hQ : (0 : ℝ) < cutoff n := by exact_mod_cast cutoff_positive n
  unfold minimumRadius
  positivity

private lemma wideWidth_eq (n q : ℕ) : wideWidth n q = 4 * minimumRadius n q := by
  unfold wideWidth minimumRadius
  ring

private lemma wideWidth_small {n q : ℕ} (hQ : 3 ≤ cutoff n)
    (hsep : 4 * (cutoff n)^2 < n) (hq : 0 < q) :
    wideWidth n q ≤ 1/6 := by
  have h : 12 * cutoff n ≤ n := by
    calc
      _ = 4 * (3 * cutoff n) := by ring
      _ ≤ 4 * (cutoff n * cutoff n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hQ)
      _ ≤ n := by simpa [pow_two] using hsep.le
  have hn : 0 < n := by omega
  have h' : (12 : ℝ) * cutoff n ≤ n := by exact_mod_cast h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold wideWidth
  apply (div_le_iff₀ (show (0 : ℝ) < (q : ℝ) * n by positivity)).mpr
  nlinarith only [h', mul_le_mul_of_nonneg_right hq' hn'.le]

private lemma radius_bounds (ρ : ℕ → ℕ → ℝ)
    (hρ : ∀ q a, (1/2 : ℝ) ≤ ρ q a ∧ ρ q a ≤ 2)
    (n q a : ℕ) :
    minimumRadius n q ≤ width ρ n q a ∧ width ρ n q a ≤ wideWidth n q := by
  constructor
  · unfold minimumRadius width
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hρ q a).1 (by positivity)) (by positivity)
  · exact width_le_twice ρ (fun q a => (hρ q a).2) n q a

private lemma min_le_wide (n q : ℕ) : minimumRadius n q ≤ wideWidth n q := by
  exact (radius_bounds (fun _ _ => 1) (by intro q a; norm_num) n q 0).1.trans
    (radius_bounds (fun _ _ => 1) (by intro q a; norm_num) n q 0).2

private lemma radius_error (ρ : ℕ → ℕ → ℝ)
    (hρ : ∀ q a, (1/2 : ℝ) ≤ ρ q a ∧ ρ q a ≤ 2) {n q a : ℕ}
    (hQ : 3 ≤ cutoff n) (hsep : 4 * (cutoff n)^2 < n) (hq : 0 < q) :
    |kernelMass n (width ρ n q a) - meanMass n q| ≤
      (n : ℝ) / (6 * cutoff n) * q := by
  have hn : 0 < n := by omega
  have hb := minimumRadius_pos hn hq
  obtain ⟨hl, hu⟩ := radius_bounds ρ hρ n q a
  have hmassl := kernelMass_mono hb.le hl n
  have hmassu := kernelMass_mono (hb.le.trans hl) hu n
  have hvariation := NumeratorDilationKernel.kernelMass_variation n hb (min_le_wide n q)
    (wideWidth_small hQ hsep hq)
  have hQr : (0 : ℝ) < cutoff n := by exact_mod_cast cutoff_positive n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hradius : (2/9 : ℝ) * (1 / minimumRadius n q - 1 / wideWidth n q) =
      2 * ((n : ℝ) / (6 * cutoff n) * q) := by
    rw [wideWidth_eq]
    unfold minimumRadius
    field_simp
    <;> ring
  rw [hradius] at hvariation
  unfold meanMass
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma numerators_interior {q : ℕ} (hq : 1 < q) :
    numerators q = (range q).filter (fun a => a.Coprime q) := by
  ext a
  constructor
  · intro ha
    exact mem_filter.mpr ⟨mem_range.mpr (interior_order hq ha).2, (mem_filter.mp ha).2⟩
  · intro ha
    obtain ⟨ha, hc⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp ha; omega), hc⟩

private lemma compare_denominator (ρ : ℕ → ℕ → ℝ)
    (hρ : ∀ q a, (1/2 : ℝ) ≤ ρ q a ∧ ρ q a ≤ 2) {n q : ℕ}
    (hQ : 3 ≤ cutoff n) (hsep : 4 * (cutoff n)^2 < n) (hq : q ∈ Icc 1 (cutoff n)) :
    ‖(∑ a ∈ numerators q, modelPiece ρ n q a) - coefficient q n * (baseWeight n q : ℂ)‖ ≤
      ((n : ℝ) / (6 * cutoff n)) * NumeratorDilationMean.cost q := by
  classical
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hρ0 (q a : ℕ) : 0 ≤ ρ q a := by linarith [(hρ q a).1]
  have hρ2 (q a : ℕ) : ρ q a ≤ 2 := (hρ q a).2
  simp only [baseWeight, ite_eq_left hq]
  rcases eq_or_lt_of_le (show 1 ≤ q from hq0) with h | h
  · subst q
    rw [endpoint_models ρ hρ0 hρ2 hsep, coefficient_one, one_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have h0 := abs_le.mp (radius_error ρ hρ hQ hsep (q := 1) (a := 0) Nat.one_pos)
    have h1 := abs_le.mp (radius_error ρ hρ hQ hsep (q := 1) (a := 1) Nat.one_pos)
    simp only [Nat.cast_one, mul_one] at h0 h1
    simp only [NumeratorDilationMean.cost, squarefree_one, if_true, Nat.totient_one, Nat.cast_one,
      div_one, mul_one]
    exact abs_le.mpr ⟨by linarith [h0.1, h1.1], by linarith [h0.2, h1.2]⟩
  · let C (a : ℕ) : ℂ := unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)
    have hc : ∑ a ∈ numerators q, C a = coefficient q n := by
      rw [numerators_interior h]
      exact sum_centers_eq_coefficient q n
    rw [← hc, sum_mul, ← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    have hcard : (numerators q).card = q.totient := by
      rw [numerators_interior h, Nat.totient_eq_card_coprime]
      congr 1
      exact filter_congr fun _ _ => Nat.coprime_comm
    have hterm (a : ℕ) (ha : a ∈ numerators q) :
        ‖modelPiece ρ n q a - C a * (meanMass n q : ℂ)‖ ≤
          (if Squarefree q then 1 / (q.totient : ℝ)^2 else 0) *
            ((n : ℝ) / (6 * cutoff n) * q) := by
      rw [modelPiece_interior ρ hρ2 hsep h ha]
      change ‖C a * (kernelMass n (width ρ n q a) : ℂ) - C a * (meanMass n q : ℂ)‖ ≤ _
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hs := scalar_norm (n := n) (mem_filter.mp ha).2
      change ‖C a‖ = _ at hs
      rw [hs]
      apply mul_le_mul_of_nonneg_left (radius_error ρ hρ hQ hsep hq0)
      split_ifs <;> positivity
    apply (sum_le_sum hterm).trans
    rw [sum_const, nsmul_eq_mul, hcard]
    by_cases hs : Squarefree q
    · simp only [ite_eq_left hs, NumeratorDilationMean.cost]
      have ht : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      apply le_of_eq
      field_simp
      <;> ring
    · simp [NumeratorDilationMean.cost, hs]

private def baseContribution (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff n), coefficient q n * (baseWeight n q : ℂ)

private lemma compare_model (ρ : ℕ → ℕ → ℝ)
    (hρ : ∀ q a, (1/2 : ℝ) ≤ ρ q a ∧ ρ q a ≤ 2) {n : ℕ}
    (hQ : 8000 ≤ cutoff n) (hsep : 4 * (cutoff n)^2 < n) :
    ‖modeledContribution ρ n - baseContribution n‖ ≤ (4/15 : ℝ) * n := by
  unfold modeledContribution baseContribution
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun q hq => compare_denominator ρ hρ (by omega) hsep hq)).trans
  rw [← mul_sum]
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) / (6 * cutoff n) := by positivity
  apply (mul_le_mul_of_nonneg_left (NumeratorDilationMean.cost_sum hQ) hnonneg).trans
  apply le_of_eq
  have hQ' : (0 : ℝ) < cutoff n := by exact_mod_cast cutoff_positive n
  field_simp
  <;> ring

private lemma baseWeight_nonneg (n q : ℕ) : 0 ≤ baseWeight n q := by
  unfold baseWeight
  split_ifs with h
  · have hmass (b : ℝ) (hb : 0 ≤ b) : 0 ≤ kernelMass n b := by
      unfold kernelMass
      exact intervalIntegral.integral_nonneg (neg_le_self hb) fun _ _ => sq_nonneg _
    have hl : 0 ≤ minimumRadius n q := by unfold minimumRadius; positivity
    unfold meanMass
    exact div_nonneg (add_nonneg (hmass _ hl) (hmass _ (wideWidth_nonneg n q))) (by norm_num)
  · rfl

private lemma base_floor {n : ℕ} (hsep : 4 * (cutoff n)^2 < n) (heven : Even n)
    (hQ : 8000 ≤ cutoff n)
    (hsmall : 1000 * GoldbachNumeratorArithmetic.smallDenominatorCutoff ≤ cutoff n) :
    (13/10 : ℝ) * ((n : ℝ) + 1) ≤ (baseContribution n).re := by
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ' : (0 : ℝ) < cutoff n := by exact_mod_cast cutoff_positive n
  have hw (q : ℕ) (hq : 0 < q) :
      0 < minimumRadius n q ∧ minimumRadius n q ≤ wideWidth n q ∧ wideWidth n q ≤ 1/2 :=
    ⟨minimumRadius_pos hn hq, min_le_wide n q,
      (wideWidth_small (by omega) hsep hq).trans (by norm_num)⟩
  have hWM (q : ℕ) : baseWeight n q ≤ (n : ℝ) + 1 := by
    unfold baseWeight
    split_ifs with h
    · obtain ⟨hmin, hm, hmax⟩ := hw q (mem_Icc.mp h).1
      have hh := NumeratorDilationKernel.kernelMass_upper n hmin.le (hm.trans hmax)
      have hw' := NumeratorDilationKernel.kernelMass_upper n (hmin.le.trans hm) hmax
      unfold meanMass
      linarith
    · positivity
  have hcut (q : ℕ) (hq : cutoff n < q) : baseWeight n q = 0 := by
    simp [baseWeight, mem_Icc, hq.not_ge]
  have hWmid (q : ℕ) (hq : 0 < q) (hqn : q ≤ cutoff n) :
      ((n : ℝ) + 1)/2 ≤ baseWeight n q := by
    obtain ⟨hmin, hm, _⟩ := hw q hq
    have hq' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hqn
    have hge : 1 / (2 * (n : ℝ)) ≤ minimumRadius n q := by
      unfold minimumRadius
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hq' hn'.le]
    have hhalf := NumeratorDilationKernel.kernelMass_half_mass hn hge
    have hmono := kernelMass_mono hmin.le hm n
    simp only [baseWeight, ite_eq_left (mem_Icc.mpr ⟨hq, hqn⟩), meanMass]
    linarith
  have hWsmall (q : ℕ) (hq : 0 < q) (hD : q ≤ GoldbachNumeratorArithmetic.smallDenominatorCutoff) :
      (999/1000 : ℝ) * ((n : ℝ) + 1) ≤ baseWeight n q := by
    have hqN : 1000*q ≤ cutoff n := (Nat.mul_le_mul_left _ hD).trans hsmall
    have hqn : q ≤ cutoff n := by omega
    obtain ⟨hmin, hm, hmax⟩ := hw q hq
    have ht := NumeratorDilationKernel.kernelMass_tail n hmin (hm.trans hmax)
    have hmono := kernelMass_mono hmin.le hm n
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hq' : (1000 : ℝ)*q ≤ cutoff n := by exact_mod_cast hqN
    have hrew : 1 / (2 * minimumRadius n q) = (q : ℝ) * n / cutoff n := by
      unfold minimumRadius
      field_simp
      <;> ring
    have hrem : (q : ℝ) * n / cutoff n ≤ ((n : ℝ) + 1) / 1000 := by
      apply (div_le_div_iff₀ hQ' (by norm_num)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hq' hn'.le, hQ'.le]
    rw [hrew] at ht
    simp only [baseWeight, ite_eq_left (mem_Icc.mpr ⟨hq, hqn⟩), meanMass]
    linarith
  have hb := GoldbachNumeratorArithmetic.reweighted_floor
    coefficient coefficient_one coefficient_mul (fun hp n => coefficient_prime hp n) coefficient_higher_power
    (show 2 ≤ cutoff n by omega) heven (baseWeight n) ((n : ℝ) + 1)
    (baseWeight_nonneg n) hWM hcut hWmid hWsmall
  unfold baseContribution
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using hb

private lemma cutoff_eventually_ge (B : ℕ) : ∀ᶠ n : ℕ in atTop, B ≤ cutoff n := by
  filter_upwards [eventually_ge_atTop (2^B : ℕ)] with n hn
  have hl : B ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hp : 1 ≤ Nat.log 2 (n+2) := by
    have hh := cutoff_positive n
    unfold cutoff at hh
    by_contra h
    have hz : Nat.log 2 (n+2) = 0 := by omega
    simp [hz] at hh
  exact hl.trans (by unfold cutoff; nlinarith)

theorem eventual_floor : ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ ρ : ℕ → ℕ → ℝ,
    (∀ q a, (1/2 : ℝ) ≤ ρ q a ∧ ρ q a ≤ 2) → (n : ℝ) ≤ (majorContribution ρ n).re := by
  have he := totalWideError_sublinear.eventually_lt_const (by norm_num : (0 : ℝ) < 1/100)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((cutoff_separated.and (cutoff_eventually_ge 8000)).and
      (cutoff_eventually_ge (1000 * GoldbachNumeratorArithmetic.smallDenominatorCutoff))).and he)
  refine ⟨N, ?_⟩
  intro n hn heven ρ hρ
  obtain ⟨⟨⟨hsep, hQ⟩, hsmall⟩, herr⟩ := hN n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha := major_error ρ (fun q a => (by linarith [(hρ q a).1])) (fun q a => (hρ q a).2) hsep
  have hb := compare_model ρ hρ hQ hsep
  have hl := base_floor hsep heven hQ hsmall
  have hr1 := Complex.re_le_norm (baseContribution n - modeledContribution ρ n)
  have hr2 := Complex.re_le_norm (modeledContribution ρ n - majorContribution ρ n)
  rw [Complex.sub_re, norm_sub_rev] at hr1 hr2
  have hz : totalWideError n < (n : ℝ)/100 := by
    have h := (div_lt_iff₀ hn').mp herr
    linarith
  linarith

end GoldbachNumeratorDilation

theorem Conjectures.Goldbach.MajorNumeratorDilation :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let A := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let M := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => (intervalIntegral (fun t => (A n r).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) → (n:ℝ) ≤ M n r := by
  exact GoldbachNumeratorDilation.eventual_floor
