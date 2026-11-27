import Conjectures.Goldbach.MajorFixed144

/-! The separation, decomposition and model error estimates adapt the Apache-2.0
proof `MajorFixed144` (#3120). Delimiters and bounds are uniform in the dilation. -/
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

namespace GoldbachDenominatorDilation

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

def width (r : ℕ → ℝ) (n q : ℕ) : ℝ :=
  r q * (cutoff n : ℝ) / ((q : ℝ) * n)

theorem width_eq (r : ℕ → ℝ) (n q : ℕ) :
    width r n q = r q * Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width n q := by
  unfold width Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width
  ring

theorem width_nonneg (r : ℕ → ℝ) (hr : ∀ q, 0 ≤ r q) (n q : ℕ) : 0 ≤ width r n q := by
  rw [width_eq]; exact mul_nonneg (hr q) (by unfold Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.width; positivity)

theorem width_le_twice (r : ℕ → ℝ) (hr : ∀ q, r q ≤ 2) (n q : ℕ) :
    width r n q ≤ 2 * (cutoff n : ℝ) / ((q : ℝ) * n) := by
  unfold width
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hr q) (by positivity)) (by positivity)

def arcs (r : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - center q a| ≤ width r n q}

def wideWidth (n q : ℕ) : ℝ := 2 * (cutoff n : ℝ) / ((q : ℝ) * n)

theorem wideWidth_nonneg (n q : ℕ) : 0 ≤ wideWidth n q := by
  unfold wideWidth; positivity

def totalWideError (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ range (q+1),
     ∫ β in -(wideWidth n q)..wideWidth n q, modelError n q a β

def window (ρ : ℕ → ℝ) (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width ρ n q) (center q a + width ρ n q)
def leftEnd (ρ : ℕ → ℝ) (n q a : ℕ) : ℝ := max (center q a - width ρ n q) 0 - center q a
def rightEnd (ρ : ℕ → ℝ) (n q a : ℕ) : ℝ := min (center q a + width ρ n q) 1 - center q a

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

theorem mem_window (ρ : ℕ → ℝ) (n q a : ℕ) (t : ℝ) : t ∈ window ρ n q a ↔ |t - center q a| ≤ width ρ n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n q r a b : ℕ} {t : ℝ} (hn : 4 * (cutoff n)^2 < n)
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
  have h₁' := h₁.trans (width_le_twice ρ hρ₂ n q)
  have h₂' := h₂.trans (width_le_twice ρ hρ₂ n r)
  change |t-(a:ℝ)/q| ≤ 2*(Q:ℝ)/(q*n) at h₁'
  change |t-(b:ℝ)/r| ≤ 2*(Q:ℝ)/(r*n) at h₂'
  linarith

private theorem center_unique (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n q r a b : ℕ} {t : ℝ} (hn : 4*(cutoff n)^2<n)
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

theorem arc_indicator_sum (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) (t : ℝ) :
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

theorem clipped_order (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width ρ n q ≤ leftEnd ρ n q a ∧ leftEnd ρ n q a ≤ rightEnd ρ n q a ∧ rightEnd ρ n q a ≤ width ρ n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg ρ hρ₀ n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width ρ n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width ρ n q) 1]

theorem indicator_clipped (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window ρ n q a).indicator F t) =
    ∫ β in leftEnd ρ n q a..rightEnd ρ n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order ρ hρ₀ (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width ρ n q) 0 ≤ min (center q a+width ρ n q) 1),
    ← integral_Icc_eq_integral_Ioc]

def majorContribution (ρ : ℕ → ℝ) (n : ℕ) : ℂ := ∫ t in (0:ℝ)..1, (arcs ρ n).indicator (integrand n) t
def actualPiece (ρ : ℕ → ℝ) (n q a : ℕ) : ℂ := ∫ β in leftEnd ρ n q a..rightEnd ρ n q a, integrand n (center q a+β)

theorem major_split (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₂ : ∀ q, ρ q ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) : majorContribution ρ n =
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

def modelPiece (ρ : ℕ → ℝ) (n q a : ℕ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n:ℝ)*center q a)) *
    ((∫ β in leftEnd ρ n q a..rightEnd ρ n q a, ‖kernel n β‖^2 : ℝ) : ℂ)

theorem model_piece_eq (ρ : ℕ → ℝ) (n q a : ℕ) :
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

theorem piece_error_le (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    ‖actualPiece ρ n q a - modelPiece ρ n q a‖ ≤ ∫ β in -(width ρ n q)..width ρ n q, modelError n q a β := by
  have hi : Continuous (fun β => integrand n (center q a+β)) := by unfold integrand primeSum phase; fun_prop
  have hm : Continuous (modelPoint n q a) := by unfold modelPoint kernel phase; fun_prop
  have ⟨hl,hord,hr⟩ := clipped_order ρ hρ₀ (n := n) hq ha
  rw [actualPiece, ← model_piece_eq ρ, ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm hord).trans
  exact intervalIntegral.integral_mono_interval hl hord hr (Eventually.of_forall fun _ => norm_nonneg _)
    ((error_cont n q a).norm.intervalIntegrable _ _)

theorem width_le_unit (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n q : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 0<q) :
    width ρ n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : 2 * cutoff n ≤ n := by nlinarith [cutoff_positive n]
  calc
    width ρ n q ≤ 2 * (cutoff n:ℝ) / ((q:ℝ)*n) := width_le_twice ρ hρ₂ n q
    _ = ((2 * (cutoff n:ℝ))/n)/q := by ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n q a : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd ρ n q a = -(width ρ n q) ∧ rightEnd ρ n q a = width ρ n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit ρ hρ₂ hn (by omega : 0<q)
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

/-- The two boundary half intervals together give the full kernel mass for q = 1. -/
private theorem endpoint_models (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₂ : ∀ q, ρ q ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) :
    (∑ a ∈ numerators 1, modelPiece ρ n 1 a) = (kernelMass n (width ρ n 1) : ℂ) := by
  let w := width ρ n 1
  have hw : 0≤w := width_nonneg ρ hρ₀ _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit ρ hρ₂ hn (by decide : 0<1)
  have h0 : leftEnd ρ n 1 0 = 0 ∧ rightEnd ρ n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd ρ n 1 1 = -w ∧ rightEnd ρ n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp), ram_one]; simp
  have hker : Continuous (fun β => ‖kernel n β‖^2) := (continuous_kernel n).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hker.intervalIntegrable (μ := volume) (-w) 0) (hker.intervalIntegrable 0 w)
  have hnSet : numerators 1 = {0,1} := by decide
  rw [hnSet]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2,hu,
    center, Nat.cast_zero,Nat.cast_one,div_one,mul_zero,mul_one,one_pow,one_mul,denom_one_phase]
  have hz : phase 0=1 := by simp [phase]
  rw [hz,one_mul,add_comm,← Complex.ofReal_add,hadd]
  rfl

theorem model_by_denominator (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₂ : ∀ q, ρ q ≤ 2) {n q : ℕ} (hn : 4*(cutoff n)^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece ρ n q a) = coefficient q n * (kernelMass n (width ρ n q):ℂ) := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    rw [coefficient_one,one_mul]
    exact endpoint_models ρ hρ₀ hρ₂ hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← sum_centers_eq_coefficient, ← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut ρ hρ₂ hn h ha
    simp only [modelPiece,hl,hr,kernelMass,center]
def modeledContribution (ρ : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff n), coefficient q n * (kernelMass n (width ρ n q) : ℂ)

/-- The original indicator integral differs from the finite arithmetic model by at most
the sum of the absolute errors on all the full rational arcs. -/
theorem major_error (ρ : ℕ → ℝ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₂ : ∀ q, ρ q ≤ 2) {n : ℕ} (hn : 4*(cutoff n)^2<n) :
    ‖majorContribution ρ n - modeledContribution ρ n‖ ≤ totalWideError n := by
  have hmodels : modeledContribution ρ n =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, modelPiece ρ n q a :=
    sum_congr rfl fun q hq => (model_by_denominator ρ hρ₀ hρ₂ hn (mem_Icc.mp hq).1).symm
  rw [major_split ρ hρ₀ hρ₂ hn, hmodels, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold totalWideError
  apply sum_le_sum
  intro q hq
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ numerators q, ∫ β in -(width ρ n q)..width ρ n q, modelError n q a β :=
      sum_le_sum fun a ha => piece_error_le ρ hρ₀ (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
    _ ≤ ∑ a ∈ numerators q,
          ∫ β in -(wideWidth n q)..wideWidth n q, modelError n q a β := by
      refine sum_le_sum fun a _ => ?_
      have hle := width_le_twice ρ hρ₂ n q
      exact intervalIntegral.integral_mono_interval (neg_le_neg hle)
        (by linarith [width_nonneg ρ hρ₀ n q]) hle
        (Eventually.of_forall fun _ => norm_nonneg _)
        ((error_cont n q a).norm.intervalIntegrable _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [wideWidth_nonneg n q]) fun _ _ => norm_nonneg _


end GoldbachDenominatorDilation

namespace GoldbachDenominatorDilation

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
    _ = _ := by dsimp [B]; field_simp <;> ring

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

end GoldbachDenominatorDilation

namespace DilationDenominatorArithmetic

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

/-- Both small positive blocks are retained and every other good-factor block
has nonnegative contribution. -/
theorem signed_powerset_two_floor (a W : ℕ → ℝ) (M : ℝ) (Q : ℕ)
    (hW0 : ∀ k, 0 ≤ W k) (hWM : ∀ k, W k ≤ M)
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q)
    (G B : Finset ℕ) (hdj : Disjoint G B) (h2G : 2 ∈ G) (h2a : a 2 = 1)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ a p = -badFactor p)
    (hG : ∀ p ∈ G, p.Prime ∧ 0 ≤ a p) :
    W 1 + W 2 - (23/25)*M ≤ ∑ t ∈ (G ∪ B).powerset, (∏ p ∈ t, a p) * W (∏ p ∈ t, p) := by
  classical
  let G' := G.erase 2
  have hdj' : Disjoint G' B := hdj.mono_left (erase_subset _ _)
  have hG' : ∀ p ∈ G', p.Prime ∧ 0 ≤ a p := fun p hp => hG _ (mem_of_mem_erase hp)
  have h2B : 2 ∉ B := fun h => (Finset.disjoint_left.mp hdj) h2G h
  have h2 : 2 ∉ G' ∪ B := by simp [G', h2B]
  have heq : G ∪ B = insert 2 (G' ∪ B) := by rw [← insert_union, insert_erase h2G]
  have hsum1 := signedBlock_lower a W M Q hW0 hWM hcut hWmid G' B hdj' hB hG' 1 (by decide)
  have hsum2 := signedBlock_lower a W M Q hW0 hWM hcut hWmid G' B hdj' hB hG' 2 (by decide)
  have hre : (∑ t ∈ (G ∪ B).powerset, (∏ p ∈ t, a p) * W (∏ p ∈ t, p)) =
      signedBlock a W (G ∪ B) 1 := by simp [signedBlock]
  rw [hre, heq, signedBlock_insert a W (G' ∪ B) h2, h2a, one_mul, one_mul]
  linarith

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
    (hcut : ∀ q, Q < q → W q = 0) (hWmid : ∀ q, 0 < q → q ≤ Q → M/2 ≤ W q) :
    W 1 + W 2 - (23/25)*M ≤ ∑ q ∈ Icc 1 Q, (c q n).re * W q := by
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
  exact signed_powerset_two_floor _ _ _ _ hW0 hWM hcut hWmid G B hdj h2G h2a hB hG

end

end
end DilationDenominatorArithmetic

namespace DilationKernelHalfMass

open Finset MeasureTheory
open scoped BigOperators

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
end DilationKernelHalfMass

open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

/- Parseval argument adapted from PEqualNP.Outside.L_goldbach_continuous_parseval in this repository. -/
namespace DilationKernel

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

private theorem norm_packet_le_inv (n : ℕ) {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1/2) :
    ‖packet n t‖ ≤ 1 / (2 * t) := by
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
  have hs : 2 * t ≤ Real.sin (Real.pi * t) := by
    have hh := Real.mul_le_sin (mul_nonneg Real.pi_pos.le ht.le)
      (show Real.pi * t ≤ Real.pi / 2 by nlinarith [mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le])
    calc
      2 * t = 2 / Real.pi * (Real.pi * t) := by field_simp
      _ ≤ _ := hh
  have hz : 4 * t ≤ ‖z - 1‖ := by
    rw [hz', Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hprod : ‖packet n t‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖z ^ (n+1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [hnorm, one_add_one_eq_two]
  have h := (mul_le_mul_of_nonneg_left hz (norm_nonneg (packet n t))).trans hprod
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  linarith

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
      _ = _ := by rw [zpow_neg]; field_simp <;> norm_num
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by decide, hzero⟩)]
  norm_num [zpow_neg]
  have hh : 0 < b⁻¹ := inv_pos.mpr hb
  ring_nf
  linarith

private theorem mass_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
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

/-- Uniform cap from the mass of the full symmetric fundamental interval. -/
theorem mass_upper (n : ℕ) {b : ℝ} (hb : 0 ≤ b) (hhalf : b ≤ 1/2) :
    mass n b ≤ (n : ℝ) + 1 := by
  rw [← mass_half]
  unfold mass
  exact intervalIntegral.integral_mono_interval (neg_le_neg hhalf) (by linarith) hhalf
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (((continuous_packet n).norm.pow 2).intervalIntegrable _ _)

/-- 98 percent of the mass is retained by a radius of at least 25/(n+1). -/
theorem mass_lower (n : ℕ) {b : ℝ} (hb : 25/((n : ℝ)+1) ≤ b) (hhalf : b ≤ 1/2) :
    (49/50 : ℝ) * ((n : ℝ) + 1) ≤ mass n b := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hb0 : 0 < b := (div_pos (by norm_num) hn).trans_le hb
  have hmul := (div_le_iff₀ hn).mp hb
  have htail : (1 : ℝ) / (2*b) ≤ ((n : ℝ)+1)/50 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*b)).mpr
    nlinarith
  linarith [mass_tail n hb0 hhalf]


end DilationKernel

open Conjectures.Goldbach.MajorFixed144_aux

theorem DilationKernel.kernelMass_upper (n : ℕ) {b : ℝ} (hb : 0 ≤ b) (hhalf : b ≤ 1/2) :
    GoldbachMajorArc.kernelMass n b ≤ (n : ℝ) + 1 :=
  DilationKernel.mass_upper n hb hhalf

theorem DilationKernel.kernelMass_lower (n : ℕ) {b : ℝ}
    (hb : 25/((n : ℝ)+1) ≤ b) (hhalf : b ≤ 1/2) :
    (49/50 : ℝ) * ((n : ℝ) + 1) ≤ GoldbachMajorArc.kernelMass n b :=
  DilationKernel.mass_lower n hb hhalf

theorem DilationKernel.small_dilation_radius {n q : ℕ} {r : ℝ}
    (hn : 1024 ≤ n) (hq : 0 < q) (hq' : q ≤ 2) (hr : (1/2 : ℝ) ≤ r) :
    25 / ((n : ℝ) + 1) ≤ r * GoldbachMajorArc.width n q := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqR' : (q : ℝ) ≤ 2 := by exact_mod_cast hq'
  have hlog : 10 ≤ Nat.log 2 (n+2) :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hcut : (100 : ℝ) ≤ GoldbachMajorArc.cutoff n := by
    exact_mod_cast (show 100 ≤ (Nat.log 2 (n + 2)) ^ 2 by
      exact pow_le_pow_left₀ (Nat.zero_le 10) hlog 2)
  calc
    _ ≤ 25 / (n : ℝ) := div_le_div_of_nonneg_left (by norm_num) hnR (by linarith)
    _ ≤ ((GoldbachMajorArc.cutoff n : ℝ)/(2*(q:ℝ)))/(n:ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    _ = (1/2 : ℝ) * GoldbachMajorArc.width n q := by
      unfold GoldbachMajorArc.width
      field_simp [ne_of_gt hnR, ne_of_gt hqR]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (GoldbachMajorArc.width_nonneg n q)

namespace GoldbachDenominatorDilation

private theorem cutoff_ge100 {n : ℕ} (hn : 1024 ≤ n) : 100 ≤ cutoff n := by
  have hlog : 10 ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by decide) (by omega)
  exact pow_le_pow_left₀ (Nat.zero_le 10) hlog 2

private theorem radius_upper (ρ : ℕ → ℝ) (hρ₂ : ∀ q, ρ q ≤ 2) {n q : ℕ}
    (hsep : 4 * (cutoff n)^2 < n) (hq : 0 < q) : width ρ n q ≤ 1 / 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQn : 4 * (cutoff n : ℝ) ≤ n := by
    exact_mod_cast (show 4 * cutoff n ≤ n by nlinarith [cutoff_positive n])
  apply (width_le_twice ρ hρ₂ n q).trans
  apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) * n)).mpr
  nlinarith only [hQn, mul_le_mul_of_nonneg_right hqr hnr.le]

private theorem radius_lower (ρ : ℕ → ℝ) (hρ : ∀ q, (1/2 : ℝ) ≤ ρ q) {n q : ℕ}
    (hn : 0 < n) (hq : 0 < q) (hqQ : q ≤ cutoff n) : 1 / (2 * (n : ℝ)) ≤ width ρ n q := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hqQ
  unfold width
  apply (le_div_iff₀ (mul_pos hqr hnr)).mpr
  have he : (1 / (2 * (n : ℝ))) * ((q : ℝ) * n) = q / 2 := by field_simp
  rw [he]
  nlinarith only [hqQ', mul_le_mul_of_nonneg_right (hρ q) (Nat.cast_nonneg (cutoff n))]

private theorem model_floor (ρ : ℕ → ℝ) (hρ₁ : ∀ q, (1/2 : ℝ) ≤ ρ q)
    (hρ₂ : ∀ q, ρ q ≤ 2) {n : ℕ} (hn : 1024 ≤ n) (heven : Even n)
    (hsep : 4 * (cutoff n)^2 < n) :
    (26/25 : ℝ) * ((n : ℝ) + 1) ≤ (modeledContribution ρ n).re := by
  let W (q : ℕ) : ℝ := if 1 ≤ q ∧ q ≤ cutoff n then kernelMass n (width ρ n q) else 0
  let M : ℝ := (n : ℝ) + 1
  have hρ₀ (q : ℕ) : 0 ≤ ρ q := (by norm_num : (0 : ℝ) ≤ 1/2).trans (hρ₁ q)
  have haccess {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ cutoff n) : W q = kernelMass n (width ρ n q) :=
    if_pos ⟨hq,hqQ⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 2 ≤ cutoff n := (by decide : 2 ≤ 100).trans (cutoff_ge100 hn)
  have hWmid (q : ℕ) (hq : 0 < q) (hqQ : q ≤ cutoff n) : M / 2 ≤ W q := by
    rw [haccess hq hqQ]
    exact DilationKernelHalfMass.half_mass (by omega : 0 < n)
      (radius_lower ρ hρ₁ (by omega : 0 < n) hq hqQ)
  have hW0 (q : ℕ) : 0 ≤ W q := by
    by_cases h : 1 ≤ q ∧ q ≤ cutoff n
    · exact (by positivity : 0 ≤ M/2).trans (hWmid q h.1 h.2)
    · simp [W, h]
  have hWM (q : ℕ) : W q ≤ M := by
    by_cases h : 1 ≤ q ∧ q ≤ cutoff n
    · rw [haccess h.1 h.2]
      exact DilationKernel.kernelMass_upper n (width_nonneg ρ hρ₀ n q) (radius_upper ρ hρ₂ hsep h.1)
    · simpa [W, h] using hM
  have hcut (q : ℕ) (hq : cutoff n < q) : W q = 0 := by simp [W, Nat.not_le_of_lt hq]
  have hsmall (q : ℕ) (hq : 0 < q) (hq₂ : q ≤ 2) : (49/50 : ℝ) * M ≤ W q := by
    rw [haccess hq (hq₂.trans hQ)]
    apply DilationKernel.kernelMass_lower n _ (radius_upper ρ hρ₂ hsep hq)
    rw [width_eq]
    exact DilationKernel.small_dilation_radius hn hq hq₂ (hρ₁ q)
  have hsum := DilationDenominatorArithmetic.reweighted_floor coefficient coefficient_one
    coefficient_mul coefficient_prime coefficient_higher_power hQ heven W M hW0 hWM hcut hWmid
  have hmodel : (modeledContribution ρ n).re = ∑ q ∈ Icc 1 (cutoff n), (coefficient q n).re * W q := by
    simp only [modeledContribution, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact sum_congr rfl fun q hq => by rw [haccess (mem_Icc.mp hq).1 (mem_Icc.mp hq).2]
  change (26/25 : ℝ) * M ≤ _
  linarith only [hsum, hmodel, hsmall 1 (by decide) (by decide), hsmall 2 (by decide) (by decide)]

theorem eventual_floor : ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ ρ : ℕ → ℝ,
    (∀ q, (1/2 : ℝ) ≤ ρ q ∧ ρ q ≤ 2) → (n : ℝ) ≤ (majorContribution ρ n).re := by
  have hsmall := totalWideError_sublinear.eventually_lt_const (by norm_num : (0 : ℝ) < 1/50)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((cutoff_separated.and hsmall).and (eventually_ge_atTop 1024))
  refine ⟨N, ?_⟩
  intro n hn heven ρ hρ
  obtain ⟨⟨hsep,herr⟩,hbig⟩ := hN n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have herr' := (div_lt_iff₀ hn').mp herr
  have hmodel := model_floor ρ (fun q => (hρ q).1) (fun q => (hρ q).2) hbig heven hsep
  have herror := major_error ρ (fun q => (by norm_num : (0:ℝ) ≤ 1/2).trans (hρ q).1)
    (fun q => (hρ q).2) hsep
  have hd := Complex.re_le_norm (modeledContribution ρ n - majorContribution ρ n)
  rw [Complex.sub_re, norm_sub_rev] at hd
  linarith only [herr', hmodel, herror, hd, hn']

end GoldbachDenominatorDilation

theorem Conjectures.Goldbach.MajorDenominatorDilation :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let A := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let M := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => (intervalIntegral (fun t => (A n r).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ r : ℕ → ℝ, (∀ q, (1/2:ℝ) ≤ r q ∧ r q ≤ 2) → (n:ℝ) ≤ M n (fun q _ => r q) := by
  exact GoldbachDenominatorDilation.eventual_floor
