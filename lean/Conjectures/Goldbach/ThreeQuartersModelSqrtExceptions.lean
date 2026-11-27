import Mathlib

/-!
# A square-root exceptional set from uniform three-quarters model error

On each block (X/2, X] freeze the prime spectrum and the arc model at X.
Integrating the square of the model against frequency m gives a positive
linear main term. Bessel's inequality then charges the square of that
linear deficit to the variance whenever m has no two-prime representation.
The frozen hypothesis enters through the supremum norm of the model error.

This file includes adaptations of the Apache-2.0 community sources credited
in the individual sections and the pull request.
-/

section

/-! Rational window normalization and exact Fourier coefficients adapt the proofs in BeaumontCentralGapDensity, BulkPrefixEquivalence and MajorDenominatorDilation (Apache-2.0). -/

namespace GB6Geometry
noncomputable section
open Finset Filter MeasureTheory

def width (Q n q : ℕ) : ℝ := (Q:ℝ)/((q:ℝ)*n)
def arcs (Q n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ width Q n q}
def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (Q n q a : ℕ) : Set ℝ := Set.Icc (center q a - width Q n q) (center q a + width Q n q)
def leftEnd (Q n q a : ℕ) : ℝ := max (center q a - width Q n q) 0 - center q a
def rightEnd (Q n q a : ℕ) : ℝ := min (center q a + width Q n q) 1 - center q a


variable {Q : ℕ}

theorem width_nonneg (n q : ℕ) : 0 ≤ width Q n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window Q n q a ↔ |t - center q a| ≤ width Q n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * Q^2 < n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : t ∈ window Q n q a) (hb : t ∈ window Q n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
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
  have h₁ := (mem_window (Q := Q) n q a t).mp ha
  have h₂ := (mem_window (Q := Q) n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*Q^2<n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window Q n q a) (htb : t ∈ window Q n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width Q n q ≤ leftEnd Q n q a ∧ leftEnd Q n q a ≤ rightEnd Q n q a ∧ rightEnd Q n q a ≤ width Q n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg (Q := Q) n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width Q n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width Q n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window Q n q a).indicator F t) =
    ∫ β in leftEnd Q n q a..rightEnd Q n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (Q := Q) (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width Q n q) 0 ≤ min (center q a+width Q n q) 1),
    ← integral_Icc_eq_integral_Ioc]

theorem width_le_unit {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    width Q n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : Q ≤ n := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) Q]
  calc
    width Q n q = ((Q:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*Q^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd Q n q a = -(width Q n q) ∧ rightEnd Q n q a = width Q n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring


def modelPiece (Q n q a : ℕ) (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ) : ℂ :=
  C q a * ∫ β in leftEnd Q n q a..rightEnd Q n q a, K β

private theorem endpoint_models (K : ℝ → ℂ) (hK : Continuous K) (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1)
    {n : ℕ} (hn : 2*Q^2<n) :
    (∑ a ∈ numerators 1, modelPiece Q n 1 a C K) =
      C 1 0 * ∫ β in -(width Q n 1)..width Q n 1, K β := by
  let w := width Q n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit hn (by decide : 0<1)
  have h0 : leftEnd Q n 1 0 = 0 ∧ rightEnd Q n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd Q n 1 1 = -w ∧ rightEnd Q n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) (-w) 0) (hK.intervalIntegrable 0 w)
  rw [show numerators 1 = {0,1} by decide]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2]
  rw [← hC, ← mul_add, add_comm, hadd]

theorem model_by_denominator (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ)
    (hK : Continuous K) (hC : C 1 0 = C 1 1) {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece Q n q a C K) =
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width Q n q)..width Q n q, K β := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    have hone : (range 1).filter (fun a => a.Coprime 1) = {0} := by decide
    rw [hone,sum_singleton]
    exact endpoint_models K hK C hC hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece,hl,hr]


end
end GB6Geometry

namespace GB6Kernel
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def kernel (M : ℕ) (t : ℝ) := ∑ k ∈ range (M + 1), phase ((k : ℝ) * t)
def twisted (M n : ℕ) (t : ℝ) := kernel M t ^ 2 * phase (-(n : ℝ) * t)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma phase_int (j : ℤ) : phase (j : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I j using 2
  push_cast; ring

private lemma centered_mode (j : ℤ) :
    (∫ t in (-(1/2) : ℝ)..1/2, phase ((j : ℝ) * t)) = if j = 0 then 1 else 0 := by
  have hp : Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
    intro t; simp only [mul_add, mul_one, phase_add, phase_int, mul_one]
  have hshift := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, zero_add] at hshift
  rw [hshift]
  by_cases hj : j = 0
  · subst j; simp [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c; congr 1; push_cast; ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hj)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]; rw [integral_exp_mul_complex hc]; simp [hj, c, Complex.exp_int_mul_two_pi_mul_I]

/-- The coefficient of the square of a length M+1 kernel at every n up to M. -/
theorem full_coefficient (M n : ℕ) (hn : n ≤ M) :
    (∫ t in (-(1/2) : ℝ)..1/2, twisted M n t) = (n : ℂ) + 1 := by
  let I := range (M+1)
  let f (k j : ℕ) (t : ℝ) := phase (((k : ℤ) + (j : ℤ) - n : ℤ) * (t : ℝ))
  have hcont (k j : ℕ) : Continuous (f k j) := by dsimp [f, phase]; fun_prop
  have hex (t : ℝ) : twisted M n t = ∑ k ∈ I, ∑ j ∈ I, f k j t := by
    dsimp [twisted, kernel, I]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [f]; push_cast; rw [← phase_add, ← phase_add]; congr 1; ring
  have hrow (k : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, ∑ j ∈ I, f k j t) = if k ≤ n then 1 else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [f, centered_mode]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, sum_eq_single_of_mem (n-k) (show n-k ∈ I by apply mem_range.mpr; omega)]
      · simp [show (k : ℤ) + ↑(n-k) - ↑n = 0 by omega]
      · intro j _ hdiff; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
    · rw [ite_eq_right hk]; apply sum_eq_zero; intro j _; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I fun j _ => hcont k j).intervalIntegrable _ _)]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  have hset : I.filter (fun k => k ≤ n) = range (n+1) := by ext k; simp [I]; omega
  simp [hset]

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by unfold kernel phase; fun_prop
private theorem norm_packet_neg (n : ℕ) (t : ℝ) : ‖kernel n (-t)‖ = ‖kernel n t‖ := by
  have h (x : ℝ) : phase (-x) = conj (phase x) := by
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hh : kernel n (-t) = conj (kernel n t) := by
    unfold kernel
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_neg, h])
  rw [hh, Complex.norm_conj]

private theorem norm_packet_le_inv (n : ℕ) {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1/2) :
    ‖kernel n t‖ ≤ 1 / (2 * t) := by
  let z := phase t
  have hnorm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  have hp (k : ℕ) : phase ((k : ℝ) * t) = z ^ k := by
    dsimp [z, phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgeom : kernel n t * (z - 1) = z ^ (n+1) - 1 := by
    unfold kernel
    simp_rw [hp]
    exact geom_sum_mul z (n+1)
  have hz' : ‖z - 1‖ = ‖2 * Real.sin (Real.pi * t)‖ := by
    dsimp [z, phase]
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
  have hprod : ‖kernel n t‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      _ ≤ ‖z ^ (n+1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [hnorm, one_add_one_eq_two]
  have h := (mul_le_mul_of_nonneg_left hz (norm_nonneg (kernel n t))).trans hprod
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  linarith

private theorem packet_tail (n : ℕ) {b : ℝ} (hb : 0 < b) (hhalf : b ≤ 1/2) :
    (∫ t in b..(1/2 : ℝ), ‖kernel n t‖^2) ≤ 1/(4*b) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc b (1/2) := by
    rw [Set.uIcc_of_le hhalf]
    exact fun h => (not_le_of_gt hb) h.1
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-2 : ℤ)) MeasureTheory.volume b (1/2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)
  have hmono :
      (∫ t in b..(1/2 : ℝ), ‖kernel n t‖^2) ≤ ∫ t in b..(1/2 : ℝ), (1/4 : ℝ) * t^(-2 : ℤ) := by
    apply intervalIntegral.integral_mono_on hhalf ((kernel_continuous n).norm.pow 2 |>.intervalIntegrable _ _)
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

theorem integral_trunc_error (n m : ℕ) (hm : m≤n) {b : ℝ} (hb : 0<b) (hb' : b≤1/2) :
    ‖(∫ t in -b..b, twisted n m t) - ((m:ℂ)+1)‖ ≤ 1/(2*b) := by
  have hi (x y : ℝ) : IntervalIntegrable (twisted n m) volume x y := by
    unfold twisted kernel phase
    apply Continuous.intervalIntegrable
    fun_prop
  have hr (x y : ℝ) (hxy : x≤y) : ‖∫ t in x..y, twisted n m t‖ ≤ ∫ t in x..y, ‖kernel n t‖^2 := by
    have h := intervalIntegral.norm_integral_le_integral_norm hxy (f := twisted n m) (μ := volume)
    simpa only [twisted, norm_mul, norm_phase, mul_one, norm_pow] using h
  have hneg : (∫ t in (-(1/2) : ℝ)..-b, ‖kernel n t‖^2) =
      ∫ t in b..(1/2 : ℝ), ‖kernel n t‖^2 := by
    rw [← intervalIntegral.integral_comp_neg (f := fun t : ℝ => ‖kernel n t‖^2) (a := b) (b := 1/2)]
    exact intervalIntegral.integral_congr (fun t _ => by rw [norm_packet_neg])
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1/2)) (-b)) (hi (-b) b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1/2)) b) (hi b (1/2))
  rw [full_coefficient n m hm] at h2
  have he : (∫ t in -b..b, twisted n m t) - ((m:ℂ)+1) =
      -((∫ t in (-(1/2):ℝ)..-b, twisted n m t)+(∫ t in b..(1/2:ℝ), twisted n m t)) := by
    linear_combination h1 + h2
  rw [he, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have h3 := hr (-(1/2)) (-b) (neg_le_neg hb')
  rw [hneg] at h3
  linarith [hr b (1/2) hb', packet_tail n hb hb', show (1:ℝ)/(2*b)=2*(1/(4*b)) by ring]

end
end GB6Kernel
namespace GB6Geometry
noncomputable section
open Finset MeasureTheory GB6Kernel
abbrev Idx := (_ : ℕ) × ℕ
def indices (Q : ℕ) : Finset Idx := (Icc 1 Q).sigma numerators
def model (Q H n : ℕ) (amp : ℕ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ q ∈ Icc 1 Q, ∑ a ∈ numerators q, (window H n q a).indicator
    (fun u => amp q a * kernel n (u-center q a)) t

theorem unique_window {n H Q : ℕ} (hs : 2*H^2<n) (hQ : Q≤H) (t : ℝ) :
    ({i : Idx | i ∈ indices Q ∧ t ∈ window H n i.1 i.2} : Set Idx).Subsingleton := by
  rintro ⟨q,a⟩ ⟨hi,ht⟩ ⟨r,b⟩ ⟨hj,hu⟩
  obtain ⟨hq,ha⟩ := mem_sigma.mp hi
  obtain ⟨hr,hb⟩ := mem_sigma.mp hj
  have lift {k : ℕ} (h : k ∈ Icc 1 Q) : k ∈ Icc 1 H :=
    mem_Icc.mpr ⟨(mem_Icc.mp h).1, (mem_Icc.mp h).2.trans hQ⟩
  obtain ⟨rfl,rfl⟩ := center_unique hs (lift hq) (lift hr) ha hb ht hu
  rfl

theorem model_sigma (Q H n : ℕ) (amp : ℕ→ℕ→ℂ) (t : ℝ) :
    model Q H n amp t = ∑ i ∈ indices Q, (window H n i.1 i.2).indicator
      (fun u => amp i.1 i.2 * kernel n (u-center i.1 i.2)) t := by
  unfold model indices
  rw [Finset.sum_sigma]
end
end GB6Geometry

end

section

namespace GB6Geometry
noncomputable section
open Finset MeasureTheory GB6Kernel

private theorem unique_square {ι : Type*} (P : Finset ι) (s : ι → Set ℝ)
    (f : ι → ℝ → ℂ) (z : ℂ) (t : ℝ)
    (hu : ({i : ι | i ∈ P ∧ t ∈ s i} : Set ι).Subsingleton) :
    (∑ i ∈ P, (s i).indicator (f i) t)^2*z =
    ∑ i ∈ P, (s i).indicator (fun u => f i u ^ 2 * z) t := by
  classical
  by_cases h : ∃ i ∈ P, t ∈ s i
  · obtain ⟨i,hi,ht⟩ := h
    have hno : ∀ j ∈ P, j ≠ i → t ∉ s j := fun j hj hji h' => hji (hu ⟨hj,h'⟩ ⟨hi,ht⟩)
    rw [sum_eq_single_of_mem i hi (fun j hj hji => Set.indicator_of_notMem (hno j hj hji) _),
      sum_eq_single_of_mem i hi (fun j hj hji => Set.indicator_of_notMem (hno j hj hji) _)]
    simp only [Set.indicator_of_mem ht]
  · have hno : ∀ i ∈ P, t ∉ s i := by simpa using h
    rw [sum_eq_zero (fun i hi => Set.indicator_of_notMem (hno i hi) _),
      sum_eq_zero (fun i hi => Set.indicator_of_notMem (hno i hi) _)]
    ring

private def coeff (amp : ℕ → ℕ → ℂ) (m q a : ℕ) :=
    (amp q a)^2 * phase (-(m:ℝ)*center q a)

set_option maxHeartbeats 2500000 in
theorem exact_model_coeff {Q H n m : ℕ} (amp : ℕ→ℕ→ℂ) (hh : amp 1 0 = amp 1 1)
    (hs : 2*H^2<n) (hQ : Q≤H) :
    (∫ t in (0:ℝ)..1, (model Q H n amp t)^2 * phase (-(m:ℝ)*t)) =
    ∑ q ∈ Icc 1 Q,
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), (amp q a)^2 * phase (-(m:ℝ)*center q a)) *
      ∫ β in -(width H n q)..width H n q, twisted n m β := by
  classical
  let f (q a : ℕ) (t : ℝ) := (amp q a * kernel n (t-center q a))^2*phase (-(m:ℝ)*t)
  have point (t : ℝ) : model Q H n amp t ^2 * phase (-(m:ℝ)*t) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ numerators q, (window H n q a).indicator (f q a) t := by
    rw [model_sigma, Finset.sum_sigma']
    apply (unique_square (indices Q) (fun i => window H n i.1 i.2)
      (fun i u => amp i.1 i.2 * kernel n (u-center i.1 i.2)) _ _ (unique_window hs hQ t)).trans
    apply sum_congr rfl
    intro i hi
    by_cases ht : t ∈ window H n i.1 i.2 <;> simp [ht, f]
  have hfi (q a : ℕ) : IntervalIntegrable ((window H n q a).indicator (f q a)) volume 0 1 := by
    have hfc : Continuous (f q a) := by dsimp [f, kernel, phase]; fun_prop
    exact ⟨(hfc.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hfc.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  have hphase (x y : ℝ) : phase (x+y) = phase x * phase y := by
    unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hm1 : phase (-(m:ℝ)) = 1 := by
    have hx : phase (((-(m:ℤ)):ℤ):ℝ) = 1 := by
      unfold phase; convert Complex.exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 2; push_cast; ring
    simpa using hx
  have hC : coeff amp m 1 0 = coeff amp m 1 1 := by
    simp [coeff, center, hh, hm1, show phase 0 = 1 by simp [phase]]
  simp_rw [point]
  have hrow (q : ℕ) : IntervalIntegrable (fun t => ∑ a ∈ numerators q, (window H n q a).indicator (f q a) t) volume 0 1 :=
    ⟨integrable_finsetSum _ (fun a _ => (hfi q a).1), integrable_finsetSum _ (fun a _ => (hfi q a).2)⟩
  rw [intervalIntegral.integral_finsetSum (fun q _ => hrow q)]
  apply sum_congr rfl
  intro q hq
  rw [intervalIntegral.integral_finsetSum (fun a _ => hfi q a)]
  refine (sum_congr rfl (g := fun a => modelPiece H n q a (coeff amp m) (twisted n m)) ?_).trans ?_
  · intro a ha
    rw [indicator_clipped (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)), modelPiece,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [f,coeff,twisted]
    rw [add_sub_cancel_left, mul_add, hphase]
    ring
  · exact model_by_denominator (coeff amp m) (twisted n m)
      (by unfold twisted kernel phase; fun_prop) hC hs (mem_Icc.mp hq).1
end
end GB6Geometry

end

section

/-!
The arithmetic main-term bound and Ramanujan identities are adapted from
the Apache-2.0 goldbach-proofs results of DFQDZZ (PR #316), XianWu18 (PR #207)
and wzhxzkk (PR #203), as reproduced by the accepted BeaumontCentralGapDensity
at revision 29a85e9c23a2243976bc2f26ccf767b97705f00a.
-/
open scoped BigOperators ComplexConjugate
open Finset
namespace ThreeQArith
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def mean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)
end
end ThreeQArith
/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace ThreeQArith.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end ThreeQArith.RamanujanCRT
namespace ThreeQArith.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end ThreeQArith.RamanujanPower

namespace ThreeQArith

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem mean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    mean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (mean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [mean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end ThreeQArith

namespace ThreeQArith

open Finset
noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      prod_eq_one fun p hp => ite_eq_right (Nat.not_le.mpr (mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, prod_range_succ, ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      prod_congr rfl fun p hp => (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

/-- Every finite set of odd primes has absolute Euler excess at most 2/3.
Separate p = 3 and telescope the comparison product starting at p = 5. -/
theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [prod_insert (notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

/-- Summing the signed factors at primes away from an even target leaves at least
a third of the mass at d. The function W may already include a denominator cutoff. -/
theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := mem_powerset.mp (mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := sum_le_sum hterm
  simp only [sum_neg_distrib, ← mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

end
end ThreeQArith

namespace ThreeQArith

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
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
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- The even-target arithmetic main term retains at least one third of the q = 1
mass under every nonnegative decreasing weight supported on the denominator cutoff. -/
theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (mem_filter.mp hp)
    have hpr := (mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

end
end ThreeQArith



/-! Adapted from `L_goldbach_coset_unit_energy_upper.lean` in goldbach-proofs (Apache-2.0).
The sharper final bound uses the integer binary logarithm directly. -/
namespace ThreeQArith.Totient
open Finset
private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem ratio_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ (Nat.log 2 q : ℝ) + 1 := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog : q.primeFactors.card ≤ Nat.log 2 q := Nat.le_log_of_pow_le (by decide) hpow
  rw [heq]
  exact hh.trans (by exact_mod_cast Nat.add_le_add_right hlog 1)

end ThreeQArith.Totient

namespace ThreeQArith
open Finset
noncomputable section

theorem main_floor (Q m : ℕ) (hQ : 1 ≤ Q) (he : Even m) :
    (1:ℝ)/3 ≤ (∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (mean q a)^2 * phase (-(m:ℝ)*((a:ℝ)/q))).re := by
  let W (q : ℕ) : ℝ := if q ≤ Q then 1 else 0
  have hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i := by
    intro i j _ hij
    by_cases h : j ≤ Q
    · simp [W,h,hij.trans h]
    · simp only [W,ite_eq_right h]; split_ifs <;> norm_num
  have h := arithmetic_floor (Q:=Q) he W (fun q => by simp [W]; positivity) hmono
    (fun q h => by simp [W,not_le.mpr h])
  simp_rw [sum_centers_eq_coefficient,Complex.re_sum]
  have heq : ∑ q ∈ Icc 1 Q, (coefficient q m).re * W q =
      ∑ q ∈ Icc 1 Q, (coefficient q m).re := by
    apply sum_congr rfl
    intro q hq
    simp [W,(mem_Icc.mp hq).2]
  simpa only [heq,W,ite_eq_left hQ] using h

private theorem norm_ram_one (q : ℕ) : ‖ram q 1‖ ≤ 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j => rw [ram_unit_power hp j 1 (by simp)]; split_ifs <;> norm_num
  | coprime a b ha hb hab ia ib =>
    rw [ram_mul (by omega) (by omega) hab, norm_mul]
    exact (mul_le_mul ia ib (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem norm_mean_le {q a : ℕ} (hc : a.Coprime q) :
    ‖mean q a‖ ≤ 1/(q.totient:ℝ) := by
  rw [mean_eq_ram hc,norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_ram_one q) (Nat.cast_nonneg _)

theorem error_sum (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (q:ℝ)*‖mean q a‖^2) ≤ (Q:ℝ)*(1+(Nat.log 2 Q:ℝ)) := by
  have hcard (q : ℕ) : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [mem_filter]
    exact and_congr_right (fun _ => Nat.coprime_comm)
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, (1+(Nat.log 2 Q:ℝ)) := by
      apply sum_le_sum
      intro q hq
      have hpos := Nat.totient_pos.mpr (mem_Icc.mp hq).1
      have hpr : (0:ℝ) < q.totient := by exact_mod_cast hpos
      calc
        _ ≤ ∑ _a ∈ (range q).filter (fun a => a.Coprime q),
            (q:ℝ)*(1/(q.totient:ℝ))^2 := by
          apply sum_le_sum
          intro a ha
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_mean_le (mem_filter.mp ha).2) _
        _ = (q:ℝ)/q.totient := by simp [hcard]; field_simp
        _ ≤ _ := (Totient.ratio_le q (mem_Icc.mp hq).1).trans (by
          have h : (Nat.log 2 q:ℝ) ≤ (Nat.log 2 Q:ℝ) := by exact_mod_cast Nat.log_mono_right (mem_Icc.mp hq).2
          linarith)
    _ = _ := by simp; ring
end
end ThreeQArith

end

section

namespace GB6Geometry
noncomputable section
open Finset MeasureTheory GB6Kernel

theorem model_floor {Q H n m : ℕ} (hs : 2*H^2<n) (hQH : Q≤H) (hQ : 1≤Q)
    (hnm : n/2 < m) (hm : m ≤ n) (he : Even m)
    (hbudget : (Q:ℝ)*(1+(Nat.log 2 Q:ℝ))/(2*(H:ℝ)) ≤ 1/32) :
    (n:ℝ)/8 ≤ (∫ t in (0:ℝ)..1, (model Q H n ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)).re := by
  classical
  let S (q : ℕ) := (range q).filter (fun a => a.Coprime q)
  let A (q a : ℕ) := (ThreeQArith.mean q a)^2 * phase (-(m:ℝ)*center q a)
  let B (q : ℕ) := ∑ a ∈ S q, A q a
  let J (q : ℕ) := ∫ t in -(width H n q)..width H n q, twisted n m t
  have hHr : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hnr : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hfloor : (1:ℝ)/3 ≤ (∑ q ∈ Icc 1 Q, B q).re := ThreeQArith.main_floor Q m hQ he
  have hcoef : (∫ t in (0:ℝ)..1, (model Q H n ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)) =
      ∑ q ∈ Icc 1 Q, B q * J q := by
    apply exact_model_coeff ThreeQArith.mean _ hs hQH
    simp [ThreeQArith.mean, ThreeQArith.phase]
  have heq : (∑ q ∈ Icc 1 Q, B q * J q) - (∑ q ∈ Icc 1 Q, B q) * ((m:ℂ)+1) =
      ∑ q ∈ Icc 1 Q, B q * (J q - ((m:ℂ)+1)) := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => (mul_sub ..).symm
  have heach (q : ℕ) (hq : q ∈ Icc 1 Q) : ‖B q * (J q - ((m:ℂ)+1))‖ ≤
      (∑ a ∈ S q, (q:ℝ)*‖ThreeQArith.mean q a‖^2)*((n:ℝ)/(2*H)) := by
    have hqr : (0:ℝ)<q := by exact_mod_cast (mem_Icc.mp hq).1
    have hw : 0<width H n q := div_pos hHr (mul_pos hqr hnr)
    have hhalf : width H n q≤1/2 := by
      have hnH : 2*H≤n := by nlinarith only [hs,Nat.le_self_pow (by decide : 2≠0) H]
      have hqr1 : (1:ℝ)≤q := by exact_mod_cast (mem_Icc.mp hq).1
      apply (div_le_iff₀ (mul_pos hqr hnr)).mpr
      have hr : 2*(H:ℝ)≤n := by exact_mod_cast hnH
      nlinarith only [hr,mul_le_mul_of_nonneg_right hqr1 hnr.le]
    have htail : ‖J q - ((m:ℂ)+1)‖ ≤ (q:ℝ) * ((n:ℝ)/(2*H)) := by
      refine (integral_trunc_error n m hm hw hhalf).trans_eq ?_
      unfold width; field_simp
    have hB : ‖B q‖ ≤ ∑ a ∈ S q, ‖ThreeQArith.mean q a‖^2 := by
      refine (norm_sum_le ..).trans_eq ?_
      apply sum_congr rfl
      intro a _
      have hp (u : ℝ) : ‖phase u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      simp only [A, norm_mul,norm_pow,hp,mul_one]
    rw [norm_mul, ← mul_sum]
    exact (mul_le_mul hB htail (norm_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)
  have hd : ‖(∑ q ∈ Icc 1 Q, B q * J q) - (∑ q ∈ Icc 1 Q, B q) * ((m:ℂ)+1)‖ ≤ (n:ℝ)/32 := by
    rw [heq]
    refine (norm_sum_le ..).trans ((sum_le_sum heach).trans ?_)
    rw [←sum_mul]
    refine (mul_le_mul_of_nonneg_right (ThreeQArith.error_sum Q) (by positivity)).trans ?_
    calc
      (Q:ℝ)*(1+(Nat.log 2 Q:ℝ))*((n:ℝ)/(2*H)) = ((Q:ℝ)*(1+(Nat.log 2 Q:ℝ))/(2*H))*n := by ring
      _ ≤ (1/32:ℝ)*n := mul_le_mul_of_nonneg_right hbudget hnr.le
      _ = _ := by ring
  have diff := (Complex.abs_re_le_norm _).trans hd
  rw [Complex.sub_re, Complex.mul_re] at diff
  simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.add_im,Complex.natCast_im,Complex.one_im,zero_add,mul_zero,sub_zero] at diff
  rw [hcoef]
  have hhalf : (n:ℝ) ≤ 2*m := by exact_mod_cast (show n ≤ 2*m by omega)
  have hmf : 0≤ (m:ℝ)+1 := by positivity
  linarith [mul_le_mul_of_nonneg_right hfloor hmf,(abs_le.mp diff).1]
end
end GB6Geometry

end

section

/-! Parseval for the finite prime spectrum is adapted from `ThreeQuartersExceptionalDirichletWindows`; the finite Fourier variance argument adapts `MaskedBesselVariance` (goldbach-proofs, Apache 2.0). -/
namespace GB5Variance
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate

def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

theorem continuous_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * phase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, phase (x + y) = phase x * phase y := by
    intro x y
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous phase := by
    unfold phase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, phase (m : ℝ) = 1 := by
    intro m
    unfold phase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (phase x) = phase (-x) := by
    intro x
    unfold phase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => phase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => phase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold phase
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
        simpa only [phase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * phase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
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
    have hmul : phase (-((k : ℝ) * t)) * phase ((j : ℝ) * t) =
        phase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * phase (-((k : ℝ) * t))) *
          ((w j : ℂ) * phase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (phase (-((k : ℝ) * t)) * phase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
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
          ((w k : ℂ) * (w j : ℂ)) * phase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

end
end GB5Variance


namespace GB5Variance
noncomputable section
open Finset MeasureTheory

abbrev unitMeasure := volume.restrict (Set.Ioc (0:ℝ) 1)

def modeCoeff (f : ℝ → ℂ) (m : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, f t * phase (-(m:ℝ)*t)

theorem finite_bessel (s : Finset ℕ) (f : ℝ → ℂ) (hf : MemLp f 2 unitMeasure) :
    ∑ m∈s, ‖modeCoeff f m‖^2 ≤ ∫ t in (0:ℝ)..1,‖f t‖^2 := by
  have hcoeff (m : ℕ) : fourierCoeffOn (zero_lt_one : (0:ℝ)<1) f (m:ℤ) = modeCoeff f m := by
    rw [fourierCoeffOn_eq_integral,sub_zero,one_div_one,one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [smul_eq_mul,fourier_coe_apply,phase]
    rw [mul_comm]
    congr 1
    push_cast
    congr 1
    ring
  let frequency : ℕ ↪ ℤ := ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hh := sum_le_hasSum (s.map frequency) (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖)
    (hasSum_sq_fourierCoeffOn (zero_lt_one : (0:ℝ)<1) hf)
  rw [Finset.sum_map] at hh
  change (∑ m ∈ s, ‖fourierCoeffOn (zero_lt_one : (0:ℝ)<1) f (m:ℤ)‖^2) ≤ _ at hh
  simpa only [hcoeff,sub_zero,inv_one,one_smul] using hh

private theorem int_sq {f : ℝ→ℂ} (hf : MemLp f 2 unitMeasure) :
    IntervalIntegrable (fun t => ‖f t‖^2) volume (0:ℝ) 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)

theorem variance (s : Finset ℕ) (F G : ℝ → ℂ) (U : ℝ)
    (hF : MemLp F 2 unitMeasure) (hG : MemLp G 2 unitMeasure)
    (hU : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖F t-G t‖ ≤ U) :
    ∑ m∈s, ‖modeCoeff (fun t => F t^2 - G t^2) m‖^2 ≤
      2*U^2*((∫ t in (0:ℝ)..1, ‖F t‖^2) + (∫ t in (0:ℝ)..1, ‖G t‖^2)) := by
  let D := fun t => F t^2-G t^2
  have hDpoint (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) : ‖D t‖ ≤ U*‖F t + G t‖ := by
    dsimp only [D]
    rw [sq_sub_sq, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hU t ht) (norm_nonneg _)
  have hDa : AEStronglyMeasurable D unitMeasure := (hF.aestronglyMeasurable.pow 2).sub (hG.aestronglyMeasurable.pow 2)
  have hD : MemLp D 2 unitMeasure := (hF.add hG).of_le_mul hDa <|
    (ae_restrict_iff' measurableSet_Ioc).2 <| Filter.Eventually.of_forall fun t ht => hDpoint t ⟨ht.1.le,ht.2⟩
  have hUp : 0 ≤ U := (norm_nonneg _).trans (hU 0 ⟨le_rfl,zero_le_one⟩)
  refine (finite_bessel s D hD).trans ?_
  have hsum := (int_sq hF).add (int_sq hG)
  calc
    (∫ t in (0:ℝ)..1, ‖D t‖^2) ≤ ∫ t in (0:ℝ)..1, (2*U^2)*(‖F t‖^2 + ‖G t‖^2) := by
      apply intervalIntegral.integral_mono_on zero_le_one (int_sq hD) (hsum.const_mul _)
      intro t ht
      have h0 := (hDpoint t ht).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hUp)
      have hh := mul_self_le_mul_self (norm_nonneg _) h0
      nlinarith [mul_nonneg (sq_nonneg U) (sq_nonneg (‖F t‖ - ‖G t‖))]
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (int_sq hF) (int_sq hG)]

end
end GB5Variance


namespace GB5Variance
noncomputable section
open Finset MeasureTheory

def kernel (Y : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (Y+1), phase ((k:ℝ)*t)

theorem kernel_continuous (Y : ℕ) : Continuous (kernel Y) := by unfold kernel phase; fun_prop

theorem kernel_periodic (Y : ℕ) : Function.Periodic (kernel Y) 1 := by
  intro t
  apply sum_congr rfl
  intro k _
  unfold phase
  have h : ((2*Real.pi*((k:ℝ)*(t+1)) : ℝ) : ℂ)*Complex.I =
      ((2*Real.pi*((k:ℝ)*t) : ℝ) : ℂ)*Complex.I + (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    push_cast; ring
  rw [h,Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,mul_one]

theorem kernel_energy (Y : ℕ) (c : ℝ) :
    (∫ t in (0:ℝ)..1, ‖kernel Y (t-c)‖^2) = (Y:ℝ)+1 := by
  have hp : Function.Periodic (fun t => ‖kernel Y t‖^2) 1 :=
    (kernel_periodic Y).comp (fun z => ‖z‖^2)
  have h := hp.intervalIntegral_add_eq (-c) 0
  have hb := continuous_parseval Y (fun _ => (1:ℝ))
  calc
    _ = ∫ t in (0:ℝ)-c..1-c, ‖kernel Y t‖^2 := intervalIntegral.integral_comp_sub_right (fun t => ‖kernel Y t‖^2) _
    _ = ∫ t in (0:ℝ)..1, ‖kernel Y t‖^2 := by simpa only [zero_sub,zero_add,sub_eq_add_neg,add_comm,add_zero] using h
    _ = _ := by simpa [kernel,phase] using hb

def disjointModel {ι : Type*} (Y : ℕ) (P : Finset ι) (window : ι → Set ℝ)
    (amp : ι → ℂ) (ctr : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ P, (window i).indicator (fun x => amp i * kernel Y (x-ctr i)) t

theorem model_memLp {ι : Type*} (Y : ℕ) (P : Finset ι) (window : ι → Set ℝ)
    (amp : ι → ℂ) (ctr : ι → ℝ) (hw : ∀ i∈P, MeasurableSet (window i)) :
    MemLp (disjointModel Y P window amp ctr) 2 unitMeasure := by
  apply memLp_finsetSum
  intro i hi
  apply MemLp.indicator (hw i hi).nullMeasurableSet
  have hc : Continuous (fun x : ℝ => amp i*kernel Y (x-ctr i)) :=
    continuous_const.mul ((kernel_continuous Y).comp (continuous_id.sub continuous_const))
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ((hc.norm.pow 2).intervalIntegrable 0 1).1

theorem model_energy {ι : Type*} (Y : ℕ) (P : Finset ι) (window : ι → Set ℝ)
    (amp : ι → ℂ) (ctr : ι → ℝ) (hw : ∀ i∈P, MeasurableSet (window i))
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ i∈P, ∀ j∈P, t∈window i → t∈window j → i=j) :
    (∫ t in (0:ℝ)..1, ‖disjointModel Y P window amp ctr t‖^2) ≤
      ((Y:ℝ)+1)*(∑ i∈P, ‖amp i‖^2) := by
  classical
  let energy (i : ι) (t : ℝ) := ‖amp i‖^2 * ‖kernel Y (t-ctr i)‖^2
  have ec (i : ι) : Continuous (energy i) :=
    continuous_const.mul (((kernel_continuous Y).comp (continuous_id.sub continuous_const)).norm.pow 2)
  have ei (i : ι) : IntervalIntegrable (energy i) volume 0 1 := (ec i).intervalIntegrable ..
  have hm := model_memLp Y P window amp ctr hw
  have hi : IntervalIntegrable (fun t => ‖disjointModel Y P window amp ctr t‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ∑ i ∈ P, energy i t := by
      apply intervalIntegral.integral_mono_on zero_le_one hi ((continuous_finsetSum _ (fun i _ => ec i)).intervalIntegrable ..)
      intro t ht
      by_cases h : ∃ i∈P, t∈window i
      · obtain ⟨i,hP,hiw⟩ := h
        have he : disjointModel Y P window amp ctr t = amp i*kernel Y (t-ctr i) := by
          unfold disjointModel
          rw [sum_eq_single_of_mem i hP _ , Set.indicator_of_mem hiw]
          intro j hj hne
          exact Set.indicator_of_notMem (fun hmem => hne (hu t ht j hj i hP hmem hiw)) _
        rw [he,norm_mul,mul_pow]
        exact single_le_sum (f := fun j => energy j t) (fun j _ => by dsimp [energy]; positivity) hP
      · unfold disjointModel
        rw [sum_eq_zero (fun i hi => Set.indicator_of_notMem (fun hiw => h ⟨i,hi,hiw⟩) _),norm_zero,zero_pow (by decide : 2≠0)]
        exact sum_nonneg (fun i _ => by dsimp [energy]; positivity)
    _ = ∑ i∈P, ‖amp i‖^2*((Y:ℝ)+1) := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => ei i)]
      apply sum_congr rfl
      intro i _
      dsimp only [energy]
      rw [intervalIntegral.integral_const_mul,kernel_energy]
    _ = _ := by rw [←sum_mul,mul_comm]

end
end GB5Variance

end

section

/-! Fourier orthogonality for the exceptional coefficient follows the Apache-2.0
BeaumontCentralGapDensity source, revision 29a85e9c23a2243976bc2f26ccf767b97705f00a. -/
namespace GB6Var
open Finset MeasureTheory GB5Variance
noncomputable section
private noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

theorem zero_from_pairs (w : ℕ → ℝ) (n Y : ℕ) (hn : ∀ k j : ℕ, k+j=n → w k*w j=0) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (Y+1), (w k : ℂ)*E ((k : ℝ)*t))^2 * E (-(n:ℝ)*t)) = 0 := by
  let I := Finset.range (Y+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  change (∫ t in (0:ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t))^2 * E (-(n:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro k _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro j _
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases heq : (k : ℤ)+j-n = 0
  · have hz : w k*w j=0 := hn k j (by omega)
    simp only [heq, ite_true, mul_one]
    exact_mod_cast hz
  · simp [heq]

def weight (k : ℕ) : ℝ := if k.Prime then Real.log (k:ℝ) else 0
def S (M : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (M+1), (weight k:ℂ)*GB5Variance.phase ((k:ℝ)*t)
abbrev G (Q H M : ℕ) := GB6Geometry.model Q H M ThreeQArith.mean
def D (Q H M m : ℕ) : ℝ := ‖modeCoeff (fun t => (S M t)^2-(G Q H M t)^2) m‖

theorem S_memLp (M : ℕ) : MemLp (S M) 2 unitMeasure := by
  have hc : Continuous (S M) := by unfold S GB5Variance.phase; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp ((hc.norm.pow 2).intervalIntegrable ..)

theorem S_energy (M : ℕ) : (∫ t in (0:ℝ)..1, ‖S M t‖^2) ≤
    ((M:ℝ)+1)*(1+Real.log ((M:ℝ)+2))^2 := by
  have h := continuous_parseval M weight
  change (∫ t in (0:ℝ)..1, ‖S M t‖^2) = _ at h
  rw [h]
  calc
    _ ≤ ∑ _k ∈ range (M+1), (1+Real.log ((M:ℝ)+2))^2 := by
      apply sum_le_sum
      intro k hk
      by_cases hp : k.Prime
      · rw [weight,ite_eq_left hp]
        apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hp.one_le))
        have hle : (k:ℝ) ≤ (M:ℝ)+2 := by exact_mod_cast (show k ≤ M+2 by have := mem_range.mp hk; omega)
        linarith [Real.log_le_log (by exact_mod_cast hp.pos) hle]
      · simp [weight,hp]; positivity
    _ = _ := by simp

theorem S_zero {m M : ℕ} (hn : (((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card)=0) :
    modeCoeff (fun t => (S M t)^2) m = 0 := by
  apply zero_from_pairs weight m M
  intro k j h
  by_cases hk : k.Prime
  · have hj : ¬j.Prime := by
      intro hj
      have hmem : k ∈ (range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime) := by
        exact mem_filter.mpr ⟨mem_range.mpr (by omega),hk,by simpa [← h] using hj⟩
      rw [card_eq_zero.mp hn] at hmem
      exact notMem_empty _ hmem
    simp [weight,hj]
  · simp [weight,hk]

private theorem square_mode_integrable {F : ℝ → ℂ} (hF : MemLp F 2 unitMeasure) (m : ℕ) :
    IntervalIntegrable (fun t => (F t)^2 * GB5Variance.phase (-(m:ℝ)*t)) volume (0:ℝ) 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  have hmeas : AEStronglyMeasurable (fun t => (F t)^2 * GB5Variance.phase (-(m:ℝ)*t)) unitMeasure :=
    (hF.aestronglyMeasurable.pow 2).mul (by unfold GB5Variance.phase; fun_prop)
  apply (integrable_norm_iff hmeas).mp
  have heq (t : ℝ) : ‖F t^2 * GB5Variance.phase (-(m:ℝ)*t)‖ = ‖F t‖^2 := by
    rw [norm_mul,norm_pow, GB5Variance.phase, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp only [heq]
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF

theorem half_gap {Q H M m : ℕ} (hG : MemLp (G Q H M) 2 unitMeasure)
    (hn : (((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card)=0) :
    (modeCoeff (fun t => (G Q H M t)^2) m).re ≤ D Q H M m := by
  unfold D
  have he : modeCoeff (fun t => S M t^2-G Q H M t^2) m =
      modeCoeff (fun t => S M t^2) m - modeCoeff (fun t => G Q H M t^2) m := by
    simp only [modeCoeff,sub_mul]
    exact intervalIntegral.integral_sub (square_mode_integrable (S_memLp M) m) (square_mode_integrable hG m)
  rw [he,S_zero hn,zero_sub,norm_neg]
  exact Complex.re_le_norm _

theorem amp_energy (Q M : ℕ) (hQ : Q ≤ M) :
    (∑ i ∈ GB6Geometry.indices Q, ‖ThreeQArith.mean i.1 i.2‖^2) ≤
      4*(1+Real.log ((M:ℝ)+2))^2 := by
  have logNN : 0 ≤ Real.log ((M:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have mlog (q : ℕ) (hq : 1 ≤ q) (hqm : q ≤ M) :
      Real.log (q:ℝ) ≤ Real.log ((M:ℝ)+2) := by
    exact Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast (show q ≤ M+2 by omega))
  have hqlog (q : ℕ) (hp : 1 ≤ q) (hqm : q ≤ M) :
      (Nat.log 2 q:ℝ) ≤ 2*Real.log ((M:ℝ)+2) := by
    have hh := Real.natLog_le_logb q 2
    have hh' : (Nat.log 2 q:ℝ)*Real.log 2 ≤ Real.log (q:ℝ) :=
      (le_div_iff₀ (Real.log_pos (by norm_num))).mp hh
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 q))
      (show (0:ℝ) ≤ Real.log 2 - 1/2 by linarith [Real.log_two_gt_d9]),mlog q hp hqm]
  have hharm : (∑ q ∈ Icc 1 Q, (q:ℝ)⁻¹) ≤ 1+Real.log ((M:ℝ)+2) := by
    by_cases h : Q=0
    · simp [h]; linarith
    have hh := harmonic_le_one_add_log Q
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,Rat.cast_natCast] at hh
    exact hh.trans (by linarith [mlog Q (by omega) hQ])
  unfold GB6Geometry.indices
  rw [sum_sigma]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (2*(1+2*Real.log ((M:ℝ)+2)))*(q:ℝ)⁻¹ := by
      apply sum_le_sum
      intro q hq
      have hqp := (mem_Icc.mp hq).1
      have hqr : (0:ℝ) < q := by exact_mod_cast hqp
      have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqp
      have hcnt : (GB6Geometry.numerators q).card ≤ 2*q.totient := by
        have hs : GB6Geometry.numerators q ⊆ insert q ((range q).filter (fun a => q.Coprime a)) := by
          intro a ha
          obtain ⟨hr,hc⟩ := mem_filter.mp ha
          rcases lt_or_ge a q with h|h
          · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr h,hc.symm⟩)
          · exact mem_insert.mpr (Or.inl (by have := mem_range.mp hr; omega))
        have h := (card_le_card hs).trans (card_insert_le q _)
        rw [← Nat.totient_eq_card_coprime] at h
        have := Nat.totient_pos.mpr hqp
        omega
      calc
        _ ≤ ∑ _a ∈ GB6Geometry.numerators q, (1/(q.totient:ℝ))^2 := by
          apply sum_le_sum
          intro a ha
          exact pow_le_pow_left₀ (norm_nonneg _) (ThreeQArith.norm_mean_le (mem_filter.mp ha).2) _
        _ = ((GB6Geometry.numerators q).card:ℝ)*(1/(q.totient:ℝ))^2 := by simp
        _ ≤ (2*(q.totient:ℝ))*(1/(q.totient:ℝ))^2 := by gcongr; exact_mod_cast hcnt
        _ = 2*((q:ℝ)/q.totient)*(q:ℝ)⁻¹ := by field_simp
        _ ≤ _ := by
          have h := (ThreeQArith.Totient.ratio_le q hqp).trans (add_le_add_left (hqlog q hqp ((mem_Icc.mp hq).2.trans hQ)) _)
          gcongr
          linarith
    _ = (2*(1+2*Real.log ((M:ℝ)+2)))*(∑ q ∈ Icc 1 Q,(q:ℝ)⁻¹) := (mul_sum ..).symm
    _ ≤ (2*(1+2*Real.log ((M:ℝ)+2)))*(1+Real.log ((M:ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ ≤ _ := by nlinarith
open GB6Geometry

private theorem G_repr (Q H M : ℕ) : G Q H M =
    disjointModel M (indices Q) (fun i => window H M i.1 i.2)
      (fun i => ThreeQArith.mean i.1 i.2) (fun i => center i.1 i.2) := by
  funext t
  exact model_sigma Q H M ThreeQArith.mean t

theorem G_memLp (Q H M : ℕ) : MemLp (G Q H M) 2 unitMeasure := by
  rw [G_repr]
  exact model_memLp M (indices Q) (fun i => window H M i.1 i.2)
    (fun i => ThreeQArith.mean i.1 i.2) (fun i => center i.1 i.2) (fun _ _ => measurableSet_Icc)

theorem G_energy {Q H M : ℕ} (hqM : Q ≤ M) (hs : 2*H^2 < M) (hQ : Q ≤ H) :
    (∫ t in (0:ℝ)..1, ‖G Q H M t‖^2) ≤ ((M:ℝ)+1)*(4*(1+Real.log ((M:ℝ)+2))^2) := by
  rw [G_repr]
  have h := model_energy M (indices Q) (fun i => window H M i.1 i.2)
    (fun i => ThreeQArith.mean i.1 i.2) (fun i => center i.1 i.2) (fun _ _ => measurableSet_Icc)
    (fun t _ _ hi _ hj hiw hjw => unique_window hs hQ t ⟨hi,hiw⟩ ⟨hj,hjw⟩)
  exact h.trans (mul_le_mul_of_nonneg_left (amp_energy Q M hqM) (by positivity))

/-- The concrete variance before absorbing the fixed logarithmic losses. -/
theorem variance_bound (s : Finset ℕ) {Q H M : ℕ} (hqM : Q ≤ M) (hs : 2*H^2 < M)
    (hQ : Q ≤ H) (U : ℝ) (hU : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖S M t-G Q H M t‖ ≤ U) :
    (∑ m ∈ s, (D Q H M m)^2) ≤ 10*U^2*((M:ℝ)+1)*(1+Real.log ((M:ℝ)+2))^2 := by
  have h := variance s (S M) (G Q H M) U (S_memLp M) (G_memLp ..) hU
  have hE := add_le_add (S_energy M) (G_energy hqM hs hQ)
  refine h.trans ((mul_le_mul_of_nonneg_left hE (by positivity)).trans_eq ?_)
  ring

theorem exception_gap {Q H M m : ℕ}
    (he : (((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card)=0)
    (hfloor : (M:ℝ)/8 ≤ (modeCoeff (fun t => (G Q H M t)^2) m).re) :
    (M:ℝ)/8 ≤ D Q H M m := hfloor.trans (half_gap (G_memLp ..) he)
end
end GB6Var

end

section

/-! The finite second-moment charge and the halving recurrence below are adapted
from the verified goldbach-proofs module `L_goldbach_grh_goldbach_exception_density`.
Their inputs here are a discrepancy for the sharp prime-log sum and a fixed-cutoff
model, with the actual prime-representation set in the statement. -/
namespace GB6Count
open Finset Filter

def reps (n : ℕ) := (range (n+1)).filter (fun p => p.Prime ∧ (n-p).Prime)
def exceptional (n : ℕ) : Prop := 4 ≤ n ∧ Even n ∧ (reps n).card = 0
instance (n : ℕ) : Decidable (exceptional n) := by unfold exceptional; infer_instance
def exceptionSet (X : ℕ) := (range (X+1)).filter exceptional

/-- Each prime-supported product at an exceptional target vanishes individually. -/
theorem reps_empty_term {R : Type*} [MulZeroClass R] (w v : ℕ → R)
    (hw : ∀ p, ¬ p.Prime → w p = 0) (hv : ∀ p, ¬ p.Prime → v p = 0)
    {n p r : ℕ} (he : (reps n).card=0) (ht : p+r=n) : w p*v r=0 := by
  by_cases hp : p.Prime
  · have hr : ¬ r.Prime := by
      intro hr
      have hmem : p ∈ reps n := mem_filter.mpr ⟨mem_range.mpr (by omega),hp,by simpa [← ht] using hr⟩
      rw [card_eq_zero.mp he] at hmem
      exact notMem_empty p hmem
    rw [hv r hr, mul_zero]
  · rw [hw p hp, zero_mul]

theorem reps_empty_no_weight {R : Type*} [Semiring R] (w v : ℕ → R)
    (hw : ∀ p, ¬ p.Prime → w p=0) (hv : ∀ p, ¬ p.Prime → v p=0)
    {n : ℕ} (he : (reps n).card=0) : (∑ p ∈ range (n+1), w p*v (n-p))=0 := by
  apply sum_eq_zero
  exact fun p hp => reps_empty_term w v hw hv he (by have := mem_range.mp hp; omega)

private theorem fresh_exceptions_bound {X : ℕ} {α A c : ℝ} {D : ℕ → ℝ}
    (hX : 0 < X) (hc : 0 < c)
    (hgap : ∀ n ∈ exceptionSet X \ exceptionSet (X/2), c * X ≤ D n)
    (hmean : ∑ n ∈ range (X+1), (D n)^2 ≤ A*(X:ℝ)^(2+α)) :
    ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ (A/c^2)*(X:ℝ)^α := by
  let S := exceptionSet X \ exceptionSet (X/2)
  have hXs : 0 < (X:ℝ) := by exact_mod_cast hX
  have hsub : S ⊆ range (X+1) := fun n hn => (mem_filter.mp (mem_sdiff.mp hn).1).1
  have ht : (S.card : ℝ)*(c*X)^2 ≤ ∑ n ∈ range (X+1), (D n)^2 := calc
    _ = ∑ _n ∈ S, (c*X)^2 := by simp
    _ ≤ ∑ n ∈ S, (D n)^2 :=
      sum_le_sum fun n hn => pow_le_pow_left₀ (by positivity) (hgap n hn) _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sq_nonneg _
  have hh := ht.trans hmean
  rw [Real.rpow_add hXs,Real.rpow_two] at hh
  change (S.card:ℝ) ≤ _
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hc)]
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hXs)
  calc
    _ = (S.card:ℝ)*(c*X)^2 := by ring
    _ ≤ _ := hh
    _ = _ := by ring

/-- A power estimate on fresh exceptions in each half-interval gives the same
power for the cumulative count, including the finitely many small inputs. -/
theorem exceptionalCount_of_half_intervals {α K : ℝ} (hα : 0 < α) (N : ℕ)
    (fresh : ∀ X : ℕ, N ≤ X → ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) ≤ K*(X:ℝ)^α) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ((exceptionSet X).card : ℝ) ≤ C*(X:ℝ)^α := by
  let B := max 2 N
  let q : ℝ := (1/2:ℝ)^α
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let C := max (B+1:ℝ) (K/(1-q))
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < (B+1:ℝ)) (le_max_left ..)
  have hbudget : C*q+K ≤ C := by
    have hb := (div_le_iff₀ (sub_pos.mpr hq)).mp (show K/(1-q) ≤ C from le_max_right ..)
    linarith
  refine ⟨C,hC,fun X => ?_⟩
  induction X using Nat.strong_induction_on with
  | ind X ih =>
    intro hX
    have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
    have hXp := Real.one_le_rpow hXr hα.le
    by_cases hB : B ≤ X
    · have hB' : max 2 N ≤ X := hB
      have hhalf : 1 ≤ X/2 := by omega
      have hsmall := ih (X/2) (Nat.div_lt_self (by omega) (by norm_num)) hhalf
      have hratio : ((X/2 : ℕ):ℝ)^α ≤ q*(X:ℝ)^α := by
        dsimp [q]; rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (Nat.cast_nonneg X)]
        apply Real.rpow_le_rpow (by positivity) _ hα.le
        have hh : X/2*2 ≤ X := Nat.div_mul_le_self ..
        have hh' : ((X/2:ℕ):ℝ)*2 ≤ X := by exact_mod_cast hh
        linarith
      have hfresh := fresh X (by omega)
      have hsub : exceptionSet (X/2) ⊆ exceptionSet X := by
        intro n hn
        obtain ⟨hr,he⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega),he⟩
      have hcard := card_sdiff_add_card_eq_card hsub
      have hh : ((exceptionSet X).card : ℝ) =
          ((exceptionSet X \ exceptionSet (X/2)).card : ℝ) + ((exceptionSet (X/2)).card : ℝ) := by
        exact_mod_cast hcard.symm
      calc
        _ = _ := hh
        _ ≤ K*(X:ℝ)^α+C*(q*(X:ℝ)^α) := add_le_add hfresh (hsmall.trans (mul_le_mul_of_nonneg_left hratio hC.le))
        _ = (C*q+K)*(X:ℝ)^α := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hcard := card_le_card (filter_subset exceptional (range (X+1)))
      simp only [card_range] at hcard
      calc
        _ ≤ ((X+1:ℕ):ℝ) := by exact_mod_cast hcard
        _ ≤ (B+1:ℝ) := by push_cast; exact_mod_cast (by omega : X+1 ≤ B+1)
        _ ≤ C := le_max_left ..
        _ ≤ _ := le_mul_of_one_le_right hC.le hXp

private theorem near_info {n X : ℕ} (h : n ∈ exceptionSet X \ exceptionSet (X/2)) :
    X/2 < n ∧ n ≤ X ∧ exceptional n := by
  obtain ⟨hmem,hnout⟩ := mem_sdiff.mp h
  obtain ⟨hr,he⟩ := mem_filter.mp hmem
  refine ⟨?_,Nat.le_of_lt_succ (mem_range.mp hr),he⟩
  by_contra! hlt
  exact hnout (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hlt),he⟩)


/-- A half-interval gap and a total mean-square discrepancy with exponent 5/2+ε/2
imply the registered eventual cumulative count, including its leading coefficient one. -/
theorem count_from_moment (ε : ℝ) (hε : 0 < ε) (c A : ℝ) (hc : 0 < c)
    (D : ℕ → ℕ → ℝ) (N₀ : ℕ)
    (hgap : ∀ X : ℕ, N₀ ≤ X → ∀ n : ℕ, X/2 < n → n ≤ X → 4 ≤ n → Even n →
      (reps n).card = 0 → c*(X:ℝ) ≤ D X n)
    (hmean : ∀ X : ℕ, N₀ ≤ X → (∑ n ∈ range (X+1), (D X n)^2) ≤ A*(X:ℝ)^(5/2+ε/2)) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (((range (X+1)).filter (fun n => 4≤n ∧ Even n ∧ (reps n).card=0)).card : ℝ) ≤
        (X:ℝ)^(1/2+ε) := by
  have hα : 0 < (1/2:ℝ)+ε/2 := by linarith
  obtain ⟨C,_,hC⟩ := exceptionalCount_of_half_intervals (α:=1/2+ε/2) (K:=A/c^2) hα (max N₀ 1) (by
    intro X hX
    have hN := (le_max_left ..).trans hX
    apply fresh_exceptions_bound (hX:= (le_max_right ..).trans hX) (D:=D X) (hc:=hc)
    · intro n hn
      obtain ⟨hl,hr,h4,hev,hR⟩ := near_info hn
      exact hgap X hN n hl hr h4 hev hR
    · simpa only [show (2:ℝ)+(1/2+ε/2)=5/2+ε/2 by ring] using hmean X hN)
  have he := ((tendsto_rpow_atTop (by positivity : 0<ε/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop C
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop (1:ℕ)))
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨hpow,hX1⟩ := hN X hX
  have hXp : 0 < (X:ℝ) := by exact_mod_cast hX1
  calc
    ((exceptionSet X).card:ℝ) ≤ C*(X:ℝ)^(1/2+ε/2) := hC X hX1
    _ ≤ (X:ℝ)^(ε/2)*(X:ℝ)^(1/2+ε/2) := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hXp.le _)
    _ = _ := by rw [← Real.rpow_add hXp]; congr 1; ring

end GB6Count

end

section

namespace GB6Growth
open Filter

noncomputable def grid (M : ℕ) := ⌊((M:ℝ)^(1/6:ℝ))^2⌋₊
noncomputable def height (M : ℕ) := 256 * grid M * (Nat.log 2 (M+2))^2
noncomputable def L (M : ℕ) : ℝ := Nat.log 2 (M+2)
noncomputable def logFactor (M : ℕ) : ℝ := 1 + L M + Real.log ((M:ℝ)+2)

private lemma log_nonneg' (M : ℕ) : 0 ≤ Real.log ((M:ℝ)+2) :=
  Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])

theorem L_one (M : ℕ) : 1 ≤ L M := by
  unfold L
  exact_mod_cast (show 1 ≤ Nat.log 2 (M+2) from Nat.le_log_of_pow_le (by decide) (by omega))

theorem L_le_logFactor (M : ℕ) : L M ≤ logFactor M := by
  unfold logFactor
  linarith [log_nonneg' M]

theorem log_le_logFactor (M : ℕ) : 1 + Real.log ((M:ℝ)+2) ≤ logFactor M := by
  unfold logFactor
  linarith [L_one M]

theorem logFactor_nonneg (M : ℕ) : 0 ≤ logFactor M :=
  (by linarith [L_one M, L_le_logFactor M])

private lemma logFactor_le (M : ℕ) (hM : (2:ℝ) ≤ M) (hL : 1 ≤ Real.log (M:ℝ)) :
    logFactor M ≤ 8*Real.log (M:ℝ) := by
  have hℓ := Real.log_le_log (by positivity : 0 < (M:ℝ)+2)
    (show (M:ℝ)+2 ≤ (M:ℝ)^2 by nlinarith [sq_nonneg ((M:ℝ)-2)])
  rw [Real.log_pow] at hℓ
  norm_num at hℓ
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.natLog_le_logb (M+2) 2
  simp only [Real.logb, Nat.cast_add, Nat.cast_ofNat] at hb
  have hm : L M * Real.log 2 ≤ Real.log ((M:ℝ)+2) := (le_div_iff₀ hlog₂).mp hb
  have hhalf : 0 ≤ Real.log 2 - 1/2 := by linarith [Real.log_two_gt_d9]
  have hpos : 0 ≤ L M := (by linarith [L_one M])
  unfold logFactor
  nlinarith [mul_nonneg hpos hhalf]

/-- Any fixed power of both logarithms appearing in the model can be absorbed. -/
theorem polylog_le_power (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop, a*(logFactor M)^k ≤ (M:ℝ)^η := by
  have ht := tendsto_natCast_atTop_atTop (R:=ℝ)
  have small := ((isLittleO_log_rpow_rpow_atTop (k:ℝ) (by positivity : 0 < η/2)).comp_tendsto ht).bound (c:=1) zero_lt_one
  have large := ((tendsto_rpow_atTop (by positivity : 0 < η/2)).comp ht).eventually_ge_atTop (a*8^k)
  filter_upwards [small,large, ht.eventually_ge_atTop 2, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1]
    with M hs hl hM hlog
  have hx : 0 < (M:ℝ) := by linarith
  change 1 ≤ Real.log (M:ℝ) at hlog
  have hlog' : 0 ≤ Real.log (M:ℝ) := by linarith
  change ‖(Real.log (M:ℝ))^(k:ℝ)‖ ≤ 1 * ‖(M:ℝ)^(η/2)‖ at hs
  rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog' _), one_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] at hs
  calc
    _ ≤ a*(8*Real.log (M:ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (logFactor_nonneg M) (logFactor_le M hM hlog) k) ha
    _ = (a*8^k)*(Real.log (M:ℝ))^k := by rw [mul_pow]; ring
    _ ≤ (M:ℝ)^(η/2)*(M:ℝ)^(η/2) := mul_le_mul hl hs (pow_nonneg hlog' k) (Real.rpow_nonneg hx.le _)
    _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring

lemma grid_eq_floor (M : ℕ) : grid M = ⌊(M:ℝ)^(1/3:ℝ)⌋₊ := by
  unfold grid
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg M)]
  norm_num

theorem grid_tendsto : Tendsto grid atTop atTop := by
  simp_rw [show grid = fun M : ℕ => ⌊(M:ℝ)^(1/3:ℝ)⌋₊ from funext grid_eq_floor]
  exact tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))

theorem grid_le_rpow (M : ℕ) : (grid M:ℝ) ≤ (M:ℝ)^(1/3:ℝ) := by
  rw [grid_eq_floor]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg M) _)

/-- The singular-series positivity theorem applies to every Fourier mode through M. -/
theorem eventual_grid_power : ∀ᶠ M : ℕ in atTop, M ≤ (grid M)^4 := by
  filter_upwards [grid_tendsto.eventually_ge_atTop 8] with M hQ
  let Q := grid M
  have h0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hu : (M:ℝ)^(1/3:ℝ) ≤ 2*(Q:ℝ) := by
    have hQ' : (8:ℝ) ≤ Q := by exact_mod_cast hQ
    have hf := (Nat.lt_floor_add_one ((M:ℝ)^(1/3:ℝ))).le
    rw [← grid_eq_floor] at hf
    change _ ≤ (Q:ℝ)+1 at hf
    linarith
  have hc : ((M:ℝ)^(1/3:ℝ))^3=(M:ℝ) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul h0]; norm_num
  have hQ' : (8:ℝ) ≤ Q := by exact_mod_cast hQ
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg h0 _) hu 3
  rw [hc, mul_pow] at hh
  have hfinal : (M:ℝ) ≤ (Q:ℝ)^4 := by
    calc
      _ ≤ 8*(Q:ℝ)^3 := by convert hh using 1; norm_num
      _ ≤ (Q:ℝ)*(Q:ℝ)^3 := mul_le_mul_of_nonneg_right hQ' (by positivity)
      _ = _ := by ring
  exact_mod_cast hfinal

/-- Eventual separation of all rational windows, including the endpoint halves. -/
theorem eventual_geometry : ∀ᶠ M : ℕ in atTop,
    1 ≤ grid M ∧ grid M ≤ height M ∧ grid M ≤ M ∧ 1 ≤ L M ∧ 2*(height M)^2 < M := by
  filter_upwards [grid_tendsto.eventually_ge_atTop 1, eventually_ge_atTop (2:ℕ),
      polylog_le_power (2*256^2) (by norm_num) 4 (1/6) (by norm_num)] with M hQ hM hℓ
  have hL : 1 ≤ Nat.log 2 (M+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hx : (1:ℝ) < M := by exact_mod_cast hM
  have hg : ((grid M:ℕ):ℝ) ≤ M := (grid_le_rpow M).trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num : (1/3:ℝ) ≤ 1))
  refine ⟨hQ, ?_, by exact_mod_cast hg, L_one M, ?_⟩
  · unfold height
    have : 1 ≤ (Nat.log 2 (M+2))^2 := Nat.one_le_pow 2 _ hL
    nlinarith [Nat.mul_le_mul_left (256*grid M) this]
  · have hsq : (grid M:ℝ)^2 ≤ (M:ℝ)^(2/3:ℝ) := by
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (grid_le_rpow M) 2).trans_eq
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg M)]; norm_num
    have hlog : 2*256^2*(L M)^4 ≤ (M:ℝ)^(1/6:ℝ) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [L_one M]) (L_le_logFactor M) 4) (by norm_num)).trans hℓ
    have hpow : (M:ℝ)^(2/3:ℝ)*(M:ℝ)^(1/6:ℝ) < (M:ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num : (2/3:ℝ)+1/6 < 1)
    have hmain := (mul_le_mul hsq hlog (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg M) _)).trans_lt hpow
    have hform : (2:ℝ)*(height M:ℝ)^2 = (grid M:ℝ)^2*(2*256^2*(L M)^4) := by
      unfold height L
      push_cast
      ring
    rw [← hform] at hmain
    exact_mod_cast hmain

/-- The square of the given pointwise error times a linear polylogarithmic energy
matches the variance exponent used by the exceptional-set count. -/
theorem variance_eventually (ε : ℝ) (hε : 0 < ε) (C D : ℝ) (hD : 0 ≤ D) (k l : ℕ) :
    ∀ᶠ M : ℕ in atTop,
      (C*(M:ℝ)^(3/4:ℝ)*(L M)^k)^2 * (D*(M:ℝ)*(1+Real.log ((M:ℝ)+2))^l) ≤
        (M:ℝ)^(5/2+ε/2) := by
  filter_upwards [polylog_le_power (C^2*D) (mul_nonneg (sq_nonneg C) hD) (2*k+l) (ε/2) (by positivity),
    eventually_ge_atTop (1:ℕ)] with M hpoly hM
  have hx : 0 < (M:ℝ) := by exact_mod_cast hM
  have h1 : 0 ≤ 1+Real.log ((M:ℝ)+2) := by linarith [log_nonneg' M]
  have hab : ((L M)^k)^2 * (1+Real.log ((M:ℝ)+2))^l ≤ (logFactor M)^(2*k+l) := by
    rw [pow_add, mul_comm 2 k, pow_mul]
    exact mul_le_mul (pow_le_pow_left₀ (pow_nonneg (by linarith [L_one M]) _) (pow_le_pow_left₀ (by linarith [L_one M]) (L_le_logFactor M) k) 2)
      (pow_le_pow_left₀ h1 (log_le_logFactor M) l) (pow_nonneg h1 _) (by positivity [logFactor_nonneg M])
  have ht : ((M:ℝ)^(3/4:ℝ))^2*(M:ℝ)=(M:ℝ)^(5/2:ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hx.le, ← Real.rpow_add_one hx.ne']; norm_num
  calc
    _ = (((M:ℝ)^(3/4:ℝ))^2*(M:ℝ))*(C^2*D*(((L M)^k)^2*(1+Real.log ((M:ℝ)+2))^l)) := by ring
    _ ≤ (M:ℝ)^(5/2:ℝ) * (M:ℝ)^(ε/2) := by
      rw [ht]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hab (mul_nonneg (sq_nonneg C) hD)).trans hpoly) (Real.rpow_nonneg hx.le _)
    _ = _ := (Real.rpow_add hx _ _).symm

end GB6Growth

end

section

open Filter GB6Growth GB6Var in
theorem Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions :
    let e := fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I); let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * e ((k : ℝ) * t); let L := fun n : ℕ => (Nat.log 2 (n + 2) : ℝ); let Q := fun n : ℕ => ⌊((n : ℝ) ^ (1 / 6 : ℝ)) ^ 2⌋₊; let H : ℕ → ℕ := fun n => 256 * Q n * (Nat.log 2 (n + 2)) ^ 2; let center := fun q a : ℕ => (a : ℝ) / q; let width := fun n q : ℕ => (H n : ℝ) / ((q : ℝ) * n); let mean := fun q a : ℕ => (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), e ((r : ℝ) * center q a)) / (q.totient : ℂ); let K := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1), e ((k : ℝ) * t); let model := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), (Set.Icc (center q a - width n q) (center q a + width n q)).indicator (fun u => mean q a * K n (u - center q a)) t; (∃ (C : ℝ) (k : ℕ), 0 < C ∧ Filter.Eventually (fun n : ℕ => ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖S n t - model n t‖ ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * L n ^ k) Filter.atTop) → ∀ ε : ℝ, 0 < ε → let reps := fun n : ℕ => (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p)); ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (((Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)).card : ℝ) ≤ (X : ℝ) ^ (1 / 2 + ε) := by
  change (∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ᶠ M : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
    ‖S M t-G (grid M) (height M) M t‖ ≤ C*(M:ℝ)^(3/4:ℝ)*(L M)^k) → _
  rintro ⟨C,k,hC,hU⟩ ε hε
  let U (M : ℕ) := C*(M:ℝ)^(3/4:ℝ)*(L M)^k
  have hrate := variance_eventually ε hε C 20 (by norm_num) k 2
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventual_geometry.and (hU.and (hrate.and (eventually_ge_atTop (1:ℕ)))))
  apply GB6Count.count_from_moment ε hε (1/8) 1 (by norm_num) (fun M => D (grid M) (height M) M) N
  · intro M hM m hmid hupper _he4 heven hempty
    obtain ⟨⟨hQ,hQH,hQM,hL,hsep⟩,_⟩ := hN M hM
    have hH : (0:ℝ)<height M := by exact_mod_cast (hQ.trans hQH)
    have hlog : (Nat.log 2 (grid M):ℝ) ≤ L M := by
      unfold L
      exact_mod_cast Nat.log_mono_right (b:=2) (hQM.trans (show M ≤ M+2 by omega))
    have hw : (height M:ℝ) = 256*(grid M:ℝ)*(L M)^2 := by simp [height,L]
    have hbudget : (grid M:ℝ)*(1+(Nat.log 2 (grid M):ℝ))/(2*height M) ≤ 1/32 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hH)).mpr
      rw [hw]
      have hcoef : 1+(Nat.log 2 (grid M):ℝ) ≤ 16*(L M)^2 := by nlinarith [sq_nonneg (L M-1)]
      convert mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (grid M)) using 1; ring
    have hgap := exception_gap hempty (GB6Geometry.model_floor hsep hQH hQ hmid hupper heven hbudget)
    convert hgap using 1; ring
  · intro M hM
    obtain ⟨⟨_,hQH,hQM,_,hsep⟩,hu,hr,hpos⟩ := hN M hM
    have hXr : (1:ℝ) ≤ M := by exact_mod_cast hpos
    have hmean := variance_bound (Finset.range (M+1)) hQM hsep hQH (U M) hu
    let B := 1+Real.log ((M:ℝ)+2)
    have hmul : 10*((M:ℝ)+1) ≤ 20*(M:ℝ) := by linarith
    have hfac := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmul (sq_nonneg B)) (sq_nonneg (U M))
    calc
      _ ≤ 10*(U M)^2*((M:ℝ)+1)*B^2 := hmean
      _ = (U M)^2*((10*((M:ℝ)+1))*B^2) := by ring
      _ ≤ (U M)^2*((20*(M:ℝ))*B^2) := hfac
      _ ≤ _ := by simpa only [one_mul] using hr

end
