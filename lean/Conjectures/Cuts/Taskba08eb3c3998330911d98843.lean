import Mathlib

import Conjectures.Goldbach.EstermannAlmostAllPolylog

section

/-!
The reciprocal-square kernel tail adapts the accepted proof in Goldbach PR #4109,
source c4b5aaca54cf1a91011c682b157ae14a3cbaf01a (Apache-2.0).
The arithmetic singular-series and centered-kernel inputs come from Goldbach PR #3615.
-/
namespace GoldbachBa08Kernel

open MeasureTheory Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachEstermannKernel

noncomputable section

private theorem positive_tail (g : ℝ → ℂ) (hg : Continuous g) {b : ℝ} (hb : 0 < b)
    (hb' : b ≤ 1/2) (h : ∀ t ∈ Set.Icc b (1/2:ℝ), ‖g t‖ ≤ 1/t^2) :
    ‖∫ t in b..(1/2:ℝ), g t‖ ≤ 1/b := by
  have hpos {x : ℝ} (hx : x ∈ Set.uIcc b (1/2:ℝ)) : 0 < x := by
    rw [Set.uIcc_of_le hb'] at hx
    exact hb.trans_le hx.1
  have hcont : ContinuousOn (fun t : ℝ => 1/t^2) (Set.uIcc b (1/2:ℝ)) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hpos hx).ne'
  have hn : (0:ℝ) ∉ Set.uIcc b (1/2:ℝ) := fun hx => (lt_irrefl 0) (hpos hx)
  have hi := integral_zpow (a:=b) (b:=(1/2:ℝ)) (n:=(-2:ℤ)) (Or.inr ⟨by decide,hn⟩)
  have hfun : (fun t : ℝ => 1/t^2) = fun t : ℝ => t^(-2:ℤ) := by
    funext t
    simp [one_div]
  calc
    _ ≤ ∫ t in b..(1/2:ℝ), ‖g t‖ := intervalIntegral.norm_integral_le_integral_norm hb'
    _ ≤ ∫ t in b..(1/2:ℝ), 1/t^2 := intervalIntegral.integral_mono_on hb'
      (hg.norm.intervalIntegrable ..) (hcont.intervalIntegrable) h
    _ ≤ _ := by
      rw [show (∫ t in b..(1/2:ℝ), 1/t^2) = ∫ t in b..(1/2:ℝ), t^(-2:ℤ) from
        congrArg (fun H : ℝ → ℝ => ∫ t in b..(1/2:ℝ), H t) hfun,hi]
      norm_num [one_div]
      linarith

/-- A uniform truncation bound for any frequency, once the square kernel is
bounded by the reciprocal square on the shoulders of the centered period. -/
theorem centered_truncation (g : ℝ → ℂ) (hg : Continuous g) {b : ℝ} (hb : 0<b)
    (hb' : b≤1/2) (h : ∀ t : ℝ, b≤|t| → |t|≤1/2 → ‖g t‖ ≤ 1/|t|^2) :
    ‖(∫ t in (-b)..b, g t) - ∫ t in (-(1/2):ℝ)..1/2, g t‖ ≤ 2/b := by
  have right := positive_tail g hg hb hb' (by
    intro t ht
    have hl := hb.trans_le ht.1
    simpa only [abs_of_nonneg hl.le] using h t (by simpa [abs_of_nonneg hl.le] using ht.1)
      (by simpa [abs_of_nonneg hl.le] using ht.2))
  have left := positive_tail (fun t => g (-t)) (hg.comp continuous_neg) hb hb' (by
    intro t ht
    have hl := hb.trans_le ht.1
    simpa only [abs_neg,abs_of_nonneg hl.le] using h (-t) (by simpa [abs_of_nonneg hl.le] using ht.1)
      (by simpa [abs_of_nonneg hl.le] using ht.2))
  rw [intervalIntegral.integral_comp_neg] at left
  have split :
      (∫ t in (-(1/2):ℝ)..1/2, g t) =
      (∫ t in (-(1/2):ℝ)..-b, g t) + (∫ t in (-b)..b, g t) + (∫ t in b..(1/2:ℝ), g t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable ..) (hg.intervalIntegrable ..),
        intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable ..) (hg.intervalIntegrable ..)]
  rw [split]
  calc
    _ = ‖-((∫ t in (-(1/2):ℝ)..-b, g t) + (∫ t in b..(1/2:ℝ), g t))‖ := by congr 1; abel
    _ ≤ _ := by
      rw [norm_neg]
      calc
        _ ≤ _ := norm_add_le _ _
        _ ≤ 1/b+1/b := add_le_add left right
        _ = 2/b := by ring


/- Adapted to the Estermann kernel from kernel_le_inv in
Conjectures.Goldbach.PacketRationalPeakExcess, using the common geometric
phase estimates imported from the verified deep-second-moment module. -/
private theorem kernel_le_recip (N : ℕ) {t : ℝ} (ht : 0 < |t|) (hh : |t| ≤ 1/2) :
    ‖GoldbachEstermannKernel.kernel N t‖ ≤ 1 / |t| := by
  have hsin := OAI.Problem337.sin_pi_mul_lower_on_middle (δ := |t|) (x := |t|) ht le_rfl (by linarith)
  have hpos : 0 < Real.sin (Real.pi * |t|) := by linarith
  have habs : |Real.sin (Real.pi*t)| = |Real.sin (Real.pi * |t|)| := by
    by_cases h : 0 ≤ t
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), mul_neg, Real.sin_neg, abs_neg]
  have ha : |Real.sin (Real.pi*t)| = Real.sin (Real.pi * |t|) := by
    rw [habs,abs_of_pos hpos]
  have hs : 0 < |Real.sin (Real.pi*t)| := by rw [ha]; exact hpos
  have h := OAI.Problem337.norm_geometric_phase_sum_le (abs_pos.mp hs) (N+1)
  calc
    _ = ‖∑ k ∈ range (N+1), Complex.exp (Complex.I*((2*Real.pi*t:ℝ):ℂ))^k‖ := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [← Complex.exp_nat_mul]
      unfold GoldbachEstermannKernel.phase
      push_cast
      congr 1
      ring
    _ ≤ 1 / |Real.sin (Real.pi*t)| := h
    _ ≤ _ := one_div_le_one_div_of_le ht (by rw [ha]; linarith)

private theorem kernel_neg (N : ℕ) (t : ℝ) :
    kernel N (-t) = phase (-(N : ℝ) * t) * kernel N t := by
  unfold kernel
  rw [mul_sum]
  calc
    _ = ∑ k ∈ range (N+1), phase (((N-k : ℕ) : ℝ) * (-t)) := by
      exact (Finset.sum_range_reflect (fun k : ℕ => phase ((k : ℝ) * (-t))) (N+1)).symm
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [Nat.cast_sub hk']
      unfold phase
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

private theorem twisted_neg (N m : ℕ) (hm : m ≤ 2*N) (t : ℝ) :
    twisted N m (-t) = twisted N (2*N-m) t := by
  unfold twisted
  rw [kernel_neg, mul_pow]
  have hfreq : phase (-(N : ℝ) * t)^2 * phase (-(m : ℝ) * (-t)) =
      phase (-((2*N-m : ℕ) : ℝ) * t) := by
    rw [Nat.cast_sub hm]
    unfold phase
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination kernel N t ^ 2 * hfreq

/-- Reflecting the summation box gives the upper half of its exact Fourier coefficient. -/
theorem full_coefficient_upper (N m : ℕ) (hNm : N ≤ m) (hm : m ≤ 2*N) :
    (∫ t in (-(1/2) : ℝ)..1/2, twisted N m t) = ((2*N-m : ℕ) : ℂ) + 1 := by
  have hReflect : (∫ t in (-(1/2) : ℝ)..1/2, twisted N m (-t)) =
      ∫ t in (-(1/2) : ℝ)..1/2, twisted N m t := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  rw [← hReflect]
  simp_rw [twisted_neg N m hm]
  exact full_coefficient N (2*N-m) (by omega)

/-- Truncating a centered interval costs at most twice the reciprocal radius, including on
the upper side of the convolution range. -/
theorem norm_twisted_tail_upper (N m : ℕ) {b : ℝ} (hb : 0<b) (hhalf : b≤1/2)
    (hNm : N ≤ m) (hm : m ≤ 2*N) :
    ‖(∫ t in (-b)..b, twisted N m t) - (((2*N-m : ℕ) : ℂ)+1)‖ ≤ 2/b := by
  rw [← full_coefficient_upper N m hNm hm]
  apply centered_truncation
  · unfold twisted kernel phase
    fun_prop
  · exact hb
  · exact hhalf
  · intro t hlow hupp
    rw [twisted, norm_mul, norm_pow]
    have hunit : ‖phase (-(m:ℝ)*t)‖ = 1 := by
      simp [phase, Complex.norm_exp]
    rw [hunit, mul_one]
    calc
      _ ≤ (1/|t|)^2 := pow_le_pow_left₀ (norm_nonneg _) (kernel_le_recip N (hb.trans_le hlow) hupp) _
      _ = _ := by rw [div_pow, one_pow]

def complexModel (N B m : ℕ) (H : ℝ) : ℂ :=
  ∑ q ∈ Icc 1 B, GoldbachMajorArc.coefficient q m *
    ∫ t in -(H/((q:ℝ)*N))..(H/((q:ℝ)*N)), twisted N m t

private theorem coefficient_floor {B m : ℕ} (hB : 1≤B) (he : Even m) :
    (1:ℝ)/3 ≤ ∑ q ∈ Icc 1 B, (GoldbachMajorArc.coefficient q m).re := by
  let W (q : ℕ) : ℝ := if q≤B then 1 else 0
  have h := GoldbachMajorArc.arithmetic_floor (Q:=B) (n:=m) he W
    (fun i => by unfold W; split <;> norm_num)
    (fun i j _ hij => by
      by_cases hj : j ≤ B
      · simp [W,hj,hij.trans hj]
      · by_cases hi : i ≤ B <;> simp [W,hj,hi])
    (fun q hq => by simp [W,not_le.mpr hq])
  have heq : ∀ q ∈ Icc 1 B, W q = 1 := fun q hq => ite_eq_left (mem_Icc.mp hq).2
  calc
    _ = W 1 / 3 := by simp [W,hB]
    _ ≤ _ := h
    _ = _ := sum_congr rfl (fun q hq => by rw [heq q hq,mul_one])

/-- Uniform signed lower bound for the truncated singular-series model when the
frequency is between the length of the row and twice that length. -/
theorem scaledModel_floor_upper (N B m : ℕ) (H : ℝ) (hN : 0 < N) (hB : 1 ≤ B)
    (hH : 0 < H) (hwidth : 2 * H ≤ N) (hNm : N ≤ m) (hm : m ≤ 2 * N) (he : Even m) :
    (((2*N-m : ℕ) : ℝ)+1)/3 - 8*(N:ℝ)*B*Real.sqrt B/H ≤
      (complexModel N B m H).re := by
  let v : ℝ := ((2*N-m : ℕ) : ℝ)+1
  let C (q : ℕ) := GoldbachMajorArc.coefficient q m
  let width (q : ℕ) := H/((q:ℝ)*N)
  let I (q : ℕ) := (∫ t in -(width q)..(width q), twisted N m t).re
  let cost := 2*(B:ℝ)*N/H
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hcost : 0 ≤ cost := by dsimp [cost]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hqbound (q) (hq : q ∈ Icc 1 B) : v*(C q).re - ‖C q‖*cost ≤ (C q).re * I q := by
    obtain ⟨hq₁,hq₂⟩ := mem_Icc.mp hq
    have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq₁
    have hpw : 0 < width q := div_pos hH (mul_pos (zero_lt_one.trans_le hqR) hn)
    have hu : width q ≤ 1/2 := by
      apply (div_le_iff₀ (mul_pos (zero_lt_one.trans_le hqR) hn)).mpr
      nlinarith only [hwidth,mul_le_mul_of_nonneg_right hqR hn.le]
    have herr := norm_twisted_tail_upper N m hpw hu hNm hm
    have hmag : |I q - v| ≤ cost := by
      have hr := (Complex.abs_re_le_norm
        ((∫ t in -(width q)..(width q), twisted N m t)-(((2*N-m : ℕ) : ℂ)+1))).trans herr
      have hc' : 2 / width q ≤ cost := by
        have hqr : (q:ℝ) ≤ B := by exact_mod_cast hq₂
        calc
          _ = (2*(q:ℝ)*N)/H := by dsimp only [width]; rw [div_div_eq_mul_div]; ring
          _ ≤ _ := by dsimp only [cost]; gcongr
      simpa [I, v, Complex.sub_re, Complex.add_re] using hr.trans hc'
    have habs : |(C q).re*(I q-v)| ≤ ‖C q‖*cost := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm _) hmag (abs_nonneg _) (norm_nonneg _)
    nlinarith only [(abs_le.mp habs).1]
  have htotal := sum_le_sum hqbound
  rw [sum_sub_distrib,← mul_sum,← sum_mul] at htotal
  have hf' := mul_le_mul_of_nonneg_left (coefficient_floor hB he) hv
  have hc := GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m
  change ∑ q ∈ Icc 1 B, ‖C q‖ ≤ _ at hc
  have hc' := mul_le_mul_of_nonneg_right hc hcost
  have hcost' : (4*Real.sqrt B)*cost = 8*N*B*Real.sqrt B/H := by dsimp only [cost]; ring
  rw [hcost'] at hc'
  unfold complexModel
  rw [Complex.re_sum]
  have heq : (∑ q ∈ Icc 1 B, (C q *
      ∫ t in -(width q)..(width q), twisted N m t).re) =
        ∑ q ∈ Icc 1 B, (C q).re * I q := by
    apply sum_congr rfl
    intro q hq
    rw [Complex.mul_re, show (C q).im=0 from GoldbachMajorArc.coefficient_im_zero m (mem_Icc.mp hq).1,
      zero_mul, sub_zero]
  rw [heq]
  refine le_trans ?_ htotal
  change v/3 - 8*(N:ℝ)*B*Real.sqrt B/H ≤ _
  linarith only [hf',hc']

/-- With logarithmic radius parameter cubed, the approximation model supplies a
convenient one-eighth linear floor throughout the target band. -/
theorem scaledModel_floor_upper_cubed (N B m : ℕ) (hN : 0 < N) (hB : 320 ≤ B)
    (hwidth : 2*B^3 ≤ N) (hNm : N ≤ m) (hm : 2*m ≤ 3*N) (he : Even m) :
    (N : ℝ)/8 ≤ (complexModel N B m ((B : ℝ)^3)).re := by
  have hB' : (320 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (B : ℝ) ≤ B := by
    apply (Real.sqrt_le_left hBp.le).mpr
    nlinarith only [mul_nonneg hBp.le (show 0 ≤ (B : ℝ)-1 by linarith)]
  have hmain := scaledModel_floor_upper N B m ((B : ℝ)^3) hN (by omega)
    (pow_pos hBp _) (by exact_mod_cast hwidth) hNm (by omega) he
  have htail : 8*(N:ℝ)*B*Real.sqrt B/(B:ℝ)^3 ≤ (N:ℝ)/40 := calc
    _ ≤ 8*(N:ℝ)*B*(B:ℝ)/(B:ℝ)^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _ = 8*(N:ℝ)/(B:ℝ) := by field_simp
    _ ≤ (N:ℝ)/40 := by
      apply (div_le_iff₀ hBp).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hB' hNr.le]
  have hc : (N:ℝ) ≤ 2*((2*N-m : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ 2*(2*N-m) by omega)
  linarith only [hc, htail, hmain, hNr]

end
end GoldbachBa08Kernel

end

section

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachBa08Approx
noncomputable section
open GoldbachBlockGeometry

/-- Rational arcs with independently specified denominator and width parameters. -/
def arcs (n D H : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a:ℝ)/q| ≤ width H n q}

-- The rational separation and integration arguments specialize the proofs in
-- GoldbachBlockGeometry from goldbach-proofs PR #3615 to two independent parameters.


/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n D H q r a b : ℕ} {t : ℝ} (hn : 2 * H * D < n)
    (hq : q ∈ Icc 1 D) (hr : r ∈ Icc 1 D)
    (ha : t ∈ window H n q a) (hb : t ∈ window H n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H * r + H * q < n := by nlinarith only [hn, Nat.mul_le_mul_left H hrQ, Nat.mul_le_mul_left H hqQ]
  have hradii : (H : ℝ) / (q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
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
  have h₁ := (mem_window (Q := H) n q a t).mp ha
  have h₂ := (mem_window (Q := H) n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (H:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (H:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n D H q r a b : ℕ} {t : ℝ} (hn : 2*H*D<n)
    (hq : q ∈ Icc 1 D) (hr : r ∈ Icc 1 D)
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window H n q a) (htb : t ∈ window H n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

private theorem arc_indicator_sum (F : ℝ → ℂ) {n D H : ℕ} (hn : 2*H*D<n) (t : ℝ) :
    (arcs n D H).indicator F t =
    ∑ q ∈ Icc 1 D, ∑ a ∈ numerators q, (window H n q a).indicator F t := by
  classical
  by_cases ht : t ∈ arcs n D H
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window (Q := H) n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window H n q b).indicator F t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window H n q a).indicator F t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window (Q := H) n q a t).mp hw⟩) _

private theorem major_split (F : ℝ → ℂ) (hcont : Continuous F) {n D H : ℕ} (hn : 2*H*D<n) : (∫ t in (0:ℝ)..1, (arcs n D H).indicator F t) =
    ∑ q ∈ Icc 1 D, ∑ a ∈ numerators q, actualPiece H n q a F := by
  have hInt (q a : ℕ) : IntervalIntegrable ((window H n q a).indicator F) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  simp_rw [arc_indicator_sum F hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩

private theorem width_le_unit_of_le {n H q : ℕ} (hn : H ≤ n) (hq : 0 < q) :
    width H n q ≤ 1/(q:ℝ) := by
  by_cases h : n = 0
  · subst n
    simp [width]
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  calc
    width H n q = ((H:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hn)) hq'.le


private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n H q a : ℕ} (hn : H ≤ n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd H n q a = -(width H n q) ∧ rightEnd H n q a = width H n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit_of_le hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring


private theorem endpoint_models (K : ℝ → ℂ) (hK : Continuous K) (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1)
    {n H : ℕ} (hn : H ≤ n) :
    (∑ a ∈ numerators 1, modelPiece H n 1 a C K) =
      C 1 0 * ∫ β in -(width H n 1)..width H n 1, K β := by
  let w := width H n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit_of_le hn (by decide : 0<1)
  have h0 : leftEnd H n 1 0 = 0 ∧ rightEnd H n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd H n 1 1 = -w ∧ rightEnd H n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) (-w) 0) (hK.intervalIntegrable 0 w)
  rw [show numerators 1 = {0,1} by decide]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2]
  rw [← hC, ← mul_add, add_comm, hadd]

private theorem model_by_denominator (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ)
    (hK : Continuous K) (hC : C 1 0 = C 1 1) {n H q : ℕ} (hn : H ≤ n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece H n q a C K) =
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width H n q)..width H n q, K β := by
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

private theorem major_error (F K : ℝ → ℂ) (hF : Continuous F) (hK : Continuous K)
    (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1) {n D H : ℕ} (hD : 1 ≤ D) (hn : 2*H*D<n) :
    ‖(∫ t in (0:ℝ)..1, (arcs n D H).indicator F t) - ∑ q ∈ Icc 1 D,
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width H n q)..width H n q, K β‖ ≤
    ∑ q ∈ Icc 1 D, ∑ a ∈ range (q+1), ∫ β in -(width H n q)..width H n q,
      ‖F (center q a+β) - C q a*K β‖ := by
  have hHn : H ≤ n := by nlinarith
  rw [major_split F hF hn]
  have hmodel (q : ℕ) (hq : q ∈ Icc 1 D) := model_by_denominator C K hK hC hHn (mem_Icc.mp hq).1
  rw [← sum_congr rfl hmodel, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun a ha => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg (Q := H) n q]) fun _ _ => norm_nonneg _)))
  have hi : Continuous (fun β => F (center q a+β)) := hF.comp (continuous_const.add continuous_id)
  have hm : Continuous (fun β => C q a*K β) := continuous_const.mul hK
  have ⟨hl,ho,hr⟩ := clipped_order (Q := H) (n := n) (mem_Icc.mp hq).1
    (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
  rw [actualPiece,modelPiece,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
    (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  exact (intervalIntegral.norm_integral_le_integral_norm ho).trans
    (intervalIntegral.integral_mono_interval hl ho hr (Eventually.of_forall fun _ => norm_nonneg _)
      ((hi.sub hm).norm.intervalIntegrable _ _))

open GoldbachMajorArc (primeSum phase unitMean)

/-- The complex Fourier coefficient restricted to the rational arcs. -/
def coefficient (n m D H : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (arcs n D H).indicator
    (fun t => primeSum n t ^ 2 * phase (-(m:ℝ)*t)) t

/-- The square-kernel model of the coefficient with one term per denominator. -/
def scaledModel (n m D H : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 D, GoldbachMajorArc.coefficient q m *
    ∫ β in -(width H n q)..width H n q, GoldbachEstermannKernel.twisted n m β

private def weight (m q a : ℕ) : ℂ :=
  (unitMean q a)^2 * phase (-(m:ℝ) * center q a)

private theorem weight_one (m : ℕ) : weight m 1 0 = weight m 1 1 := by
  have hu (a : ℕ) : unitMean 1 a = 1 := by
    rw [GoldbachMajorArc.unitMean_eq_ram (by simp), GoldbachMajorArc.ram_one]
    simp
  have hm : phase (-(m:ℝ)) = 1 := by
    unfold GoldbachMajorArc.phase
    convert Complex.exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 2
    push_cast
    ring
  simp only [weight, hu, one_pow, one_mul, center, Nat.cast_zero, Nat.cast_one, zero_div,
    one_div_one, mul_zero, mul_one, hm]
  simp [GoldbachMajorArc.phase]

/-- The full polylogarithmic error controls every smaller denominator range
at the same width, uniformly in the target frequency. -/
theorem approx {n m D H : ℕ} (hD : 1 ≤ D) (hDH : D ≤ H) (hn : 2*H*D < n) :
    ‖coefficient n m D H - scaledModel n m D H‖ ≤
      GoldbachMajorArc.Polylog.totalArcError H n (m:ℝ) := by
  let F := fun t : ℝ => primeSum n t ^ 2 * phase (-(m:ℝ)*t)
  let K := GoldbachEstermannKernel.twisted n m
  have hF : Continuous F := by
    unfold F GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hK : Continuous K := by
    unfold K GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  have hg := major_error F K hF hK (weight m) (weight_one m) hD hn
  have hcoef (q : ℕ) : (∑ a ∈ (range q).filter (fun a => a.Coprime q), weight m q a) =
      GoldbachMajorArc.coefficient q m := GoldbachMajorArc.sum_centers_eq_coefficient q m
  simp_rw [hcoef] at hg
  refine hg.trans ?_
  unfold GoldbachMajorArc.Polylog.totalArcError
  have he (q a : ℕ) : (∫ β in -(width H n q)..width H n q,
      ‖F (center q a+β) - weight m q a * K β‖) =
      ∫ β in -(width H n q)..width H n q, GoldbachMajorArc.Polylog.modelError n q a (m:ℝ) β := by
    apply intervalIntegral.integral_congr
    intro β _
    let c := center q a
    let z := primeSum n (c+β)
    let u := unitMean q a
    let k := GoldbachMajorArc.kernel n β
    have hphase : -(m:ℝ)*(c+β) = -(m:ℝ)*c + -(m:ℝ)*β := by ring
    change ‖z^2*phase (-(m:ℝ)*(c+β)) - (u^2*phase (-(m:ℝ)*c)) *
      (k^2*phase (-(m:ℝ)*β))‖ = ‖z^2*phase (-(m:ℝ)*(c+β)) - (u*k)^2*phase (-(m:ℝ)*(c+β))‖
    rw [hphase, BulkCircle.phase_add]
    congr 1
    ring
  simp_rw [he]
  exact sum_le_sum_of_subset_of_nonneg (fun q hq =>
    mem_Icc.mpr ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2.trans hDH⟩) (fun q _ _ =>
      sum_nonneg fun a _ => intervalIntegral.integral_nonneg
        (by linarith [width_nonneg (Q := H) n q]) fun _ _ => norm_nonneg _)

/-- The dyadic logarithm and its cube eventually fit inside the separation range. -/
theorem eventually_geometry : ∀ᶠ n : ℕ in atTop,
    let k := Nat.log 2 (n+2)
    1 ≤ k ∧ k ≤ k^3 ∧ 2*(k^3)^2 < n := by
  have asy := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := asy.bound (show 0 < (1 : ℝ) / (4 * 4^6) by positivity)
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  let k := Nat.log 2 (n+2)
  have hk : 1 ≤ k := Nat.le_log_of_pow_le (by decide) (by dsimp [k]; omega)
  have hnpos : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  change ‖(Real.log (n:ℝ)) ^ (6:ℝ)‖ ≤ _ * ‖(n:ℝ) ^ (1:ℝ)‖ at hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _), Real.rpow_one,
    Real.norm_eq_abs, abs_of_pos hnpos] at hn
  rw [show (6:ℝ) = (↑(6:ℕ):ℝ) by norm_num, Real.rpow_natCast] at hn
  have hc : (k:ℝ)^6 ≤ (4 * Real.log (n:ℝ))^6 := by
    simpa [k, GoldbachMajorArc.Polylog.cutoff] using GoldbachMajorArc.Polylog.cutoff_le_log 6 hn2
  rw [mul_pow] at hc
  have hreal : (2:ℝ) * ((k:ℝ)^3)^2 < n := by nlinarith only [hc, hn, hnpos]
  exact ⟨hk, Nat.le_self_pow (by decide) k, by exact_mod_cast hreal⟩

theorem eventually_approx {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    let k := Nat.log 2 (n+2)
    ∀ m : ℕ, ‖coefficient n m k (k^3) - scaledModel n m k (k^3)‖ ≤ ε*n := by
  filter_upwards [eventually_geometry,
    GoldbachMajorArc.Polylog.eventually_totalArcError_lt 3 0 (by decide) hε] with n hgeom herr
  let k := Nat.log 2 (n+2)
  obtain ⟨hk, hkH, hgeom⟩ := hgeom
  change ∀ m : ℕ, ‖coefficient n m k (k^3) - scaledModel n m k (k^3)‖ ≤ ε*n
  intro m
  have hsep : 2*(k^3)*k < n := by nlinarith only [Nat.mul_le_mul_left (2*(k^3)) hkH, hgeom]
  refine (approx hk hkH hsep).trans ?_
  simpa only [pow_zero, one_mul, GoldbachMajorArc.Polylog.cutoff] using (herr (m:ℝ)).le

/-- The arithmetic weighted prime sum agrees with the frozen filtered sum. -/
theorem primeSum_eq (n : ℕ) (t : ℝ) : primeSum n t =
    ∑ p ∈ range (n+1) with Nat.Prime p, (Real.log (p:ℝ):ℂ) * phase ((p:ℝ)*t) := by
  unfold GoldbachMajorArc.primeSum
  rw [sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp [GoldbachMajorArc.primeWeight, hp]

end
end GoldbachBa08Approx
end

namespace GoldbachBa08

open Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

theorem eventually_floor : ∀ᶠ N : ℕ in atTop,
    let k := Nat.log 2 (N + 2)
    ∀ m : ℕ, 2*m ≤ 3*N → 4*N ≤ 3*m → Even m →
      (7 : ℝ)*(N : ℝ)/64 ≤ (GoldbachBa08Approx.coefficient N m k (k^3)).re := by
  have hl : ∀ᶠ N : ℕ in atTop, 320 ≤ Nat.log 2 (N + 2) := by
    filter_upwards [eventually_ge_atTop (2^320 : ℕ)] with N hN
    exact Nat.le_log_of_pow_le (by decide) (hN.trans (Nat.le_add_right N 2))
  filter_upwards [hl, GoldbachBa08Approx.eventually_geometry,
    GoldbachBa08Approx.eventually_approx (show 0 < (1 : ℝ)/64 by norm_num)] with N hlarge hg ha
  let k := Nat.log 2 (N + 2)
  obtain ⟨hk, hkcube, hsep⟩ := hg
  have hkCube : 1 ≤ k^3 := hk.trans hkcube
  have hN : 0 < N := by omega
  have hwidth : 2*k^3 ≤ N := by
    have hmul := Nat.mul_le_mul_left (2*k^3) hkCube
    nlinarith only [hmul, hsep]
  change ∀ m : ℕ, 2*m ≤ 3*N → 4*N ≤ 3*m → Even m →
    (7 : ℝ)*(N : ℝ)/64 ≤ (GoldbachBa08Approx.coefficient N m k (k^3)).re
  intro m hu hl he
  have hmodel := GoldbachBa08Kernel.scaledModel_floor_upper_cubed N k m hN hlarge
    hwidth (by omega) hu he
  have heq : GoldbachBa08Approx.scaledModel N m k (k^3) =
      GoldbachBa08Kernel.complexModel N k m ((k : ℝ)^3) := by
    simp only [GoldbachBa08Approx.scaledModel, GoldbachBa08Kernel.complexModel,
      GoldbachBlockGeometry.width, Nat.cast_pow]
  rw [← heq] at hmodel
  have herror :=
    (Complex.abs_re_le_norm (GoldbachBa08Approx.coefficient N m k (k^3) -
      GoldbachBa08Approx.scaledModel N m k (k^3))).trans (ha m)
  rw [Complex.sub_re] at herror
  linarith only [hmodel, (abs_le.1 herror).1]

end GoldbachBa08


open Finset Filter MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

theorem Conjectures.Cuts.Taskba08eb3c3998330911d98843 :
    (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range (x2 + (1 : ℕ)) with Nat.Prime x4, (↑(Real.log (↑x4 : ℝ)) : ℂ) * x1 ((↑x4 : ℝ) * x3); have x3 : ℕ → ℕ → ℝ → ℂ := fun (x3 x4 : ℕ) (x5 : ℝ) => x2 x3 x5 ^ (2 : ℕ) * x1 (-(↑x4 : ℝ) * x5); have x4 : ℕ → Set ℝ := fun (x4 : ℕ) =>   have x5 : ℕ := Nat.log (2 : ℕ) (x4 + (2 : ℕ));   {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x5 ^ (3 : ℕ)) : ℝ) / ((↑x7 : ℝ) * (↑x4 : ℝ))}; have x5 : Set ℝ → ℕ → ℕ → ℂ := fun (x5 : Set ℝ) (x6 x7 : ℕ) => intervalIntegral (x5.indicator (x3 x6 x7)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; ∃ (x6 : ℕ), ∀ x7 ≥ x6, ∀ (x9 : ℕ), (2 : ℕ) * x9 ≤ (3 : ℕ) * x7 → (4 : ℕ) * x7 ≤ (3 : ℕ) * x9 → Even x9 → (7 : ℝ) * (↑x7 : ℝ) / (64 : ℝ) ≤ (x5 (x4 x7) x7 x9).re) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 GoldbachBa08.eventually_floor
  refine ⟨T, ?_⟩
  intro N hN m hu hl he
  simpa only [GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    GoldbachBlockGeometry.width, GoldbachBa08Approx.primeSum_eq, GoldbachMajorArc.phase]
    using hT N hN m hu hl he
