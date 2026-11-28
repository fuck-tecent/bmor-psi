import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment

/-! Fixed-row estimate for missed even frequencies with middle real part at least -X/32.
The Fourier orthogonality argument is adapted from SaladDay's PR 3079
(0e1a3dd13643a90c925d13c4e660c445e03820e8). The finite Bessel estimate and
Vaughan argument use muxkin's PR 2394 (7e4c7c13ec453579f424d41fab776c3b955b0cc5).
The low-window arithmetic and variance estimates use the verified Estermann
and low-modulus modules. The adaptations are from Apache-2.0 sources. -/

namespace GoldbachDyadicShiftTail
open MeasureTheory
private noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem phase_add (u v : ℝ) : phase (u + v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

private theorem zero_from_pairs (w : ℕ → ℝ) (n Y : ℕ)
    (hn : ∀ k j : ℕ, k + j = n → w k * w j = 0) :
    (∫ t in (0 : ℝ)..1,
      (∑ k ∈ Finset.range (Y+1), (w k : ℂ) * phase ((k : ℝ) * t))^2 *
        phase (-(n:ℝ)*t)) = 0 := by
  let I := Finset.range (Y+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) *
      phase (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by
    dsimp [term, phase]
    fun_prop
  have hpoint (t : ℝ) :
      (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t)) ^ 2 *
          phase (-(n : ℝ) * t) =
        ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t =
        ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  change (∫ t in (0:ℝ)..1,
    (∑ k ∈ I, (w k : ℂ) * phase ((k : ℝ) * t))^2 *
      phase (-(n:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro k _
  rw [intervalIntegral.integral_finsetSum
    (fun j _ => (hcont k j).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro j _
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases heq : (k : ℤ) + j - n = 0
  · have hz : w k * w j = 0 := hn k j (by omega)
    simp only [heq, ite_true, mul_one]
    exact_mod_cast hz
  · simp [heq]

private theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume =
        intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]

noncomputable section
open Finset MeasureTheory Filter Topology

def count (n : ℕ) := ((range (n+1)).filter fun p => p.Prime ∧ (n-p).Prime).card

def candidates (X : ℕ) :=
  (Icc (X/2) (2*X)).filter fun n => 4 ≤ n ∧ Even n

def w (k : ℕ) : ℝ := if k.Prime then Real.log (k:ℝ) else 0
def Q (N : ℕ) := ⌊(N:ℝ)^(1/3:ℝ)⌋₊
def height (N : ℕ) := 256 * Q N * (Nat.log 2 (N+2))^2
def wide (N : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1≤q ∧ q≤Q N ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (height N:ℝ)/((q:ℝ)*(N:ℝ))}
def spectrum (N : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (N+1), (w k : ℂ) * phase ((k:ℝ)*t)
def integrand (N m : ℕ) (t : ℝ) : ℂ := (spectrum N t)^2 * phase (-(m:ℝ)*t)
def coeff (s : Set ℝ) (N m : ℕ) : ℂ := ∫ t in (0:ℝ)..1, s.indicator (integrand N m) t
def big (N m : ℕ) : ℂ := coeff (wide N) N m
def deep (N m : ℕ) : ℂ := coeff (wide N)ᶜ N m

/-- Wide and deep coefficients are exact negatives at every genuine Goldbach
exception. The row N may differ from the frequency m. -/
theorem wide_add_deep_zero {m : ℕ} (hbad : count m=0) (N : ℕ) :
    big N m + deep N m = 0 := by
  have hnorep : ∀ k j : ℕ, k+j=m → w k * w j=0 := by
    intro k j he
    by_cases hpk : k.Prime
    · by_cases hpj : j.Prime
      · have hm : k ∈ (range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime) :=
          mem_filter.mpr ⟨mem_range.mpr (by omega), hpk,by simpa [← he] using hpj⟩
        have hemt := card_eq_zero.mp hbad
        exact (notMem_empty k (hemt ▸ hm)).elim
      · simp [w,hpj]
    · simp [w,hpk]
  have hc : Continuous (integrand N m) := by unfold integrand spectrum phase; fun_prop
  have hs := EffectiveArcEndpoint.frontierMeasurable (Q N) (height N) N
  exact (indicator_integral_split hs (hc.intervalIntegrable 0 1)).trans (zero_from_pairs w m N hnorep)


end
end GoldbachDyadicShiftTail

/-! ## Fixed-row rational model
The arithmetic lower bound, the coefficient norm sum, and the full-period
Dirichlet kernel coefficient are the verified results of
Conjectures.Goldbach.EstermannAlmostAllPolylog. We separate the polynomial
denominator cutoff N^(5/24) from the arc height N^(1/3). This yields a model
floor N/16 for every even frequency with N ≤ 4(m+1) and m ≤ N.
-/

namespace GoldbachWideModel
open MeasureTheory Finset
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


open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachEstermannKernel

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

private theorem twisted_tail (N m : ℕ) {b : ℝ} (hb : 0<b) (hhalf : b≤1/2) (hm : m≤N) :
    ‖(∫ t in (-b)..b, twisted N m t) - ((m:ℂ)+1)‖ ≤ 2/b := by
  rw [← full_coefficient N m hm]
  apply centered_truncation
  · unfold twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  · exact hb
  · exact hhalf
  · intro t hlow hupp
    rw [twisted,norm_mul,norm_pow]
    have hunit : ‖GoldbachEstermannKernel.phase (-(m:ℝ)*t)‖ = 1 := by
      simp [GoldbachEstermannKernel.phase,Complex.norm_exp]
    rw [hunit,mul_one]
    calc
      _ ≤ (1/|t|)^2 := pow_le_pow_left₀ (norm_nonneg _) (kernel_le_recip N (hb.trans_le hlow) hupp) _
      _ = _ := by rw [div_pow, one_pow]

def scaledModel (N B m : ℕ) (H : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 B, (GoldbachMajorArc.coefficient q m).re *
    (∫ t in -(H/((q:ℝ)*N))..(H/((q:ℝ)*N)), twisted N m t).re

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

/-- With an independent width H and denominator cutoff B, the error from
replacing each interval integral by its full Fourier coefficient is uniform
in the frequency. In particular this bound does not grow with N-m. -/
theorem scaled_model_floor (N B m : ℕ) (H : ℝ) (hN : 0<N) (hB : 1≤B)
    (hH : 0<H) (hwidth : 2*H ≤ N) (hm : m≤N) (he : Even m) :
    ((m:ℝ)+1)/3 - 8*(N:ℝ)*B*Real.sqrt B/H ≤ scaledModel N B m H := by
  let C (q : ℕ) := GoldbachMajorArc.coefficient q m
  let width (q : ℕ) := H/((q:ℝ)*N)
  let I (q : ℕ) := (∫ t in -(width q)..width q, twisted N m t).re
  let cost := 2*(B:ℝ)*N/H
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hcost : 0 ≤ cost := by dsimp [cost]; positivity
  have hqbound (q) (hq : q ∈ Icc 1 B) :
      ((m:ℝ)+1)*(C q).re - ‖C q‖*cost ≤ (C q).re * I q := by
    obtain ⟨hq₁,hq₂⟩ := mem_Icc.mp hq
    have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq₁
    have hpw : 0 < width q := div_pos hH (mul_pos (zero_lt_one.trans_le hqR) hn)
    have hu : width q ≤ 1/2 := by
      apply (div_le_iff₀ (mul_pos (zero_lt_one.trans_le hqR) hn)).mpr
      nlinarith only [hwidth,mul_le_mul_of_nonneg_right hqR hn.le]
    have herr := twisted_tail N m hpw hu hm
    have hmag : |I q - ((m:ℝ)+1)| ≤ cost := by
      have hr := (Complex.abs_re_le_norm
        ((∫ t in -(width q)..width q, twisted N m t)-((m:ℂ)+1))).trans herr
      have hc' : 2 / width q ≤ cost := by
        have hqr : (q:ℝ) ≤ B := by exact_mod_cast hq₂
        calc
          _ = (2*(q:ℝ)*N)/H := by dsimp only [width]; rw [div_div_eq_mul_div]; ring
          _ ≤ _ := by dsimp only [cost]; gcongr
      simpa [I, Complex.sub_re, Complex.add_re] using hr.trans hc'
    have habs : |(C q).re*(I q-((m:ℝ)+1))| ≤ ‖C q‖*cost := by
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm _) hmag (abs_nonneg _) (norm_nonneg _)
    nlinarith only [(abs_le.mp habs).1]
  have htotal := sum_le_sum hqbound
  rw [sum_sub_distrib,← mul_sum,← sum_mul] at htotal
  have hf := coefficient_floor hB he
  have hc := GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m
  change ∑ q ∈ Icc 1 B, ‖C q‖ ≤ _ at hc
  have hf' := mul_le_mul_of_nonneg_left hf (show 0 ≤ (m:ℝ)+1 by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc hcost
  change _ ≤ ∑ q ∈ Icc 1 B, (C q).re * I q
  apply (le_trans ?_ htotal)
  have hc'' : (4*Real.sqrt B)*cost = 8*N*B*Real.sqrt B/H := by dsimp only [cost]; ring
  rw [hc''] at hc'
  linarith only [hf',hc']

def modelCut (N : ℕ) := ⌊(N:ℝ)^(5/24:ℝ)⌋₊
def modelHeight (N : ℕ) : ℝ := (⌊(N:ℝ)^(1/3:ℝ)⌋₊ : ℕ)

open Filter Topology

private theorem eventually_model_parameters :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ modelCut N ∧ 0 < modelHeight N ∧
      2 * modelHeight N ≤ N ∧
      8*(N:ℝ)*modelCut N*Real.sqrt (modelCut N)/modelHeight N ≤ (N:ℝ)/48 := by
  have hlim := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/48)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_ge_atTop (768:ℝ)] with N hn hscale
  change 768 ≤ (N:ℝ)^(1/48:ℝ) at hscale
  have h1 : (1:ℝ)≤N := by exact_mod_cast hn
  have hpos : (0:ℝ)<N := zero_lt_one.trans_le h1
  have hB : (modelCut N : ℝ) ≤ (N:ℝ)^(5/24:ℝ) := Nat.floor_le (by positivity)
  have hS : Real.sqrt (modelCut N) ≤ (N:ℝ)^(5/48:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hB (by norm_num : (0:ℝ)≤1/2)
    rwa [← Real.rpow_mul hpos.le,show (5/24:ℝ)*(1/2)=5/48 by norm_num] at h
  have hroot : (2:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := (show (2:ℝ) ≤ 768 by norm_num).trans
    (hscale.trans (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)))
  have hfloor := Nat.lt_floor_add_one ((N:ℝ)^(1/3:ℝ))
  change (N:ℝ)^(1/3:ℝ) < modelHeight N + 1 at hfloor
  have hH : 0 < modelHeight N := by linarith
  have hupper : modelHeight N ≤ (N:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hw : 2*modelHeight N ≤ N := calc
    _ ≤ 2*(N:ℝ)^(1/3:ℝ) := by gcongr
    _ ≤ (N:ℝ)^(2/3:ℝ)*(N:ℝ)^(1/3:ℝ) := by
      exact mul_le_mul_of_nonneg_right ((show (2:ℝ) ≤ 768 by norm_num).trans (hscale.trans
        (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)))) (Real.rpow_nonneg hpos.le _)
    _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  have hscale' : 768 * (modelCut N:ℝ) * Real.sqrt (modelCut N) ≤ (N:ℝ)^(1/3:ℝ) := calc
    _ ≤ (N:ℝ)^(1/48:ℝ) * (N:ℝ)^(5/24:ℝ) * (N:ℝ)^(5/48:ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hpos,← Real.rpow_add hpos]; norm_num
  have hp : 384 * (modelCut N:ℝ) * Real.sqrt (modelCut N) ≤ modelHeight N := by linarith
  refine ⟨by omega, (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow h1 (by norm_num)),hH,hw,?_⟩
  apply (div_le_iff₀ hH).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hp hpos.le]

/-- One common row, one denominator cutoff and one main-term lower bound
throughout a fixed positive proportion of the spectrum. -/
theorem uniform_truncated_model_floor :
    ∀ᶠ N : ℕ in atTop, ∀ U : ℕ, 1 ≤ U → U ≤ modelCut N →
      ∀ m : ℕ, m ≤ N → N ≤ 4*(m+1) → Even m →
      (N:ℝ)/16 ≤ scaledModel N U m (modelHeight N) := by
  filter_upwards [eventually_model_parameters] with N hN
  intro U hU hUB m hm hband he
  obtain ⟨hpos,_,hH,hw,hcost⟩ := hN
  have h := scaled_model_floor N U m (modelHeight N) hpos hU hH hw hm he
  have hUB' : (U:ℝ) ≤ modelCut N := by exact_mod_cast hUB
  have hsmall : 8*(N:ℝ)*U*Real.sqrt U/modelHeight N ≤ (N:ℝ)/48 := by
    apply le_trans _ hcost
    gcongr
  have hbandR : (N:ℝ) ≤ 4*((m:ℝ)+1) := by exact_mod_cast hband
  linarith only [h,hsmall,hbandR]

theorem uniform_model_floor :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N → N ≤ 4*(m+1) → Even m →
      (N:ℝ)/16 ≤ scaledModel N (modelCut N) m (modelHeight N) := by
  filter_upwards [uniform_truncated_model_floor,eventually_model_parameters] with N hf hN
  exact hf _ hN.2.1 le_rfl

end
end GoldbachWideModel

/- The Dirichlet-approximation and Vaughan steps below specialize muxkin's
Apache-2.0 proof in Goldbach PR 2394 (7e4c7c13ec453579f424d41fab776c3b955b0cc5),
which in turn adapts OpenAI's openai/math, EgyptianFractions Vaughan estimate
at 3344da59991ed94f9ba711217b29c1d760badfa6. The cutoff is 5/24 and
the resulting pointwise exponent is 43/48. -/
namespace GoldbachSmallerArc
open Filter Topology
private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]



private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

theorem shortMaskVaughan :
    ∀ ε : ℝ, 0 < ε → let e := fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I); let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let Q := fun n : ℕ => ⌊(n : ℝ) ^ (5/24 : ℝ)⌋₊; let H : ℕ → ℕ := Q; ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, (¬ ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (H n : ℝ) / ((q : ℝ) * n)) → ‖∑ k ∈ Finset.range (n + 1), (w k : ℂ) * e ((k : ℝ) * t)‖ ≤ (n : ℝ) ^ (43 / 48 + ε) := by
  intro ε hε e w Q H
  let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * e ((k:ℝ)*t)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).comp_tendsto ht).bound (by norm_num : (0:ℝ)<1/100000)
  have hcube := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/24)).comp ht
  have hlog := Real.tendsto_log_atTop.comp ht
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2:ℕ), hsmall, hcube.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop 1, OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound] with n hn hlogs hcub hL hv
  intro t htu hm
  let x : ℝ := n
  let L := Real.log x
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  change 1 ≤ L at hL
  change 2 ≤ x^(5/24:ℝ) at hcub
  have hlog4 : L^4 ≤ (1/100000:ℝ)*x^ε := by
    change ‖L^(4:ℝ)‖ ≤ (1/100000:ℝ)*‖x^ε‖ at hlogs
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,
      abs_of_nonneg (show 0 ≤ L^4 by positivity),abs_of_nonneg (Real.rpow_nonneg hx.le ε)] using hlogs
  have hQ : 1 ≤ Q n := (Nat.le_floor_iff (Real.rpow_nonneg hx.le _)).mpr (by push_cast; linarith)
  have hQn : Q n ≤ n := Nat.floor_le_of_le <| (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5/24:ℝ) ≤ 1)).trans_eq (Real.rpow_one x)
  have hH : Q n ≤ H n := le_rfl
  have hm' : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q n:ℝ)/(q*n)} := by
    rintro ⟨q,a,hq,hqQ,ha,hc,he⟩
    exact hm ⟨q,a,hq,hqQ,ha,hc,he.trans (div_le_div_of_nonneg_right (by exact_mod_cast hH) (by positivity))⟩
  obtain ⟨q,a,hPq,hqB,_ha,hcop,happrox⟩ := minor_approximant (Q n) n t hQ hQn htu hm'
  have hqp : 0 < q := by omega
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqp
  have hPr : (0:ℝ) < Q n := Nat.cast_pos.mpr hQ
  have hqN : q ≤ n := hqB.trans (Nat.div_le_self _ _)
  have hqsec : |t - (a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happrox.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hvq := hv t (a:ℤ) q hqp hcop.isCoprime (by simpa using hqsec) hqN
  have hsum : S n ArithmeticFunction.vonMangoldt t = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 n) (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [S,e,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k:ℝ)]
  have hhigh : (q:ℝ) ≤ x/(Q n) := (le_div_iff₀ hPr).mpr (by dsimp [x]; exact_mod_cast (Nat.le_div_iff_mul_le hQ).mp hqB)
  have hT : 0 < x^(5/48:ℝ)/2 := by positivity
  have hTsq : (x^(5/48:ℝ))^2 = x^(5/24:ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]; norm_num
  have hTlow : x^(5/48:ℝ)/2 ≤ Real.sqrt (Q n) := by
    apply (Real.le_sqrt (by positivity) hPr.le).mpr
    have hf : x^(5/24:ℝ) < (Q n:ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith only [hf,hTsq,hcub]
  obtain ⟨hl,hr⟩ := vaughan_denominator_terms hx hT hPr hTlow (by exact_mod_cast hPq.le : (Q n:ℝ) ≤ q) hhigh
  have xid : x / (x^(5/48:ℝ)/2) = 2*x^(43/48:ℝ) := by
    have hdiv := Real.rpow_pos_of_pos hx (5/48:ℝ)
    have hid : x^(43/48:ℝ)*x^(5/48:ℝ)=x := by rw [←Real.rpow_add hx];norm_num
    field_simp; nlinarith only [hid]
  rw [xid] at hl hr
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (4/5:ℝ) ≤ 43/48)
  have hbound : ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ 81000*L^4*x^(43/48:ℝ) := by
    rw [hsum]
    apply hvq.trans
    change 16200*L^4*(x/Real.sqrt q+x^(4/5:ℝ)+Real.sqrt (x*q)) ≤ _
    calc _ ≤ 16200*L^4*(5*x^(43/48:ℝ)) := by gcongr; linarith only [hl,hr,hmiddle]
         _ = _ := by ring
  have herr : ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ 2*Real.sqrt x*L := by
    simpa only [S, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub] using mangoldt_pointwise_bridge n (by omega) t
  have hsqrt : Real.sqrt x ≤ x^(43/48:ℝ) := by
    rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlogle : L ≤ L^4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
  have hres : 2*Real.sqrt x*L ≤ 2*L^4*x^(43/48:ℝ) := by
    calc _ = 2*(L*Real.sqrt x) := by ring
         _ ≤ 2*(L^4*x^(43/48:ℝ)) := by gcongr
         _ = _ := by ring
  have htriangle := norm_sub_le (S n ArithmeticFunction.vonMangoldt t) (S n ArithmeticFunction.vonMangoldt t - S n w t)
  rw [sub_sub_cancel] at htriangle
  change ‖S n w t‖ ≤ x^(43/48+ε)
  rw [Real.rpow_add hx]
  have hsave := mul_le_mul_of_nonneg_right hlog4 (Real.rpow_nonneg hx.le (43/48:ℝ))
  nlinarith only [htriangle,herr,hbound,hres, hsave, mul_nonneg (show 0≤L^4 by positivity) (Real.rpow_nonneg hx.le (43/48:ℝ))]

end GoldbachSmallerArc

namespace GoldbachSmallerArc
open Filter Topology MeasureTheory Finset GoldbachWideModel GoldbachDyadicShiftTail
noncomputable section

def actualArcs (N : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ modelCut N ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ modelHeight N / ((q:ℝ)*N)}

theorem measurable_actualArcs (N : ℕ) : MeasurableSet (actualArcs N) := by
  unfold actualArcs
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ modelCut N ∧ a ≤ q ∧ a.Coprime q
  · rcases h with ⟨h₁,h₂,h₃,h₄⟩
    convert (isClosed_le (f:=fun t:ℝ => |t - (a:ℝ)/q|)
      (g:=fun _ => modelHeight N/((q:ℝ)*N)) (by fun_prop) continuous_const).measurableSet using 1
    ext t
    exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h₁,h₂,h₃,h₄,ht⟩⟩
  · convert MeasurableSet.empty (α:=ℝ) using 1
    ext t
    exact iff_of_false (fun ht => h ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩) (fun ht => ht)

theorem minor_cap (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ actualArcs N →
      ‖spectrum N t‖ ≤ (N:ℝ)^(43/48+ε : ℝ) := by
  obtain ⟨T,hT⟩ := shortMaskVaughan ε hε
  filter_upwards [eventually_ge_atTop T,eventually_ge_atTop 1] with N hN h1
  intro t ht hout
  apply hT N hN t ht
  rintro ⟨q,a,hq,hB,ha,hab,hw⟩
  have hx : (1:ℝ)≤N := by exact_mod_cast h1
  have hc : (modelCut N:ℝ) ≤ modelHeight N := Nat.cast_le.mpr
    (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (5/24:ℝ)≤1/3)))
  exact hout ⟨q,a,hq,hB,ha,hab,hw.trans (div_le_div_of_nonneg_right hc (by positivity))⟩

def offCoeff (N m : ℕ) := coeff (actualArcs N)ᶜ N m
def onCoeff (N m : ℕ) := coeff (actualArcs N) N m

private theorem split_any (N m : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    coeff A N m + coeff Aᶜ N m = ∫ t in (0:ℝ)..1, integrand N m t := by
  let f := integrand N m
  have hc : Continuous f := by
    change Continuous (fun t : ℝ =>
      (∑ k ∈ range (N+1), (w k:ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))^2 *
        Complex.exp (((2*Real.pi*(-(m:ℝ)*t):ℝ):ℂ)*Complex.I))
    fun_prop
  have hi {s : Set ℝ} (hs : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 :=
    ⟨(hc.intervalIntegrable ..).1.indicator hs,(hc.intervalIntegrable ..).2.indicator hs⟩
  change (∫ t in (0:ℝ)..1, A.indicator f t) + (∫ t in (0:ℝ)..1, Aᶜ.indicator f t) =
    ∫ t in (0:ℝ)..1, f t
  rw [← intervalIntegral.integral_add (hi hA) (hi hA.compl)]
  apply congrArg (fun g : ℝ → ℂ => ∫ t in (0:ℝ)..1, g t)
  funext t
  by_cases h : t∈A <;> simp [h]

theorem exception_row_zero {m : ℕ} (hm : count m=0) (N : ℕ) : onCoeff N m + offCoeff N m = 0 := by
  have hs := split_any N m (EffectiveArcEndpoint.frontierMeasurable
    (GoldbachDyadicShiftTail.Q N) (height N) N)
  exact (split_any N m (measurable_actualArcs N)).trans (hs.symm.trans (wide_add_deep_zero hm N))

theorem short_row_energy (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (∑ m ∈ range (N+1), ‖offCoeff N m‖^2) ≤ (N:ℝ)^(67/24+η : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (show 0 < η/2 by linarith)).comp_tendsto ht).bound
    (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (minor_cap (η/4) (by linarith))
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 2, hlog] with N hn hN hL
  have hpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog' : (Real.log (N:ℝ))^2 ≤ (1/2:ℝ)*(N:ℝ)^(η/2) := by
    change ‖Real.log (N:ℝ)^(2:ℝ)‖ ≤ (1/2:ℝ)*‖(N:ℝ)^(η/2)‖ at hL
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (N:ℝ))),
      abs_of_nonneg (Real.rpow_nonneg hpos.le _)] using hL
  let U := (N:ℝ)^(43/48+η/4)
  have hsup : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ actualArcs N → ‖spectrum N t‖ ≤ U := hN₀ N hn
  have hb := PEqualNP.Outside.frontierSourceBesselCap N (N+1) w (actualArcs N) U
    (measurable_actualArcs N) (Real.rpow_nonneg hpos.le _) hsup
  have hw : (∑ k ∈ range (N+1), (w k)^2) ≤ (N:ℝ)*(N:ℝ)^(η/2) := by
    calc
      _ ≤ ∑ _k ∈ range (N+1), (Real.log (N:ℝ))^2 := by
        apply sum_le_sum
        intro k hk
        have hkn := mem_range.mp hk
        by_cases hp : k.Prime
        · simp only [w,ite_eq_left hp]
          apply pow_le_pow_left₀ (Real.log_natCast_nonneg k) _ 2
          exact Real.log_le_log (by exact_mod_cast hp.pos : (0:ℝ)<k) (by exact_mod_cast (show k ≤ N by omega))
        · simpa only [w,ite_eq_right hp,zero_pow (by decide : (2:ℕ)≠0)] using sq_nonneg (Real.log (N:ℝ))
      _ = ((N:ℝ)+1)*(Real.log (N:ℝ))^2 := by simp
      _ ≤ (2*(N:ℝ))*((1/2:ℝ)*(N:ℝ)^(η/2)) := mul_le_mul (by linarith) hlog' (sq_nonneg _) (by positivity)
      _ = _ := by ring
  apply hb.trans ((mul_le_mul_of_nonneg_left hw (sq_nonneg U)).trans_eq ?_)
  dsimp [U]
  calc
    _ = (N:ℝ)^((43/48+η/4)*(2:ℕ)) * (N:ℝ)^(1+η/2) := by
      rw [Real.rpow_mul_natCast hpos.le,Real.rpow_add hpos 1,Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hpos]; congr 1; push_cast; ring

/-- Frequencies carrying enough complementary mass to hide a positive
model-sized coefficient. -/
def loud (X : ℕ) : Finset ℕ := by
  classical
  exact (range (2*X+1)).filter fun m => (X:ℝ)/16 ≤ ‖offCoeff (2*X) m‖

theorem loud_energy (X : ℕ) (hx : 0<X) :
    ((loud X).card:ℝ) ≤ (∑ m ∈ range (2*X+1), ‖offCoeff (2*X) m‖^2) / ((X:ℝ)/16)^2 := by
  classical
  have hxR : (0:ℝ)<X := by exact_mod_cast hx
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ∑ _m ∈ loud X, ((X:ℝ)/16)^2 := by simp
    _ ≤ ∑ m ∈ loud X, ‖offCoeff (2*X) m‖^2 :=
      sum_le_sum fun m hm => pow_le_pow_left₀ (by positivity) (mem_filter.mp hm).2 _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)


end
end GoldbachSmallerArc

/-! ## Low rational windows and the strict middle band
The low-modulus energy and character estimates are the accepted #2992 of
wzhxzkk and LogTruSoul (7b1ff2d1a620e4a2d359c14345f41a7acb336c48).
The inner comparison is from the accepted Estermann module, #3615. The
true low-window floor for reflected rows and the use of signed middle tails
are also studied by HymnOfLight in #3883 (b3e8a9fec6067484ff44957e93f85e23697040a5).
Our spectrum is a single row N=2X. Its height is the integral cube root and
its even frequencies run from N/4 up to N. The model and prime sums on the
central arcs have distinct coefficients for nonreduced rational numerators.
-/

namespace GoldbachShiftedLowArcs
open Filter Finset MeasureTheory
open scoped Topology Classical
noncomputable section

def lowCenters (N : ℕ) := V19.centers (V20.narrow N)
def skirtCell (N : ℕ) := V19.cell N (V20.narrow N) (V20.width N)

private theorem cell_square_mono {f : ℝ → ℂ} (hf : Continuous f) {D E : Set ℝ}
    (hDE : D ⊆ E) (hE : E ⊆ Set.Ioc 0 1) :
    (∫ t in D, ‖f t‖^2) ≤ ∫ t in E, ‖f t‖^2 := by
  exact setIntegral_mono_set (((hf.norm.pow 2).intervalIntegrable 0 1).1.mono_set hE)
    (Eventually.of_forall fun _ => sq_nonneg _) (Filter.Eventually.of_forall fun _ ht => hDE ht)

/-- Uniform in the portions of the individual arcs and in the frequency.
The absolute error is summed over rational centers, so cancellation between
different rational centers is unnecessary for this range. -/
theorem masked_low_skirt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (D : ℕ × ℕ → Set ℝ),
      (∀ i ∈ lowCenters N, D i ⊆ skirtCell N i) → ∀ m : ℝ,
      (∑ i ∈ lowCenters N, ‖∫ t in D i,
        ((V31.Vi3 N t)^2-(Va2.model N i t)^2)*V31.phase (-m*t)‖) ≤ ε*(N:ℝ) := by
  let C := Vm.V2i/2
  have hC : 0 ≤ C := by unfold C; exact div_nonneg (Real.exp_pos _).le (by norm_num)
  have hδ : 0 < ε^2/(2*(ε+2*(C+1))) := by positivity
  have herr : V8j.V3d Vuh.V1h4 := V8i.V1kv (V3z.V1p5
    (V19d.V10v (Vie.V1ew (V7e.Vzg (V6h.Vz5 30)))))
  filter_upwards [Vmk.V1lq, herr _ hδ] with N hmodel he D hD m
  let η := ε/(2*(C+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hpart (i : ℕ × ℕ) : skirtCell N i ⊆ Set.Ioc 0 1 := Set.inter_subset_right
  have hS : Continuous (V31.Vi3 N) := by unfold V31.Vi3 V31.phase; fun_prop
  have he' : (∑ i ∈ lowCenters N, ∫ t in D i, ‖V31.Vi3 N t-Va2.model N i t‖^2) ≤
      (ε^2/(2*(ε+2*(C+1))))*(N:ℝ) := by
    apply le_trans _ he
    exact sum_le_sum fun i hi => cell_square_mono (hS.sub (Va2.Ve5 N i)) (hD i hi) (hpart i)
  have hm' : (∑ i ∈ lowCenters N, ∫ t in D i, ‖Va2.model N i t‖^2) ≤ C*(N:ℝ) := by
    apply le_trans _ hmodel
    exact sum_le_sum fun i hi => cell_square_mono (Va2.Ve5 N i) (hD i hi) (hpart i)
  let osc := fun t : ℝ => V31.phase (-m*t)
  have ho : Continuous osc := by unfold osc V31.phase; fun_prop
  apply (V8j.Vvf (lowCenters N) D (fun i hi => (hD i hi).trans (hpart i))
    (V31.Vi3 N) (Va2.model N) osc hS (fun i _ => Va2.Ve5 N i) ho
    (fun t => (Complex.norm_exp_ofReal_mul_I (2*Real.pi*(-m*t))).le) hη).trans
  exact V8j.V1w6 hε hC (Nat.cast_nonneg N) he' hm'

end
end GoldbachShiftedLowArcs

namespace GoldbachShiftedLowArcs
open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology Classical
noncomputable section

def localTwist (N m : ℕ) := GoldbachEstermannKernel.twisted N m
def modeIntegral (N m H q : ℕ) := ∫ β in -(V19.radius N H q)..(V19.radius N H q), localTwist N m β
def complexModel (N m U H : ℕ) :=
  ∑ q ∈ Icc 1 U, GoldbachMajorArc.coefficient q m * modeIntegral N m H q
def rationalPart (N m U H : ℕ) := ∫ t in (0:ℝ)..1,
  (V19.cap N U H).indicator (fun t => (V31.Vi3 N t)^2 * V31.phase (-(m:ℝ)*t)) t

private theorem continuous_localTwist (N m : ℕ) : Continuous (localTwist N m) := by
  unfold localTwist GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
  fun_prop

private theorem local_factor (N m q a : ℕ) (t : ℝ) :
    (Va2.model N (q,a) t)^2 * V31.phase (-(m:ℝ)*t) =
      V4o.Vc5 m q a * localTwist N m (t-V19.center (q,a)) := by
  have he : -(m:ℝ)*t = -(m:ℝ)*V19.center (q,a) + -(m:ℝ)*(t-V19.center (q,a)) := by ring
  rw [he,V31.V13v,Va2.model,V24.V1h5]
  unfold V4o.Vc5 localTwist GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel
  change (_ * ∑ k ∈ range (N+1), V31.phase ((k:ℝ)*(t-V19.center (q,a))))^2 *
    (V31.phase _ * V31.phase _) = _ * ((∑ k ∈ range (N+1), V31.phase ((k:ℝ)*(t-V19.center (q,a))))^2 * V31.phase _)
  ring

private theorem cell_factor (N m Q H q a : ℕ) :
    (∫ t in V19.cell N Q H (q,a), (Va2.model N (q,a) t)^2*V31.phase (-(m:ℝ)*t)) =
      V4o.Vc5 m q a * ∫ t in V19.cell N Q H (q,a), localTwist N m (t-V19.center (q,a)) := by
  simp_rw [local_factor]
  rw [integral_const_mul]

private theorem center_weights_one (m : ℕ) : V4o.Vc5 m 1 0 = 1 ∧ V4o.Vc5 m 1 1 = 1 := by
  have hz : V31.phase 0 = 1 := by simp [V31.phase]
  have hneg : V31.phase (-(m:ℝ)) = 1 := by
    have h := V31.V13v (m:ℝ) (-(m:ℝ))
    simpa only [add_neg_cancel,V24.V22q,one_mul,hz] using h.symm
  constructor <;> simp [V4o.Vc5,V19.center,hneg,hz]

/-- Reassemble rational centers at any integer frequency on a fixed spectral row. -/
theorem low_shell_model (N m Q H : ℕ) (hQH : Q ≤ H) (hHN : H ≤ N) :
    (∑ i ∈ V19.centers Q, ∫ t in V19.cell N Q H i,
      (Va2.model N i t)^2*V31.phase (-(m:ℝ)*t)) =
      complexModel N m Q H - complexModel N m Q Q := by
  classical
  rw [V19.V1mo,complexModel,complexModel,←sum_sub_distrib]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨hq1,hqQ⟩ := mem_Icc.mp hq
  have hc : GoldbachMajorArc.coefficient q m = Vr.V3f q m := rfl
  rw [hc]
  by_cases hOne : q=1
  · subst q
    have hset : ((range (1+1)).filter (fun a : ℕ => a.Coprime 1)) = ({0,1}:Finset ℕ) := by decide
    rw [hset,sum_pair (by decide : (0:ℕ)≠1)]
    simp only [cell_factor,(center_weights_one m).1,(center_weights_one m).2,one_mul,Vr.V13x]
    exact (V4g.V1qg hQH hHN (localTwist N m) (continuous_localTwist N m)).trans (by simp [hqQ,modeIntegral])
  · have h2 : 2 ≤ q := by omega
    have hset : ((range (q+1)).filter (fun a => a.Coprime q)) = (range q).filter (fun a => a.Coprime q) := by
      ext a
      simp only [mem_filter,mem_range]
      constructor
      · rintro ⟨ha,hab⟩
        have hne : a≠q := by rintro rfl; exact hOne (by simpa [Nat.Coprime] using hab)
        exact ⟨by omega,hab⟩
      · exact fun ⟨ha,hab⟩ => ⟨by omega,hab⟩
    rw [hset,← mul_sub,← V4o.V1bq,Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨ha,hcop⟩ := mem_filter.mp ha
    rw [cell_factor,V4g.V1s8 hQH hHN h2 (mem_range.mp ha).le hcop _ (continuous_localTwist N m)]
    simp [hqQ,modeIntegral]

private def coreWeight (m q a : ℕ) : ℂ :=
  (GoldbachMajorArc.unitMean q a)^2 * V31.phase (-(m:ℝ)*V19.center (q,a))

/-- The usual Siegel–Walfisz core error works simultaneously at all integer frequencies. -/
theorem narrow_error (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
    ‖rationalPart N m (V20.narrow N) (V20.narrow N)-complexModel N m (V20.narrow N) (V20.narrow N)‖ ≤ ε*N := by
  have he := GoldbachMajorArc.Polylog.eventually_totalArcError_lt 2 0 (by decide) hε
  filter_upwards [he,V20.Vhd] with N herr hgeom m
  obtain ⟨hN,hQ,hQU,_,_,hbudget⟩ := hgeom
  let Q := V20.narrow N
  have hQH := hQU.trans (V20.Vrx N hQ)
  have hsep : 2*Q^2<N := by
    calc
      _ = 2*Q*Q := by ring
      _ ≤ 2*V20.width N*V20.cutoff N := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hQH) hQU
      _ < N := hbudget
  let F := fun t : ℝ => (V31.Vi3 N t)^2 * V31.phase (-(m:ℝ)*t)
  have hF : Continuous F := by unfold F V31.Vi3 V31.phase; fun_prop
  have hu (a : ℕ) : GoldbachMajorArc.unitMean 1 a = 1 := by
    rw [GoldbachMajorArc.unitMean_eq_ram (by simp),GoldbachMajorArc.ram_one]; simp
  have hc : coreWeight m 1 0 = coreWeight m 1 1 := by
    simpa only [coreWeight,hu,one_pow,one_mul,V4o.Vc5,ArithmeticFunction.moebius_apply_one,
      Int.cast_one,Nat.totient_one,Nat.cast_one,div_one] using (center_weights_one m).1.trans (center_weights_one m).2.symm
  have hg := GoldbachBlockGeometry.major_error F (localTwist N m) hF (continuous_localTwist N m) (coreWeight m) hc hsep
  have hcoef (q : ℕ) : (∑ a ∈ (range q).filter (fun a => a.Coprime q), coreWeight m q a) =
      GoldbachMajorArc.coefficient q m := GoldbachMajorArc.sum_centers_eq_coefficient q m
  simp_rw [hcoef] at hg
  apply hg.trans
  have H := herr (m:ℝ)
  simp only [pow_zero,one_mul] at H
  apply le_trans (le_of_eq ?_) H.le
  unfold GoldbachMajorArc.Polylog.totalArcError
  refine sum_congr rfl fun q hq => sum_congr rfl fun a ha => ?_
  apply intervalIntegral.integral_congr
  intro β _
  let c := V19.center (q,a)
  let z := V31.Vi3 N (c+β)
  let u := GoldbachMajorArc.unitMean q a
  let k := GoldbachEstermannKernel.kernel N β
  have hphase : -(m:ℝ)*(c+β) = -(m:ℝ)*c + -(m:ℝ)*β := by ring
  change ‖z^2*V31.phase (-(m:ℝ)*(c+β)) - (u^2*V31.phase (-(m:ℝ)*c)) *
    (k^2*V31.phase (-(m:ℝ)*β))‖ = ‖z^2*V31.phase (-(m:ℝ)*(c+β)) - (u*k)^2*V31.phase (-(m:ℝ)*(c+β))‖
  rw [hphase,V31.V13v]
  congr 1
  ring

end
end GoldbachShiftedLowArcs

namespace GoldbachShiftedLowArcs
open Filter Finset MeasureTheory
open scoped Topology Classical
noncomputable section

private theorem core_subset {N Q H : ℕ} (hQH : Q≤H) : V19.cap N Q Q ⊆ V19.cap N Q H := by
  rintro t ⟨q,a,hq,hqQ,ha,hab,hw⟩
  exact ⟨q,a,hq,hqQ,ha,hab,hw.trans (div_le_div_of_nonneg_right (by exact_mod_cast hQH) (by positivity))⟩

private theorem restrict_coeff_sub {N m : ℕ} {A B : Set ℝ} (ha : MeasurableSet A)
    (hb : MeasurableSet B) (hab : A ⊆ B) :
    GoldbachDyadicShiftTail.coeff B N m - GoldbachDyadicShiftTail.coeff A N m =
      GoldbachDyadicShiftTail.coeff (B \ A) N m := by
  let F := GoldbachDyadicShiftTail.integrand N m
  have hc : Continuous F := by
    change Continuous (fun t : ℝ => (V31.Vi3 N t)^2*V31.phase (-(m:ℝ)*t))
    unfold V31.Vi3 V31.phase
    fun_prop
  have hint {S : Set ℝ} (h : MeasurableSet S) : IntervalIntegrable (S.indicator F) volume 0 1 :=
    ⟨(hc.intervalIntegrable ..).1.indicator h,(hc.intervalIntegrable ..).2.indicator h⟩
  change (∫ t in (0:ℝ)..1, B.indicator F t) - (∫ t in (0:ℝ)..1, A.indicator F t) = _
  rw [← intervalIntegral.integral_sub (hint hb) (hint ha)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases hA : t∈A
  · have hB := hab hA
    simp [hA,hB,F]
  · by_cases hB : t∈B <;> simp [hA,hB,F]

private theorem shell_error {N m Q H : ℕ} (hQH : Q≤H) (hHN : H≤N) (hbudget : 2*H*Q<N) :
    ‖(rationalPart N m Q H-rationalPart N m Q Q) -
      (complexModel N m Q H-complexModel N m Q Q)‖ ≤
      ∑ i ∈ V19.centers Q, ‖∫ t in V19.cell N Q H i,
        ((V31.Vi3 N t)^2-(Va2.model N i t)^2)*V31.phase (-(m:ℝ)*t)‖ := by
  let osc := fun t : ℝ => V31.phase (-(m:ℝ)*t)
  let F := fun t : ℝ => (V31.Vi3 N t)^2*osc t
  have ho : Continuous osc := by unfold osc V31.phase; fun_prop
  have hS : Continuous (V31.Vi3 N) := by unfold V31.Vi3 V31.phase; fun_prop
  have hF : Continuous F := (hS.pow 2).mul ho
  have hcut : rationalPart N m Q H - rationalPart N m Q Q =
      ∑ i ∈ V19.centers Q, ∫ t in V19.cell N Q H i, F t :=
    (restrict_coeff_sub (N:=N) (m:=m) (V19.Vpr N Q Q) (V19.Vpr N Q H) (core_subset hQH)).trans
      (V19.V1ff le_rfl hQH hbudget F hF)
  rw [hcut,←low_shell_model N m Q H hQH hHN,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply le_of_eq
  refine sum_congr rfl fun i _ => ?_
  have hpart : V19.cell N Q H i ⊆ Set.Ioc (0:ℝ) 1 := Set.inter_subset_right
  have h₁ := (hF.intervalIntegrable (μ:=volume) 0 1).1.mono_set hpart
  have hm : Continuous (fun t => Va2.model N i t ^2*osc t) := ((Va2.Ve5 N i).pow 2).mul ho
  have h₂ := (hm.intervalIntegrable (μ:=volume) 0 1).1.mono_set hpart
  change ‖(∫ t in V19.cell N Q H i, F t) - (∫ t in V19.cell N Q H i, Va2.model N i t^2*osc t)‖ = _
  rw [←integral_sub h₁ h₂]
  simp only [F,osc,sub_mul]

/-- The complete low-denominator windows permit any intermediate outer height,
with an error uniform in that height and in the integer Fourier frequency. -/
theorem uniform_low_comparison (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, V20.narrow N ≤ H → H ≤ V20.width N → ∀ m : ℕ,
      ‖rationalPart N m (V20.narrow N) H-complexModel N m (V20.narrow N) H‖ ≤ ε*(N:ℝ) := by
  filter_upwards [masked_low_skirt (ε/2) (by positivity),narrow_error (ε/2) (by positivity),V20.Vhd]
    with N hskirt hinner hgeom H hQH hHW m
  obtain ⟨_,_,hQU,_,hWN,hbud⟩ := hgeom
  let Q := V20.narrow N
  have hbud' : 2*H*Q < N := (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hHW) hQU).trans_lt hbud
  have hHN : H≤N := by omega
  have hpart (i : ℕ × ℕ) (_ : i ∈ lowCenters N) : V19.cell N Q H i ⊆ skirtCell N i := by
    rintro t ⟨⟨hwide,hnarrow⟩,hunit⟩
    exact ⟨⟨V19.V1zw hHW i hwide,hnarrow⟩,hunit⟩
  have hshell := (shell_error (m:=m) hQH hHN hbud').trans (hskirt _ hpart (m:ℝ))
  have hadd : rationalPart N m Q H - complexModel N m Q H =
      ((rationalPart N m Q H-rationalPart N m Q Q)-(complexModel N m Q H-complexModel N m Q Q)) +
      (rationalPart N m Q Q - complexModel N m Q Q) := by abel
  change ‖rationalPart N m Q H - complexModel N m Q H‖ ≤ _
  rw [hadd]
  apply (norm_add_le _ _).trans
  linarith only [hshell,hinner m]

end
end GoldbachShiftedLowArcs

namespace GoldbachShiftedLowArcs
open Filter Finset MeasureTheory GoldbachDyadicShiftTail GoldbachWideModel GoldbachSmallerArc
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology Classical
noncomputable section

theorem low_cut_le : ∀ᶠ N : ℕ in atTop, V20.narrow N ≤ modelCut N := by
  filter_upwards [eventually_ge_atTop 2,V20.V90 2 (5/24) (1/16) (by norm_num) (by norm_num)] with N hN hs
  apply Nat.le_floor
  have h := GoldbachMajorArc.Polylog.cutoff_le_log 2 hN
  change (V20.narrow N:ℝ) ≤ (4*Real.log N)^2 at h
  linarith only [h,hs]

private theorem model_real (N m U H : ℕ) :
    (complexModel N m U H).re = scaledModel N U m H := by
  rw [complexModel,Complex.re_sum]
  refine sum_congr rfl fun q hq => ?_
  rw [Complex.mul_re, GoldbachMajorArc.coefficient_im_zero m (mem_Icc.mp hq).1,zero_mul,sub_zero]
  rfl

/-- Actual low frequencies have a linear lower bound on a single spectral row
with natural cube-root height and all even targets from a quarter of the row. -/
theorem fixed_row_low_floor : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m≤N → N≤4*(m+1) → Even m →
    7*(N:ℝ)/128 ≤ (rationalPart N m (V20.narrow N) (V20.cutoff N)).re := by
  filter_upwards [uniform_low_comparison (1/128) (by norm_num),
    uniform_truncated_model_floor,V20.Vhd,low_cut_le] with N hcomp hf hgeo hQB m hm hband he
  obtain ⟨_,hQ,hQH,_,_,_⟩ := hgeo
  have h := hf _ hQ hQB m hm hband he
  have hcompare := hcomp _ hQH (V20.Vrx N hQ) m
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hcompare)).1
  rw [Complex.sub_re,model_real] at hr
  change (N:ℝ)/16 ≤ scaledModel N (V20.narrow N) m (V20.cutoff N) at h
  linarith

def middleBand (N : ℕ) : Set ℝ := {t | ∃ q a : ℕ, V20.narrow N < q ∧ q ≤ modelCut N ∧
    a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ modelHeight N/((q:ℝ)*N)}

private theorem band_split : ∀ᶠ N : ℕ in atTop,
    V19.cap N (V20.narrow N) (V20.cutoff N) ⊆ actualArcs N ∧
    actualArcs N \ V19.cap N (V20.narrow N) (V20.cutoff N) = middleBand N := by
  filter_upwards [V20.Vhd,low_cut_le] with N hgeo hlb
  obtain ⟨hn,hq,_,_,_,hbudget⟩ := hgeo
  have hx : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hcut : modelCut N ≤ V20.cutoff N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (5/24:ℝ)≤1/3))
  have hsep : 2*V20.cutoff N*modelCut N<N :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (V20.Vrx N hq)) hcut).trans_lt hbudget
  constructor
  · rintro t ⟨q,a,hq₁,hq₂,ha,hc,hw⟩
    exact ⟨q,a,hq₁,hq₂.trans hlb,ha,hc,hw⟩
  · ext t
    constructor
    · rintro ⟨⟨q,a,hq₁,hq₂,ha,hc,hw⟩,hout⟩
      exact ⟨q,a,lt_of_not_ge (fun hl => hout ⟨q,a,hq₁,hl,ha,hc,hw⟩),hq₂,ha,hc,hw⟩
    · rintro ⟨q,a,hlo,hhi,ha,hc,hw⟩
      have hq₁ : 1 ≤ q := by omega
      refine ⟨⟨q,a,hq₁,hhi,ha,hc,hw⟩,?_⟩
      rintro ⟨r,b,hr₁,hr₂,hb,hbc,hrw⟩
      have heq := V19.Vtg (n:=N) (H:=V20.cutoff N) (U:=modelCut N) (i:=(q,a)) (j:=(r,b)) hsep
        (V19.Vcx.mpr ⟨hq₁,hhi,ha,hc⟩) (V19.Vcx.mpr ⟨hr₁,hr₂.trans hlb,hb,hbc⟩) hw hrw
      have hqr : q=r := congrArg Prod.fst heq
      omega


end
end GoldbachShiftedLowArcs


namespace GoldbachShiftedLowArcs
open Filter Finset GoldbachDyadicShiftTail GoldbachSmallerArc
open scoped Topology Classical
noncomputable section

theorem nonnegative_side_support :
    (let e := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
  let S := fun (N : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (N+1), (w k:ℂ)*e ((k:ℝ)*t)
  let B := fun N : ℕ => {t : ℝ | ∃ q a : ℕ, (Nat.log 2 (N+2))^2 < q ∧
    q ≤ ⌊(N:ℝ)^(5/24:ℝ)⌋₊ ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (⌊(N:ℝ)^(1/3:ℝ)⌋₊ : ℕ)/((q:ℝ)*N)}
  let J := fun (X m : ℕ) => (intervalIntegral (fun t => (B (2*X)).indicator
    (fun u => (S (2*X) u)^2*e (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re
  let I := fun X : ℕ => (Finset.Icc (X/2) (2*X)).filter (fun m => 4 ≤ m ∧ Even m)
  let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card
  ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    (((I X).filter (fun m => G m=0 ∧ -(X:ℝ)/32 ≤ J X m)).card:ℝ) ≤ C*(X:ℝ)^(191/240:ℝ)) := by
  let A := fun X : ℕ => (candidates X).filter fun m => count m=0 ∧
    -(X:ℝ)/32 ≤ (coeff (middleBand (2*X)) (2*X) m).re
  change ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ((A X).card:ℝ) ≤ C*(X:ℝ)^(191/240:ℝ)
  let s : ℝ := 1/240
  let C := (16:ℝ)^2*(2:ℝ)^(67/24+s)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (fixed_row_low_floor.and (band_split.and (short_row_energy s (by norm_num [s]))))
  refine ⟨max N 8,?_⟩
  intro X hX
  have h8 : 8≤X := (le_max_right N 8).trans hX
  have hx : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  obtain ⟨hfloor,⟨hsub,hsplit⟩,hmoment⟩ := hN (2*X) (by omega)
  have hs : A X ⊆ loud X := by
    intro m hm
    obtain ⟨hcan,hbad,hgood⟩ := mem_filter.mp hm
    obtain ⟨hi,_,heven⟩ := mem_filter.mp hcan
    obtain ⟨hml,hmh⟩ := mem_Icc.mp hi
    have hlow := hfloor m hmh (by omega) heven
    let U := V20.narrow (2*X)
    let H := V20.cutoff (2*X)
    have hfull : onCoeff (2*X) m-rationalPart (2*X) m U H = coeff (middleBand (2*X)) (2*X) m := by
      rw [←hsplit]
      exact restrict_coeff_sub (N:=2*X) (m:=m) (V19.Vpr (2*X) U H) (measurable_actualArcs (2*X)) hsub
    have hr := congrArg Complex.re hfull
    rw [Complex.sub_re] at hr
    have heq := eq_neg_of_add_eq_zero_left (exception_row_zero hbad (2*X))
    have hnorm := Complex.re_le_norm (onCoeff (2*X) m)
    rw [heq,norm_neg] at hnorm
    rw [←heq] at hnorm
    change 7*((2*X:ℕ):ℝ)/128 ≤ (rationalPart (2*X) m U H).re at hlow
    push_cast at hlow
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by linarith only [hlow,hr,hgood,hnorm,hx]⟩
  apply (Nat.cast_le.mpr (card_le_card hs)).trans
  apply (loud_energy X (by omega)).trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<((X:ℝ)/16)^2)).mpr
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le] at hmoment
  apply hmoment.trans_eq
  have hpower : (X:ℝ)^(67/24+s) = (X:ℝ)^(191/240:ℝ)*(X:ℝ)^2 := by
    rw [show (67/24:ℝ)+s=191/240+2 by norm_num [s],Real.rpow_add hx,Real.rpow_ofNat]
  rw [hpower]
  dsimp [C]
  ring

end
end GoldbachShiftedLowArcs


theorem Conjectures.Cuts.Taskb6e27f994eefd2cb29d16cb2 :
  (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → ℝ := fun (x2 : ℕ) => if Nat.Prime x2 then Real.log (↑x2 : ℝ) else (0 : ℝ); have x3 : ℕ → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x2 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x4 : ℕ → Set ℝ := fun (x4 : ℕ) => {x5 : ℝ | ∃ (x6 : ℕ) (x7 : ℕ), Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ) < x6 ∧ x6 ≤ ⌊(↑x4 : ℝ) ^ (5 / 24 : ℝ)⌋₊ ∧ x7 ≤ x6 ∧ x7.Coprime x6 ∧ |x5 - (↑x7 : ℝ) / (↑x6 : ℝ)| ≤ (↑⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) / ((↑x6 : ℝ) * (↑x4 : ℝ))}; have x5 : ℕ → ℕ → ℝ := fun (x5 x6 : ℕ) => (∫ (x7 : ℝ) in (0 : ℝ)..(1 : ℝ), (x4 ((2 : ℕ) * x5)).indicator (fun (x8 : ℝ) => x3 ((2 : ℕ) * x5) x8 ^ (2 : ℕ) * x1 (-(↑x6 : ℝ) * x8)) x7).re; have x6 : ℕ → Finset ℕ := fun (x6 : ℕ) => {x7 ∈ Finset.Icc (x6 / (2 : ℕ)) ((2 : ℕ) * x6) | (4 : ℕ) ≤ x7 ∧ Even x7}; have x7 : ℕ → ℕ := fun (x7 : ℕ) => {x8 ∈ Finset.range (x7 + (1 : ℕ)) | Nat.Prime x8 ∧ Nat.Prime (x7 - x8)}.card; ∃ (x8 : ℝ), (0 : ℝ) < x8 ∧ ∃ (x9 : ℕ), ∀ x10 ≥ x9, (↑{x12 ∈ x6 x10 | x7 x12 = (0 : ℕ) ∧ -(↑x10 : ℝ) / (32 : ℝ) ≤ x5 x10 x12}.card : ℝ) ≤ x8 * (↑x10 : ℝ) ^ (191 / 240 : ℝ)) :=
  GoldbachShiftedLowArcs.nonnegative_side_support
