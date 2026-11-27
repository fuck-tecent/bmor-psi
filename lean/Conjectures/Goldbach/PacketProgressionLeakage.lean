import Mathlib

open MeasureTheory Set Real Complex
open scoped BigOperators

noncomputable section

namespace Conjectures.Goldbach.PacketProgressionLeakage_aux

def Qf (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

def arcsf (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q ∧
     |t - (a:ℝ)/(q:ℝ)| ≤ (Qf n : ℝ)/((q:ℝ)*(n:ℝ))}

def Ef (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

def Pf (d M : ℕ) (t : ℝ) : ℂ := ∑ j ∈ Finset.range M, (Ef ((d:ℝ)*t))^(j+1)

def wt (δ v : ℝ) : ℝ := ((max v 0 + δ)^2)⁻¹

lemma arcsf_measurable (n : ℕ) : MeasurableSet (arcsf n) := by
  have hEq : arcsf n = ⋃ q : ℕ, ⋃ a : ℕ,
      (if 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q then
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Qf n : ℝ) / ((q : ℝ) * (n : ℝ))}
      else (∅ : Set ℝ)) := by
    ext t
    simp only [arcsf, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hcop, hdist⟩
      refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      refine Set.mem_iUnion.mpr ⟨a, ?_⟩
      rw [if_pos ⟨hq, hQ, ha, hcop⟩]
      exact hdist
    · intro ht
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ht
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hq
      by_cases h : 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
      · rw [if_pos h] at ha
        exact ⟨q, a, h.1, h.2.1, h.2.2.1, h.2.2.2, ha⟩
      · rw [if_neg h] at ha
        exact absurd ha (Set.notMem_empty t)
  rw [hEq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
  · rw [if_pos h]
    exact measurableSet_le ((measurable_id.sub measurable_const).abs) measurable_const
  · rw [if_neg h]
    exact MeasurableSet.empty

set_option maxHeartbeats 1000000 in
lemma coprime_reduced (m d : ℕ) (hd : 0 < d) :
    Nat.Coprime (m / Nat.gcd m d) (d / Nat.gcd m d) := by
  have hgpos : 0 < Nat.gcd m d := Nat.gcd_pos_of_pos_right _ hd
  have hgdm : Nat.gcd m d ∣ m := Nat.gcd_dvd_left m d
  have hgdd : Nat.gcd m d ∣ d := Nat.gcd_dvd_right m d
  have hmg : m / Nat.gcd m d * Nat.gcd m d = m := Nat.div_mul_cancel hgdm
  have hdg : d / Nat.gcd m d * Nat.gcd m d = d := Nat.div_mul_cancel hgdd
  have hG1 : Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) * Nat.gcd m d ∣ m := by
    have h := mul_dvd_mul (Nat.gcd_dvd_left (m / Nat.gcd m d) (d / Nat.gcd m d))
      (dvd_refl (Nat.gcd m d))
    rwa [hmg] at h
  have hG2 : Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) * Nat.gcd m d ∣ d := by
    have h := mul_dvd_mul (Nat.gcd_dvd_right (m / Nat.gcd m d) (d / Nat.gcd m d))
      (dvd_refl (Nat.gcd m d))
    rwa [hdg] at h
  have hG3 : Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) * Nat.gcd m d ∣ Nat.gcd m d :=
    Nat.dvd_gcd hG1 hG2
  have hle : Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) * Nat.gcd m d ≤ Nat.gcd m d :=
    Nat.le_of_dvd hgpos hG3
  have hqpos : 0 < d / Nat.gcd m d := by
    rcases Nat.eq_zero_or_pos (d / Nat.gcd m d) with h | h
    · exfalso
      have h1 : d = 0 := by rw [← hdg, h, zero_mul]
      omega
    · exact h
  have hGpos : 0 < Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) :=
    Nat.gcd_pos_of_pos_right _ hqpos
  have hGeq : Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) = 1 := by
    by_contra hcon
    have h2 : 2 ≤ Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) := by omega
    have h3 : 2 * Nat.gcd m d ≤
        Nat.gcd (m / Nat.gcd m d) (d / Nat.gcd m d) * Nat.gcd m d := by
      have h4 := Nat.mul_le_mul_right (Nat.gcd m d) h2
      simpa [mul_comm] using h4
    have h5 : 2 * Nat.gcd m d ≤ Nat.gcd m d := le_trans h3 hle
    omega
  exact Nat.coprime_iff_gcd_eq_one.mpr hGeq

set_option maxHeartbeats 1000000 in
lemma gap_of_not_mem (n d m : ℕ) (hn : 0 < n) (hd : 0 < d) (hdQ : d ≤ Qf n) (hm : m ≤ d)
    {t : ℝ} (ht : t ∉ arcsf n) :
    (Qf n : ℝ)/(n:ℝ) < |(d:ℝ)*t - (m:ℝ)| := by
  have hgpos : 0 < Nat.gcd m d := Nat.gcd_pos_of_pos_right _ hd
  have hgdm : Nat.gcd m d ∣ m := Nat.gcd_dvd_left m d
  have hgdd : Nat.gcd m d ∣ d := Nat.gcd_dvd_right m d
  have hqpos : 0 < d / Nat.gcd m d := by
    rcases Nat.eq_zero_or_pos (d / Nat.gcd m d) with h | h
    · exfalso
      have h1 : d = 0 := by rw [← Nat.div_mul_cancel hgdd, h, zero_mul]
      omega
    · exact h
  have hq1 : 1 ≤ d / Nat.gcd m d := hqpos
  have hqQ : d / Nat.gcd m d ≤ Qf n :=
    le_trans (Nat.div_le_self d (Nat.gcd m d)) hdQ
  have haq : m / Nat.gcd m d ≤ d / Nat.gcd m d := by
    rw [Nat.le_div_iff_mul_le hgpos]
    rw [Nat.div_mul_cancel hgdm]
    exact hm
  have hcop : Nat.Coprime (m / Nat.gcd m d) (d / Nat.gcd m d) := coprime_reduced m d hd
  have hg0 : (Nat.gcd m d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hgpos)
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hfrac : ((m / Nat.gcd m d : ℕ):ℝ)/((d / Nat.gcd m d : ℕ):ℝ) = (m:ℝ)/(d:ℝ) :=
    Nat.cast_div_div_div_cancel_right hgdd hgdm
  have hkey : (Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ)) <
      |t - ((m / Nat.gcd m d : ℕ):ℝ)/((d / Nat.gcd m d : ℕ):ℝ)| := by
    by_contra hcon
    refine ht ?_
    unfold arcsf
    exact ⟨d / Nat.gcd m d, m / Nat.gcd m d, hq1, hqQ, haq, hcop, le_of_not_gt hcon⟩
  rw [hfrac] at hkey
  have hdd : (0:ℝ) < d := by exact_mod_cast hd
  have hmul : |(d:ℝ)*t - (m:ℝ)| = (d:ℝ) * |t - (m:ℝ)/(d:ℝ)| := by
    have h1 : (d:ℝ)*t - (m:ℝ) = (d:ℝ) * (t - (m:ℝ)/(d:ℝ)) := by field_simp <;> ring
    rw [h1, abs_mul, abs_of_pos hdd]
  have hstep : (Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ)) * (d:ℝ)
      = ((Nat.gcd m d):ℝ) * ((Qf n : ℝ)/(n:ℝ)) := by
    rw [Nat.cast_div hgdd hg0]
    field_simp <;> ring
  have hQpos : (0:ℝ) < Qf n := by
    have h1 : 0 < Qf n := lt_of_lt_of_le hd hdQ
    exact_mod_cast h1
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : (d:ℝ) * ((Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ)))
      < (d:ℝ) * |t - (m:ℝ)/(d:ℝ)| := mul_lt_mul_of_pos_left hkey hdd
  have h2 : (d:ℝ) * ((Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ)))
      = ((Nat.gcd m d):ℝ) * ((Qf n : ℝ)/(n:ℝ)) := by
    calc (d:ℝ) * ((Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ)))
        = ((Qf n : ℝ)/(((d / Nat.gcd m d : ℕ):ℝ)*(n:ℝ))) * (d:ℝ) := by ring
      _ = ((Nat.gcd m d):ℝ) * ((Qf n : ℝ)/(n:ℝ)) := hstep
  rw [h2] at h1
  have hg1 : (1:ℝ) ≤ ((Nat.gcd m d):ℝ) := by exact_mod_cast hgpos
  have h3 : (Qf n : ℝ)/(n:ℝ) ≤ ((Nat.gcd m d):ℝ) * ((Qf n : ℝ)/(n:ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_right hg1 (le_of_lt (div_pos hQpos hnpos))
    simpa using h4
  rw [hmul]
  linarith

lemma Ef_cont : Continuous Ef := by
  unfold Ef
  fun_prop

lemma Ef_norm (x : ℝ) : ‖Ef x‖ = 1 := by
  unfold Ef
  exact Complex.norm_exp_ofReal_mul_I _

lemma Ef_sub_one (x : ℝ) : ‖Ef x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  unfold Ef
  rw [show (((2*Real.pi*x:ℝ):ℂ)*Complex.I) = Complex.I * ((2*Real.pi*x:ℝ):ℂ) from by ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2*Real.pi*x:ℝ)/2 = Real.pi * x from by ring]
  simp [Real.norm_eq_abs, abs_mul]

private lemma continuous_fsum {ι : Type*} [DecidableEq ι] (g : ι → ℝ → ℂ)
    (hg : ∀ i, Continuous (g i)) (s : Finset ι) :
    Continuous (fun x => ∑ i ∈ s, g i x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuous_const
  | insert a s ha ih =>
    have hc : (fun x => ∑ i ∈ insert a s, g i x) = (fun x => g a x + ∑ i ∈ s, g i x) := by
      funext x
      exact Finset.sum_insert ha
    rw [hc]
    exact (hg a).add ih

lemma Pf_cont (d M : ℕ) : Continuous (fun t => ‖Pf d M t‖^2) := by
  have h1 : Continuous (fun t => Ef ((d:ℝ)*t)) :=
    Ef_cont.comp (continuous_const.mul continuous_id)
  have h2 : Continuous (fun t => Pf d M t) := by
    unfold Pf
    exact continuous_fsum (fun j t => Ef ((d:ℝ)*t)^(j+1)) (fun j => h1.pow (j+1))
      (Finset.range M)
  exact (h2.norm).pow 2

lemma packet_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (M : ℕ) :
    ‖∑ j ∈ Finset.range M, z^(j+1)‖ ≤ 2 / ‖z - 1‖ := by
  have hsum : ∑ j ∈ Finset.range M, z^(j+1) = z * ∑ j ∈ Finset.range M, z^j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgs : ∑ j ∈ Finset.range M, z^j = (z^M - 1)/(z - 1) := geom_sum_eq hz1 M
  rw [hsum, hgs, norm_mul, hz, one_mul, norm_div]
  have h2 : ‖z^M - 1‖ ≤ 2 := by
    have h3 := norm_sub_le (z^M) (1:ℂ)
    have h4 : ‖z^M‖ = 1 := by rw [norm_pow, hz, one_pow]
    rw [h4, norm_one] at h3
    linarith
  have hpos : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hz1
  exact div_le_div_of_nonneg_right h2 hpos.le

lemma sin_lower (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    2 * min u (1-u) ≤ Real.sin (Real.pi * u) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  rcases le_or_gt u (1-u) with h | h
  · rw [min_eq_left h]
    have hx : Real.pi * u ≤ Real.pi / 2 := by
      have h1 : u ≤ 1/2 := by linarith
      have h2 : Real.pi * u ≤ Real.pi * (1/2) := mul_le_mul_of_nonneg_left h1 hpi.le
      linarith
    have hb := Real.mul_le_sin (x := Real.pi * u) (by positivity) hx
    have h1 : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp <;> ring
    linarith
  · rw [min_eq_right (le_of_lt h)]
    have hx : Real.pi * (1-u) ≤ Real.pi / 2 := by
      have h1 : 1-u ≤ 1/2 := by linarith
      have h2 : Real.pi * (1-u) ≤ Real.pi * (1/2) := mul_le_mul_of_nonneg_left h1 hpi.le
      linarith
    have hb := Real.mul_le_sin (x := Real.pi * (1-u)) (by positivity) hx
    have h1 : 2 / Real.pi * (Real.pi * (1-u)) = 2 * (1-u) := by field_simp <;> ring
    have hsinEq : Real.sin (Real.pi * u) = Real.sin (Real.pi * (1-u)) := by
      have h2 : Real.pi * (1-u) = Real.pi - Real.pi * u := by ring
      rw [h2, Real.sin_pi_sub]
    linarith

set_option maxHeartbeats 1000000 in
lemma packet_sq_le (d M : ℕ) (t : ℝ) (k : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hdt : (d:ℝ)*t = (k:ℝ) + u)
    (hlow : 0 < u) (hupp : u < 1) :
    ‖Pf d M t‖^2 ≤ (4 * (min u (1-u))^2)⁻¹ := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hsin : |Real.sin (Real.pi * ((d:ℝ)*t))| = Real.sin (Real.pi * u) := by
    have h1 : Real.pi * ((d:ℝ)*t) = Real.pi * u + (k:ℝ) * Real.pi := by
      rw [hdt]; ring
    rw [h1, Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith))
  have hsinpos : 0 < Real.sin (Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hzs : ‖Ef ((d:ℝ)*t) - 1‖ = 2 * Real.sin (Real.pi * u) := by
    rw [Ef_sub_one, hsin]
  have hzne : Ef ((d:ℝ)*t) ≠ 1 := by
    intro hcon
    have h1 : ‖Ef ((d:ℝ)*t) - 1‖ = 0 := by rw [hcon]; simp
    rw [hzs] at h1
    linarith
  have hbound : ‖Pf d M t‖ ≤ 2 / ‖Ef ((d:ℝ)*t) - 1‖ := by
    have h3 := packet_le (Ef ((d:ℝ)*t)) (Ef_norm _) hzne M
    simpa [Pf] using h3
  rw [hzs] at hbound
  have hb2 : ‖Pf d M t‖ ≤ 1 / Real.sin (Real.pi * u) := by
    have h2 : (2:ℝ) / (2 * Real.sin (Real.pi * u)) = 1 / Real.sin (Real.pi * u) := by
      field_simp <;> ring
    rw [h2] at hbound
    exact hbound
  have hinv : 0 < 1 / Real.sin (Real.pi * u) := div_pos one_pos hsinpos
  have hmin : 0 < min u (1-u) := lt_min hlow (by linarith)
  have hj : 2 * min u (1-u) ≤ Real.sin (Real.pi * u) := sin_lower u hu0 hu1
  have h3 : 4 * (min u (1-u))^2 ≤ (Real.sin (Real.pi * u))^2 := by
    have h4 : (0:ℝ) ≤ Real.sin (Real.pi * u) - 2 * min u (1-u) := by linarith
    have h5 : (0:ℝ) ≤ Real.sin (Real.pi * u) + 2 * min u (1-u) := by linarith
    nlinarith [mul_nonneg h4 h5]
  have hsq : ‖Pf d M t‖^2 ≤ (1 / Real.sin (Real.pi * u))^2 := by
    have h4 : (0:ℝ) ≤ ‖Pf d M t‖ := norm_nonneg _
    have h5 : (0:ℝ) ≤ 1 / Real.sin (Real.pi * u) - ‖Pf d M t‖ := by linarith
    have h6 : (0:ℝ) ≤ 1 / Real.sin (Real.pi * u) + ‖Pf d M t‖ := by linarith
    nlinarith [mul_nonneg h5 h6]
  calc ‖Pf d M t‖^2 ≤ (1 / Real.sin (Real.pi * u))^2 := hsq
    _ = ((Real.sin (Real.pi * u))^2)⁻¹ := by rw [div_pow, one_pow, one_div]
    _ ≤ (4 * (min u (1-u))^2)⁻¹ := by
      have h4 : 0 < 4 * (min u (1-u))^2 := by positivity
      simpa using one_div_le_one_div_of_le h4 h3

lemma wt_of_nonneg (δ v : ℝ) (h : 0 ≤ v) : wt δ v = ((v+δ)^2)⁻¹ := by
  unfold wt
  rw [max_eq_left h]

lemma wt_nonneg (δ v : ℝ) : 0 ≤ wt δ v := by
  unfold wt
  exact inv_nonneg.mpr (sq_nonneg _)

lemma wt_cont (δ : ℝ) (hδ : 0 < δ) : Continuous (wt δ) := by
  unfold wt
  have h1 : Continuous (fun v : ℝ => (max v 0 + δ)^2) := by fun_prop
  refine h1.inv₀ ?_
  intro v
  have h2 : (0:ℝ) < max v 0 + δ := by
    have h3 : (0:ℝ) ≤ max v 0 := le_max_right v 0
    linarith
  have h4 : (0:ℝ) < (max v 0 + δ)^2 := by positivity
  exact h4.ne'

lemma wt_ge (δ u : ℝ) (hδ : 0 < δ) (hu : δ ≤ u) : (4*u^2)⁻¹ ≤ wt δ u := by
  have huδ : (0:ℝ) < u + δ := by linarith
  have h3 : (u+δ)^2 ≤ 4*u^2 := by
    have hA : (0:ℝ) ≤ 2*u - (u+δ) := by linarith
    have hB : (0:ℝ) ≤ 2*u + (u+δ) := by linarith
    nlinarith [mul_nonneg hA hB]
  have h4 : 0 < (u+δ)^2 := sq_pos_of_pos huδ
  have h5 : (4*u^2)⁻¹ ≤ ((u+δ)^2)⁻¹ := by
    simpa using one_div_le_one_div_of_le h4 h3
  rw [wt_of_nonneg δ u (by linarith)]
  exact h5

lemma wt_min_le (δ u v : ℝ) (hδ : 0 < δ) (hu : δ ≤ u) (hv : δ ≤ v) :
    (4 * (min u v)^2)⁻¹ ≤ wt δ u + wt δ v := by
  rcases le_or_gt u v with h | h
  · rw [min_eq_left h]
    exact le_trans (wt_ge δ u hδ hu) (le_add_of_nonneg_right (wt_nonneg δ v))
  · rw [min_eq_right (le_of_lt h)]
    exact le_trans (wt_ge δ v hδ hv) (le_add_of_nonneg_left (wt_nonneg δ u))

lemma wt_int (δ : ℝ) (hδ : 0 < δ) : (∫ v in (0:ℝ)..1, wt δ v) ≤ δ⁻¹ := by
  have hcont : ContinuousOn (fun v : ℝ => -(v+δ)⁻¹) (Set.Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun v : ℝ => (v+δ)⁻¹) (Set.Icc (0:ℝ) 1) := by
      refine (continuousOn_id.add continuousOn_const).inv₀ ?_
      intro v hv
      have h2 : (0:ℝ) < v + δ := by linarith [hv.1]
      exact h2.ne'
    exact h1.neg
  have hint : IntervalIntegrable (wt δ) volume 0 1 := (wt_cont δ hδ).intervalIntegrable 0 1
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun v : ℝ => -(v+δ)⁻¹) (wt δ x) (Set.Ioi x) x := by
    intro x hx
    have hx0 : x + δ ≠ 0 := by
      have h1 : (0:ℝ) < x + δ := by linarith [hx.1]
      exact h1.ne'
    have h2 : HasDerivAt (fun v : ℝ => v + δ) 1 x := by
      have h3 := (hasDerivAt_id x : HasDerivAt (id : ℝ → ℝ) 1 x).add
        (hasDerivAt_const x δ : HasDerivAt (fun _ : ℝ => δ) 0 x)
      have h4 : (1:ℝ) + 0 = 1 := by ring
      rw [h4] at h3
      exact h3
    have h3 : HasDerivAt (fun v : ℝ => (v+δ)⁻¹) (-(1:ℝ) / (x+δ)^2) x := h2.inv hx0
    have h4 : HasDerivAt (fun v : ℝ => -(v+δ)⁻¹) (-(-(1:ℝ) / (x+δ)^2)) x := h3.neg
    have h5 : -(-(1:ℝ) / (x+δ)^2) = wt δ x := by
      rw [wt_of_nonneg δ x hx.1.le]
      ring
    rw [h5] at h4
    exact h4.hasDerivWithinAt
  have hval : (∫ v in (0:ℝ)..1, wt δ v) = δ⁻¹ - (1+δ)⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := (0:ℝ)) (b := 1)
      (f := fun v : ℝ => -(v+δ)⁻¹) (f' := wt δ) (by norm_num) hcont hderiv hint
    calc (∫ v in (0:ℝ)..1, wt δ v) = (-(1+δ)⁻¹) - (-((0:ℝ)+δ)⁻¹) := by simpa using h
      _ = (-(1+δ)⁻¹) - (-δ⁻¹) := by ring
      _ = δ⁻¹ - (1+δ)⁻¹ := by ring
  rw [hval]
  have h1 : (0:ℝ) < (1+δ)⁻¹ := by positivity
  linarith

set_option maxHeartbeats 1000000 in
lemma main_bound (n d M : ℕ) (hn : 0 < n) (hd : 0 < d) (hdQ : d ≤ Qf n) :
    intervalIntegral ((arcsf n)ᶜ.indicator (fun t => ‖Pf d M t‖^2)) (0:ℝ) 1
      MeasureTheory.volume ≤ 2 * Real.pi * (n:ℝ)/(Qf n) := by
  have hQf1 : 1 ≤ Qf n := le_trans hd hdQ
  have hQfpos : (0:ℝ) < Qf n := by
    have h2 : 0 < Qf n := lt_of_lt_of_le hd hdQ
    exact_mod_cast h2
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  set δ := (Qf n : ℝ)/(n:ℝ) with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hQfpos hnpos
  set S := ∫ v in (0:ℝ)..1, wt δ v with hS
  have hSle : S ≤ δ⁻¹ := wt_int δ hδpos
  set f : ℝ → ℝ := (arcsf n)ᶜ.indicator (fun t => ‖Pf d M t‖^2) with hfdef
  have hmeas : MeasurableSet (arcsf n)ᶜ := (arcsf_measurable n).compl
  have hfc : Continuous (fun t => ‖Pf d M t‖^2) := Pf_cont d M
  set a : ℕ → ℝ := fun k => (k:ℝ)/(d:ℝ) with hadef
  have hak : ∀ k : ℕ, (d:ℝ) * a k = (k:ℝ) := by
    intro k
    rw [hadef]
    exact mul_div_cancel₀ _ hd0
  have hak1 : ∀ k : ℕ, (d:ℝ) * a (k+1) = (k:ℝ) + 1 := by
    intro k
    rw [hak]
    push_cast
    ring
  have hle : ∀ k : ℕ, a k ≤ a (k+1) := by
    intro k
    rw [hadef]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hdpos.le
  have hstep : ∀ k < d, IntervalIntegrable f volume (a k) (a (k+1)) := by
    intro k hk
    rw [hfdef, intervalIntegrable_iff_integrableOn_Ioc_of_le (hle k)]
    exact ((hfc.intervalIntegrable (μ := volume) (a k) (a (k+1))).1).indicator hmeas
  have hsum : (∫ t in (0:ℝ)..1, f t) = ∑ k ∈ Finset.range d, ∫ t in a k..a (k+1), f t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals hstep
    have ha0 : a 0 = 0 := by rw [hadef]; simp
    have had : a d = 1 := by rw [hadef]; exact div_self hd0
    rw [ha0, had] at h
    exact h.symm
  have hpiece : ∀ k < d, (∫ t in a k..a (k+1), f t) ≤ 2 * ((d:ℝ)⁻¹ * S) := by
    intro k hk
    have hkm : k ≤ d := le_of_lt hk
    have hkm1 : k + 1 ≤ d := hk
    have hpt : ∀ t ∈ Set.Icc (a k) (a (k+1)), f t ≤
        wt δ ((d:ℝ)*t - (k:ℝ)) + wt δ (((k:ℝ) + 1) - (d:ℝ)*t) := by
      intro t ht
      have hu0 : 0 ≤ (d:ℝ)*t - (k:ℝ) := by
        have h1 : (d:ℝ) * a k ≤ (d:ℝ) * t := mul_le_mul_of_nonneg_left ht.1 hdpos.le
        rw [hak k] at h1
        linarith
      have hu1 : (d:ℝ)*t - (k:ℝ) ≤ 1 := by
        have h1 : (d:ℝ) * t ≤ (d:ℝ) * a (k+1) := mul_le_mul_of_nonneg_left ht.2 hdpos.le
        rw [hak1 k] at h1
        linarith
      by_cases hmem : t ∈ arcsf n
      · have hnm : t ∉ (arcsf n)ᶜ := fun h => h hmem
        have hz : f t = 0 := by
          rw [hfdef]
          simp [hnm]
        rw [hz]
        have h1 := wt_nonneg δ ((d:ℝ)*t - (k:ℝ))
        have h2 := wt_nonneg δ (((k:ℝ) + 1) - (d:ℝ)*t)
        linarith
      · have hmm : t ∈ (arcsf n)ᶜ := Set.mem_compl hmem
        have hz : f t = ‖Pf d M t‖^2 := by
          rw [hfdef]
          simp [hmm]
        rw [hz]
        have hgap1 := gap_of_not_mem n d k hn hd hdQ hkm hmem
        have hgap2 := gap_of_not_mem n d (k+1) hn hd hdQ hkm1 hmem
        have hlow : δ < (d:ℝ)*t - (k:ℝ) := by
          rw [abs_of_nonneg hu0] at hgap1
          exact hgap1
        have hupp : δ < ((k:ℝ) + 1) - (d:ℝ)*t := by
          have h2 : |(d:ℝ)*t - ((k+1:ℕ):ℝ)| = ((k:ℝ) + 1) - (d:ℝ)*t := by
            have h3 : ((k+1:ℕ):ℝ) = (k:ℝ)+1 := by push_cast; ring
            rw [h3]
            have h4 : (d:ℝ)*t - ((k:ℝ)+1) = -(((k:ℝ)+1) - (d:ℝ)*t) := by ring
            rw [h4, abs_neg]
            exact abs_of_nonneg (by linarith)
          rw [h2] at hgap2
          exact hgap2
        have hsq := packet_sq_le d M t k ((d:ℝ)*t - (k:ℝ)) hu0 hu1 (by ring)
          (lt_trans hδpos hlow) (by linarith)
        have heq : 1 - ((d:ℝ)*t - (k:ℝ)) = ((k:ℝ) + 1) - (d:ℝ)*t := by ring
        rw [heq] at hsq
        have hwt := wt_min_le δ ((d:ℝ)*t - (k:ℝ)) (((k:ℝ) + 1) - (d:ℝ)*t) hδpos
          (le_of_lt hlow) (le_of_lt hupp)
        exact le_trans hsq hwt
    have hGc1 : Continuous (fun t => wt δ ((d:ℝ)*t - (k:ℝ))) :=
      (wt_cont δ hδpos).comp ((continuous_const.mul continuous_id).sub continuous_const)
    have hGc2 : Continuous (fun t => wt δ (((k:ℝ) + 1) - (d:ℝ)*t)) :=
      (wt_cont δ hδpos).comp (continuous_const.sub (continuous_const.mul continuous_id))
    have hGi1 : IntervalIntegrable (fun t => wt δ ((d:ℝ)*t - (k:ℝ))) volume (a k) (a (k+1)) :=
      hGc1.intervalIntegrable _ _
    have hGi2 : IntervalIntegrable (fun t => wt δ (((k:ℝ) + 1) - (d:ℝ)*t))
        volume (a k) (a (k+1)) := hGc2.intervalIntegrable _ _
    have hmono : (∫ t in a k..a (k+1), f t) ≤
        ∫ t in a k..a (k+1), (wt δ ((d:ℝ)*t - (k:ℝ)) + wt δ (((k:ℝ) + 1) - (d:ℝ)*t)) :=
      intervalIntegral.integral_mono_on (h := hpt) (hab := hle k) (hf := hstep k hk)
        (hg := (hGc1.add hGc2).intervalIntegrable _ _)
    have e1 : (∫ t in a k..a (k+1), wt δ ((d:ℝ)*t - (k:ℝ))) = (d:ℝ)⁻¹ * S := by
      have h := intervalIntegral.integral_comp_mul_sub (wt δ) hd0 (k:ℝ) (a := a k) (b := a (k+1))
      rw [h]
      have b1 : (d:ℝ) * a k - (k:ℝ) = 0 := by rw [hak k]; ring
      have b2 : (d:ℝ) * a (k+1) - (k:ℝ) = 1 := by rw [hak1 k]; ring
      rw [b1, b2, ← hS, smul_eq_mul]
    have e2 : (∫ t in a k..a (k+1), wt δ (((k:ℝ) + 1) - (d:ℝ)*t)) = (d:ℝ)⁻¹ * S := by
      have h := intervalIntegral.integral_comp_sub_mul (wt δ) hd0 ((k:ℝ)+1)
        (a := a k) (b := a (k+1))
      rw [h]
      have b1 : ((k:ℝ)+1) - (d:ℝ) * a (k+1) = 0 := by rw [hak1 k]; ring
      have b2 : ((k:ℝ)+1) - (d:ℝ) * a k = 1 := by rw [hak k]; ring
      rw [b1, b2, ← hS, smul_eq_mul]
    have hval : (∫ t in a k..a (k+1),
        (wt δ ((d:ℝ)*t - (k:ℝ)) + wt δ (((k:ℝ) + 1) - (d:ℝ)*t))) = 2 * ((d:ℝ)⁻¹ * S) := by
      rw [intervalIntegral.integral_add hGi1 hGi2, e1, e2]
      ring
    linarith
  calc (∫ t in (0:ℝ)..1, f t) = ∑ k ∈ Finset.range d, ∫ t in a k..a (k+1), f t := hsum
    _ ≤ ∑ k ∈ Finset.range d, (2 * ((d:ℝ)⁻¹ * S)) :=
        Finset.sum_le_sum (fun k hk => hpiece k (Finset.mem_range.mp hk))
    _ = (d:ℝ) * (2 * ((d:ℝ)⁻¹ * S)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = 2 * S := by
      have hinv : (d:ℝ) * (d:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd0
      calc (d:ℝ) * (2 * ((d:ℝ)⁻¹ * S)) = 2 * (((d:ℝ) * (d:ℝ)⁻¹) * S) := by ring
        _ = 2 * S := by rw [hinv, one_mul]
    _ ≤ 2 * δ⁻¹ := by linarith
    _ = 2 * ((n:ℝ)/(Qf n)) := by rw [hδ, inv_div]
    _ ≤ 2 * Real.pi * (n:ℝ)/(Qf n) := by
        have hpi : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
        have hc : (0:ℝ) ≤ 2 * ((n:ℝ)/(Qf n)) :=
          mul_nonneg (by norm_num) (div_nonneg hnpos.le hQfpos.le)
        have h1 : 2 * ((n:ℝ)/(Qf n)) * 1 ≤ 2 * ((n:ℝ)/(Qf n)) * Real.pi :=
          mul_le_mul_of_nonneg_left hpi hc
        calc 2 * ((n:ℝ)/(Qf n)) = 2 * ((n:ℝ)/(Qf n)) * 1 := by ring
          _ ≤ 2 * ((n:ℝ)/(Qf n)) * Real.pi := h1
          _ = 2 * Real.pi * (n:ℝ)/(Qf n) := by ring

end Conjectures.Goldbach.PacketProgressionLeakage_aux

set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.PacketProgressionLeakage : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let P := fun (d M : ℕ) (t : ℝ) => ∑ j ∈ Finset.range M, (E ((d:ℝ)*t))^(j+1); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ n d M : ℕ, 0<n → 0<d → d ≤ Q n → m (arcs n)ᶜ (fun t => ‖P d M t‖^2) ≤ 2*Real.pi*(n:ℝ)/(Q n:ℝ) := by
  show ∀ n d M : ℕ, 0 < n → 0 < d → d ≤ ((Nat.log 2 (n+2))^2 : ℕ) →
      intervalIntegral
        ((({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ((Nat.log 2 (n+2))^2 : ℕ) ∧ a ≤ q ∧
              Nat.Coprime a q ∧
              |t - (a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))})ᶜ).indicator
          (fun t => ‖∑ j ∈ Finset.range M,
            (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖^2))
        (0:ℝ) 1 MeasureTheory.volume ≤
      2*Real.pi*(n:ℝ)/(((Nat.log 2 (n+2))^2 : ℕ):ℝ)
  intro n d M hn hd hdQ
  exact Conjectures.Goldbach.PacketProgressionLeakage_aux.main_bound n d M hn hd hdQ

end
