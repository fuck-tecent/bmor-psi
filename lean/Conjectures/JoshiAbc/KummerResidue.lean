import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Ring.GeomSum

namespace Conjectures.JoshiAbc.KummerResidue_aux

variable {p : ℕ} [Fact p.Prime]

lemma two_lt_p (hodd : Odd p) : 2 < p := by
  have hp : p.Prime := Fact.out
  rcases hp.two_le.eq_or_lt with h | h
  · exact absurd (h ▸ even_two) (Nat.not_even_iff_odd.mpr hodd)
  · exact h

lemma sum_pow_eq (a t : ℤ_[p]) (hat : a = 1 + (p:ℤ_[p]) * t) (n : ℕ) :
    ∃ V : ℤ_[p], ∑ j ∈ Finset.range n, a^j = (n : ℤ_[p]) + (p:ℤ_[p]) * V := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨V, hV⟩ := ih
    refine ⟨V + t * ((n : ℤ_[p]) + (p:ℤ_[p]) * V), ?_⟩
    have hgeom : a ^ n = 1 + (a - 1) * ∑ j ∈ Finset.range n, a ^ j := by
      have h := mul_geom_sum a n
      rw [h]; ring
    rw [Finset.sum_range_succ, hV, hgeom, hV, hat]
    push_cast
    ring

lemma sum_pow_range_p (hodd : Odd p) (a t : ℤ_[p]) (hat : a = 1 + (p:ℤ_[p]) * t) :
    ∃ W : ℤ_[p], ∑ j ∈ Finset.range p, a^j = (p:ℤ_[p]) + (p:ℤ_[p])^2 * W := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : 2 < p := two_lt_p hodd
  obtain ⟨q, hq⟩ := hp.dvd_choose_self (by norm_num) hp3
  choose V hV using fun l : ℕ => sum_pow_eq a t hat l
  refine ⟨t * ((q : ℤ_[p]) + ∑ l ∈ Finset.range p, V l), ?_⟩
  have hstep : ∀ l : ℕ, a ^ l = 1 + (a - 1) * ∑ j ∈ Finset.range l, a ^ j := by
    intro l
    have h := mul_geom_sum a l
    rw [h]; ring
  have hone : ∑ _l ∈ Finset.range p, (1 : ℤ_[p]) = (p : ℤ_[p]) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hsum1 : ∑ j ∈ Finset.range p, a ^ j
      = (p : ℤ_[p]) + (a - 1) * ∑ l ∈ Finset.range p, ∑ j ∈ Finset.range l, a ^ j := by
    calc ∑ j ∈ Finset.range p, a ^ j
        = ∑ l ∈ Finset.range p, (1 + (a - 1) * ∑ j ∈ Finset.range l, a ^ j) :=
          Finset.sum_congr rfl (fun l _ => hstep l)
      _ = ∑ l ∈ Finset.range p, (1 : ℤ_[p])
            + ∑ l ∈ Finset.range p, ((a - 1) * ∑ j ∈ Finset.range l, a ^ j) :=
          Finset.sum_add_distrib
      _ = (p : ℤ_[p]) + (a - 1) * ∑ l ∈ Finset.range p, ∑ j ∈ Finset.range l, a ^ j := by
          rw [hone, Finset.mul_sum]
  have hsum2 : ∑ l ∈ Finset.range p, ∑ j ∈ Finset.range l, a ^ j
      = ((p.choose 2 : ℕ) : ℤ_[p]) + (p:ℤ_[p]) * ∑ l ∈ Finset.range p, V l := by
    calc ∑ l ∈ Finset.range p, ∑ j ∈ Finset.range l, a ^ j
        = ∑ l ∈ Finset.range p, ((l : ℤ_[p]) + (p:ℤ_[p]) * V l) :=
          Finset.sum_congr rfl (fun l _ => hV l)
      _ = ∑ l ∈ Finset.range p, (l : ℤ_[p])
            + (p:ℤ_[p]) * ∑ l ∈ Finset.range p, V l := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ((p.choose 2 : ℕ) : ℤ_[p]) + (p:ℤ_[p]) * ∑ l ∈ Finset.range p, V l := by
          congr 1
          rw [← Nat.cast_sum, Finset.sum_range_id, ← Nat.choose_two_right]
  have hq' : ((p.choose 2 : ℕ) : ℤ_[p]) = (p:ℤ_[p]) * (q : ℤ_[p]) := by
    rw [hq]; push_cast; ring
  rw [hsum1, hsum2, hq', hat]
  ring

lemma pow_p_step (a t : ℤ_[p]) (hat : a = 1 + (p:ℤ_[p]) * t) :
    ∃ W : ℤ_[p], a^p = 1 + (p:ℤ_[p]) * ((a - 1) * W) := by
  obtain ⟨V, hV⟩ := sum_pow_eq a t hat p
  have h := mul_geom_sum a p
  rw [hV] at h
  refine ⟨1 + V, ?_⟩
  calc a ^ p = 1 + (a ^ p - 1) := by ring
    _ = 1 + (a - 1) * ((p : ℤ_[p]) + (p:ℤ_[p]) * V) := by rw [← h]
    _ = 1 + (p:ℤ_[p]) * ((a - 1) * (1 + V)) := by ring

lemma pow_iterate {a t : ℤ_[p]} (hat : a = 1 + (p:ℤ_[p]) * t) (k : ℕ) :
    ∃ W : ℤ_[p], a^(p^k) = 1 + (p:ℤ_[p])^(k+1) * W := by
  induction k with
  | zero =>
    refine ⟨t, ?_⟩
    rw [pow_zero, pow_one, hat]
    ring
  | succ k ih =>
    obtain ⟨W, hW⟩ := ih
    have hrw : a ^ (p ^ (k+1)) = (a ^ (p^k))^p := by rw [pow_succ, pow_mul]
    have ha' : a^(p^k) = 1 + (p:ℤ_[p]) * ((p:ℤ_[p])^k * W) := by
      rw [hW, pow_succ]; ring
    obtain ⟨W', hW'⟩ := pow_p_step _ _ ha'
    refine ⟨W * W', ?_⟩
    rw [hrw, hW', hW, pow_succ]
    ring

lemma norm_one_add_p_mul (z : ℤ_[p]) : ‖1 + (p:ℤ_[p]) * z‖ = 1 := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlt : ‖(p:ℤ_[p]) * z‖ < 1 := by
    calc ‖(p:ℤ_[p]) * z‖ = ‖(p:ℤ_[p])‖ * ‖z‖ := norm_mul _ _
      _ ≤ ‖(p:ℤ_[p])‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (PadicInt.norm_le_one z) (norm_nonneg _)
      _ = (p:ℝ)⁻¹ := by rw [mul_one, PadicInt.norm_p]
      _ < 1 := by
        have h2 : (0:ℝ) < (p:ℝ) := lt_trans zero_lt_one hp1
        rw [← one_div]
        exact (div_lt_one h2).mpr hp1
  have hne : ‖(1:ℤ_[p])‖ ≠ ‖(p:ℤ_[p]) * z‖ := by
    rw [norm_one]
    exact ne_of_gt hlt
  rw [PadicInt.norm_add_eq_max_of_ne hne, norm_one, max_eq_left (le_of_lt hlt)]

lemma zmod_pow_pow (z : ZMod p) (k : ℕ) : z ^ (p ^ k) = z :=
  ZMod.pow_card_pow z

lemma sub_one_mem_span_p {vz : ℤ_[p]} {k : ℕ}
    (h : vz ^ (p ^ k) - 1 ∈ Ideal.span {((p : ℤ_[p]))}) :
    vz - 1 ∈ Ideal.span {((p : ℤ_[p]))} := by
  have hzmod : PadicInt.toZMod vz ^ (p ^ k) = 1 := by
    have hzero : PadicInt.toZMod (vz ^ (p ^ k) - 1) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
      exact h
    rw [map_sub, map_pow, map_one] at hzero
    exact sub_eq_zero.mp hzero
  have hz : PadicInt.toZMod vz = 1 :=
    (zmod_pow_pow (PadicInt.toZMod vz) k).symm.trans hzmod
  rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hz,
    map_one, sub_self]

lemma exists_pth_root (hodd : Odd p) {m : ℕ} (hm : 2 ≤ m) (s : ℤ_[p])
    (w : ℤ_[p]) (hw : w = 1 + (p:ℤ_[p])^m * s) :
    ∃ z : ℤ_[p], z^p = w ∧ ∃ s' : ℤ_[p], z = 1 + (p:ℤ_[p])^(m-1) * s' := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 2 := ⟨m - 2, by omega⟩
  have hpR : (1:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnp : ‖(p:ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ hpR
  have hnp0 : (0:ℝ) < ‖(p:ℤ_[p])‖ := by
    rw [PadicInt.norm_p]; exact inv_pos.mpr (lt_trans zero_lt_one hpR)
  have hp_ne : (p:ℤ_[p]) ≠ 0 := by
    intro h
    have h0 : (p:ℕ) = 0 := by exact_mod_cast h
    exact (Fact.out : p.Prime).ne_zero h0
  set a : ℤ_[p] := 1 + (p:ℤ_[p])^(k+1) * s with ha_def
  obtain ⟨W, hW⟩ := sum_pow_range_p hodd a ((p:ℤ_[p])^k * s) (by rw [ha_def]; ring)
  have hgeom : a^p - 1 = (a - 1) * ∑ j ∈ Finset.range p, a^j := (mul_geom_sum a p).symm
  have hsub : a - 1 = (p:ℤ_[p])^(k+1) * s := by rw [ha_def]; ring
  have hap : a^p - 1 = (p:ℤ_[p])^(k+2) * s + (p:ℤ_[p])^(k+3) * (s * W) := by
    rw [hgeom, hsub, hW]; ring
  have hkey : a^p - w = (p:ℤ_[p])^(k+3) * (s * W) := by
    calc a^p - w = a^p - (1 + (p:ℤ_[p])^(k+2) * s) := by rw [hw]
      _ = a^p - 1 - (p:ℤ_[p])^(k+2) * s := by ring
      _ = (p:ℤ_[p])^(k+3) * (s * W) := by rw [hap]; ring
  have hxa : ‖(p:ℤ_[p])^(k+1) * s‖ < 1 := by
    have h1 : ‖(p:ℤ_[p])^(k+1) * s‖ ≤ ‖(p:ℤ_[p])‖ := by
      rw [show (p:ℤ_[p])^(k+1) * s = (p:ℤ_[p]) * ((p:ℤ_[p])^k * s) by ring, norm_mul]
      calc ‖(p:ℤ_[p])‖ * ‖(p:ℤ_[p])^k * s‖ ≤ ‖(p:ℤ_[p])‖ * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
        _ = ‖(p:ℤ_[p])‖ := mul_one _
    exact lt_of_le_of_lt h1 hnp
  have ha_norm : ‖a‖ = 1 := by
    have hne : ‖(1:ℤ_[p])‖ ≠ ‖(p:ℤ_[p])^(k+1) * s‖ := by
      rw [norm_one]; exact fun h => (ne_of_lt hxa) h.symm
    rw [ha_def, PadicInt.norm_add_eq_max_of_ne hne, norm_one, max_eq_left (le_of_lt hxa)]
  set F : Polynomial ℤ_[p] := Polynomial.X^p - Polynomial.C w with hF_def
  have hFeval : ∀ z : ℤ_[p], F.aeval z = z^p - w := by
    intro z
    have h : F.aeval z = F.eval z := by rw [Polynomial.coe_aeval_eq_eval]
    rw [h, hF_def]
    simp
  have hFderiv : F.derivative = Polynomial.C (p:ℤ_[p]) * Polynomial.X^(p-1) := by
    rw [hF_def, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero]
  have hderiv_aeval : F.derivative.aeval a = (p:ℤ_[p]) * a^(p-1) := by
    have h : F.derivative.aeval a = F.derivative.eval a := by
      rw [Polynomial.coe_aeval_eq_eval]
    rw [h, hFderiv]
    simp
  have hFa_norm : ‖F.aeval a‖ ≤ ‖(p:ℤ_[p])‖^(k+3) := by
    rw [hFeval a, hkey, norm_mul, norm_pow]
    calc ‖(p:ℤ_[p])‖^(k+3) * ‖s * W‖ ≤ ‖(p:ℤ_[p])‖^(k+3) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) _)
      _ = ‖(p:ℤ_[p])‖^(k+3) := mul_one _
  have hderiv_norm : ‖F.derivative.aeval a‖ = ‖(p:ℤ_[p])‖ := by
    rw [hderiv_aeval, norm_mul, norm_pow, ha_norm, one_pow, mul_one]
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 := by
    rw [hderiv_norm]
    exact lt_of_le_of_lt hFa_norm (pow_lt_pow_right_of_lt_one₀ hnp0 hnp (by omega))
  obtain ⟨z, hz0, hzdist, hz4, hz5⟩ :=
    hensels_lemma (R := ℤ_[p]) (F := F) (a := a) hnorm
  have hzp : z^p = w := by
    have h : z^p - w = 0 := by rw [← hFeval z]; exact hz0
    exact sub_eq_zero.mp h
  refine ⟨z, hzp, ?_⟩
  have hdist : ‖z - a‖ < ‖(p:ℤ_[p])‖ := by rw [hderiv_norm] at hzdist; exact hzdist
  have hdvd : (p:ℤ_[p]) ∣ z - a := by
    rw [← PadicInt.norm_lt_one_iff_dvd]
    exact lt_trans hdist hnp
  have hdvd_a : (p:ℤ_[p]) ∣ a - 1 := by
    refine ⟨(p:ℤ_[p])^k * s, ?_⟩
    rw [ha_def]; ring
  have hdvd_z : (p:ℤ_[p]) ∣ z - 1 := by
    have h : z - 1 = (z - a) + (a - 1) := by ring
    rw [h]
    exact dvd_add hdvd hdvd_a
  obtain ⟨t, ht⟩ := hdvd_z
  obtain ⟨Wz, hWz⟩ := sum_pow_range_p hodd z t (by rw [← ht]; ring)
  set u : ℤ_[p] := 1 + (p:ℤ_[p]) * Wz with hu_def
  have hu_norm : ‖u‖ = 1 := by
    have hpW : ‖(p:ℤ_[p]) * Wz‖ < 1 := by
      calc ‖(p:ℤ_[p]) * Wz‖ = ‖(p:ℤ_[p])‖ * ‖Wz‖ := norm_mul _ _
        _ ≤ ‖(p:ℤ_[p])‖ * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hnp
    have hne : ‖(1:ℤ_[p])‖ ≠ ‖(p:ℤ_[p]) * Wz‖ := by
      rw [norm_one]; exact fun h => (ne_of_lt hpW) h.symm
    rw [hu_def, PadicInt.norm_add_eq_max_of_ne hne, norm_one, max_eq_left (le_of_lt hpW)]
  have hsum : ∑ j ∈ Finset.range p, z^j = (p:ℤ_[p]) * u := by rw [hWz, hu_def]; ring
  have hgeomz : z^p - 1 = (z - 1) * ∑ j ∈ Finset.range p, z^j := (mul_geom_sum z p).symm
  have hzp1 : z^p - 1 = (p:ℤ_[p])^(k+2) * s := by rw [hzp, hw]; ring
  have hcancel : (p:ℤ_[p]) * ((z - 1) * u) = (p:ℤ_[p]) * ((p:ℤ_[p])^(k+1) * s) := by
    have h1 : (p:ℤ_[p]) * ((z - 1) * u) = (z - 1) * ∑ j ∈ Finset.range p, z^j := by
      rw [hsum]; ring
    rw [h1, ← hgeomz, hzp1]
    ring
  have hzmain : (z - 1) * u = (p:ℤ_[p])^(k+1) * s := mul_left_cancel₀ hp_ne hcancel
  refine ⟨s * u.inv, ?_⟩
  have hfin : z - 1 = (p:ℤ_[p])^(k+1) * (s * u.inv) := by
    calc z - 1 = (z - 1) * (u * u.inv) := by rw [PadicInt.mul_inv hu_norm, mul_one]
      _ = ((z - 1) * u) * u.inv := by ring
      _ = ((p:ℤ_[p])^(k+1) * s) * u.inv := by rw [hzmain]
      _ = (p:ℤ_[p])^(k+1) * (s * u.inv) := by ring
  calc z = 1 + (z - 1) := by ring
    _ = 1 + (p:ℤ_[p])^(k+1) * (s * u.inv) := by rw [hfin]

lemma root_exists (hodd : Odd p) : ∀ (k : ℕ) (d : ℤ_[p]),
    ∃ v : ℤ_[p], v^(p^k) = 1 + (p:ℤ_[p])^(k+1) * d := by
  intro k
  induction k with
  | zero =>
    intro d
    refine ⟨1 + (p:ℤ_[p]) * d, ?_⟩
    rw [pow_zero, pow_one]
    ring
  | succ k ih =>
    intro d
    obtain ⟨z, hz, d', hd'⟩ := exists_pth_root hodd (m := k+2) (by omega) d
      (1 + (p:ℤ_[p])^(k+2) * d) rfl
    obtain ⟨v, hv⟩ := ih d'
    refine ⟨v, ?_⟩
    have hexpk : k + 2 - 1 = k + 1 := by omega
    have hstep : v ^ (p^k) = z := by rw [hv, hd', hexpk]
    rw [pow_succ, pow_mul, hstep, hz]

end Conjectures.JoshiAbc.KummerResidue_aux

open Conjectures.JoshiAbc.KummerResidue_aux

theorem Conjectures.JoshiAbc.KummerResidue :
    ∀ (p k : ℕ) [Fact p.Prime], Odd p → ∀ x y : PadicInt p, let u := fun (z : PadicInt p) => 1+(p:Padic p)*(z:Padic p); (∃ v : Padic p, v^(p^k)=u x/u y) ↔ ‖(x:Padic p)-y‖ ≤ (1/(p:ℝ))^k := by
  intro p k _ hodd x y
  dsimp only
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hnorm_eq : ‖(x:Padic p) - (y:Padic p)‖ = ‖x - y‖ := by
    rw [← PadicInt.coe_sub, PadicInt.norm_coe]
  have hpow : (1/(p:ℝ))^k = (p:ℝ)^(-(k:ℤ)) := by
    rw [one_div, inv_pow, zpow_neg, zpow_natCast]
  set b : ℤ_[p] := 1 + (p:ℤ_[p]) * y with hb
  have hb1 : ‖b‖ = 1 := by rw [hb]; exact norm_one_add_p_mul y
  have hbne : ((b:Padic p)) ≠ 0 := by
    intro h
    have hz : b = 0 := PadicInt.coe_eq_zero.mp h
    rw [hz, norm_zero] at hb1
    exact zero_ne_one hb1
  set binv : ℤ_[p] := b.inv with hbinv_def
  have hbinv : b * binv = 1 := PadicInt.mul_inv hb1
  set c : ℤ_[p] := (x - y) * binv with hc
  have hcb : c * b = x - y := by
    rw [hc, mul_assoc, mul_comm binv b, hbinv, mul_one]
  have hbcoe : ((b : Padic p)) = 1 + (p:Padic p) * (y:Padic p) := by
    rw [hb]; push_cast; ring
  have hkey : ((1 + (p:ℤ_[p]) * c : ℤ_[p]) : Padic p)
      = (1 + (p:Padic p) * (x:Padic p)) / (1 + (p:Padic p) * (y:Padic p)) := by
    rw [← hbcoe, eq_div_iff hbne]
    have h1 : (1 + (p:ℤ_[p]) * c) * b = 1 + (p:ℤ_[p]) * x := by
      calc (1 + (p:ℤ_[p]) * c) * b = b + (p:ℤ_[p]) * (c * b) := by ring
        _ = b + (p:ℤ_[p]) * (x - y) := by rw [hcb]
        _ = 1 + (p:ℤ_[p]) * x := by rw [hb]; ring
    exact congrArg (fun z : ℤ_[p] => (z : Padic p)) h1
  rw [hnorm_eq, hpow, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨v, hv⟩
    have hw : v ^ (p^k) = ((1 + (p:ℤ_[p]) * c : ℤ_[p]) : Padic p) := by
      rw [hkey]; exact hv
    have hc1 : ‖(1 + (p:ℤ_[p]) * c : ℤ_[p])‖ = 1 := norm_one_add_p_mul c
    have hv1 : ‖v‖ = 1 := by
      have h1 : ‖v‖ ^ (p^k) = 1 := by
        rw [← norm_pow, hw, PadicInt.norm_coe, hc1]
      have hne : p^k ≠ 0 := pow_ne_zero _ hp0
      by_contra hcon
      rcases lt_or_gt_of_ne hcon with h | h
      · have h2 := pow_lt_one₀ (norm_nonneg v) h hne
        linarith
      · have h2 := one_lt_pow₀ h hne
        linarith
    obtain ⟨vz, hvz⟩ : ∃ vz : ℤ_[p], (vz : Padic p) = v := ⟨Padic.lift v (le_of_eq hv1), rfl⟩
    have hz : vz ^ (p^k) = 1 + (p:ℤ_[p]) * c := by
      apply PadicInt.coe_inj.mp
      rw [PadicInt.coe_pow, hvz]
      exact hw
    have hmem : vz ^ (p^k) - 1 ∈ Ideal.span {((p : ℤ_[p]))} := by
      rw [hz, add_sub_cancel_left]
      exact Ideal.mem_span_singleton.mpr ⟨c, rfl⟩
    have hmem2 : vz - 1 ∈ Ideal.span {((p : ℤ_[p]))} := sub_one_mem_span_p hmem
    obtain ⟨t, ht⟩ : ∃ t : ℤ_[p], vz = 1 + (p:ℤ_[p]) * t := by
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem2
      exact ⟨t, by rw [← ht]; ring⟩
    obtain ⟨W, hW⟩ := pow_iterate ht k
    have hpc : (p:ℤ_[p]) * c = (p:ℤ_[p]) ^ (k+1) * W := by
      have h2 : (1:ℤ_[p]) + (p:ℤ_[p]) * c = 1 + (p:ℤ_[p])^(k+1) * W := by rw [← hz, hW]
      exact add_left_cancel h2
    have hcc : c = (p:ℤ_[p])^k * W := by
      have h2 : (p:ℤ_[p]) * c = (p:ℤ_[p]) * ((p:ℤ_[p])^k * W) := by
        rw [hpc, pow_succ]; ring
      exact mul_left_cancel₀ PadicInt.prime_p.ne_zero h2
    refine ⟨W * b, ?_⟩
    calc x - y = c * b := hcb.symm
      _ = ((p:ℤ_[p])^k * W) * b := by rw [hcc]
      _ = (p:ℤ_[p])^k * (W * b) := by ring
  · intro hdiv
    obtain ⟨e, he⟩ := hdiv
    have hc' : c = (p:ℤ_[p])^k * (e * binv) := by
      rw [hc, he, mul_assoc]
    have hw : (1 + (p:ℤ_[p]) * c) = 1 + (p:ℤ_[p])^(k+1) * (e * binv) := by
      rw [hc', pow_succ]
      ring
    obtain ⟨v, hv⟩ := root_exists hodd k (e * binv)
    refine ⟨(v : Padic p), ?_⟩
    rw [← PadicInt.coe_pow, hv, ← hw, hkey]
