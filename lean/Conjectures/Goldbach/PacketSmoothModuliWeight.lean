import Mathlib

noncomputable section

open Nat

namespace Conjectures.Goldbach.PacketSmoothModuliWeight_aux

def fw (q : ℕ) : ℝ := ((q:ℝ)^((1:ℝ)/16)) / ((Nat.totient q : ℝ))

def rr (p : ℕ) : ℝ := ((p:ℝ)^((15:ℝ)/16))⁻¹

lemma totient_cast_pos {q : ℕ} (hq : 0 < q) : (0:ℝ) < ((Nat.totient q : ℕ):ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr hq

lemma fw_one : fw 1 = 1 := by
  simp [fw, Nat.totient_one]

lemma rr_one : rr 1 = 1 := by
  simp [rr]

lemma fw_nonneg (q : ℕ) : 0 ≤ fw q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [fw]
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _) (totient_cast_pos hq).le

lemma fw_norm (q : ℕ) : ‖fw q‖ = fw q := by
  rw [Real.norm_eq_abs, abs_of_nonneg (fw_nonneg q)]

lemma fw_mul {m n : ℕ} (h : Nat.Coprime m n) : fw (m * n) = fw m * fw n := by
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have ht : ((Nat.totient (m*n) : ℕ):ℝ)
      = ((Nat.totient m : ℕ):ℝ) * ((Nat.totient n : ℕ):ℝ) := by
    exact_mod_cast Nat.totient_mul h
  simp only [fw, Nat.cast_mul]
  rw [Real.mul_rpow hm hn, ht]
  ring

lemma five_thirds_le_two_rpow : ((5:ℝ)/3) ≤ (2:ℝ)^((15:ℝ)/16) := by
  have hpow : ((5:ℝ)/3)^16 ≤ (2:ℝ)^15 := by norm_num
  have hstep : (((5:ℝ)/3)^16)^((1:ℝ)/16) ≤ ((2:ℝ)^15)^((1:ℝ)/16) :=
    Real.rpow_le_rpow (by positivity) hpow (by norm_num)
  have he1 : ((16:ℕ):ℝ) * ((1:ℝ)/16) = 1 := by norm_num
  have hl : (((5:ℝ)/3)^16)^((1:ℝ)/16) = (5:ℝ)/3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5/3), he1, Real.rpow_one]
  have he2 : ((15:ℕ):ℝ) * ((1:ℝ)/16) = (15:ℝ)/16 := by norm_num
  have hr : ((2:ℝ)^15)^((1:ℝ)/16) = (2:ℝ)^((15:ℝ)/16) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), he2]
  rw [hl, hr] at hstep
  exact hstep

lemma rr_le {p : ℕ} (hp : 2 ≤ p) : rr p ≤ 3/5 := by
  have h4 : ((5:ℝ)/3) ≤ (p:ℝ)^((15:ℝ)/16) :=
    le_trans five_thirds_le_two_rpow
      (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) (by norm_num))
  have h6 : rr p ≤ (1:ℝ)/((5:ℝ)/3) := by
    rw [rr, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h4
  have h7 : (1:ℝ)/((5:ℝ)/3) = 3/5 := by norm_num
  rw [h7] at h6
  exact h6

lemma rr_nonneg (p : ℕ) : 0 ≤ rr p := by
  unfold rr
  positivity

lemma rpow_pow_div (p k : ℕ) (hp : 0 < p) :
    ((p^k : ℕ):ℝ)^((1:ℝ)/16) / ((p^k:ℕ):ℝ) = (rr p)^k := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hcast : ((p^k:ℕ):ℝ) = (p:ℝ)^((k:ℕ):ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast]
  have hP : (0:ℝ) < ((p^k:ℕ):ℝ) := by exact_mod_cast pow_pos hp k
  have h1 : ((p^k:ℕ):ℝ)^((1:ℝ)/16) / ((p^k:ℕ):ℝ) = ((p^k:ℕ):ℝ)^((-((15:ℝ)/16))) := by
    rw [show (-((15:ℝ)/16)) = (1:ℝ)/16 - 1 by ring, Real.rpow_sub hP, Real.rpow_one]
  calc ((p^k:ℕ):ℝ)^((1:ℝ)/16) / ((p^k:ℕ):ℝ)
      = ((p^k:ℕ):ℝ)^((-((15:ℝ)/16))) := h1
    _ = ((p:ℝ)^((k:ℕ):ℝ))^((-((15:ℝ)/16))) := by rw [hcast]
    _ = (p:ℝ)^(((k:ℕ):ℝ) * (-((15:ℝ)/16))) := by rw [Real.rpow_mul hp0.le]
    _ = (p:ℝ)^(((-((15:ℝ)/16))) * ((k:ℕ):ℝ)) := by rw [mul_comm]
    _ = ((p:ℝ)^((-((15:ℝ)/16))))^((k:ℕ):ℝ) := by rw [Real.rpow_mul hp0.le]
    _ = ((p:ℝ)^((-((15:ℝ)/16))))^k := by rw [Real.rpow_natCast]
    _ = (((p:ℝ)^((15:ℝ)/16))⁻¹)^k := by rw [Real.rpow_neg hp0.le]
    _ = (rr p)^k := by rw [rr]

lemma fw_prime_pow_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    fw (p^k) ≤ 2 * (rr p)^k := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hpn : (0:ℝ) ≤ (p:ℝ)^m := by positivity
  have hden : ((Nat.totient (p^(m+1)) : ℕ):ℝ) ≥ ((p^(m+1) : ℕ):ℝ) / 2 := by
    rw [Nat.totient_prime_pow_succ hp m, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow]
    have hpp : (p:ℝ)^(m+1) = (p:ℝ)^m * (p:ℝ) := by ring
    rw [hpp]
    nlinarith [mul_nonneg hpn (by linarith : (0:ℝ) ≤ (p:ℝ)/2 - 1)]
  have hnum : (0:ℝ) ≤ ((p^(m+1) : ℕ):ℝ)^((1:ℝ)/16) := by positivity
  have hc : (0:ℝ) < ((p^(m+1) : ℕ):ℝ) / 2 := by
    have hpos : (0:ℝ) < ((p^(m+1) : ℕ):ℝ) := by exact_mod_cast pow_pos hp.pos _
    linarith
  have hstep : fw (p^(m+1)) ≤ ((p^(m+1) : ℕ):ℝ)^((1:ℝ)/16) / (((p^(m+1) : ℕ):ℝ) / 2) := by
    unfold fw
    exact div_le_div_of_nonneg_left hnum hc hden
  calc fw (p^(m+1)) ≤ ((p^(m+1) : ℕ):ℝ)^((1:ℝ)/16) / (((p^(m+1) : ℕ):ℝ) / 2) := hstep
    _ = 2 * (((p^(m+1) : ℕ):ℝ)^((1:ℝ)/16) / ((p^(m+1) : ℕ):ℝ)) := by ring
    _ = 2 * (rr p)^(m+1) := by rw [rpow_pow_div p (m+1) hp.pos]

lemma fw_prime_pow_zero (p : ℕ) : fw (p^0) = 1 := by
  rw [pow_zero]
  exact fw_one

lemma summable_fw_prime_pow {p : ℕ} (hp : p.Prime) : Summable (fun n : ℕ => fw (p^n)) := by
  have hr : 0 ≤ rr p := rr_nonneg p
  have hr1 : rr p < 1 := lt_of_le_of_lt (rr_le hp.two_le) (by norm_num)
  have hgeo : Summable (fun n : ℕ => (2:ℝ) * (rr p)^n) :=
    Summable.mul_left 2 (summable_geometric_of_lt_one hr hr1)
  refine Summable.of_nonneg_of_le (fun n => fw_nonneg _) ?_ hgeo
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [fw_prime_pow_zero p, pow_zero]
    norm_num
  · exact fw_prime_pow_le hp hn

lemma tsum_fw_prime_pow_le {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, fw (p^n)) ≤ Real.exp (5 * rr p) := by
  have hr : 0 ≤ rr p := rr_nonneg p
  have hr1 : rr p < 1 := lt_of_le_of_lt (rr_le hp.two_le) (by norm_num)
  have hnorm : ‖(rr p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
    exact hr1
  have hgeo : Summable (fun n : ℕ => (rr p : ℝ)^n) := summable_geometric_of_lt_one hr hr1
  have hshift : Summable (fun n : ℕ => (rr p : ℝ)^(n+1)) :=
    hgeo.comp_injective (fun a b hab => by omega)
  have hshift2 : Summable (fun n : ℕ => (2:ℝ) * (rr p)^(n+1)) := Summable.mul_left 2 hshift
  have hle : ∀ n : ℕ, fw (p^(n+1)) ≤ (2:ℝ) * (rr p)^(n+1) :=
    fun n => fw_prime_pow_le hp (by omega)
  have hsum1 : Summable (fun n : ℕ => fw (p^(n+1))) :=
    Summable.of_nonneg_of_le (fun n => fw_nonneg _) hle hshift2
  have htsum : (∑' n : ℕ, fw (p^(n+1))) ≤ ∑' n : ℕ, (2:ℝ) * (rr p)^(n+1) :=
    Summable.tsum_le_tsum hle hsum1 hshift2
  have hval : (∑' n : ℕ, (2:ℝ) * (rr p)^(n+1)) = 2 * ((rr p) * (1 - rr p)⁻¹) := by
    rw [tsum_mul_left]
    have h2 : (fun n : ℕ => (rr p)^(n+1)) = fun n : ℕ => (rr p) * (rr p)^n := by
      funext n; rw [pow_succ]; ring
    rw [h2, tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
  have hinv : (1 - rr p)⁻¹ ≤ 5/2 := by
    have hpos : (0:ℝ) < 1 - rr p := by linarith [rr_le hp.two_le]
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith [rr_le hp.two_le]
  have hfive : (2:ℝ) * ((rr p) * (1 - rr p)⁻¹) ≤ 5 * rr p := by
    have h := mul_le_mul_of_nonneg_left hinv (by linarith : (0:ℝ) ≤ 2 * rr p)
    linarith
  have hsplit : (∑' n : ℕ, fw (p^n)) = fw (p^0) + ∑' n : ℕ, fw (p^(n+1)) :=
    (summable_fw_prime_pow hp).tsum_eq_zero_add
  have hexp : (5:ℝ) * rr p + 1 ≤ Real.exp (5 * rr p) := Real.add_one_le_exp _
  rw [hsplit, fw_prime_pow_zero p]
  linarith

lemma smooth_summable (N : ℕ) : Summable (fun m : Nat.smoothNumbers N => fw (m:ℕ)) := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (R := ℝ)
    (f := fw) fw_one fw_mul
    (fun {p} hp => by simpa only [fw_norm] using summable_fw_prime_pow hp) N).1
  exact Summable.of_norm h

lemma smooth_tsum_le (N : ℕ) :
    (∑' m : Nat.smoothNumbers N, fw (m:ℕ)) ≤ Real.exp (5 * ∑ p ∈ N.primesBelow, rr p) := by
  obtain ⟨hsum, hHas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (R := ℝ) (f := fw)
      fw_one fw_mul
      (fun {p} hp => by simpa only [fw_norm] using summable_fw_prime_pow hp) N
  rw [hHas.tsum_eq]
  refine (Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (fun n => fw_nonneg _))
    (fun i hi => tsum_fw_prime_pow_le (Nat.mem_primesBelow.mp hi).2)).trans ?_
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr (by rw [Finset.mul_sum])

lemma finset_le_tsum (S : Finset ℕ) (Nn : ℕ) (hsub : ∀ q ∈ S, q ∈ Nat.smoothNumbers Nn) :
    (∑ q ∈ S, fw q) ≤ ∑' m : Nat.smoothNumbers Nn, fw (m:ℕ) := by
  classical
  let g : {q // q ∈ S} → Nat.smoothNumbers Nn := fun q => ⟨q.1, hsub q.1 q.2⟩
  have hginj : Function.Injective g := by
    intro a b hab
    have h2 : (a : ℕ) = (b : ℕ) := congrArg (fun z : Nat.smoothNumbers Nn => (z : ℕ)) hab
    exact Subtype.ext h2
  let e : {q // q ∈ S} ↪ Nat.smoothNumbers Nn := ⟨g, hginj⟩
  have hval : ∀ x ∈ S.attach, ((e x : Nat.smoothNumbers Nn) : ℕ) = (x : ℕ) := by
    intro x _
    rfl
  have hsum : (∑ z ∈ S.attach.map e, fw (z:ℕ)) = ∑ q ∈ S, fw q := by
    rw [Finset.sum_map]
    refine Eq.trans (Finset.sum_congr rfl (fun x hx => ?_)) (Finset.sum_attach S fw)
    rw [hval x hx]
  rw [← hsum]
  exact Summable.sum_le_tsum _ (fun i _ => fw_nonneg i.1) (smooth_summable Nn)

lemma integral_pow_neg (N : ℕ) :
    (∫ x in ((1:ℕ):ℝ)..((N:ℕ):ℝ), x ^ (-((15:ℝ)/16)))
      = 16 * (((N:ℕ):ℝ)^((1:ℝ)/16) - 1) := by
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -((15:ℝ)/16)))]
  have h1 : (((1:ℕ):ℝ)) = 1 := Nat.cast_one
  rw [h1, Real.one_rpow]
  have h : (-((15:ℝ)/16)) + 1 = (1:ℝ)/16 := by ring
  rw [h]
  ring

lemma sum_rr_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ Finset.Icc 1 N, rr m) ≤ 16 * (((N:ℕ):ℝ)^((1:ℝ)/16)) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-((15:ℝ)/16)))
      (Set.Icc ((1:ℕ):ℝ) ((N:ℕ):ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -((15:ℝ)/16))
      (by norm_num)).mono ?_
    intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1
  have hIco := AntitoneOn.sum_le_integral_Ico
    (f := fun t : ℝ => t ^ (-((15:ℝ)/16))) (a := 1) (b := N) hN hanti
  rw [integral_pow_neg] at hIco
  have hrr : ∀ i : ℕ, rr (i+1) = (((↑(i+1) : ℕ):ℝ)) ^ (-((15:ℝ)/16)) := by
    intro i
    rw [rr, ← Real.rpow_neg (Nat.cast_nonneg (i+1))]
  have hset : Finset.Icc 2 N = (Finset.Ico 1 N).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_Ico, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨m - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have hsum2 : (∑ m ∈ Finset.Icc 2 N, rr m) = ∑ i ∈ Finset.Ico 1 N, rr (i+1) := by
    rw [hset, Finset.sum_map]
    rfl
  have hset2 : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.eq_or_lt_of_le h.1 with rfl | hlt
      · left; rfl
      · right; exact ⟨by omega, h.2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_refl 1, hN⟩
      · exact ⟨by omega, h2⟩
  have hmem1 : (1:ℕ) ∉ Finset.Icc 2 N := by simp
  have hsplit : (∑ m ∈ Finset.Icc 1 N, rr m) = rr 1 + ∑ m ∈ Finset.Icc 2 N, rr m := by
    rw [hset2, Finset.sum_insert hmem1]
  have hcong : (∑ i ∈ Finset.Ico 1 N, rr (i+1))
      = ∑ i ∈ Finset.Ico 1 N, (((↑(i+1) : ℕ):ℝ)) ^ (-((15:ℝ)/16)) :=
    Finset.sum_congr rfl (fun i _ => hrr i)
  rw [hsplit, hsum2, hcong, rr_one]
  linarith

lemma primesBelow_sum_le (u : ℕ) :
    (∑ p ∈ ((1+u)^8+1).primesBelow, rr p) ≤ 32 * Real.sqrt ((u:ℝ)+1) := by
  have h1 : (∑ p ∈ ((1+u)^8+1).primesBelow, rr p)
      ≤ ∑ m ∈ Finset.Icc 1 ((1+u)^8+1), rr m := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpm := Nat.mem_primesBelow.mp hp
      have hp2 : 2 ≤ p := hpm.2.two_le
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ _
      exact rr_nonneg i
  have h2 : (∑ m ∈ Finset.Icc 1 ((1+u)^8+1), rr m)
      ≤ 16 * ((((1+u)^8+1:ℕ):ℝ)^((1:ℝ)/16)) := sum_rr_le _ (by omega)
  have hpos : (1:ℝ) ≤ ((1+u:ℕ):ℝ) := by
    have : (1:ℕ) ≤ 1+u := by omega
    exact_mod_cast this
  have hA : (1:ℝ) ≤ ((1+u:ℕ):ℝ)^8 := by
    calc (1:ℝ) = 1^8 := by norm_num
      _ ≤ ((1+u:ℕ):ℝ)^8 := pow_le_pow_left₀ (by norm_num) hpos 8
  have hcast : ((((1+u)^8+1:ℕ):ℝ)) = ((1+u:ℕ):ℝ)^8 + 1 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  have hle : ((((1+u)^8+1:ℕ):ℝ)) ≤ 2 * ((1+u:ℕ):ℝ)^8 := by
    rw [hcast]; linarith
  have hrw : ((((1+u)^8+1:ℕ):ℝ))^((1:ℝ)/16) ≤ (2 * ((1+u:ℕ):ℝ)^8)^((1:ℝ)/16) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by norm_num)
  have hmul : (2 * ((1+u:ℕ):ℝ)^8)^((1:ℝ)/16)
      = (2:ℝ)^((1:ℝ)/16) * (((1+u:ℕ):ℝ)^8)^((1:ℝ)/16) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hexp : (((1+u:ℕ):ℝ)^8)^((1:ℝ)/16) = Real.sqrt ((1+u:ℕ):ℝ) := by
    have he : ((8:ℕ):ℝ) * ((1:ℝ)/16) = (1:ℝ)/2 := by norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), he, ← Real.sqrt_eq_rpow]
  have h2le : (2:ℝ)^((1:ℝ)/16) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (1:ℝ)/16 ≤ 1)
    rwa [Real.rpow_one] at h
  have hcast2 : ((1+u:ℕ):ℝ) = (u:ℝ)+1 := by push_cast; ring
  have h3 : ((((1+u)^8+1:ℕ):ℝ))^((1:ℝ)/16) ≤ 2 * Real.sqrt ((u:ℝ)+1) := by
    calc ((((1+u)^8+1:ℕ):ℝ))^((1:ℝ)/16) ≤ (2 * ((1+u:ℕ):ℝ)^8)^((1:ℝ)/16) := hrw
      _ = (2:ℝ)^((1:ℝ)/16) * Real.sqrt ((1+u:ℕ):ℝ) := by rw [hmul, hexp]
      _ = (2:ℝ)^((1:ℝ)/16) * Real.sqrt ((u:ℝ)+1) := by rw [hcast2]
      _ ≤ 2 * Real.sqrt ((u:ℝ)+1) :=
          mul_le_mul_of_nonneg_right h2le (Real.sqrt_nonneg _)
  linarith

lemma tail_le (Qn u : ℕ) (hQu : 2^u ≤ Qn) (hu : 300000000 ≤ u) :
    (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * Real.exp (160 * Real.sqrt ((u:ℝ)+1))
      ≤ Real.exp (-((u:ℝ) * Real.log 2 / 32)) := by
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (Real.exp (1/2))^2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp (1/2) < 2 := by nlinarith [Real.exp_pos (1/2)]
    exact (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)).mpr h3.le
  have hcast : (((2^u : ℕ):ℝ)) = (2:ℝ)^((u:ℕ):ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast, Nat.cast_ofNat]
  have hle : ((2:ℝ)^((u:ℕ):ℝ))^((1:ℝ)/16) ≤ ((Qn:ℕ):ℝ)^((1:ℝ)/16) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [← hcast]
    exact_mod_cast hQu
  have hpos1 : (0:ℝ) < ((2:ℝ)^((u:ℕ):ℝ))^((1:ℝ)/16) := by positivity
  have hinv : (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ ≤ (((2:ℝ)^((u:ℕ):ℝ))^((1:ℝ)/16))⁻¹ := by
    have h := one_div_le_one_div_of_le hpos1 hle
    simpa only [inv_eq_one_div] using h
  have hrw2 : ((2:ℝ)^((u:ℕ):ℝ))^((1:ℝ)/16) = Real.exp (((u:ℝ)/16) * Real.log 2) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hQinv : (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ ≤ Real.exp (-(((u:ℝ)/16) * Real.log 2)) := by
    rw [hrw2] at hinv
    rw [Real.exp_neg]
    exact hinv
  have hA : (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * Real.exp (160 * Real.sqrt ((u:ℝ)+1))
      ≤ Real.exp (-(((u:ℝ)/16) * Real.log 2)) * Real.exp (160 * Real.sqrt ((u:ℝ)+1)) :=
    mul_le_mul_of_nonneg_right hQinv (by positivity)
  have hC : Real.exp (-(((u:ℝ)/16) * Real.log 2)) * Real.exp (160 * Real.sqrt ((u:ℝ)+1))
      = Real.exp (160 * Real.sqrt ((u:ℝ)+1) - ((u:ℝ)/16) * Real.log 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hu3 : (300000000:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  have hsq : ((u:ℝ)+1) ≤ ((u:ℝ)/10240)^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (u:ℝ))
      (by linarith : (0:ℝ) ≤ (u:ℝ) - 104857601)]
  have hsqrt : Real.sqrt ((u:ℝ)+1) ≤ (u:ℝ)/10240 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩
  have hdom : 160 * Real.sqrt ((u:ℝ)+1) ≤ ((u:ℝ)/16) * Real.log 2 / 2 := by
    have h4 : 160 * Real.sqrt ((u:ℝ)+1) ≤ 160 * ((u:ℝ)/10240) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    have h6 : (u:ℝ)/64 ≤ ((u:ℝ)/16) * Real.log 2 / 2 := by
      have h := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ) ≤ (u:ℝ)/16)
      linarith
    linarith
  calc (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * Real.exp (160 * Real.sqrt ((u:ℝ)+1))
      ≤ Real.exp (-(((u:ℝ)/16) * Real.log 2)) * Real.exp (160 * Real.sqrt ((u:ℝ)+1)) := hA
    _ = Real.exp (160 * Real.sqrt ((u:ℝ)+1) - ((u:ℝ)/16) * Real.log 2) := hC
    _ ≤ Real.exp (-((u:ℝ) * Real.log 2 / 32)) := Real.exp_le_exp.mpr (by linarith)

lemma term_le (Qn q : ℕ) (hQ : 0 < Qn) (hq : 1 ≤ q) :
    min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ)
      ≤ (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * fw q := by
  have hphi : (0:ℝ) < ((Nat.totient q:ℕ):ℝ) := totient_cast_pos hq
  have hQn0 : (0:ℝ) < ((Qn:ℕ):ℝ) := by exact_mod_cast hQ
  have hx : (0:ℝ) ≤ (q:ℝ)/((Qn:ℕ):ℝ) := div_nonneg (Nat.cast_nonneg q) hQn0.le
  have hmin : min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ)) ≤ ((q:ℝ)/((Qn:ℕ):ℝ))^((1:ℝ)/16) := by
    rcases lt_or_ge ((q:ℝ)/((Qn:ℕ):ℝ)) 1 with h | h
    · rw [min_eq_right h.le]
      exact Real.self_le_rpow_of_le_one hx h.le (by norm_num)
    · rw [min_eq_left h]
      exact Real.one_le_rpow h (by norm_num)
  have hrpow : ((q:ℝ)/((Qn:ℕ):ℝ))^((1:ℝ)/16)
      = (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * (q:ℝ)^((1:ℝ)/16) := by
    rw [Real.div_rpow (Nat.cast_nonneg q) hQn0.le, div_eq_mul_inv]
    ring
  calc min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ)
      ≤ ((q:ℝ)/((Qn:ℕ):ℝ))^((1:ℝ)/16)/((Nat.totient q:ℕ):ℝ) :=
        div_le_div_of_nonneg_right hmin hphi.le
    _ = (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * (q:ℝ)^((1:ℝ)/16) / ((Nat.totient q:ℕ):ℝ) := by
        rw [hrpow]
    _ = (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * fw q := by rw [fw]; ring

lemma smooth_mem (u q : ℕ) (hq : 1 ≤ q) (hsm : ∀ p ∈ q.primeFactors, p ≤ (1+u)^8) :
    q ∈ Nat.smoothNumbers ((1+u)^8+1) := by
  refine Nat.mem_smoothNumbers_iff_primeFactors_subset.mpr ⟨by omega, ?_⟩
  intro p hp
  have hle := hsm p hp
  exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hp⟩

lemma exp_neg_log2 (u : ℕ) :
    Real.exp (-((u:ℝ) * Real.log 2 / 32)) = ((2:ℝ)^(-((1:ℝ)/32)))^u := by
  have hb : Real.exp (-(Real.log 2 / 32)) = (2:ℝ)^(-((1:ℝ)/32)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have h1 : Real.exp (-((u:ℝ) * Real.log 2 / 32)) = (Real.exp (-(Real.log 2/32)))^u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h1, hb]

lemma sum_bound (Qn u : ℕ) (hQpos : 0 < Qn) (hQu : 2^u ≤ Qn) (hu : 300000000 ≤ u)
    (S : Finset ℕ)
    (hsub : ∀ q ∈ S, 1 ≤ q ∧ (∀ p ∈ q.primeFactors, p ≤ (1+u)^8)) :
    (∑ q ∈ S, min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ))
      ≤ ((2:ℝ)^(-((1:ℝ)/32)))^u := by
  have hsum1 : ∀ q ∈ S, min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ)
      ≤ (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * fw q :=
    fun q hq => term_le Qn q hQpos (hsub q hq).1
  have hmem : ∀ q ∈ S, q ∈ Nat.smoothNumbers ((1+u)^8+1) :=
    fun q hq => smooth_mem u q (hsub q hq).1 (hsub q hq).2
  have hA : (∑ q ∈ S, fw q) ≤ ∑' m : Nat.smoothNumbers ((1+u)^8+1), fw (m:ℕ) :=
    finset_le_tsum S ((1+u)^8+1) hmem
  have hB : (∑' m : Nat.smoothNumbers ((1+u)^8+1), fw (m:ℕ))
      ≤ Real.exp (5 * ∑ p ∈ ((1+u)^8+1).primesBelow, rr p) :=
    smooth_tsum_le ((1+u)^8+1)
  have hC : Real.exp (5 * ∑ p ∈ ((1+u)^8+1).primesBelow, rr p)
      ≤ Real.exp (160 * Real.sqrt ((u:ℝ)+1)) :=
    Real.exp_le_exp.mpr (by have h := primesBelow_sum_le u; linarith)
  have hD : (∑ q ∈ S, fw q) ≤ Real.exp (160 * Real.sqrt ((u:ℝ)+1)) :=
    le_trans hA (le_trans hB hC)
  have hE : (∑ q ∈ S, min (1:ℝ) ((q:ℝ)/((Qn:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ))
      ≤ (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ * (∑ q ∈ S, fw q) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hsum1
  have hF : (0:ℝ) ≤ (((Qn:ℕ):ℝ)^((1:ℝ)/16))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact (le_trans hE (le_trans (mul_le_mul_of_nonneg_left hD hF)
    (tail_le Qn u hQu hu))).trans (le_of_eq (exp_neg_log2 u))

end Conjectures.Goldbach.PacketSmoothModuliWeight_aux

open Conjectures.Goldbach.PacketSmoothModuliWeight_aux

theorem Conjectures.Goldbach.PacketSmoothModuliWeight :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε := by
  dsimp only
  intro ε hε
  have ht1 : (2:ℝ)^(-((1:ℝ)/32)) < 1 := by
    have hb : (1:ℝ) < (2:ℝ)^((1:ℝ)/32) := by
      have h := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
        (by norm_num : (0:ℝ) < (1:ℝ)/32)
      rwa [Real.one_rpow] at h
    have he : (2:ℝ)^(-((1:ℝ)/32)) = (1:ℝ)/((2:ℝ)^((1:ℝ)/32)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), inv_eq_one_div]
    rw [he, div_lt_iff₀ (by positivity)]
    linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε ht1
  refine ⟨2^(2^(max M 300000000)), ?_⟩
  intro n hn
  have hL : 2^(max M 300000000) ≤ Nat.log 2 (n+2) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have h : 2^(2^(max M 300000000)) ≤ n := hn
    omega
  have hQ1 : 2^(max M 300000000) ≤ (Nat.log 2 (n+2))^2 := by
    have h2 : (2^(max M 300000000))^2 ≤ (Nat.log 2 (n+2))^2 := by
      rw [pow_two, pow_two]
      exact Nat.mul_self_le_mul_self hL
    have hkk : 2^(max M 300000000) ≤ (2^(max M 300000000))^2 := by
      rw [pow_two]
      exact Nat.le_mul_self _
    exact le_trans hkk h2
  have hQpos : 0 < (Nat.log 2 (n+2))^2 := lt_of_lt_of_le (by positivity) hQ1
  have hU : max M 300000000 ≤ Nat.log 2 ((Nat.log 2 (n+2))^2) :=
    Nat.le_log_of_pow_le (by norm_num) hQ1
  have hQu : 2^(Nat.log 2 ((Nat.log 2 (n+2))^2)) ≤ (Nat.log 2 (n+2))^2 :=
    Nat.pow_log_le_self 2 (ne_of_gt hQpos)
  have hu3 : 300000000 ≤ Nat.log 2 ((Nat.log 2 (n+2))^2) :=
    le_trans (le_max_right M 300000000) hU
  have huM : M ≤ Nat.log 2 ((Nat.log 2 (n+2))^2) :=
    le_trans (le_max_left M 300000000) hU
  refine (sum_bound ((Nat.log 2 (n+2))^2) (Nat.log 2 ((Nat.log 2 (n+2))^2))
    hQpos hQu hu3 _ ?_).trans ?_
  · intro q hq
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1, (Finset.mem_filter.mp hq).2⟩
  · exact (pow_le_pow_of_le_one (Real.rpow_nonneg (by norm_num) _) ht1.le huM).trans hM.le
