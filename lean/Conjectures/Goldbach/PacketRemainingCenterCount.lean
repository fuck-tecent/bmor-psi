import Mathlib

/-!
# Resonant numerators for the remaining Goldbach packet moduli

For the dyadic cosine average, the weighted number of resonant primitive
numerators tends to zero, uniformly over every denominator in the registered
range. Smooth denominators and denominators with a large prime factor of short
binary period each have negligible total weight. On all remaining denominators,
Fourier orthogonality bounds the second moment by the number of collisions
between separated binary frequencies. The Euler totient second-moment estimate
then bounds their combined contribution.

The component proofs below retain their original attribution. The long-factor
argument is related to the reference proof in goldbach-proofs PR #3669.
-/

/-! The finite character orthogonality and second moment below are reproduced from
Conjectures.Goldbach.PacketBinaryOrbitSecondMoment, goldbach-proofs,
commit 99020bf57fb80332fceb70bec7f5bb7b49d3dc3d, Apache-2.0. -/

open scoped BigOperators

namespace Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

noncomputable def ph (q a k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)

private lemma ph_unit (q a k : ℕ) : ‖ph q a k‖ = 1 := by
  unfold ph
  exact Complex.norm_exp_ofReal_mul_I _

private theorem orth (q u v : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ph q a u * (starRingEnd ℂ) (ph q a v)) =
      if u % q = v % q then (q : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (a k : ℕ) : ph q a k = (ζ ^ k) ^ a := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have term (a : ℕ) : ph q a u * (starRingEnd ℂ) (ph q a v) =
      (ζ ^ u / ζ ^ v) ^ a := by
    rw [← Complex.inv_eq_conj (ph_unit q a v), phase, phase, div_pow, div_eq_mul_inv]
  simp_rw [term]
  have hpowiff (x y : ℕ) : ζ ^ x = ζ ^ y ↔ x % q = y % q := by
    have hfin := hζ.isOfFinOrder hq.ne'
    rw [hfin.pow_inj_mod, hζ.eq_orderOf]
  by_cases huv : u % q = v % q
  · have hbase : ζ ^ u / ζ ^ v = 1 :=
      (div_eq_one_iff_eq (pow_ne_zero v hζ0)).2 ((hpowiff u v).2 huv)
    rw [ite_eq_left huv, hbase]
    simp
  · rw [ite_eq_right huv, geom_sum_eq]
    · have hpow (x : ℕ) : (ζ ^ x) ^ q = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [div_pow, hpow]
    · intro hbase
      apply huv
      apply (hpowiff u v).1
      exact (div_eq_one_iff_eq (pow_ne_zero v hζ0)).1 hbase

theorem second_moment (q m : ℕ) (k : ℕ → ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, ph q a (k j)‖ ^ 2) =
      (q : ℝ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℝ)) := by
  have expand (a : ℕ) :
      (∑ j ∈ Finset.range m, ph q a (k j)) *
          (starRingEnd ℂ) (∑ j ∈ Finset.range m, ph q a (k j)) =
        ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  have hswap :
      (∑ a ∈ Finset.range q, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l))) =
      ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, ∑ a ∈ Finset.range q,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => orth q (k j) (k l) hq))]
  rw [← Finset.sum_product']
  calc
    (∑ ij ∈ Finset.range m ×ˢ Finset.range m,
        if k ij.1 % q = k ij.2 % q then (q : ℂ) else 0) =
        (q : ℂ) * ∑ ij ∈ Finset.range m ×ˢ Finset.range m,
          if k ij.1 % q = k ij.2 % q then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ij _
            split_ifs <;> ring
    _ = (q : ℂ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℂ)) := by
      rw [Finset.sum_boole]

end Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

namespace GB4Moment
open Finset Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

noncomputable def K (L : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)

private theorem collision_count (q L m : ℕ) (hm : 0 < m)
    (sep : ∀ i j : ℕ, i < j → j < L →
      (2:ℕ)^(i+1)%q = 2^(j+1)%q → m ≤ j-i) :
    (((range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)).card) ≤ L * (L/m+1) := by
  let P := (range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)
  change P.card ≤ _
  have data {i j : ℕ} (h : (i,j) ∈ P) :
      i < L ∧ j < L ∧ (2:ℕ)^(i+1)%q = 2^(j+1)%q := by
    simpa only [P, mem_filter, mem_product, mem_range, and_assoc] using h
  have inj : Set.InjOn (fun ij : ℕ × ℕ => (ij.1,ij.2/m)) (P : Set (ℕ × ℕ)) := by
    rintro ⟨i,j⟩ hx ⟨i',k⟩ hy heq
    change (i,j/m) = (i',k/m) at heq
    obtain ⟨rfl,hjk⟩ := Prod.mk.inj heq
    have dx := data hx
    have dy := data hy
    have ee := dx.2.2.symm.trans dy.2.2
    have hj := Nat.mod_add_div j m
    have hk := Nat.mod_add_div k m
    rw [hjk] at hj
    have hj' := Nat.mod_lt j hm
    have hk' := Nat.mod_lt k hm
    have h : j = k := by
      rcases lt_trichotomy j k with hl | he | hl
      · have := sep j k hl dy.2.1 ee
        omega
      · exact he
      · have := sep k j hl dx.2.1 ee.symm
        omega
    cases h
    rfl
  calc
    P.card = (P.image (fun ij : ℕ × ℕ => (ij.1,ij.2/m))).card :=
      (card_image_of_injOn inj).symm
    _ ≤ (range L ×ˢ range (L/m+1)).card := by
      apply card_le_card
      intro y hy
      obtain ⟨⟨i,j⟩,h,rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_range.mpr (data h).1,
        mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (data h).2.1.le))⟩
    _ = _ := by simp

theorem centers_le (q L m : ℕ) (hq : 1 < q) (hm : 0 < m) (hmL : m ≤ L)
    (sep : ∀ i j : ℕ, i < j → j < L →
      (2:ℕ)^(i+1)%q = 2^(j+1)%q → m ≤ j-i) :
    (((range (q+1)).filter (fun a : ℕ => a.Coprime q ∧ (1:ℝ)/3 < K L ((a:ℝ)/q))).card : ℝ) ≤
      18*(q:ℝ)/m := by
  classical
  let H := (range (q+1)).filter (fun a : ℕ => a.Coprime q ∧ (1:ℝ)/3 < K L ((a:ℝ)/q))
  let F := fun a : ℕ => ∑ j ∈ range L, ph q a ((2:ℕ)^(j+1))
  have hL : (0:ℝ) < L := by exact_mod_cast hm.trans_le hmL
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hsub : H ⊆ range q := by
    intro a ha
    obtain ⟨har,hcop,_⟩ := mem_filter.mp ha
    have hle := mem_range.mp har
    have hne : a ≠ q := by
      rintro rfl
      have : a = 1 := by simpa [Nat.Coprime] using hcop
      omega
    exact mem_range.mpr (by omega)
  have reF (a : ℕ) : (F a).re = K L ((a:ℝ)/q)*L := by
    unfold K
    rw [div_mul_cancel₀ _ hL.ne']
    dsimp only [F]
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro j _
    unfold ph
    rw [Complex.exp_ofReal_mul_I_re]
    push_cast
    congr 1
    ring
  have energy : (H.card:ℝ)*((L:ℝ)/3)^2 ≤ ∑ a ∈ range q, ‖F a‖^2 := by
    calc
      _ = ∑ _a ∈ H, ((L:ℝ)/3)^2 := by simp
      _ ≤ ∑ a ∈ H, ‖F a‖^2 := by
        apply sum_le_sum
        intro a ha
        have h := (mem_filter.mp ha).2.2
        have hs := Complex.re_le_norm (F a)
        rw [reF] at hs
        have hh : (L:ℝ)/3 ≤ ‖F a‖ := by nlinarith [mul_le_mul_of_nonneg_right h.le hL.le]
        exact pow_le_pow_left₀ (by positivity) hh 2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hcard := collision_count q L m hm sep
  have he := second_moment q L (fun j => (2:ℕ)^(j+1)) (by omega)
  change (∑ a ∈ range q, ‖F a‖^2) = _ at he
  rw [he] at energy
  have hc : ((((range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)).card):ℝ) ≤
      (L:ℝ)*((L/m:ℕ)+1) := by exact_mod_cast hcard
  have div_le : (↑(L/m):ℝ)*(m:ℝ) ≤ L := by exact_mod_cast Nat.div_mul_le_self L m
  have hmlr : (m:ℝ) ≤ L := by exact_mod_cast hmL
  have hblock : ((↑(L/m):ℝ)+1)*m ≤ 2*L := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hblock (show 0 ≤ (q:ℝ)*L by positivity)
  have hc2 := energy.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  change (H.card : ℝ) ≤ _
  apply (le_div_iff₀ hmr).mpr
  apply (mul_le_mul_iff_left₀ (show 0 < ((L:ℝ)/3)^2 by positivity)).mp
  nlinarith [mul_le_mul_of_nonneg_right hc2 hmr.le]

end GB4Moment

/-! The Rankin estimate and the divisor and totient sums adapt the Apache-2.0
Goldbach proofs from PRs #3341 and #2327 and the previously submitted short-order
center count at revision 33d9880d26eca803a13c4e6371e6960037e9ad73. Here the smooth cutoff is the twelfth power of the binary-log scale,
and a single large prime factor, rather than the whole modulus, has short period. -/

namespace GB4Bad
open Finset
open scoped Classical

def grid (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def u (n : ℕ) : ℕ := 1 + Nat.log 2 (grid n)
def smooth (n q : ℕ) : Prop := ∀ p ∈ q.primeFactors, p ≤ (u n)^12
def shortLarge (n q : ℕ) : Prop := ∃ p ∈ q.primeFactors, (u n)^12 < p ∧
  ∃ j ∈ Finset.Icc 1 ((u n)^4), p ∣ 2^j-1
noncomputable def weight (n q : ℕ) : ℝ := min 1 ((q:ℝ)/(grid n:ℝ))/(q.totient:ℝ)

namespace GoldbachSmoothModuli

private theorem rankin_min (x : ℝ) (hx : 0 < x) : min 1 x ≤ x^(1/32 : ℝ) := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num : (1/32:ℝ) ≤ 1)
  · rw [min_eq_left (le_of_not_ge hx1)]
    exact Real.one_le_rpow (le_of_not_ge hx1) (by norm_num)

private theorem reciprocal_totient (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / q := by
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _d ∈ q.divisors, q.totient := sum_le_sum fun d hd =>
        Nat.le_of_dvd (Nat.totient_pos.mpr hq) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hq) (by exact_mod_cast hq)).2
  simpa using (show (q : ℝ) ≤ (q.divisors.card : ℝ) * q.totient by exact_mod_cast hcount)

/-- Expanding the divisor count sends each factor pair into the square of the smooth set. -/
theorem smooth_convolution_bound (Q Y : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y),
      min (1 : ℝ) ((q : ℝ) / Q) / (q.totient : ℝ)) ≤
    (Q : ℝ)^(-(1/32:ℝ)) *
      (∑ a ∈ (Icc 1 (Q^2)).filter (fun a => ∀ p ∈ a.primeFactors, p ≤ Y),
        (a:ℝ)^((1/32:ℝ)-1))^2 := by
  classical
  let S := (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y)
  let w (a : ℕ) := (a:ℝ)^((1/32:ℝ)-1)
  let F (ab : ℕ × ℕ) := w ab.1 * w ab.2
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have w_nonneg (a : ℕ) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsingle (q : ℕ) (hq : q ∈ S) :
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
      (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hsum : (∑ ab ∈ q.divisorsAntidiagonal, F ab) = (q.divisors.card : ℝ) * w q := by
      calc
        _ = ∑ _ab ∈ q.divisorsAntidiagonal, w q := by
          apply sum_congr rfl
          intro ab hab
          unfold F w
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
            ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hab).1]
        _ = _ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => w q)]
          simp
    rw [hsum]
    calc
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
          ((q : ℝ)/Q)^(1/32:ℝ) * (1/(q.totient : ℝ)) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_right (rankin_min _ (div_pos hqr hQR)) (Nat.cast_nonneg _)
      _ ≤ ((q : ℝ)/Q)^(1/32:ℝ) * ((q.divisors.card : ℝ)/q) :=
        mul_le_mul_of_nonneg_left (reciprocal_totient q hq0) (Real.rpow_nonneg (div_pos hqr hQR).le _)
      _ = _ := by
        rw [Real.div_rpow hqr.le hQR.le, Real.rpow_neg hQR.le]
        simp only [w, Real.rpow_sub hqr, Real.rpow_one]
        ring
  have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint a.divisorsAntidiagonal b.divisorsAntidiagonal := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro ab ha hb
    exact hab ((Nat.mem_divisorsAntidiagonal.mp ha).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hb).1)
  have hsub : S.biUnion Nat.divisorsAntidiagonal ⊆ S ×ˢ S := by
    intro ab hab
    obtain ⟨q, hq, habq⟩ := mem_biUnion.mp hab
    obtain ⟨hqI,hqS⟩ := mem_filter.mp hq
    obtain ⟨hqpos,hqle⟩ := mem_Icc.mp hqI
    have hd (d : ℕ) (hdq : d ∈ q.divisors) : d ∈ S := by
      have hdiv := Nat.dvd_of_mem_divisors hdq
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdq, ?_⟩, ?_⟩
      · exact (Nat.le_of_dvd hqpos hdiv).trans hqle
      · exact fun p hp => hqS p (Nat.primeFactors_mono hdiv (by omega) hp)
    exact mem_product.mpr ⟨hd _ (Nat.fst_mem_divisors_of_mem_antidiagonal habq),
      hd _ (Nat.snd_mem_divisors_of_mem_antidiagonal habq)⟩
  change (∑ q ∈ S, _) ≤ (Q : ℝ)^(-(1/32:ℝ)) * (∑ a ∈ S, w a)^2
  calc
    _ ≤ ∑ q ∈ S, (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab :=
      sum_le_sum hsingle
    _ = (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S.biUnion Nat.divisorsAntidiagonal, F ab := by
      rw [← mul_sum, sum_biUnion hdisj]
    _ ≤ (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S ×ˢ S, F ab := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply sum_le_sum_of_subset_of_nonneg hsub
      exact fun ab _ _ => mul_nonneg (w_nonneg ab.1) (w_nonneg ab.2)
    _ = _ := by
      congr 1
      rw [Finset.sum_product, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

private noncomputable def rankinWeight : ℕ →* ℝ where
  toFun m := (m : ℝ) ^ ((1 / 32 : ℝ) - 1)
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem finite_smooth_weight_le_product (y : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ∈ Nat.smoothNumbers (y + 1)) :
    (∑ m ∈ S, (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  classical
  have hin : ∀ {p : ℕ}, p.Prime → ‖rankinWeight p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ ((1 / 32 : ℝ) - 1)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rankinWeight) hin (y + 1)).2
  change (∑ m ∈ S, rankinWeight m) ≤ _
  rw [← S.sum_subtype_of_mem (fun m => rankinWeight m) hS]
  exact sum_le_hasSum _ (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg (m : ℕ)) _) hs

theorem smooth_interval_weight_le_product (y N : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y),
        (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  apply finite_smooth_weight_le_product
  intro m hm
  obtain ⟨hrange, hfactors⟩ := Finset.mem_filter.mp hm
  have hmpos := (Finset.mem_Icc.mp hrange).1
  apply Nat.mem_smoothNumbers'.2
  intro p hp hpm
  exact Nat.lt_succ_of_le (hfactors p (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩))

private theorem factor_bound {p : ℕ} (hp : Nat.Prime p) :
    let t := (p : ℝ)^((1/32:ℝ)-1)
    0 < 1-t ∧ (1-t)⁻¹ ≤ Real.exp (4*t) := by
  let t := (p : ℝ)^((1/32:ℝ)-1)
  change 0 < 1-t ∧ _
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht2 : t*t ≤ (p:ℝ)⁻¹ := by
    dsimp [t]
    rw [← Real.rpow_add hp0, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
  have hinv : (p:ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have h34 : t ≤ 3/4 := by nlinarith
  have hpos : 0 < 1-t := by linarith
  refine ⟨hpos, le_trans ?_ (Real.add_one_le_exp (4*t))⟩
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith [mul_nonneg ht0 (show 0 ≤ 3-4*t by linarith)]

/-- Compare the logarithm of the Euler product with a weighted harmonic sum. -/
theorem eulerProduct_le (y : ℕ) (hy : 1 ≤ y) :
    (∏ p ∈ (y+1).primesBelow, (1 - (p:ℝ)^((1/32:ℝ)-1))⁻¹) ≤
      Real.exp (500 * (y:ℝ)^(1/16:ℝ)) := by
  let P := (y+1).primesBelow
  let t (p : ℕ) := (p:ℝ)^((1/32:ℝ)-1)
  have hsub : P ⊆ Icc 1 y := by
    intro p hp
    obtain ⟨hpy,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_lt_succ hpy⟩
  have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hpow : 0 ≤ (y:ℝ)^(1/32:ℝ) := Real.rpow_nonneg hy0.le _
  have hlog : 1 + Real.log (y:ℝ) ≤ 32 * (y:ℝ)^(1/32:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (1/32:ℝ))
    rw [Real.log_rpow hy0] at h
    linarith
  have hs : (∑ p ∈ P, t p) ≤ 32 * (y:ℝ)^(1/16:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, (y:ℝ)^(1/32:ℝ) * (p:ℝ)⁻¹ := by
        apply sum_le_sum
        intro p hp
        have hpy : p ≤ y := (mem_Icc.mp (hsub hp)).2
        have hp0 : (0:ℝ) < p := by exact_mod_cast (mem_Icc.mp (hsub hp)).1
        dsimp only [t]
        rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le (by exact_mod_cast hpy) (by norm_num)) (inv_nonneg.mpr hp0.le)
      _ = (y:ℝ)^(1/32:ℝ) * ∑ p ∈ P, (p:ℝ)⁻¹ := (mul_sum ..).symm
      _ ≤ (y:ℝ)^(1/32:ℝ) * ∑ p ∈ Icc 1 y, (p:ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) hpow
      _ ≤ (y:ℝ)^(1/32:ℝ) * (1+Real.log (y:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log y
      _ ≤ (y:ℝ)^(1/32:ℝ) * (32*(y:ℝ)^(1/32:ℝ)) := mul_le_mul_of_nonneg_left hlog hpow
      _ = 32 * (y:ℝ)^(1/16:ℝ) := by
        rw [show (1/16:ℝ)=1/32+1/32 by norm_num, Real.rpow_add hy0]; ring
  calc
    _ ≤ ∏ p ∈ P, Real.exp (4*t p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact inv_nonneg.mpr (factor_bound (Nat.prime_of_mem_primesBelow hp)).1.le
      · intro p hp
        exact (factor_bound (Nat.prime_of_mem_primesBelow hp)).2
    _ = Real.exp (4*∑ p ∈ P, t p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith [Real.rpow_nonneg hy0.le (1/16:ℝ)]

/-- Exponential growth of Q in its binary logarithm absorbs the three-quarter-power
growth in the exponent of the smooth Euler product. -/
theorem eventual_rankin_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
      let Y : ℕ := (1 + Nat.log 2 Q) ^ 12
      (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
        (Real.exp (500 * (Y : ℝ) ^ (1 / 16 : ℝ))) ^ 2 ≤ ε := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 128000)
  obtain ⟨b, hb⟩ := exists_nat_ge (max t (128 * (1 - Real.log ε)))
  refine ⟨2 ^ (2 ^ b), fun n hn => ?_⟩
  let L := Nat.log 2 (n + 2)
  let Q : ℕ := L ^ 2
  let k := Nat.log 2 Q
  have hLb : 2 ^ b ≤ L :=
    Nat.le_log_of_pow_le (by decide) (hn.trans (by omega))
  have hL : 1 ≤ L := (Nat.one_le_two_pow (n := b)).trans hLb
  have hQ : L ≤ Q := by dsimp [Q]; nlinarith
  have hk : b ≤ k := Nat.le_log_of_pow_le (by decide) (hLb.trans hQ)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hdyadic : (2 : ℝ) ^ k ≤ Q := by
    exact_mod_cast Nat.pow_log_le_self 2 (show Q ≠ 0 by omega)
  have hlog := Real.log_le_log (by positivity) hdyadic
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hklog : (k : ℝ) / 2 ≤ Real.log Q := by
    calc
      (k : ℝ) / 2 = (k : ℝ) * (1 / 2) := by ring
      _ ≤ (k : ℝ) * Real.log 2 := by gcongr
      _ ≤ Real.log Q := hlog
  have hrpow : ((((1 + k)^12 : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
      (1 + (k : ℝ))^(3/4:ℝ) := by
    push_cast
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  change (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
    (Real.exp (500 * ((((1 + k)^12 : ℕ) : ℝ) ^ (1 / 16 : ℝ)))) ^ 2 ≤ ε
  rw [hrpow, Real.rpow_def_of_pos hQpos, sq, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_log hε, Real.exp_le_exp]
  have hb' : (b : ℝ) ≤ k := by exact_mod_cast hk
  have hkt : t ≤ 1 + (k:ℝ) := by linarith [(le_max_left ..).trans hb]
  have hlarge := ht (1 + (k:ℝ)) hkt
  have hprod := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg (by positivity : 0 ≤ 1+(k:ℝ)) (3/4:ℝ))
  change (1+(k:ℝ))^(3/4:ℝ)*128000 ≤ (1+(k:ℝ))^(3/4:ℝ)*(1+(k:ℝ))^(1/4:ℝ) at hprod
  rw [← Real.rpow_add (by positivity), show (3/4:ℝ)+1/4=1 by norm_num, Real.rpow_one] at hprod
  linarith [(le_max_right ..).trans hb]

end GoldbachSmoothModuli

private theorem smoothDenominatorWeightRaw :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^12; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε := by
  dsimp only
  intro ε hε
  obtain ⟨N, hN⟩ := GoldbachSmoothModuli.eventual_rankin_budget ε hε
  refine ⟨N, fun n hn => ?_⟩
  let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
  let Y : ℕ := (1 + Nat.log 2 Q) ^ 12
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 1 ≤ Q := Nat.pow_pos hlog
  have hY : 1 ≤ Y := Nat.pow_pos (by omega : 0 < 1 + Nat.log 2 Q)
  have he := (GoldbachSmoothModuli.smooth_interval_weight_le_product Y (Q^2)).trans
    (GoldbachSmoothModuli.eulerProduct_le Y hY)
  refine (GoldbachSmoothModuli.smooth_convolution_bound Q Y hQ).trans (le_trans ?_ (hN n hn))
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) _)) he 2



theorem smooth_budget : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Icc 1 ((grid n)^2)).filter (smooth n), weight n q) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := smoothDenominatorWeightRaw ε hε
  refine ⟨N, fun n hn => ?_⟩
  apply le_trans _ (hN n hn)
  apply le_of_eq
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [mem_filter, smooth, u, grid]

theorem periodPrimeBudget (H Y : ℕ) (hY : 0<Y) :
    (∑ j ∈ Finset.Icc 1 H, ∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)),
      1/((p:ℝ)-1)) ≤ (H:ℝ)^2/Y := by
  have one (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
      (∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)), 1/((p:ℝ)-1)) ≤ (H:ℝ)/(Y:ℝ) := by
    let M : ℕ := 2^j-1
    let primes := M.primeFactors
    let T := primes.filter (fun p => Y<p)
    have jpos := (Finset.mem_Icc.mp hj).1
    have jle := (Finset.mem_Icc.mp hj).2
    have Mpos : 0<M := by
      have two : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) jpos
      dsimp [M]; omega
    have hc : 2^primes.card ≤ M := by
      calc
        _ = ∏ _p ∈ primes, (2:ℕ) := by simp
        _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
        _ ≤ M := Nat.le_of_dvd Mpos (Nat.prod_primeFactors_dvd M)
    have card : primes.card ≤ j := by
      by_contra! hh
      have lower := Nat.pow_le_pow_right (by decide : 0<2) (show j+1 ≤ primes.card by omega)
      rw [pow_succ] at lower
      dsimp [M] at hc
      omega
    have cr : (T.card:ℝ) ≤ (H:ℝ) := by exact_mod_cast
      ((Finset.card_le_card (Finset.filter_subset _ primes)).trans card).trans jle
    change (∑ p ∈ T, _) ≤ _
    calc
      _ ≤ ∑ _p ∈ T, 1/(Y:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi : (Y:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (T.card:ℝ)/(Y:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (H:ℝ)/(Y:ℝ) := Finset.sum_le_sum one
    _ = _ := by simp [pow_two]; ring


private theorem fractionProduct (S : Finset ℕ) (hs : ∀ p ∈ S, 2≤p) :
    (∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)) ≤ (S.card:ℝ)+1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := hs a (Finset.mem_insert_self ..)
    have old (p : ℕ) (hp : p∈S) := hs p (Finset.mem_insert_of_mem hp)
    have ha' : 0 < (a:ℝ)-1 := by
      have h : (2:ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have notMem : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have sub : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨old p hp,hmax p hp⟩
    have count := Finset.card_le_card sub
    rw [Nat.card_Ico] at count
    have cr : (S.card:ℝ)+2 ≤ (a:ℝ) := by exact_mod_cast (show S.card+2≤a by omega)
    rw [Finset.prod_insert notMem,Finset.card_insert_of_notMem notMem,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left (ih old) (div_nonneg (Nat.cast_nonneg _) ha'.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha').mpr
    linarith

theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod hs
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have id : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by
    rw [Finset.prod_div_distrib]
    have pos : 0 < ∏ p ∈ S, ((p:ℝ)-1) := Finset.prod_pos (fun p hp => by
      have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
      linarith)
    apply (div_eq_div_iff hf.ne' pos.ne').mpr
    have formula := congrArg (fun k : ℕ => (k:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul,Nat.cast_prod] at formula
    change (q:ℝ)*_ = _*(q.totient:ℝ)
    rw [mul_comm _ (q.totient:ℝ)]
    dsimp [S]
    rw [formula]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have h := hs p hp; omega),Nat.cast_one]
  rw [id]
  exact (fractionProduct S hs).trans (by exact_mod_cast (show S.card+1≤Nat.log 2 q+1 by omega))

private theorem harmonicBlock (k : ℕ) :
    (∑ m ∈ Finset.range (2^k), 1/((m:ℝ)+1)) ≤ (k:ℝ)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have block : (∑ j ∈ Finset.range (2^k), 1/(((2^k+j:ℕ):ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), 1/((2:ℝ)^k) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = _ := by simp
    push_cast at block ⊢
    linarith only [ih,block]

theorem reciprocalTotientLogBound (X : ℕ) (_ : 0<X) :
    (∑ m ∈ Finset.Icc 1 X, 1/(m.totient:ℝ)) ≤ ((Nat.log 2 X:ℝ)+2)^2 := by
  let k := Nat.log 2 X
  have idx : Finset.Icc 1 X = (Finset.range X).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨m-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  have upper := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have harm : (∑ m ∈ Finset.range X, 1/((m:ℝ)+1)) ≤ (k:ℝ)+2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono upper) (fun m _ _ => by positivity)).trans
    convert harmonicBlock (k+1) using 1; push_cast; ring
  rw [idx,Finset.sum_map]
  calc
    _ ≤ ∑ j ∈ Finset.range X, ((k:ℝ)+1)*(1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have le : j+1 ≤ X := Finset.mem_range.mp hj
      have hk : Nat.log 2 (j+1) ≤ k := Nat.log_mono_right le
      have b := totientLogLower (j+1) (by omega)
      have h : (((j+1:ℕ):ℝ)/((j+1).totient:ℝ)) ≤ (k:ℝ)+1 := b.trans (by exact_mod_cast (Nat.add_le_add_right hk 1))
      change 1/((j+1).totient:ℝ) ≤ _
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      push_cast at h
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
    _ = ((k:ℝ)+1)*_ := (Finset.mul_sum ..).symm
    _ ≤ ((k:ℝ)+1)*((k:ℝ)+2) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ _ := by dsimp [k]; nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.log 2 X)]


private theorem chargeWitnesses {α β : Type*} [DecidableEq β]
    (S : Finset β) (T : Finset α) (key : α → β) (w : β → ℝ) (v : α → ℝ)
    (pos : ∀ a∈T, 0≤v a) (charge : ∀ b∈S, ∃ a∈T, key a=b ∧ w b≤v a) :
    (∑ b ∈ S, w b) ≤ ∑ a ∈ T, v a := by
  calc
    _ ≤ ∑ b ∈ S, ∑ a ∈ T, if key a=b then v a else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a,ha,e,h⟩ := charge b hb
      apply h.trans
      simpa only [e,ite_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]

private theorem largePeriodWeightFinite (n : ℕ) :
    (∑ q ∈ (Finset.Icc 1 ((grid n)^2)).filter (shortLarge n),
      weight n q) ≤
      (∑ m ∈ Finset.Icc 1 ((grid n)^2), 1/(m.totient:ℝ)) *
        (((1+Nat.log 2 (grid n):ℕ):ℝ)^8 / ((1+Nat.log 2 (grid n):ℕ):ℝ)^12) := by
  classical
  let u := 1+Nat.log 2 (grid n)
  let H := u^4
  let Y := u^12
  let X := (grid n)^2
  let D := Finset.Icc 1 X
  let J := Finset.Icc 1 H
  let Ps := fun j : ℕ => (2^j-1:ℕ).primeFactors.filter (fun p => Y<p)
  let T : Finset (Σ _j : ℕ, ℕ × ℕ) := J.sigma (fun j => Ps j ×ˢ D)
  let S := D.filter (shortLarge n)
  let v := fun a : (Σ _j : ℕ, ℕ × ℕ) => (1/((a.2.1:ℝ)-1))*(1/(a.2.2.totient:ℝ))
  let M := ∑ m ∈ D, 1/(m.totient:ℝ)
  have vpos (a : Σ _j : ℕ, ℕ × ℕ) (ha : a∈T) : 0≤v a := by
    have h := (Finset.mem_product.mp (Finset.mem_sigma.mp ha).2).1
    have hp := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1).two_le
    have hp' : (2:ℝ)≤a.2.1 := by exact_mod_cast hp
    exact mul_nonneg (one_div_nonneg.mpr (by linarith)) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have witnesses (q : ℕ) (hq : q∈S) : ∃ a∈T, a.2.1*a.2.2=q ∧ weight n q≤v a := by
    obtain ⟨hd,p,hp,hY,j,hj',dvd⟩ := Finset.mem_filter.mp hq
    have pPrime := Nat.prime_of_mem_primeFactors hp
    have dp := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨m,eq⟩ := dp
    have qpos : 0<q := (Finset.mem_Icc.mp hd).1
    have mpos : 0< m := Nat.pos_of_ne_zero (fun e => (Nat.ne_of_gt qpos) (by simp [eq,e]))
    have mQ : m≤q := Nat.le_of_dvd qpos ⟨p,by simpa only [mul_comm] using eq⟩
    have hpos : 0<(2^j-1:ℕ) := by
      have two : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (Finset.mem_Icc.mp hj').1
      omega
    have pm : p∈Ps j := Finset.mem_filter.mpr ⟨pPrime.mem_primeFactors dvd hpos.ne',hY⟩
    refine ⟨⟨j,(p,m)⟩, Finset.mem_sigma.mpr ⟨hj', Finset.mem_product.mpr ⟨pm,Finset.mem_Icc.mpr ⟨mpos,mQ.trans (Finset.mem_Icc.mp hd).2⟩⟩⟩,eq.symm, ?_⟩
    have phip : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr pPrime.pos
    have phim : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mpos
    have phi : (p.totient:ℝ)*(m.totient:ℝ) ≤ (q.totient:ℝ) := by rw [eq]; exact_mod_cast Nat.totient_super_multiplicative p m
    have phiq : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr qpos
    have primeId : (p.totient:ℝ)=(p:ℝ)-1 := by
      rw [Nat.totient_prime pPrime,Nat.cast_sub (by have := pPrime.two_le; omega),Nat.cast_one]
    calc
      _ ≤ 1/(q.totient:ℝ) := div_le_div_of_nonneg_right (min_le_left ..) phiq.le
      _ ≤ 1/((p.totient:ℝ)*(m.totient:ℝ)) := one_div_le_one_div_of_le (mul_pos phip phim) phi
      _ = _ := by dsimp [v]; rw [primeId]; simp only [one_div,mul_inv_rev,mul_comm]
  have eq : (∑ a ∈ T, v a) = M*(∑ j ∈ J, ∑ p ∈ Ps j, 1/((p:ℝ)-1)) := by
    dsimp only [T]
    rw [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [v]
    rw [← Finset.mul_sum,mul_comm]
  have ub := periodPrimeBudget H Y (by dsimp [H,Y,u]; positivity)
  have conv : (H:ℝ)^2/(Y:ℝ) = (u:ℝ)^8/(u:ℝ)^12 := by dsimp [H,Y]; push_cast; ring
  rw [conv] at ub
  apply (chargeWitnesses S T (fun a => a.2.1*a.2.2) (weight n) v vpos witnesses).trans
  rw [eq]
  exact mul_le_mul_of_nonneg_left ub (Finset.sum_nonneg fun _ _ => by positivity)

theorem shortLarge_budget : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Finset.Icc 1 ((grid n)^2)).filter (shortLarge n),
      weight n q) ≤ ε := by
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_ge (16/ε)
  refine ⟨2^(2^M), ?_⟩
  intro n hn
  let Q := grid n
  let u := 1+Nat.log 2 Q
  have hlog : 2^M ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 2^M ≤ Q := by dsimp [Q,grid]; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have qpos : 0<Q := lt_of_lt_of_le (by positivity : 0<2^M) hQ
  have hu : M ≤ u := by have h := Nat.le_log_of_pow_le (by decide : 1<2) hQ; dsimp [u]; omega
  have u1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1≤u by dsimp [u]; omega)
  have upos : (0:ℝ)<u := by linarith
  have cap := Nat.lt_pow_succ_log_self (by decide : 1<2) Q
  have cap' : Q < 2^u := by simpa only [u,Nat.add_comm 1] using cap
  have both : Q^2 < 2^(2*u) := by
    rw [mul_comm 2 u,pow_mul]
    exact Nat.pow_lt_pow_left cap' (by decide)
  have hL : Nat.log 2 (Q^2) < 2*u := by
    by_contra! hh
    have power := Nat.pow_le_pow_right (by decide : 0<2) hh
    have b := Nat.pow_log_le_self 2 (by positivity : Q^2≠0)
    omega
  have hR : (Nat.log 2 (Q^2):ℝ)+2 ≤ 4*(u:ℝ) := by exact_mod_cast (show Nat.log 2 (Q^2)+2≤4*u by omega)
  have hb := (reciprocalTotientLogBound (Q^2) (by positivity)).trans (pow_le_pow_left₀ (by positivity) hR 2)
  apply (largePeriodWeightFinite n).trans
  change _ * ((u:ℝ)^8/(u:ℝ)^12) ≤ ε
  apply (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (u:ℝ)^8/(u:ℝ)^12)).trans
  have limit : 16 ≤ ε*(u:ℝ) := by
    have h := (div_le_iff₀ hε).mp (hM.trans (by exact_mod_cast hu : (M:ℝ) ≤ u))
    linarith
  calc
    _ = 16/(u:ℝ)^2 := by field_simp; ring
    _ ≤ 16/(u:ℝ) := div_le_div_of_nonneg_left (by norm_num) upos (by nlinarith [sq_nonneg ((u:ℝ)-1)])
    _ ≤ ε := (div_le_iff₀ upos).mpr limit


end GB4Bad

/-! The singular-factor second moment is adapted from goldbach-proofs,
`BeaumontScaledDeletionSurvival.lean` (Apache 2.0). -/
namespace GB4Totient
open Finset

private def oddFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ oddFactors n, (1 + 1 / ((p : ℝ) - 2))

private noncomputable def increment (p : ℕ) : ℝ := (1 + 1 / ((p : ℝ) - 2))^2 - 1

private theorem increment_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ increment p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 ≤ 1 / ((p : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  unfold increment
  nlinarith [sq_nonneg (1 / ((p : ℝ) - 2))]

/-- A telescoping rational product bounds the averaged Euler factors at integers from 5 onwards. -/
private theorem tail_product (N : ℕ) (hN : 4 ≤ N) :
    ∏ p ∈ Icc 5 N, (1 + increment p / (p : ℝ)) ≤ 2 * ((N : ℝ) - 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hI : Icc 5 (k + 1) = insert (k + 1) (Icc 5 k) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp)]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hinc := increment_nonneg (p := k + 1) (by omega)
    calc
      _ ≤ (1 + increment (k+1) / ((k+1 : ℕ) : ℝ)) * (2 * ((k : ℝ) - 2) / k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
        simp only [increment, Nat.cast_succ]
        rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
        have h0 : (k : ℝ) ≠ 0 := by linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
        calc
          _ = 2 * ((k : ℝ) - 1) / (k + 1) - 2 / ((k + 1) * (k - 1 : ℝ)^2) := by
            field_simp [h0, h1, h2]
            ring
          _ ≤ _ := sub_le_self _ (by positivity)

/-- Every odd prime factor of a positive integer at most `M` is 3 or lies in this tail. -/
private def candidates (M : ℕ) : Finset ℕ := insert 3 (Icc 5 (M+4))

private theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p := by
  rcases mem_insert.mp hp with rfl | hp
  · decide
  · have := (mem_Icc.mp hp).1
    omega

private theorem candidates_product (M : ℕ) :
    ∏ p ∈ candidates M, (1 + increment p / (p : ℝ)) ≤ 4 := by
  have htail := tail_product (M+4) (by omega)
  have hpos : (0 : ℝ) < (M+4 : ℕ) := by positivity
  have hbound : 2 * (((M+4 : ℕ) : ℝ) - 2) / (M+4 : ℕ) ≤ 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  rw [candidates, prod_insert (by simp)]
  have hthree : 1 + increment 3 / (3 : ℝ) = 2 := by norm_num [increment]
  change (1 + increment 3 / (3 : ℝ)) * _ ≤ 4
  rw [hthree]
  linarith [htail.trans hbound]

private theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  obtain ⟨hdiv, hodd⟩ := mem_filter.mp hp
  have hpN := Nat.le_of_mem_primeFactors hdiv
  have hfour : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) (Nat.prime_of_mem_primeFactors hdiv)
  by_cases h : p = 3
  · exact mem_insert.mpr (Or.inl h)
  · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨by omega, by omega⟩))

private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    singular n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    singular n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold singular
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
private theorem prefix_square (M : ℕ) : (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ 4*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 * (M : ℝ) := by
      rw [mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)


private theorem singular_nonneg (q : ℕ) : 0 ≤ singular q := by
  apply Finset.prod_nonneg
  intro p hp
  have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  positivity

private theorem ratio_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ 2*singular q := by
  classical
  let F (p : ℕ) := (p:ℝ)/((p:ℝ)-1)
  let O := oddFactors q
  have hfac : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ q.primeFactors, F p := by
    have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hP1 : 0 < ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
      apply Finset.prod_pos
      intro p hp
      have hh : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    have hid := congrArg (fun x : ℕ => (x : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul, Nat.cast_prod] at hid
    have he : ∏ p ∈ q.primeFactors, ((p-1:ℕ):ℝ) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    rw [he] at hid
    dsimp only [F]
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hoff : (∏ p ∈ O, F p) ≤ singular q := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp
      have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      dsimp [F]
      field_simp [show (0:ℝ)<p-2 by linarith,show (0:ℝ)<p-1 by linarith]
      nlinarith
  rw [hfac]
  by_cases h : 2 ∈ q.primeFactors
  · have ho : q.primeFactors = insert 2 O := by
      ext p
      change p ∈ q.primeFactors ↔ p ∈ insert 2 (q.primeFactors.filter (2 < ·))
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        by_cases he:p=2
        · exact Or.inl he
        · exact Or.inr ⟨hp,by omega⟩
      · rintro (rfl | ⟨hp,_⟩) <;> assumption
    have h2 : 2 ∉ O := by simp [O,oddFactors]
    rw [ho, Finset.prod_insert h2]
    have hf : F 2 = 2 := by norm_num [F]
    rw [hf]
    linarith
  · have ho : q.primeFactors = O := by
      ext p
      change p ∈ q.primeFactors ↔ p ∈ q.primeFactors.filter (2 < ·)
      simp only [Finset.mem_filter, iff_self_and]
      intro hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have hh : p ≠ 2 := by rintro rfl; contradiction
      omega
    rw [ho]
    linarith [singular_nonneg q]

private noncomputable def w (q : ℕ) : ℝ := (q:ℝ)/(q.totient:ℝ)^2

private theorem dyadic_step (d : ℕ) (hd : 0 < d) : (∑ q ∈ Ioc d (2*d), w q) ≤ 32 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hsub : Ioc d (2*d) ⊆ Icc 1 (2*d) := by intro q hq; simp_all [mem_Ioc, mem_Icc]; omega
  have h := prefix_square (2*d)
  calc
    (∑ q ∈ Ioc d (2*d), w q) ≤ ∑ q ∈ Ioc d (2*d), 4/(d:ℝ)*singular q^2 := by
      apply sum_le_sum
      intro q hq
      have dq := (mem_Ioc.mp hq).1
      have hq' : 0 < q := hd.trans dq
      have hqR : (0:ℝ)<q := by exact_mod_cast hq'
      have hdqR : (d:ℝ)≤q := by exact_mod_cast dq.le
      have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq'
      have hs := sq_le_sq₀ (show 0≤(q:ℝ)/q.totient by positivity) (mul_nonneg (by norm_num : (0:ℝ)≤2) (singular_nonneg q)) |>.mpr (ratio_le q hq')
      calc
        w q = ((q:ℝ)/q.totient)^2 / q := by dsimp [w]; field_simp
        _ ≤ (2*singular q)^2 / q := by gcongr
        _ ≤ (2*singular q)^2 / d := by gcongr
        _ = _ := by ring
    _ = 4/(d:ℝ)*(∑ q ∈ Ioc d (2*d), singular q^2) := (mul_sum ..).symm
    _ ≤ 4/(d:ℝ)*(∑ q ∈ Icc 1 (2*d), singular q^2) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) (by positivity)
    _ ≤ 4/(d:ℝ)*(4*((2*d:ℕ):ℝ)) := by gcongr
    _ = 32 := by push_cast; field_simp; ring

private theorem prefix_pow (k : ℕ) :
    (∑ q ∈ Icc 1 (2^k), w q) ≤ 32*((k:ℝ)+1) := by
  induction k with
  | zero => norm_num [w]
  | succ k ih =>
    have hs : Icc 1 (2^(k+1)) = Icc 1 (2^k) ∪ Ioc (2^k) (2*2^k) := by
      ext q
      have hk : 0 < (2:ℕ)^k := by positivity
      simp only [mem_Icc, mem_union, mem_Ioc, pow_succ]
      omega
    have hd : Disjoint (Icc 1 (2^k)) (Ioc (2^k) (2*2^k)) := by
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      exact (not_lt_of_ge (mem_Icc.mp hq).2) (mem_Ioc.mp hq').1
    rw [hs, sum_union hd]
    have hh := dyadic_step (2^k) (by positivity)
    push_cast
    linarith

/-- The weighted totient sum costs only a single logarithm. -/
theorem sum_totient (Q : ℕ) :
    (∑ q ∈ Icc 1 (Q^2), (q:ℝ)/(q.totient:ℝ)^2) ≤ 96*(1+(Nat.log 2 Q:ℝ)) := by
  let k := Nat.log 2 Q + 1
  have h : Q ≤ 2^k := (Nat.lt_pow_succ_log_self (by decide : 1<2) Q).le
  have h2 : Q^2 ≤ 2^(k*2) := by rw [pow_mul]; gcongr
  have hs : Icc 1 (Q^2) ⊆ Icc 1 (2^(k*2)) := Finset.Icc_subset_Icc_right h2
  calc
    (∑ q ∈ Icc 1 (Q^2), (q:ℝ)/(q.totient:ℝ)^2) ≤ ∑ q ∈ Icc 1 (2^(k*2)), w q :=
      sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => by positivity)
    _ ≤ _ := (prefix_pow (k*2)).trans (by dsimp [k]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) (Nat.log 2 Q)])

end GB4Totient

namespace GB4Scale

def grid (n : ℕ) := (Nat.log 2 (n+2))^2
def depth (n : ℕ) := 1 + Nat.log 2 (grid n)
def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

/-- An explicit comparison used only to make the orbit block fit inside the
available binary frequencies. No Goldbach instances are enumerated. -/
private theorem pow_dominates (k : ℕ) (hk : 128 ≤ k) : 16*(1+k)^8 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have step : (1+(k+1))^8 ≤ 2*(1+k)^8 := by
      obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hk
      ring_nf
      omega
    omega

theorem eventual_scales (b : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
    2 ≤ depth n ∧ b ≤ depth n ∧ (depth n)^4 ≤ length n := by
  let B := max 128 b
  refine ⟨2^(2^B),fun n hn => ?_⟩
  have hB : 128 ≤ B := le_max_left 128 b
  have hb : b ≤ B := le_max_right 128 b
  have hn2 : 2 ≤ n := (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.one_le_two_pow (n:=B))).trans hn
  let v := Nat.log 2 (n+2)
  let k := Nat.log 2 (grid n)
  have hv : 2^B ≤ v := Nat.le_log_of_pow_le (by decide) (hn.trans (by omega))
  have hv1 : 1 ≤ v := (Nat.one_le_two_pow (n:=B)).trans hv
  have hv2 : v ≤ grid n := by change v ≤ v^2; nlinarith
  have hk : B ≤ k := Nat.le_log_of_pow_le (by decide) (hv.trans hv2)
  have hq0 : grid n ≠ 0 := by omega
  have he := (pow_dominates k (hB.trans hk)).trans (Nat.pow_log_le_self 2 hq0)
  change 16*(1+k)^8 ≤ v^2 at he
  have hsq : (4*(1+k)^4)^2 ≤ v^2 := by convert he using 1; ring
  have hl := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  have hshift : v ≤ Nat.log 2 n + 1 := by
    have := Nat.log_mono_right (b:=2) (show n+2 ≤ n*2 by omega)
    rwa [Nat.log_mul_base (by decide) (by omega)] at this
  change 2 ≤ 1+k ∧ b ≤ 1+k ∧ (1+k)^4 ≤ max 1 (Nat.log 2 n / 2)
  have : 1 ≤ (1+k)^4 := Nat.one_le_pow _ _ (by omega)
  omega

theorem separation {q p m : ℕ} (hprime : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q)
    (hnone : ∀ h ∈ Finset.Icc 1 m, ¬ p ∣ 2^h-1)
    {i j : ℕ} (hij : i < j) (heq : (2:ℕ)^(i+1)%q = 2^(j+1)%q) : m ≤ j-i := by
  by_contra! hshort
  have hsplit : j+1 = i+1+(j-i) := by omega
  have hmod : 2^(i+1)*1 ≡ 2^(i+1)*2^(j-i) [MOD p] := by
    have h : (2:ℕ)^(i+1) ≡ 2^(j+1) [MOD p] := (show _ ≡ _ [MOD q] from heq).of_dvd hpq
    simpa only [mul_one, hsplit, pow_add] using h
  have hcop : p.Coprime 2 := (Nat.coprime_primes hprime Nat.prime_two).mpr hp2
  have hcancel := Nat.ModEq.cancel_left_of_coprime (hcop.pow_right (i+1)) hmod
  exact hnone (j-i) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n:=j-i))).mp hcancel)

end GB4Scale

namespace GB4Centers
open Finset GB4Bad GB4Moment
open scoped Classical

noncomputable def centers (n q : ℕ) : ℕ :=
  ((range (q+1)).filter (fun a : ℕ =>
    Nat.Coprime a q ∧ (1:ℝ)/3 < K (GB4Scale.length n) ((a:ℝ)/q))).card

noncomputable def mass (n q : ℕ) : ℝ :=
  min 1 ((q:ℝ)/(grid n:ℝ)) * (centers n q:ℝ)/(q.totient:ℝ)^2

private theorem mass_nonneg (n q : ℕ) : 0 ≤ mass n q := by
  unfold mass
  positivity

-- The coprime counting argument is adapted from PacketShortCentersFromModuli.
private theorem mass_trivial (n q : ℕ) (hq : 1 ≤ q) : mass n q ≤ 2*weight n q := by
  let V := (range q).filter (fun a => Nat.Coprime q a)
  have cnt : centers n q ≤ (insert q V).card := by
    apply card_le_card
    intro a ha
    obtain ⟨hr,hc,_⟩ := mem_filter.mp ha
    rcases lt_or_ge a q with h|h
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr h,hc.symm⟩)
    · exact mem_insert.mpr (Or.inl (by have := mem_range.mp hr; omega))
  have card := cnt.trans (card_insert_le q V)
  change centers n q ≤ q.totient+1 at card
  have hp : 0 < q.totient := Nat.totient_pos.mpr hq
  have hc : (centers n q:ℝ) ≤ 2*(q.totient:ℝ) := by exact_mod_cast (show centers n q ≤ 2*q.totient by omega)
  have hpos : (0:ℝ) < q.totient := by exact_mod_cast hp
  unfold mass weight
  calc
    _ ≤ min 1 ((q:ℝ)/(grid n:ℝ)) * (2*(q.totient:ℝ))/(q.totient:ℝ)^2 := by
      gcongr
    _ = _ := by field_simp

private theorem mass_long (n q : ℕ) (hu : 2 ≤ u n) (hL : (u n)^4 ≤ GB4Scale.length n)
    (hs : ¬ smooth n q) (hb : ¬shortLarge n q) :
    mass n q ≤ (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2) := by
  unfold smooth at hs
  push Not at hs
  obtain ⟨p,hp,hlarge⟩ := hs
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    have := Nat.pow_le_pow_left hu 12
    omega
  have hq : 1 < q := hprime.one_lt.trans_le (Nat.le_of_mem_primeFactors hp)
  have hnone : ∀ j ∈ Icc 1 ((u n)^4), ¬p ∣ 2^j-1 :=
    fun j hj hd => hb ⟨p,hp,hlarge,j,hj,hd⟩
  have hm : 0 < (u n)^4 := by positivity
  have hcard := centers_le q (GB4Scale.length n) ((u n)^4) hq hm hL
    (fun _ _ hij _ heq => GB4Scale.separation hprime hp2 hpq hnone hij heq)
  change (centers n q:ℝ) ≤ _ at hcard
  push_cast at hcard
  unfold mass
  calc
    _ ≤ (centers n q:ℝ)/(q.totient:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg _)).trans_eq (one_mul _)
    _ ≤ (18*(q:ℝ)/(u n:ℝ)^4)/(q.totient:ℝ)^2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by ring

private theorem finite_bound (n : ℕ) (hu : 2 ≤ u n) (hL : (u n)^4 ≤ GB4Scale.length n) :
    ∑ q ∈ Icc 1 ((grid n)^2), mass n q ≤
      2*(∑ q ∈ (Icc 1 ((grid n)^2)).filter (smooth n), weight n q) +
      2*(∑ q ∈ (Icc 1 ((grid n)^2)).filter (shortLarge n), weight n q) +
      (18/(u n:ℝ)^4)*(96*(u n:ℝ)) := by
  classical
  let S := Icc 1 ((grid n)^2)
  have hsum : (∑ q ∈ S, mass n q) ≤
      ∑ q ∈ S, ((if smooth n q then 2*weight n q else 0) +
        (if shortLarge n q then 2*weight n q else 0) +
        (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2)) := by
    apply sum_le_sum
    intro q hq
    have hw : 0 ≤ weight n q := by unfold weight; positivity
    have hr : 0 ≤ (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2) := by positivity
    have ht := mass_trivial n q (mem_Icc.mp hq).1
    by_cases hs : smooth n q <;> by_cases hb : shortLarge n q
    · simp only [ite_eq_left hs, ite_eq_left hb]; linarith
    · simp only [ite_eq_left hs, ite_eq_right hb]; linarith
    · simp only [ite_eq_right hs, ite_eq_left hb]; linarith
    · simpa only [ite_eq_right hs, ite_eq_right hb, zero_add] using mass_long n q hu hL hs hb
  simp only [sum_add_distrib, ← sum_filter, ← mul_sum] at hsum
  have ht := GB4Totient.sum_totient (grid n)
  have hu' : (u n:ℝ) = 1+(Nat.log 2 (grid n):ℝ) := by simp [u]
  change (∑ q ∈ S, mass n q) ≤ _
  have last : (18/(u n:ℝ)^4)*(∑ q ∈ S, (q:ℝ)/(q.totient:ℝ)^2) ≤ (18/(u n:ℝ)^4)*(96*(u n:ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [hu'] using ht
  exact hsum.trans (add_le_add (le_refl _) last)

/-- The full family of reduced binary-orbit centers has vanishing weighted mass. -/
theorem all_centers (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Icc 1 ((grid n)^2), mass n q) ≤ ε := by
  obtain ⟨A,hA⟩ := smooth_budget (ε/8) (by positivity)
  obtain ⟨B,hB⟩ := shortLarge_budget (ε/8) (by positivity)
  obtain ⟨b,hb⟩ := exists_nat_ge (3456/ε)
  obtain ⟨C,hC⟩ := GB4Scale.eventual_scales b
  refine ⟨max A (max B C),fun n hn => ?_⟩
  have ha := hA n ((le_max_left ..).trans hn)
  have hbc := (le_max_right ..).trans hn
  have hx := hB n ((le_max_left ..).trans hbc)
  obtain ⟨hu,hbu,hL⟩ := hC n ((le_max_right ..).trans hbc)
  change 2 ≤ u n at hu
  change b ≤ u n at hbu
  have hge : (2:ℝ) ≤ u n := by exact_mod_cast hu
  have hpos : (0:ℝ) < u n := by linarith
  have heps : 3456 ≤ (u n:ℝ)*ε :=
    (div_le_iff₀ hε).mp (hb.trans (by exact_mod_cast hbu))
  have hrate : 18/(u n:ℝ)^4*(96*(u n:ℝ)) ≤ ε/2 := by
    calc
      _ = 1728/(u n:ℝ)^3 := by field_simp; ring
      _ ≤ 1728/(u n:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hpos
        have := pow_le_pow_right₀ (show (1:ℝ) ≤ u n by linarith) (show 1 ≤ 3 by decide)
        simpa using this
      _ ≤ _ := (div_le_iff₀ hpos).mpr (by linarith)
  linarith [finite_bound n hu hL]

end GB4Centers

theorem Conjectures.Goldbach.PacketRemainingCenterCount :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => ¬ o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε := by
  classical
  intro Q L K o ε hε
  obtain ⟨N,hN⟩ := GB4Centers.all_centers ε hε
  refine ⟨N,fun n hn => ?_⟩
  apply le_trans _ (hN n hn)
  change (∑ q ∈ (Finset.Icc 1 ((GB4Bad.grid n)^2)).filter (fun q => ¬o n q), GB4Centers.mass n q) ≤ _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
    (fun q _ _ => GB4Centers.mass_nonneg n q)
