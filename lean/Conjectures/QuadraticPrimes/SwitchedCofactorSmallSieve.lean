import Mathlib
import Conjectures.TwinPrimes.CofactorTwoLinearSieve

/-! The finite Selberg inequality, the periodic counting estimate and the definitions
of its weights come from `Conjectures.TwinPrimes.CofactorTwoLinearSieve`.
The affine change of variable below applies that sieve to the switched progression. -/

namespace Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux

open Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux
open OAI.Problem337 Finset
noncomputable section

def splitPrimes (y : ℕ) := y.primesLE.filter fun q => q % 4 = 1
def wheel (y : ℕ) := ∏ q ∈ splitPrimes y, q
def value (p r t : ℕ) := 4 * (p*t+r)^2 + 1

theorem mem_split {q y : ℕ} (hq : q ∈ splitPrimes y) :
    q.Prime ∧ q ≤ y ∧ q % 4 = 1 := by
  obtain ⟨h,hm⟩ := mem_filter.mp hq
  exact ⟨Nat.prime_of_mem_primesLE h, (Nat.mem_primesLE.mp h).1, hm⟩

theorem wheel_sq (y : ℕ) : Squarefree (wheel y) := by
  apply (squarefree_primorial y).squarefree_of_dvd
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

theorem wheel_factors (y : ℕ) : (wheel y).primeFactors = splitPrimes y :=
  Nat.primeFactors_prod fun q hq => (mem_split hq).1

theorem affine_discrepancy (N p r d : ℕ) [NeZero d] (hd : Squarefree d)
    (hs : ∀ q ∈ d.primeFactors, q % 4 = 1) (hp : p.Coprime d) :
    |(((range N).filter fun t => d ∣ value p r t).card : ℝ) -
      (N : ℝ) * goldbachSieveRootCount 2 d / d| ≤ goldbachSieveRootCount 2 d := by
  classical
  have hodd : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
    by have := hs 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,NeZero.ne _⟩); omega
  obtain ⟨i, hi⟩ := (ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hd).2
    (fun q hq => by rw [hs q hq]; decide)
  have hii : i*i = -1 := hi.symm
  have hunit : IsUnit i := isUnit_iff_exists_inv.2 ⟨-i, by rw [mul_neg, hii, neg_neg]⟩
  let v := hunit.mul ((ZMod.isUnit_iff_coprime (2*p) d).2 (hodd.mul_left hp))
  let e : ZMod d ≃ ZMod d := v.unit.mulLeft.trans (Equiv.addRight (1 + i*(2*r)))
  let R := univ.filter (fun t : ZMod d => 4*((p:ZMod d)*t+r)^2 + 1 = 0)
  have he (t : ZMod d) : e t = 1 + i*(2*((p:ZMod d)*t+r)) := by
    change (↑v.unit : ZMod d)*t + (1 + i*(2*r)) = _
    rw [v.unit_spec]
    push_cast
    ring
  have hc : R.card = goldbachSieveRootCount 2 d := by
    rw [goldbachSieveRootCount_eq_filter_card]
    apply Finset.card_equiv e
    intro t
    simp only [R, mem_filter, mem_univ, true_and, he, Nat.cast_ofNat]
    have h : (1+i*(2*((p:ZMod d)*t+r)))*(2-(1+i*(2*((p:ZMod d)*t+r)))) =
        4*((p:ZMod d)*t+r)^2 + 1 := by
      linear_combination -4*((p:ZMod d)*t+r)^2 * hii
    rw [h]
  have hset : ((range N).filter fun t => d ∣ value p r t) =
      ((range N).filter fun t : ℕ => (t : ZMod d) ∈ R) := by
    apply filter_congr
    intro t _
    rw [← ZMod.natCast_eq_zero_iff]
    simp [R, value]
  rw [hset, ← hc]
  exact abs_card_range_zmod_mem_sub N R

def sieve (N p r y : ℕ) := PrimePairSieve.imageSieve (range N) (value p r) (wheel y)
  (wheel_sq y) (goldbachSieveDensity 2) (goldbachSieveDensity_isMultiplicative 2)
  (fun q hq _ => goldbachSieveDensity_prime_pos _ _ hq)
  (fun q hq _ => goldbachSieveDensity_prime_lt_one _ _ hq (fun _ => dvd_refl _))

theorem finite_upper (N p r y z : ℕ) (hp : p.Prime) (hy : y < p) (hz : 1 ≤ z) :
    (((range N).filter fun t => (wheel y).Coprime (value p r t)).card : ℝ) ≤
      N / GoldbachSelberg.denominator 2 (wheel y) z + (z : ℝ)^2 * (1+Real.log z)^4 := by
  let s := sieve N p r y
  have hP := wheel_sq y
  have hf := wheel_factors y
  have hrem (d : ℕ) [NeZero d] (hd : d ∣ wheel y) :
      |s.rem d| ≤ goldbachSieveRootCount 2 d := by
    have sub := Nat.primeFactors_mono hd hP.ne_zero
    rw [hf] at sub
    have hc : p.Coprime d := hp.coprime_iff_not_dvd.mpr (by
      intro h
      have := (mem_split (sub (Nat.mem_primeFactors.mpr ⟨hp,h,NeZero.ne _⟩))).2.1
      omega)
    have H := affine_discrepancy N p r d (hP.squarefree_of_dvd hd)
      (fun q hq => (mem_split (sub hq)).2.2) hc
    dsimp only [s, sieve]
    rw [PrimePairSieve.imageSieve_rem, card_range, goldbachSieveDensity_apply]
    convert H using 2 <;> ring
  have hh := SelbergOptimal.siftedSum_le_log_error s hz (by
    intro a ha b hb
    letI : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
    letI : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
    letI : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    have ha' : a ∣ wheel y := Nat.dvd_of_mem_divisors ha
    have hb' : b ∣ wheel y := Nat.dvd_of_mem_divisors hb
    apply (hrem _ (Nat.lcm_dvd ha' hb')).trans
    exact_mod_cast (goldbachSieveRootCount_lcm_le 2 a b).trans (Nat.mul_le_mul
      (goldbachSieveRootCount_le_two_pow 2 a (hP.squarefree_of_dvd ha'))
      (goldbachSieveRootCount_le_two_pow 2 b (hP.squarefree_of_dvd hb'))))
  have hnorm : SelbergOptimal.normalizer s z = GoldbachSelberg.denominator 2 (wheel y) z := by
    unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
    apply sum_congr rfl
    intro d _
    rw [BoundingSieve.selbergTerms_apply]
    rfl
  rw [hnorm] at hh
  dsimp only [s, sieve] at hh
  rw [PrimePairSieve.imageSieve_siftedSum] at hh
  simpa only [PrimePairSieve.imageSieve, card_range] using hh

open CentralSelberg

def splitMass (n y : ℕ) : ℝ := ∏ p ∈ splitPrimes y, (1+wgt n p)

/- The logarithmic first-moment argument is adapted from
`CentralSelberg.retained`, restricting its finite prime set to the split primes. -/
theorem split_denominator_sum (n y z : ℕ) :
    GoldbachSelberg.denominator n (wheel y) z =
      ∑ t ∈ (splitPrimes y).powerset, if index t ≤ z then weight n t else 0 := by
  classical
  let P := wheel y
  have prime (t : Finset ℕ) (ht : t∈(splitPrimes y).powerset) : ∀ p∈t, p.Prime :=
    fun p hp => (mem_split ((Finset.mem_powerset.mp ht) hp)).1
  have hfac (t : Finset ℕ) (ht : t∈(splitPrimes y).powerset) :
      (index t).primeFactors=t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = (splitPrimes y).powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (wheel_sq y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) ((wheel_sq y).ne_zero)
      rw [wheel_factors] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono, Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht),(wheel_sq y).ne_zero⟩
  unfold GoldbachSelberg.denominator
  change (∑ d ∈ P.divisors, _) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh => (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  split_ifs
  · rw [hfac t ht, index, (goldbachSieveDensity_isMultiplicative n).map_prod_of_prime t (prime t ht)]
    exact (Finset.prod_mul_distrib).symm
  · rfl

theorem split_retained (n y : ℕ) (hn : 2∣n) (hy : 2≤y) :
    splitMass n y ≤ 2 * GoldbachSelberg.denominator n (wheel y) (y^8) := by
  let T := (splitPrimes y).powerset
  let W := weight n
  let D := GoldbachSelberg.denominator n (wheel y) (y^8)
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp => (wgt_pos n hn p ((mem_split ((Finset.mem_powerset.mp ht) hp)).1)).le
  have total : (∑ t ∈ T, W t) = splitMass n y := (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y^8 < index t then W t else 0)*(8*Real.log y) ≤ W t*Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      ((mem_split ((Finset.mem_powerset.mp ht) hp)).1).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0:ℝ) < ((y^8:ℕ):ℝ) by positivity) (show ((y^8:ℕ):ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := powerset_moment (splitPrimes y) (wgt n) (fun p => Real.log (p:ℝ))
    (fun p hp => (wgt_pos n hn p ((mem_split hp).1)).le)
  have hsumlog (t : Finset ℕ) (ht : t∈T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p:ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp; exact_mod_cast ((mem_split ((Finset.mem_powerset.mp ht) hp)).1).ne_zero
  have bound : (∑ p ∈ (splitPrimes y), wgt n p/(1+wgt n p)*Real.log p) ≤ 4*Real.log y := by
    calc
      _ ≤ ∑ p ∈ (splitPrimes y), 2*(Real.log p/p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := (mem_split hp).1
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        rw [wgt_ratio n hn p hpP]
        unfold rho
        rw [goldbachSieveDensity_prime n p hpP]
        split <;> ring_nf <;> first | rfl | nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ) ≤ _))]
      _ ≤ ∑ p ∈ y.primesLE, 2*(Real.log p/p) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p _ _
        exact mul_nonneg (by norm_num) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      _ ≤ _ := by rw [←Finset.mul_sum]; linarith [weighted_harmonic y (by omega)]
  have hmass : 0 ≤ splitMass n y := Finset.prod_nonneg (fun p hp => by
    linarith [wgt_pos n hn p ((mem_split hp).1)])
  have moment : (∑ t ∈ T, W t*Real.log (index t)) ≤ splitMass n y * (4*Real.log y) := by
    calc
      _ = ∑ t ∈ (splitPrimes y).powerset, (∏ p ∈ t, wgt n p)*(∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y^8 < index t then W t else 0) = splitMass n y - D := by
    rw [← total, show D = _ from split_denominator_sum n y (y^8), ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro t _; by_cases h : index t ≤ y^8 <;> simp [h,not_lt.mpr,lt_of_not_ge,W]
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1<y by omega))
  change splitMass n y ≤ 2*D
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]



/-! The convolution of the mod-four character with the constant-one arithmetic
function has nonnegative coefficients. Its harmonic sum is large because each
nonempty initial sum of the alternating odd reciprocals is at least 2/3. -/
open ArithmeticFunction

def character : ArithmeticFunction ℝ where
  toFun n := (ZMod.χ₄ (n : ZMod 4) : ℤ)
  map_zero' := by change ((0:ℤ):ℝ) = 0; norm_num

theorem character_mul (m n : ℕ) : character (m*n) = character m * character n := by
  change (↑(ZMod.χ₄ ((m*n:ℕ) : ZMod 4)) : ℝ) = _
  simp only [Nat.cast_mul, map_mul, Int.cast_mul]
  rfl

theorem character_one : character 1 = 1 := by
  change (↑(ZMod.χ₄ ((1:ℕ) : ZMod 4)) : ℝ) = 1
  simp

def coeff := character * (zeta : ArithmeticFunction ℝ)

theorem coeff_mult : coeff.IsMultiplicative :=
  (show character.IsMultiplicative from ⟨character_one, fun {_ _} _ => character_mul _ _⟩).mul
    (by arith_mult)

theorem character_formula (n : ℕ) :
    character n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  change ((ZMod.χ₄ n : ℤ) : ℝ) = _
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

theorem coeff_prime_power (p j : ℕ) (hp : p.Prime) :
    coeff (p^j) = ∑ k ∈ range (j+1), (character p)^k := by
  rw [coeff, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro k hk
  clear hk
  induction k with
  | zero => simp [character_one]
  | succ k ih => rw [pow_succ, character_mul, ih, pow_succ]

theorem alternating_geom (j : ℕ) :
    (∑ k ∈ range (j+1), (-1:ℝ)^k) = if Even j then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, pow_succ]
    rcases Nat.even_or_odd j with hj|hj
    · simp [hj, hj.neg_one_pow, Nat.even_add_one]
    · simp [(Nat.not_even_iff_odd.mpr hj), hj.neg_one_pow, Nat.even_add_one, hj]

theorem prime_coeff_values (p j : ℕ) (hp : p.Prime) : coeff (p^j) =
    if p=2 then 1 else if p % 4=1 then ((j+1:ℕ):ℝ) else if Even j then 1 else 0 := by
  rw [coeff_prime_power p j hp, character_formula]
  by_cases h : p=2
  · subst p
    simp [Finset.sum_range_succ']
  · have ho := hp.eq_two_or_odd.resolve_left h
    simp only [h, ho, one_ne_zero, ite_false]
    by_cases h4 : p % 4=1
    · simp [h4]
    · simp only [h4, ite_false, alternating_geom]

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p j hp => rw [prime_coeff_values p j hp]; split_ifs <;> positivity
  | coprime a b _ _ hab ha hb => rw [coeff_mult.2 hab]; exact mul_nonneg ha hb

def charTerm (n : ℕ) := character n / n

theorem char_block (m : ℕ) :
    (0:ℝ) ≤ charTerm (4*m) + charTerm (4*m+1) + charTerm (4*m+2) + charTerm (4*m+3) := by
  simp only [charTerm,character_formula]
  have h0 : 4*m % 2=0 := by omega
  have h1 : (4*m+1)%2=1 := by omega
  have h2 : (4*m+2)%2=0 := by omega
  have h3 : (4*m+3)%2=1 := by omega
  have h4 : (4*m+1)%4=1 := by omega
  have h5 : (4*m+3)%4≠1 := by omega
  simp [h0,h1,h2,h3,h4,h5,div_eq_mul_inv]
  exact inv_anti₀ (by positivity) (by linarith)

theorem char_four_blocks (j : ℕ) :
    (2/3:ℝ) ≤ ∑ n ∈ range (4*j+4), charTerm n := by
  induction j with
  | zero => norm_num [charTerm, character_formula, Finset.sum_range_succ]
  | succ j ih =>
    have h := char_block (j+1)
    rw [show 4*(j+1)+4 = (4*j+4)+1+1+1+1 by omega]
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    rw [show 4*(j+1)=4*j+4 by omega] at h
    linarith only [h,ih]

theorem char_lower (N : ℕ) (hN : 1 ≤ N) :
    (2/3:ℝ) ≤ ∑ n ∈ Icc 1 N, charTerm n := by
  have hr : (∑ n ∈ Icc 1 N, charTerm n) = ∑ n ∈ range (N+1), charTerm n := by
    have he : range (N+1) = insert 0 (Icc 1 N) := by ext n; simp; omega
    rw [he,sum_insert (by simp)]
    simp [charTerm]
  rw [hr]
  by_cases h : N<4
  · interval_cases N <;> norm_num [charTerm,character_formula,sum_range_succ]
  let j := N/4
  have hj : 1 ≤ j := by dsimp [j]; omega
  have H := char_four_blocks (j-1)
  rw [show 4*(j-1)+4=4*j by omega] at H
  have H' := char_four_blocks j
  have hc : ∀ n : ℕ, n % 2=0 → charTerm n = 0 := by
    intro n hn; simp [charTerm,character_formula,hn]
  have h1 : 0 ≤ charTerm (4*j+1) := by
    simp [charTerm,character_formula,show (4*j+1)%2=1 by omega,show (4*j+1)%4=1 by omega]
    positivity
  have hx : N=4*j ∨ N=4*j+1 ∨ N=4*j+2 ∨ N=4*j+3 := by dsimp [j]; omega
  rcases hx with h|h|h|h
  · rw [h,sum_range_succ,hc _ (by omega),add_zero]; exact H
  · rw [h,sum_range_succ,sum_range_succ,hc _ (by omega),add_zero]; linarith
  · rw [h,sum_range_succ,hc _ (by omega),add_zero,sum_range_succ,sum_range_succ,hc _ (by omega),add_zero]; linarith
  · simpa only [h] using H'


theorem coeff_harmonic_lower (N : ℕ) :
    (2/3:ℝ) * Real.log ((N:ℝ)+1) ≤ ∑ n ∈ Icc 1 N, coeff n / n := by
  classical
  let D := ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun ab : ℕ × ℕ => ab.1*ab.2 ≤ N
  let F := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * charTerm ab.2
  have maps : ∀ ab ∈ D, ab.1*ab.2 ∈ Icc 1 N := by
    intro ab h
    obtain ⟨hp,hle⟩ := mem_filter.mp h
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1,hle⟩
  have fiber (n : ℕ) (hn : n ∈ Icc 1 N) :
      D.filter (fun ab => ab.1*ab.2=n) = n.divisorsAntidiagonal := by
    ext ⟨a,b⟩
    simp only [D, mem_filter,mem_product,mem_Icc,Nat.mem_divisorsAntidiagonal]
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    constructor
    · exact fun h => ⟨h.2,by omega⟩
    · rintro ⟨hab,hn0⟩
      have ha := left_ne_zero_of_mul (hab.trans_ne hn0)
      have hb := right_ne_zero_of_mul (hab.trans_ne hn0)
      have haN := (Nat.le_of_dvd hn1 (show a ∣ n from ⟨b,hab.symm⟩)).trans hnN
      have hbN := (Nat.le_of_dvd hn1 (show b ∣ n from ⟨a,by rw [mul_comm,hab]⟩)).trans hnN
      exact ⟨⟨⟨⟨by omega,haN⟩,⟨by omega,hbN⟩⟩,hab.trans_le hnN⟩,hab⟩
  have hcoeff (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ ab ∈ D.filter (fun ab => ab.1*ab.2=n), F ab) = coeff n / n := by
    rw [fiber n hn, coeff, mul_comm character, ArithmeticFunction.mul_apply, sum_div]
    apply sum_congr rfl
    rintro ⟨a,b⟩ hab
    obtain ⟨hab,hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    change a*b=n at hab
    have ha : a ≠ 0 := by intro h; simp [h] at hab; omega
    rw [← hab, Nat.cast_mul]
    simp [F, charTerm, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne ha]
    <;> ring
  have tri (a : ℕ) (ha : a ∈ Icc 1 N) :
      (Icc 1 N).filter (fun b => a*b≤N) = Icc 1 (N/a) := by
    ext b
    have h := (mem_Icc.mp ha).1
    rw [mem_filter,mem_Icc,mem_Icc,Nat.le_div_iff_mul_le h,mul_comm b a]
    constructor
    · exact fun z => ⟨z.1.1,z.2⟩
    · intro z
      exact ⟨⟨z.1,(Nat.le_mul_of_pos_left b h).trans z.2⟩,z.2⟩
  calc
    _ ≤ (2/3:ℝ) * (harmonic N : ℝ) := by gcongr; exact_mod_cast log_add_one_le_harmonic N
    _ = ∑ a ∈ Icc 1 N, (a:ℝ)⁻¹ * (2/3) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, mul_comm, sum_mul]; push_cast; rfl
    _ ≤ ∑ a ∈ Icc 1 N, (a:ℝ)⁻¹ * ∑ b ∈ Icc 1 (N/a), charTerm b := by
      apply sum_le_sum; intro a ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply char_lower
      exact (Nat.le_div_iff_mul_le (mem_Icc.mp ha).1).2 (by simpa using (mem_Icc.mp ha).2)
    _ = ∑ ab ∈ D, F ab := by
      dsimp only [D]
      rw [sum_filter, sum_product]
      refine sum_congr rfl fun a ha => ?_
      rw [← tri a ha, mul_sum, sum_filter]
    _ = ∑ n ∈ Icc 1 N, coeff n / n := by
      rw [← sum_fiberwise_of_maps_to maps F]
      exact sum_congr rfl hcoeff


def densityWeight (n : ℕ) : ℝ := coeff n / n

theorem weight_nonneg (n : ℕ) : 0 ≤ densityWeight n := div_nonneg (coeff_nonneg n) (Nat.cast_nonneg n)

theorem weight_power (p j : ℕ) : densityWeight (p^j) = coeff (p^j)*((p:ℝ)⁻¹)^j := by
  simp [densityWeight,div_eq_mul_inv]

theorem prime_majorant (p j : ℕ) (hp : p.Prime) :
    densityWeight (p^j) ≤ (if p=2 then (p:ℝ)⁻¹ else 2*(p:ℝ)⁻¹)^j := by
  rw [weight_power,prime_coeff_values p j hp]
  by_cases h : p=2
  · simp [h]
  · simp only [h,ite_false,mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hj : (j+1:ℝ) ≤ 2^j := by
      induction j with
      | zero => norm_num
      | succ j hj => rw [pow_succ]; push_cast; linarith [one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=j)]
    split_ifs <;> push_cast <;> first | linarith | positivity

theorem weight_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => densityWeight (p^j)) := by
  let t : ℝ := if p=2 then (p:ℝ)⁻¹ else 2*(p:ℝ)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; split <;> positivity
  have hl : t < 1 := by
    dsimp [t]; split_ifs with h
    · norm_num [h]
    · have hp2 : 2<p := by have := hp.two_le; omega
      have hpr : (2:ℝ)<p := by exact_mod_cast hp2
      rw [← div_eq_mul_inv, div_lt_one (by positivity : (0:ℝ)<p)]
      exact hpr
  exact (summable_geometric_of_lt_one ht hl).of_nonneg_of_le
    (fun j => weight_nonneg _) (fun j => prime_majorant p j hp)

theorem local_two : (∑' j : ℕ, densityWeight (2^j)) = 2 := by
  calc _ = ∑' j : ℕ, ((2:ℝ)⁻¹)^j := tsum_congr (fun j => by
          rw [weight_power, prime_coeff_values 2 j Nat.prime_two]; norm_num)
       _ = 2 := tsum_geometric_inv_two

theorem local_split {p : ℕ} (hp : p.Prime) (h4 : p % 4=1) :
    (∑' j : ℕ, densityWeight (p^j)) ≤ 1+CentralSelberg.wgt 2 p := by
  have h2 : p≠2 := by omega
  have hp2 : 2<p := by have := hp.two_le; omega
  have hpr : (2:ℝ)<p := by exact_mod_cast hp2
  have hp0 : 0<(p:ℝ) := by positivity
  have hlt : 2*(p:ℝ)⁻¹ < 1 := by rw [← div_eq_mul_inv,div_lt_one hp0]; exact hpr
  have h := (weight_summable hp).tsum_le_tsum
    (fun j => (prime_majorant p j hp).trans_eq (by simp [h2]))
    (summable_geometric_of_lt_one (by positivity : 0≤2*(p:ℝ)⁻¹) hlt)
  rw [tsum_geometric_of_lt_one (by positivity) hlt] at h
  apply h.trans_eq
  have hn : ¬p ∣ 2 := fun h => (Nat.le_of_dvd (by decide) h).not_gt hp2
  unfold CentralSelberg.wgt CentralSelberg.rho
  rw [goldbachSieveDensity_prime 2 p hp, if_neg hn,div_eq_mul_inv]
  field_simp [show 1-2*(p:ℝ)⁻¹≠0 by linarith]
  <;> ring

theorem local_inert {p : ℕ} (hp : p.Prime) (h2 : p≠2) (h4 : p % 4≠1) :
    (∑' j : ℕ, densityWeight (p^j)) ≤ 1 + 2/(p:ℝ)^2 := by
  let t : ℝ := (p:ℝ)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ht2 : t ≤ 1/2 := by dsimp [t]; rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hl : t<1 := by linarith
  have hs := weight_summable hp
  have major (j : ℕ) : densityWeight (p^(j+2)) ≤ t^j * t^2 := by
    rw [weight_power,prime_coeff_values p (j+2) hp,if_neg h2,if_neg h4, pow_add]
    change (if Even (j+2) then (1:ℝ) else 0)*(t^j*t^2) ≤ _
    split <;> simp [mul_nonneg (pow_nonneg ht _) (sq_nonneg t)]
  have hm := ((summable_nat_add_iff 2).2 hs).tsum_le_tsum major
    ((summable_geometric_of_lt_one ht hl).mul_right _)
  rw [tsum_mul_right,tsum_geometric_of_lt_one ht hl] at hm
  have hc : (1-t)⁻¹ ≤ 2 := by
    rw [← one_div,div_le_iff₀ (by linarith)]
    linarith
  have hfirst : (∑ j ∈ range 2, densityWeight (p^j)) = 1 := by
    simp [Finset.sum_range_succ, weight_power,prime_coeff_values p _ hp,h2,h4,
      densityWeight, coeff_mult.map_one]
  rw [← hs.sum_add_tsum_nat_add 2, hfirst]
  apply add_le_add_right
  apply hm.trans
  calc (1-t)⁻¹ * t^2 ≤ 2*t^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
       _ = _ := by simp [t,div_eq_mul_inv]

/-! Only the split primes contribute a first-order term to the Euler product.
The remaining factors are controlled by the convergent sum of inverse squares. -/

def eulerConstant := 2*Real.exp (∑' m : ℕ, 2/(m:ℝ)^2)

theorem eulerConstant_pos : 0 < eulerConstant := by unfold eulerConstant; positivity

theorem euler_lower (y : ℕ) :
    (2/3:ℝ)*Real.log ((y:ℝ)+1) ≤ eulerConstant *
      ∏ p ∈ y.primesLE.filter (fun p => p % 4=1), (1+CentralSelberg.wgt 2 p) := by
  have hE := smooth_sum_le_euler_product densityWeight weight_nonneg
    (by simp [densityWeight, coeff_mult.map_one])
    (fun hc => by simp only [densityWeight, coeff_mult.2 hc,Nat.cast_mul,mul_div_mul_comm])
    (fun hp => by simpa only [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg _)] using weight_summable hp)
    (y+1) (Icc 1 y) (fun n hn => Nat.mem_smoothNumbers_of_lt (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega))
  let g := fun p : ℕ => if p % 4=1 then 1+CentralSelberg.wgt 2 p else (1:ℝ)
  let h := fun p : ℕ => if p=2 then (2:ℝ) else 1
  let b := fun p : ℕ => 2/(p:ℝ)^2
  have hg (p : ℕ) (hp : p.Prime) : 1 ≤ g p := by
    dsimp [g]; split <;> linarith [CentralSelberg.wgt_pos 2 (dvd_refl _) p hp]
  have hb (p : ℕ) : 1+b p ≤ Real.exp (b p) := by linarith [Real.add_one_le_exp (b p)]
  have hb0 (p : ℕ) : 0 ≤ b p := by dsimp [b]; positivity
  have hloc (p : ℕ) (hp : p.Prime) :
      (∑' j : ℕ, densityWeight (p^j)) ≤ h p * Real.exp (b p) * g p := by
    have h1 : 1 ≤ Real.exp (b p) := (Real.one_le_exp_iff.mpr (hb0 p))
    by_cases h2 : p=2
    · subst p; rw [local_two]; simp only [h,ite_true]; nlinarith [hg 2 Nat.prime_two, mul_le_mul_of_nonneg_left (hg 2 Nat.prime_two) (Real.exp_pos (b 2)).le]
    · by_cases h4 : p % 4=1
      · apply (local_split hp h4).trans
        simp only [h,h2,ite_false,one_mul,g,h4,ite_true]
        exact le_mul_of_one_le_left (by linarith [CentralSelberg.wgt_pos 2 (dvd_refl _) p hp]) h1
      · simpa [h,h2,g,h4,b] using (local_inert hp h2 h4).trans (hb p)
  have htwo : (∏ p ∈ y.primesLE, h p) ≤ 2 := by
    dsimp [h]; rw [prod_ite_eq']; split <;> norm_num
  have hbS : Summable b := by
    simpa only [b,div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).mul_left (2:ℝ)
  have hsum := hbS.sum_le_tsum y.primesLE (fun n _ => hb0 n)
  have hgP : 0 ≤ ∏ p ∈ y.primesLE, g p :=
    prod_nonneg fun p hp => (zero_le_one.trans (hg p (Nat.prime_of_mem_primesLE hp)))
  calc
    _ ≤ _ := coeff_harmonic_lower y
    _ ≤ ∏ p ∈ y.primesLE, ∑' j : ℕ, densityWeight (p^j) := hE
    _ ≤ ∏ p ∈ y.primesLE, (h p * Real.exp (b p) * g p) :=
      Finset.prod_le_prod₀ (fun _ _ => tsum_nonneg fun _ => weight_nonneg _) (fun p hp => hloc p (Nat.prime_of_mem_primesLE hp))
    _ = ((∏ p ∈ y.primesLE, h p)*Real.exp (∑ p ∈ y.primesLE, b p))*(∏ p ∈ y.primesLE, g p) := by
      rw [prod_mul_distrib,prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := by
      unfold eulerConstant
      rw [Finset.prod_filter]
      apply mul_le_mul_of_nonneg_right _ hgP
      exact mul_le_mul htwo (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le (by norm_num)


open Filter in
theorem upper_of_mass (A : ℝ) (hA : 0<A)
    (hMass : ∀ y : ℕ, (2/3:ℝ)*Real.log ((y:ℝ)+1) ≤ A*splitMass 2 y) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x p r : ℕ, N≤x → p.Prime → Nat.nthRoot 5 (x^2) < p → p ≤ 5 * Nat.nthRoot 3 (x^2) → r < p → (4*r^2+1)%p=0 → (((Finset.range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p).card : ℝ) ≤ C*x/(p*Real.log x) := by
  obtain ⟨M,hM⟩ := eventually_atTop.1 CentralSelberg.scales
  have logEventually := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  obtain ⟨L,hL⟩ := eventually_atTop.1 logEventually
  let K := max 125 (max M L)
  refine ⟨2*(384*A+72),by positivity,125*K^3+2,?_⟩
  intro x p r hx hp hlo hup _ _
  let n := x/p+1
  have hx0 : 0<x := by omega
  have hx2 : 2≤x := by omega
  have hn0 : 0<n := Nat.succ_pos _
  have hxnp : x < n*p := (Nat.div_lt_iff_lt_mul hp.pos).1 (Nat.lt_succ_self _)
  have hp3 : p^3 ≤ 125*x^2 := by
    calc _ ≤ (5*Nat.nthRoot 3 (x^2))^3 := Nat.pow_le_pow_left hup _
         _ = 125*(Nat.nthRoot 3 (x^2))^3 := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le_iff.mpr (.inl (by decide)))
  have hxScale : x ≤ 125*n^3 := by
    have H : x^2*x ≤ x^2*(125*n^3) := calc
      _ = x^3 := by ring
      _ ≤ (n*p)^3 := Nat.pow_le_pow_left hxnp.le _
      _ = n^3*p^3 := mul_pow _ _ _
      _ ≤ n^3*(125*x^2) := Nat.mul_le_mul_left _ hp3
      _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left H (by positivity)
  have hKn : K≤n := by
    by_contra! hn
    have := Nat.mul_le_mul_left 125 (Nat.pow_le_pow_left hn.le 3)
    omega
  have h125 : 125≤n := (le_max_left _ _).trans hKn
  have hMn : M≤n := (le_max_left M L).trans ((le_max_right 125 _).trans hKn)
  have hLn : L≤n := (le_max_right M L).trans ((le_max_right 125 _).trans hKn)
  have hlog : 1 ≤ Real.log (n:ℝ) := hL n hLn
  have hx4 : x≤n^4 := hxScale.trans (by calc
    125*n^3 ≤ n*n^3 := Nat.mul_le_mul_right _ h125
    _ = _ := by ring)
  have hlogx : Real.log (x:ℝ) ≤ 4*Real.log (n:ℝ) := by
    have H := Real.log_le_log (by exact_mod_cast hx0 : 0<(x:ℝ)) (by exact_mod_cast hx4 : (x:ℝ)≤(n:ℝ)^4)
    simpa using H
  obtain ⟨y,hy,hny,herr⟩ := hM n hMn
  let z := y^8
  let E := (z:ℝ)^2*(1+Real.log (z:ℝ))^4
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by omega : 0<y)
  have hzlog : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast hz)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he2 : E * (Real.log n)^2 ≤ 18*n := by
    exact (mul_le_mul_of_nonneg_right (show E ≤ E+2*y from le_add_of_nonneg_right (by positivity)) (sq_nonneg _)).trans herr
  have he : E*Real.log n ≤ 18*n := (mul_le_mul_of_nonneg_left
    (by rw [sq]; exact le_mul_of_one_le_right (by linarith only [hlog]) hlog : Real.log (n:ℝ) ≤ (Real.log n)^2) hE).trans he2
  have hE18 : E ≤ 18*n := (le_mul_of_one_le_right hE hlog).trans he
  have h16 : y^16 ≤ 18*n := by
    have hh : (y:ℝ)^16 ≤ E := by
      calc _ = (z:ℝ)^2 := by dsimp [z]; push_cast; ring
           _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (by linarith : 1≤1+Real.log (z:ℝ)))
    exact_mod_cast hh.trans hE18
  have hpx : x^2 < p^5 := (Nat.nthRoot_lt_iff (by decide : 5≠0)).mp hlo
  have hn5 : n ≤ p^5 := by
    have hnx : n ≤ x+1 := Nat.succ_le_succ (Nat.div_le_self _ _)
    have : x ≤ x^2 := Nat.le_self_pow (by decide : 2 ≠ 0) x
    omega
  have hyp : y < p := by
    by_contra! h
    have H := Nat.pow_le_pow_left h 16
    have h11 := Nat.pow_le_pow_left hp.two_le 11
    have hbig : 18*p^5 < p^16 := calc
      _ < p^11*p^5 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos 5)
      _ = _ := by ring
    omega
  let D := GoldbachSelberg.denominator 2 (wheel y) z
  have hD : 0<D := GoldbachSelberg.denominator_pos 2 _ (dvd_refl _) (wheel_sq y) hz
  have hret := split_retained 2 y (dvd_refl _) hy
  have hDA := (hMass y).trans (mul_le_mul_of_nonneg_left hret hA.le)
  have hxD : Real.log (x:ℝ) ≤ (384*A)*D := by
    dsimp only [D,z]
    linarith only [hDA,hny,hlogx]
  have main : ((n:ℝ)/D)*Real.log x ≤ (384*A)*n := by
    have H := mul_le_mul_of_nonneg_left hxD (show 0 ≤ (n:ℝ)/D by positivity)
    convert H using 1
    field_simp
  have err : E*Real.log x ≤ 72*n := by
    linarith only [he, mul_le_mul_of_nonneg_left hlogx hE]
  have H := finite_upper n p r y z hp hyp hz
  let T := (range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p
  have sub : T ⊆ (range n).filter (fun t => (wheel y).Coprime (value p r t)) := by
    intro t ht
    obtain ⟨_,_,hk,hfac⟩ := mem_filter.mp ht
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp.pos).2 (by
      simpa only [mul_comm t p] using (show p*t≤x by omega)))),?_⟩
    unfold wheel
    rw [Nat.coprime_prod_left_iff]
    intro q hq
    apply (mem_split hq).1.coprime_iff_not_dvd.mpr
    intro hd
    have Hq := Nat.minFac_le_of_dvd (mem_split hq).1.two_le hd
    change (value p r t).minFac=p at hfac
    rw [hfac] at Hq
    have := (mem_split hq).2.1
    omega
  have hcard : (T.card:ℝ) ≤ n/D+E := (Nat.cast_le.mpr (card_le_card sub)).trans H
  have hxlog : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (show 1<x by omega))
  have hmid : (T.card:ℝ)*Real.log x ≤ (384*A+72)*n := by
    nlinarith only [mul_le_mul_of_nonneg_right hcard hxlog.le,main,err]
  have hpx' : p ≤ x := by
    have H : 1 ≤ x/p := by dsimp [n] at h125; omega
    simpa using (Nat.le_div_iff_mul_le hp.pos).mp H
  have hnp : n*p ≤ 2*x := by
    dsimp [n]; rw [Nat.add_mul,one_mul]
    have := Nat.div_mul_le_self x p
    omega
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast hp.pos) hxlog)).2
  change T.card * ((p:ℝ)*Real.log x) ≤ _
  have hnpr : (n:ℝ)*p ≤ 2*x := by exact_mod_cast hnp
  nlinarith only [mul_le_mul_of_nonneg_right hmid (Nat.cast_nonneg p),
    mul_le_mul_of_nonneg_left hnpr (by positivity : 0≤384*A+72)]

end
end Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux

open Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux in
theorem Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieve :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x p r : ℕ, N≤x → p.Prime → Nat.nthRoot 5 (x^2) < p → p ≤ 5 * Nat.nthRoot 3 (x^2) → r < p → (4*r^2+1)%p=0 → (((Finset.range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p).card : ℝ) ≤ C*x/(p*Real.log x) :=
  upper_of_mass eulerConstant eulerConstant_pos euler_lower
