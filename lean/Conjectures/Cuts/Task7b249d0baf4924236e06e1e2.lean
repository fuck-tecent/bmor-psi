import Mathlib
import Conjectures.Goldbach.Type2FixedTargetReciprocalError

/-!
# Divisor bound for close cofactor pairs

The reference proof below specializes its uniform counting bound to the first
Type-II band and retains the original wide-arc mask in the final equivalence.
The dependency is Y-nuclear's Apache-2.0 contribution in goldbach-proofs PR 3253,
commit 35c37addd4a46ffcef40c7c4b91ae538d24a86db. We use its finite Fourier
coefficient formula, divisor estimate, and masked prime-power reduction.
The one-row congruence argument is adapted from that contribution.
-/

namespace GoldbachFirstCorner

open Filter Topology GoldbachTransitionSquare
open Finset MeasureTheory
noncomputable section

private def residualSize (n s p : ℕ) : ℕ := ((n : ℤ) - s * p).natAbs

private theorem close_factors {n B D a b p q : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hbB : b ≤ B) (heq : a*p + b*q = n) (hnear : |(p : ℤ) - q| ≤ D) (hne : p ≠ q) :
    n / (a+b) - D ≤ p ∧ p ≤ n / (a+b) + D ∧
    0 < residualSize n (a+b) p ∧ residualSize n (a+b) p ≤ B*D ∧
    b ∣ residualSize n (a+b) p := by
  have hgap := abs_le.mp hnear
  have hpq : p-D ≤ q := by omega
  have hqp : q ≤ p+D := by omega
  have hs : 0 < a+b := by omega
  have hl : p-D ≤ n/(a+b) := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    rw [← heq, mul_comm (p-D), add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le ..)) (Nat.mul_le_mul_left _ hpq)
  have hu : n/(a+b) ≤ p+D := by
    have hu' : n ≤ (a+b)*(p+D) := by
      rw [← heq, add_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hqp)
    exact (Nat.div_le_div_right hu').trans_eq (Nat.mul_div_cancel_left _ hs)
  have hres : residualSize n (a+b) p = b * ((q : ℤ) - p).natAbs := by
    unfold residualSize
    rw [← heq]
    push_cast
    rw [show (a : ℤ)*p + b*q - (a+b)*p = b*(q-p) by ring, Int.natAbs_mul, Int.natAbs_natCast]
  have habs : ((q : ℤ) - p).natAbs ≤ D := by
    exact_mod_cast (show (↑((q : ℤ) - p).natAbs : ℤ) ≤ D by
      rw [Int.natCast_natAbs, abs_sub_comm]; exact hnear)
  have hnz : 0 < ((q : ℤ) - p).natAbs := Int.natAbs_pos.mpr (by omega)
  rw [hres]
  exact ⟨by omega, by omega, Nat.mul_pos hb hnz, Nat.mul_le_mul hbB habs, dvd_mul_right ..⟩

/-- Off the diagonal a+b and p determine a nonzero integer with b as a divisor. -/
private theorem offDiagonal_card {n B D T : ℕ} (S : Finset Representation)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B*D → m.divisors.card ≤ T)
    (hspec : ∀ r ∈ S, 0 < r.a ∧ r.a ≤ B ∧ 0 < r.b ∧ r.b ≤ B ∧
      r.a*r.p + r.b*r.q = n ∧ |(r.p:ℤ)-r.q| ≤ D ∧ r.p ≠ r.q) :
    S.card ≤ (2*B) * (2*D+1) * T := by
  classical
  let centers (s : ℕ) := Icc (n/s-D) (n/s+D)
  let divisors (s p : ℕ) := if 0 < residualSize n s p ∧ residualSize n s p ≤ B*D
    then (residualSize n s p).divisors else ∅
  let box := (Icc 1 (2*B)).sigma fun s => (centers s).sigma (divisors s)
  let code (r : Representation) : Σ _s : ℕ, Σ _p : ℕ, ℕ := ⟨r.a+r.b, ⟨r.p,r.b⟩⟩
  have into (r : Representation) (hr : r ∈ S) : code r ∈ box := by
    obtain ⟨ha, ha', hb, hb', heq, hgap, hne⟩ := hspec r hr
    obtain ⟨hl, hu, hpos, hcap, hdvd⟩ := close_factors ha hb hb' heq hgap hne
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨by dsimp [code]; omega, by dsimp [code]; omega⟩,
      mem_sigma.mpr ⟨mem_Icc.mpr ⟨hl,hu⟩, ?_⟩⟩
    change r.b ∈ divisors (r.a+r.b) r.p
    dsimp only [divisors]
    rw [ite_eq_left ⟨hpos,hcap⟩]
    exact Nat.mem_divisors.mpr ⟨hdvd,hpos.ne'⟩
  have hinj : Set.InjOn code (S : Set Representation) := by
    intro r hr u hu he
    obtain ⟨a,b,p,q⟩ := r
    obtain ⟨a',b',p',q'⟩ := u
    have hs := congrArg (fun i => i.1) he
    have hp := congrArg (fun i => i.2.1) he
    have hb := congrArg (fun i => i.2.2) he
    change a+b = a'+b' at hs
    change p = p' at hp
    change b = b' at hb
    subst p'; subst b'
    have ha : a=a' := by omega
    subst a'
    have h₁ := hspec _ hr
    have h₂ := hspec _ hu
    have hs₁ : a*p+b*q=n := h₁.2.2.2.2.1
    have hs₂ : a*p+b*q'=n := h₂.2.2.2.2.1
    have hbpos : 0 < b := h₁.2.2.1
    have hq : q=q' := Nat.eq_of_mul_eq_mul_left hbpos (Nat.add_left_cancel (hs₁.trans hs₂.symm))
    subst q'
    rfl
  have hcount (s p : ℕ) : (divisors s p).card ≤ T := by
    unfold divisors
    split_ifs with h
    · exact hdiv _ h.1 h.2
    · simp
  have hcenters (s : ℕ) : (centers s).card ≤ 2*D+1 := by
    dsimp only [centers]
    rw [Nat.card_Icc]; omega
  refine (card_le_card_of_injOn code into hinj).trans ?_
  unfold box
  rw [card_sigma]
  calc
    _ ≤ ∑ s ∈ Icc 1 (2*B), (2*D+1)*T := by
      apply sum_le_sum
      intro s _
      rw [card_sigma]
      calc
        _ ≤ ∑ _p ∈ centers s, T := sum_le_sum fun p _ => hcount s p
        _ = (centers s).card*T := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (hcenters s)
    _ = _ := by simp [Nat.card_Icc, Nat.mul_assoc]

theorem divisor_near_card {n B D T : ℕ} (S : Finset Representation)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B*D → m.divisors.card ≤ T)
    (hspec : ∀ r ∈ S, 0 < r.a ∧ r.a ≤ B ∧ 0 < r.b ∧ r.b ≤ B ∧
      r.a*r.p+r.b*r.q=n ∧ |(r.p:ℤ)-r.q| ≤ D) :
    S.card ≤ min (B^2*(2*D+1)) (B^2 + 2*B*(2*D+1)*T) := by
  classical
  refine le_min (representation_card_near S hspec) ?_
  let diag := S.filter fun r => r.p=r.q
  let off := S.filter fun r => r.p≠r.q
  have hd : diag.card ≤ B^2 := by
    have h := representation_card_near (n:=n) (B:=B) (D:=0) diag (by
      intro r hr
      obtain ⟨hm,he⟩ := mem_filter.mp hr
      obtain ⟨ha,ha',hb,hb',hs,_⟩ := hspec r hm
      exact ⟨ha,ha',hb,hb',hs,by simp [he]⟩)
    simpa using h
  have ho : off.card ≤ 2*B*(2*D+1)*T := by
    apply offDiagonal_card off hdiv
    intro r hr
    obtain ⟨hm,he⟩ := mem_filter.mp hr
    obtain ⟨ha,ha',hb,hb',hs,hg⟩ := hspec r hm
    exact ⟨ha,ha',hb,hb',hs,hg,he⟩
  have heq : diag.card + off.card = S.card := card_filter_add_card_filter_not ..
  omega

def nearSolutions (n B D : ℕ) (P : Finset ℕ) :=
  (((P ×ˢ P).filter (fun pq : ℕ × ℕ => |(pq.1 : ℤ) - pq.2| ≤ D)) ×ˢ
    (Icc 1 B ×ˢ Icc 1 B)).filter (fun z => z.2.1*z.1.1 + z.2.2*z.1.2 = n)

private def asRep (z : (ℕ × ℕ) × ℕ × ℕ) : Representation :=
  ⟨z.2.1, z.2.2, z.1.1, z.1.2⟩

private theorem asRep_injective : Function.Injective asRep := by
  rintro ⟨⟨p,q⟩,a,b⟩ ⟨⟨u,v⟩,i,j⟩ he
  simpa [asRep, and_assoc, and_left_comm, and_comm] using he

theorem weighted_near (n B D T : ℕ) (P : Finset ℕ) (c : ℕ → ℕ → ℂ) (M : ℝ)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B*D → m.divisors.card ≤ T)
    (hweight : ∀ p ∈ P, ∀ a ∈ Icc 1 B, ‖c p a‖ ≤ M) :
    ‖∑ z ∈ nearSolutions n B D P, c z.1.1 z.2.1 * c z.1.2 z.2.2‖ ≤
      ((min (B^2*(2*D+1)) (B^2 + 2*B*(2*D+1)*T) : ℕ) : ℝ) * M^2 := by
  classical
  let S := nearSolutions n B D P
  have hcard : S.card ≤ min (B^2*(2*D+1)) (B^2 + 2*B*(2*D+1)*T) := by
    rw [← card_image_of_injective S asRep_injective]
    apply divisor_near_card _ hdiv
    intro r hr
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
    obtain ⟨hm, he⟩ := mem_filter.mp hz
    obtain ⟨hpq, hab⟩ := mem_product.mp hm
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    exact ⟨(mem_Icc.mp ha).1, (mem_Icc.mp ha).2, (mem_Icc.mp hb).1,
      (mem_Icc.mp hb).2, he, (mem_filter.mp hpq).2⟩
  calc
    _ ≤ ∑ z ∈ S, ‖c z.1.1 z.2.1 * c z.1.2 z.2.2‖ := norm_sum_le ..
    _ ≤ ∑ _z ∈ S, M^2 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hpq,hab⟩ := mem_product.mp (mem_filter.mp hz).1
      obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hpq).1
      obtain ⟨ha,hb⟩ := mem_product.mp hab
      rw [norm_mul, pow_two]
      exact mul_le_mul (hweight _ hp _ ha) (hweight _ hq _ hb) (norm_nonneg _)
        ((norm_nonneg _).trans (hweight _ hp _ ha))
    _ = (S.card : ℝ) * M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

theorem near_fullCircle (n B D : ℕ) (P : Finset ℕ) (c : ℕ → ℕ → ℂ)
    (hzero : ∀ p, c p 0 = 0) :
    (∫ t in (0 : ℝ)..1, pairRows (closePairs P D) (B+1) n c t) =
    ∑ z ∈ nearSolutions n B D P, c z.1.1 z.2.1 * c z.1.2 z.2.2 := by
  classical
  rw [full_pairRows]
  let Q := closePairs P D
  let A := (Q ×ˢ (range (B+1) ×ˢ range (B+1))).filter
    (fun z => z.2.1*z.1.1 + z.2.2*z.1.2 = n)
  change (∑ z ∈ A, c z.1.1 z.2.1 * c z.1.2 z.2.2) = _
  symm
  apply sum_subset
  · intro z hz
    obtain ⟨hm,he⟩ := mem_filter.mp hz
    obtain ⟨hpq,hab⟩ := mem_product.mp hm
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hpq, mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp ha).2),
       mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hb).2)⟩⟩, he⟩
  · intro z hz hout
    obtain ⟨hm,he⟩ := mem_filter.mp hz
    obtain ⟨hpq,hab⟩ := mem_product.mp hm
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    by_cases haz : z.2.1 = 0
    · rw [haz,hzero,zero_mul]
    by_cases hbz : z.2.2 = 0
    · rw [hbz,hzero,mul_zero]
    exact (hout (mem_filter.mpr ⟨mem_product.mpr ⟨hpq, mem_product.mpr
      ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero haz,Nat.le_of_lt_succ (mem_range.mp ha)⟩,
       mem_Icc.mpr ⟨Nat.pos_of_ne_zero hbz,Nat.le_of_lt_succ (mem_range.mp hb)⟩⟩⟩,he⟩)).elim

/-- Both divisor cutoffs in this integral are those of the first band.
The denominators in the arc mask still run up to the cube root. -/
def firstIntegral (n : ℕ) (weight : ℕ → ℝ) : ℂ :=
  let coefficients := band (cutoffU n) (cutoffU n) (cutoffL n) weight
  pairIntegral (deep n) n coefficients coefficients

theorem cofactor_error :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖firstIntegral n ArithmeticFunction.vonMangoldt -
        firstIntegral n (largePrimeWeight n)‖ ≤ K * (n : ℝ) ^ (31 / 32 : ℝ) := by
  obtain ⟨K, hK, hmask⟩ := transition_power_saving
  refine ⟨K, hK, fun n hn => ?_⟩
  have hreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcut : (cutoffL n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hreal (by norm_num))
  have h := hmask n (cutoffU n) (cutoffU n) (cutoffL n) hn hcut
    (deep n) (wide_measurable ..).compl
  simpa only [firstIntegral, full, core, show (124 / 128 : ℝ) = 31 / 32 by norm_num] using h

theorem sublinear_cofactor_error (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖firstIntegral n ArithmeticFunction.vonMangoldt -
        firstIntegral n (largePrimeWeight n)‖ ≤ ε * (n : ℝ) := by
  obtain ⟨K, _, hK⟩ := cofactor_error
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(1 / 32) : ℝ)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, mul_zero] using (tendsto_const_nhds (x := K)).mul hp
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_lt_const hε] with n hn hsmall
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  calc
    _ ≤ K * (n : ℝ) ^ (31 / 32 : ℝ) := hK n hn
    _ = (K * (n : ℝ) ^ (-(1 / 32) : ℝ)) * (n : ℝ) := by
      rw [mul_assoc, show (31 / 32 : ℝ) = -(1 / 32 : ℝ) + 1 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hpos.le

/-- On every sufficiently large even target, the full first-corner estimate is
equivalent to the one in which both complementary factors are primes above √n. -/
theorem first_corner_iff_large_primes :
    smallEven (fun n => firstIntegral n ArithmeticFunction.vonMangoldt) ↔
    smallEven (fun n => firstIntegral n (largePrimeWeight n)) := by
  constructor
  · apply smallEven_transfer
    intro ε hε
    filter_upwards [sublinear_cofactor_error ε hε] with n hn
    simpa only [norm_sub_rev (firstIntegral n (largePrimeWeight n))
      (firstIntegral n ArithmeticFunction.vonMangoldt)] using hn
  · exact smallEven_transfer sublinear_cofactor_error

/-- The contribution of fixed cofactor primes to the full-circle coefficient at n. -/
def rowMass (n B : ℕ) (c : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  ∑ ab ∈ range (B + 1) ×ˢ range (B + 1),
    if ab.1 * p + ab.2 * q = n then c p ab.1 * c q ab.2 else 0

/-- For distinct cofactor primes, the short multiplier on the p-side is fixed
by n times the inverse of p modulo q. The bound B < q makes this unique. -/
private theorem rowMass_eq_inversePair {n B p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hB : B < q) (c : ℕ → ℕ → ℂ) :
    rowMass n B c p q = inversePair n B c p q := by
  classical
  let a := inverseResidue n p q
  let b := partnerFactor n p q
  let hits := (range (B + 1) ×ˢ range (B + 1)).filter
    (fun ab : ℕ × ℕ => ab.1 * p + ab.2 * q = n)
  have unique {ab : ℕ × ℕ} (hm : ab ∈ hits) : ab = (a, b) := by
    obtain ⟨hab, heq⟩ := mem_filter.mp hm
    have ha := (Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hab).1)).trans_lt hB
    obtain ⟨h₁, h₂⟩ := resonance_inverse hp hq hne ha heq
    exact Prod.ext h₁ h₂
  unfold rowMass
  rw [← sum_filter]
  change (∑ ab ∈ hits, c p ab.1 * c q ab.2) =
    if a ≤ B ∧ b ≤ B ∧ a * p + b * q = n then c p a * c q b else 0
  by_cases h : a ≤ B ∧ b ≤ B ∧ a * p + b * q = n
  · rw [ite_eq_left h]
    have hm : (a, b) ∈ hits := mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le h.1), mem_range.mpr (Nat.lt_succ_of_le h.2.1)⟩, h.2.2⟩
    exact sum_eq_single_of_mem (a, b) hm fun ab hab hne' => (hne' (unique hab)).elim
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro ab hab
    obtain rfl := unique hab
    obtain ⟨hi, heq⟩ := mem_filter.mp hab
    exact (h ⟨Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hi).1),
      Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hi).2), heq⟩).elim

def firstRow (n : ℕ) := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)

def primePairMass (n : ℕ) : ℂ :=
  ∑ pq ∈ bigPrimes n ×ˢ bigPrimes n,
    if pq.1 = pq.2 then rowMass n (cutoffL n) (firstRow n) pq.1 pq.2
    else inversePair n (cutoffL n) (firstRow n) pq.1 pq.2

def widePrimePairMass (n : ℕ) : ℂ :=
  arcRows (wide n (cutoffB n) (arcHeight n)) (bigPrimes n ×ˢ bigPrimes n)
    (cutoffL n + 1) n (firstRow n)

private theorem fourthRoot_le_sqrt {n : ℕ} (hn : 1 ≤ n) : cutoffL n ≤ n.sqrt := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (cutoffL n : ℝ) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffL n) (α := ℝ)) hr 2
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  exact Nat.le_sqrt'.mpr (by exact_mod_cast hh)

theorem core_eq_discrepancy (n : ℕ) (hn : 1 ≤ n) :
    firstIntegral n (largePrimeWeight n) = primePairMass n - widePrimePairMass n := by
  classical
  let P := bigPrimes n
  let B := cutoffL n
  let c := firstRow n
  let W := wide n (cutoffB n) (arcHeight n)
  have hcoeff : (∫ t in (0 : ℝ)..1, pairRows (P ×ˢ P) (B + 1) n c t) = primePairMass n := by
    rw [full_pairRows, sum_filter]
    change (∑ i ∈ (P ×ˢ P) ×ˢ (range (B + 1) ×ˢ range (B + 1)),
      if i.2.1 * i.1.1 + i.2.2 * i.1.2 = n then c i.1.1 i.2.1 * c i.1.2 i.2.2 else 0) = _
    rw [sum_product]
    apply sum_congr rfl
    intro pq hpq
    by_cases heq : pq.1 = pq.2
    · simp only [ite_eq_left heq]
      rfl
    · rw [ite_eq_right heq]
      obtain ⟨hp, hq⟩ := mem_product.mp hpq
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      exact rowMass_eq_inversePair hp'.2 hq'.2 heq ((fourthRoot_le_sqrt hn).trans_lt hq'.1) c
  change pairIntegral Wᶜ n (core n (cutoffU n) (cutoffU n) B)
    (core n (cutoffU n) (cutoffU n) B) = _
  rw [core_square_rows Wᶜ (wide_measurable ..).compl]
  exact eq_sub_iff_add_eq.mpr ((arcRows_partition W (wide_measurable ..)
    (P ×ˢ P) (B + 1) n c).trans hcoeff)

theorem full_error_from_discrepancy :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖firstIntegral n ArithmeticFunction.vonMangoldt -
        (primePairMass n - widePrimePairMass n)‖ ≤ K * (n : ℝ) ^ (31 / 32 : ℝ) := by
  obtain ⟨K, hK, h⟩ := cofactor_error
  exact ⟨K, hK, fun n hn => by rw [← core_eq_discrepancy n hn]; exact h n hn⟩

/-- Pairs within this distance can be discarded from the full-circle term. -/
def distanceCut (n : ℕ) := ⌊(n : ℝ) ^ (5 / 8 : ℝ)⌋₊

def distantPrimeMass (n : ℕ) : ℂ :=
  ∑ pq ∈ farPairs (bigPrimes n) (distanceCut n),
    inversePair n (cutoffL n) (firstRow n) pq.1 pq.2

private theorem fullCircle_rows (edges : Finset (ℕ × ℕ)) (B n : ℕ) (c : ℕ → ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, pairRows edges (B + 1) n c t) =
    ∑ pq ∈ edges, rowMass n B c pq.1 pq.2 := by
  rw [full_pairRows, sum_filter]
  change (∑ i ∈ edges ×ˢ (range (B + 1) ×ˢ range (B + 1)),
    if i.2.1 * i.1.1 + i.2.2 * i.1.2 = n then c i.1.1 i.2.1 * c i.1.2 i.2.2 else 0) = _
  rw [sum_product]
  rfl

private theorem nearPairMass_eq (n : ℕ) (hn : 1 ≤ n) :
    primePairMass n - distantPrimeMass n =
      ∫ t in (0 : ℝ)..1, pairRows (closePairs (bigPrimes n) (distanceCut n))
        (cutoffL n + 1) n (firstRow n) t := by
  classical
  let P := bigPrimes n
  let D := distanceCut n
  let f := fun pq : ℕ × ℕ => rowMass n (cutoffL n) (firstRow n) pq.1 pq.2
  have hrow (pq : ℕ × ℕ) (hm : pq ∈ P ×ˢ P) (hne : pq.1 ≠ pq.2) :
      f pq = inversePair n (cutoffL n) (firstRow n) pq.1 pq.2 := by
    obtain ⟨hp, hq⟩ := mem_product.mp hm
    exact rowMass_eq_inversePair (mem_filter.mp hp).2.2 (mem_filter.mp hq).2.2 hne
      ((fourthRoot_le_sqrt hn).trans_lt (mem_filter.mp hq).2.1) _
  have hall : (∑ pq ∈ P ×ˢ P, f pq) = primePairMass n := by
    apply sum_congr rfl
    intro pq hm
    by_cases heq : pq.1 = pq.2
    · rw [ite_eq_left heq]
    · rw [ite_eq_right heq]
      exact hrow pq hm heq
  have hfar : (∑ pq ∈ farPairs P D, f pq) = distantPrimeMass n := by
    apply sum_congr rfl
    intro pq hpq
    obtain ⟨hm, hout⟩ := mem_sdiff.mp hpq
    apply hrow pq hm
    intro heq
    exact hout (mem_filter.mpr ⟨hm, by simp [heq]⟩)
  have hsubset : closePairs P D ⊆ P ×ˢ P := filter_subset _ _
  rw [fullCircle_rows, ← hall, ← hfar]
  change (∑ i ∈ P ×ˢ P, f i) - (∑ i ∈ (P ×ˢ P) \ closePairs P D, f i) =
    ∑ i ∈ closePairs P D, f i
  rw [sub_eq_iff_eq_add, add_comm, sum_sdiff hsubset]

private theorem firstRow_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p ∈ bigPrimes n, ∀ a ≤ cutoffL n,
      ‖firstRow n p a‖ ≤ C * ((n : ℝ) ^ (1 / 64 : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hdiv⟩ := divisorPower 64 (by decide)
  let d : ℝ := 1 / 64
  have hd : 0 < d := by norm_num [d]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨64 * K ^ d, by positivity, ?_⟩
  intro n hn p hp a ha
  let X := (n : ℝ) ^ d
  have hx : 0 < X := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n from hn)) _
  have hcoef : 0 ≤ 64 * K ^ d * X ^ 2 := by positivity
  by_cases hs : (p, a) ∈ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n)
  · have haPos : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (mem_filter.mp hs).2.1
    have han : a ≤ n := ha.trans ((fourthRoot_le_sqrt hn).trans (Nat.sqrt_le_self n))
    have hbase := (hdiv a haPos).trans
      (mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ n by exact_mod_cast han) hKpos.le)
    have hpow := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg a.divisors.card) 64) hbase hd.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Real.mul_rpow hKpos.le
      (Nat.cast_nonneg n), show ((64 : ℕ) : ℝ) * d = 1 by norm_num [d], Real.rpow_one] at hpow
    have hprime := (mem_filter.mp hp).2.2
    have hpn : p ≤ n := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1)
    have hlog : Real.log p ≤ 64 * X := calc
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpn)
      _ ≤ X / d := Real.log_le_rpow_div (Nat.cast_nonneg _) hd
      _ = _ := by dsimp [d]; ring
    unfold firstRow primeRowCoeff
    rw [ite_eq_left hs]
    change ‖((lowMoebiusWeight (cutoffU n) a * Real.log p : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
    exact (mul_le_mul ((abs_lowMoebiusWeight_le ..).trans hpow) hlog
      (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (mul_nonneg (by positivity) hx.le)).trans_eq
        (by change (K ^ d * X) * (64 * X) = (64 * K ^ d) * X ^ 2; ring)
  · simpa only [firstRow, primeRowCoeff, ite_eq_right hs, norm_zero] using hcoef

theorem nearPair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖primePairMass n - distantPrimeMass n‖ ≤ C * (n : ℝ) ^ (61 / 64 : ℝ) := by
  obtain ⟨K, hK, hweight⟩ := firstRow_envelope
  obtain ⟨A, hA, hτ⟩ := divisorPower 64 (by decide)
  let d : ℝ := 1 / 64
  let V := A ^ d
  have hd : 0 < d := by norm_num [d]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hV : 0 < V := Real.rpow_pos_of_pos hApos _
  refine ⟨(1 + 6 * V) * K^2, by positivity, fun n hn => ?_⟩
  let X := (n : ℝ) ^ d
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : 1 ≤ X := Real.one_le_rpow hnR hd.le
  have hX0 := zero_le_one.trans hX
  have hpow (m : ℕ) : X ^ m = (n : ℝ) ^ ((m : ℝ) / 64) := by
    dsimp [X,d]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  have hB : (cutoffL n : ℝ) ≤ X ^ 16 := by
    rw [hpow, show ((16 : ℕ) : ℝ) / 64 = (1 / 4 : ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hD : (distanceCut n : ℝ) ≤ X ^ 40 := by
    rw [hpow, show ((40 : ℕ) : ℝ) / 64 = (5 / 8 : ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hmain : (cutoffL n : ℝ) * distanceCut n ≤ n := calc
    _ ≤ X ^ 16 * X ^ 40 := mul_le_mul hB hD (Nat.cast_nonneg _) (pow_nonneg hX0 _)
    _ = X ^ 56 := by ring
    _ ≤ X ^ 64 := pow_le_pow_right₀ hX (by decide)
    _ = _ := by rw [hpow]; norm_num
  let T := ⌊V * X⌋₊
  have hdiv (m : ℕ) (hm : 0 < m) (hlim : m ≤ cutoffL n * distanceCut n) :
      m.divisors.card ≤ T := by
    have hmn : (m : ℝ) ≤ n := (show (m : ℝ) ≤ (cutoffL n : ℝ) * distanceCut n by
      exact_mod_cast hlim).trans hmain
    have h := (hτ m hm).trans (mul_le_mul_of_nonneg_left hmn hApos.le)
    have hp := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) 64) h hd.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      Real.mul_rpow hApos.le (Nat.cast_nonneg _),
      show ((64 : ℕ) : ℝ) * d = 1 by norm_num [d], Real.rpow_one] at hp
    exact Nat.le_floor hp
  have hzero (p : ℕ) : firstRow n p 0 = 0 := by
    have hoff : (p, 0) ∉ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n) :=
      fun h => (Nat.not_lt_zero _) (mem_filter.mp h).2.1
    simp only [firstRow, primeRowCoeff, ite_eq_right hoff]
  rw [nearPairMass_eq n hn, near_fullCircle n _ _ _ _ hzero]
  apply (weighted_near n _ _ T _ _ (K * X^2) hdiv
    (fun p hp a ha => hweight n hn p hp a (mem_Icc.mp ha).2)).trans
  let B := cutoffL n
  let D := distanceCut n
  have hcount : ((min (B^2*(2*D+1)) (B^2 + 2*B*(2*D+1)*T) : ℕ) : ℝ) ≤
      (1 + 6*V) * X ^ 57 := by
    have hD' : 2 * (D : ℝ) + 1 ≤ 3 * X^40 := by
      linarith only [hD, one_le_pow₀ hX (n := 40)]
    have hT : (T : ℝ) ≤ V * X := Nat.floor_le (mul_nonneg hV.le hX0)
    calc
      _ ≤ ((B^2 + 2*B*(2*D+1)*T : ℕ) : ℝ) := by exact_mod_cast min_le_right _ _
      _ ≤ (X^16)^2 + 2*X^16*(3*X^40)*(V*X) := by push_cast; gcongr
      _ = X^32 + 6*V*X^57 := by ring
      _ ≤ X^57 + 6*V*X^57 := add_le_add_left (pow_le_pow_right₀ hX (by decide)) _
      _ = _ := by ring
  calc
    _ ≤ ((1 + 6*V) * X^57) * (K * X^2)^2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = ((1 + 6*V) * K^2) * X^61 := by ring
    _ = _ := by rw [hpow]; norm_num

/-- The quantitative close-pair estimate on the original first-corner rows. -/
theorem first_corner_close_full :
    (  let e := fun (k : ℤ) (t : ℝ) => Complex.exp (((k:ℂ)*(2*(Real.pi:ℂ)*Complex.I))*(t:ℂ))
  let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
  let B := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
  let P := fun n : ℕ => (Finset.range (n+1)).filter fun p => n.sqrt < p ∧ p.Prime
  let D := fun n : ℕ => ⌊(n:ℝ)^(5/8:ℝ)⌋₊
  let c := fun (n p a : ℕ) => if (p,a) ∈ ((P n).product (Finset.range (B n+1))).filter
    (fun i => U n < i.2 ∧ U n < i.1 ∧ i.2*i.1 ≤ n) then
    (((∑ d ∈ a.divisors.filter (fun d => U n < d), (ArithmeticFunction.moebius d : ℝ))*Real.log p:ℝ):ℂ) else 0
  let R := fun (n p : ℕ) (t : ℝ) => ∑ a ∈ Finset.range (B n+1), c n p a * e a ((p:ℝ)*t)
  let A := fun n : ℕ => (P n).product (P n)
  let C := fun n : ℕ => (A n).filter fun i => |(i.1:ℤ)-i.2| ≤ D n
  let F := fun (n : ℕ) (T : Finset (ℕ×ℕ)) (t : ℝ) => (∑ i ∈ T, R n i.1 t * R n i.2 t)*e (-(n:ℤ)) t
  ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 1≤n → ‖intervalIntegral (F n (C n)) (0:ℝ) 1 MeasureTheory.volume‖ ≤ K*(n:ℝ)^(61/64:ℝ)) := by
  change ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 1≤n →
    ‖∫ t in (0:ℝ)..1, pairRows (closePairs (bigPrimes n) (distanceCut n))
      (cutoffL n+1) n (firstRow n) t‖ ≤ K*(n:ℝ)^(61/64:ℝ)
  obtain ⟨K,hK,h⟩ := nearPair_bound
  refine ⟨K,hK,?_⟩
  intro n hn
  rw [←nearPairMass_eq n hn]
  exact h n hn

end
end GoldbachFirstCorner

theorem Conjectures.Cuts.Task7b249d0baf4924236e06e1e2 :
  (have x1 : ℤ → ℝ → ℂ := fun (x1 : ℤ) (x2 : ℝ) => Complex.exp ((↑x1 : ℂ) * ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I) * (↑x2 : ℂ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 4 : ℝ)⌋₊; have x4 : ℕ → Finset ℕ := fun (x4 : ℕ) => {x5 ∈ Finset.range (x4 + (1 : ℕ)) | x4.sqrt < x5 ∧ Nat.Prime x5}; have x5 : ℕ → ℕ := fun (x5 : ℕ) => ⌊(↑x5 : ℝ) ^ (5 / 8 : ℝ)⌋₊; have x6 : ℕ → ℕ → ℕ → ℂ := fun (x6 x7 x8 : ℕ) => if (x7, x8) ∈ {x9 ∈ (x4 x6).product (Finset.range (x3 x6 + (1 : ℕ))) | x2 x6 < x9.2 ∧ x2 x6 < x9.1 ∧ x9.2 * x9.1 ≤ x6} then (↑((∑ x9 ∈ x8.divisors with x2 x6 < x9, (↑((ArithmeticFunction.moebius : ℕ → ℤ) x9) : ℝ)) * Real.log (↑x7 : ℝ)) : ℂ) else (0 : ℂ); have x7 : ℕ → ℕ → ℝ → ℂ := fun (x7 x8 : ℕ) (x9 : ℝ) => ∑ x10 ∈ Finset.range (x3 x7 + (1 : ℕ)), x6 x7 x8 x10 * x1 (↑x10 : ℤ) ((↑x8 : ℝ) * x9); have x8 : ℕ → Finset (ℕ × ℕ) := fun (x8 : ℕ) => (x4 x8).product (x4 x8); have x9 : ℕ → Finset (ℕ × ℕ) := fun (x9 : ℕ) => {x10 ∈ x8 x9 | |(↑x10.1 : ℤ) - (↑x10.2 : ℤ)| ≤ (↑(x5 x9) : ℤ)}; have x10 : ℕ → Finset (ℕ × ℕ) → ℝ → ℂ := fun (x10 : ℕ) (x11 : Finset (ℕ × ℕ)) (x12 : ℝ) => (∑ x13 ∈ x11, x7 x10 x13.1 x12 * x7 x10 x13.2 x12) * x1 (-(↑x10 : ℤ)) x12; ∃ (x11 : ℝ), (0 : ℝ) < x11 ∧ ∀ (x12 : ℕ), (1 : ℕ) ≤ x12 → ‖intervalIntegral (x10 x12 (x9 x12)) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume‖ ≤ x11 * (↑x12 : ℝ) ^ (61 / 64 : ℝ)) :=
  GoldbachFirstCorner.first_corner_close_full
