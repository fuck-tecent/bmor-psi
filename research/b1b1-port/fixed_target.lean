import Conjectures.Goldbach.Type2FixedTargetReciprocalError

/-!
# Fixed-target form of the first Type-II cell

This module is separate from `b1b1_port.lean` because the fixed-target library and the
b1-b4 library currently define duplicate constants in `DyadicMixedB4Fourier` and cannot be
imported together.  All cutoffs below are those of the first band: `L = U`, `B = B₁`.
-/

open Filter Topology Finset MeasureTheory
open GoldbachTransitionSquare DyadicMixedB4Fourier

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section

namespace B1B1Fixed

/-- Local copy of the library's divisor envelope, reproved from the **public**
`divisorPower`.  Keeping it here means this file needs no change to any existing
module, so the tree stays single-file for a proof PR. -/
theorem divisor_envelope : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower 128 (by decide)
  let p : ℝ := 1 / 128
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by norm_num [p]), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) 128) standard
      (show 0 ≤ p by norm_num [p])
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    norm_num [p] at powered ⊢
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The first-band coefficient with only prime cofactors above `V`. -/
def topPrime (n V m : ℕ) : ℝ :=
  ∑ a ∈ (Nat.divisors m).filter
      (fun a => cutoffU n < a ∧ a ≤ cutoffL n ∧ cutoffU n < m / a ∧ V < m / a),
    lowMoebiusWeight (cutoffU n) a *
      if (m / a).Prime then Real.log ((m / a : ℕ) : ℝ) else 0

/-- At `V = √n`, this is exactly the library's prime-cofactor `core`. -/
theorem topPrime_sqrt_eq_core (n m : ℕ) :
    topPrime n n.sqrt m = core n (cutoffU n) (cutoffU n) (cutoffL n) m := by
  classical
  unfold topPrime core band largePrimeWeight primeWeight
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hs : n.sqrt < m / a <;> by_cases hp : (m / a).Prime <;> simp [hs, hp]

/-- Function-level form, needed when the coefficient is an argument of `pairIntegral`. -/
theorem topPrime_sqrt_eq_core_fun (n : ℕ) :
    topPrime n n.sqrt = core n (cutoffU n) (cutoffU n) (cutoffL n) :=
  funext (topPrime_sqrt_eq_core n)

/-- The original first-band cell in the fixed-target library's normal form. -/
def fullCell (n : ℕ) : ℂ :=
  pairIntegral (deep n) n
    (full n (cutoffU n) (cutoffU n) (cutoffL n))
    (full n (cutoffU n) (cutoffU n) (cutoffL n))

/-- The cell after restriction to prime cofactors above `√n`. -/
def primeCell (n : ℕ) : ℂ :=
  pairIntegral (deep n) n (topPrime n n.sqrt) (topPrime n n.sqrt)

/-- **Power-saving replacement by prime cofactors above `√n`.** -/
theorem fullCell_primeCell_error :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖fullCell n - primeCell n‖ ≤ K * (n : ℝ) ^ (124 / 128 : ℝ) := by
  obtain ⟨K, hK, h⟩ := transition_power_saving
  refine ⟨K, hK, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : (cutoffL n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hh := h n (cutoffU n) (cutoffU n) (cutoffL n) hn hB (deep n)
    (wide_measurable ..).compl
  simpa only [fullCell, primeCell, topPrime_sqrt_eq_core_fun] using hh

/-- The replacement error is `o(n)`. -/
theorem fullCell_primeCell_error_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖fullCell n - primeCell n‖ ≤ e * (n : ℝ) := by
  obtain ⟨K, _, hK⟩ := fullCell_primeCell_error
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(1 / 32 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_const_nhds (x := K)).mul hp
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_lt_const he] with n hn hsmall
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ K * (n : ℝ) ^ (124 / 128 : ℝ) := hK n hn
    _ = (K * (n : ℝ) ^ (-(1 / 32 : ℝ))) * (n : ℝ) := by
      rw [mul_assoc, show (124 / 128 : ℝ) = -(1 / 32 : ℝ) + 1 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hpos.le

/-- **The b1-b1 estimate is equivalent to its prime-cofactor form.** -/
theorem fullCell_iff_primeCell : smallEven fullCell ↔ smallEven primeCell := by
  constructor
  · apply smallEven_transfer
    intro e he
    filter_upwards [fullCell_primeCell_error_eventually e he] with n hn
    simpa only [norm_sub_rev (primeCell n) (fullCell n)] using hn
  · exact smallEven_transfer fullCell_primeCell_error_eventually

/-- **Prime-row form of the remaining deep-minor integral.** -/
theorem primeCell_eq_arcRows (n : ℕ) :
    primeCell n = arcRows (deep n) (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) := by
  simp only [primeCell, topPrime_sqrt_eq_core_fun]
  exact core_square_rows (deep n) (wide_measurable ..).compl n
    (cutoffU n) (cutoffU n) (cutoffL n)

/-- **Exact residual**: the full prime-pair circle coefficient minus its wide-arc part. -/
theorem primeCell_eq_full_sub_wide (n : ℕ) :
    primeCell n =
      (∫ t in (0:ℝ)..1, pairRows (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t) -
      arcRows (wide n (cutoffB n) (arcHeight n)) (bigPrimes n ×ˢ bigPrimes n)
        (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) := by
  rw [primeCell_eq_arcRows]
  exact eq_sub_iff_add_eq.mpr (arcRows_partition (wide n (cutoffB n) (arcHeight n))
    (wide_measurable ..) (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)))

/-- The row coefficient is bounded by the divisor envelope times `log n`. -/
theorem primeRowCoeff_norm_le_envelope (n : ℕ) (hn : 1 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ)) (p a : ℕ) :
    ‖primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) p a‖ ≤
      C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n := by
  unfold primeRowCoeff
  by_cases hi : (p, a) ∈ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n)
  · rw [if_pos hi]
    simp only [rowSupport, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff] at hi
    obtain ⟨⟨hpP, haB⟩, haU, hpU, han⟩ := hi
    have hpprime : p.Prime := (Finset.mem_filter.mp hpP).2.2
    have hp0 : 0 < p := hpprime.pos
    have hpN : p ≤ n := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hpP).1)
    have haN : a ≤ n := by
      have hap : a ≤ a * p := by nlinarith [hp0]
      exact hap.trans han
    have hlog : Real.log p ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hp0) (by exact_mod_cast hpN)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    change ‖((lowMoebiusWeight (cutoffU n) a * Real.log p : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hpprime.one_le))]
    calc
      _ ≤ (a.divisors.card : ℝ) * Real.log n :=
        mul_le_mul (abs_lowMoebiusWeight_le ..) hlog hlogp0 (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hC a haN) hlog0
  · rw [if_neg hi, norm_zero]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (Real.log_nonneg hnR)

theorem primeRowCoeff_zero (n p : ℕ) :
    primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) p 0 = 0 := by
  simp [primeRowCoeff, rowSupport]

/-- The wide-arc prime-pair term, with all pairs retained. -/
def widePrimePairs (n : ℕ) : ℂ :=
  arcRows (wide n (cutoffB n) (arcHeight n)) (bigPrimes n ×ˢ bigPrimes n)
    (cutoffL n + 1) n (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))

/-- The strengthened close/distant cutoff `D = ⌊n^(2/3)⌋`. -/
def distanceCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊

/-- Full-circle contribution of pairs at distance greater than `D = n^(2/3)`. -/
def distantPrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (farPairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- Full-circle contribution of pairs at distance at most `distanceCut n = ⌊n^(2/3)⌋`. -/
def closePrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (closePairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- The remaining residual after discarding close pairs from the full circle only. -/
def distantResidual (n : ℕ) : ℂ := distantPrimeFull n - widePrimePairs n

/-- Full-circle prime pairs split into distant and close pairs. -/
theorem full_eq_distant_add_close (n : ℕ) :
    (∫ t in (0:ℝ)..1, pairRows (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t) =
    distantPrimeFull n + closePrimeFull n := by
  have hsubset : closePairs (bigPrimes n) (distanceCut n) ⊆ bigPrimes n ×ˢ bigPrimes n :=
    Finset.filter_subset _ _
  have point (t : ℝ) :
      pairRows (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t =
      pairRows (farPairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t +
      pairRows (closePairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t := by
    unfold pairRows farPairs
    rw [← add_mul, sum_sdiff hsubset]
  simp_rw [point]
  apply intervalIntegral.integral_add
  · exact (continuous_pairRows (farPairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))).intervalIntegrable 0 1
  · exact (continuous_pairRows (closePairs (bigPrimes n) (distanceCut n)) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))).intervalIntegrable 0 1

/-- The discrepancy from the distant-pair residual is exactly the close full-circle mass. -/
theorem primeCell_sub_distantResidual (n : ℕ) :
    primeCell n - distantResidual n = closePrimeFull n := by
  unfold distantResidual widePrimePairs
  rw [primeCell_eq_full_sub_wide, full_eq_distant_add_close]
  ring

/-! The divisor-of-residue counting argument is adapted from the Apache-2.0 reference proof
in PR 3790, itself building on PR 3253. -/

private def residualSize (n s p : ℕ) : ℕ := ((n : ℤ) - s * p).natAbs

private theorem close_factors {n B D a b p q : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hbB : b ≤ B) (heq : a * p + b * q = n) (hnear : |(p : ℤ) - q| ≤ D) (hne : p ≠ q) :
    n / (a + b) - D ≤ p ∧ p ≤ n / (a + b) + D ∧
    0 < residualSize n (a + b) p ∧ residualSize n (a + b) p ≤ B * D ∧
    b ∣ residualSize n (a + b) p := by
  have hgap := abs_le.mp hnear
  have hpq : p - D ≤ q := by omega
  have hqp : q ≤ p + D := by omega
  have hs : 0 < a + b := by omega
  have hl : p - D ≤ n / (a + b) := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    rw [← heq, mul_comm (p - D), add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le ..)) (Nat.mul_le_mul_left _ hpq)
  have hu : n / (a + b) ≤ p + D := by
    have hu' : n ≤ (a + b) * (p + D) := by
      rw [← heq, add_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hqp)
    exact (Nat.div_le_div_right hu').trans_eq (Nat.mul_div_cancel_left _ hs)
  have hres : residualSize n (a + b) p = b * ((q : ℤ) - p).natAbs := by
    unfold residualSize
    rw [← heq]
    push_cast
    rw [show (a : ℤ) * p + b * q - (a + b) * p = b * (q - p) by ring,
      Int.natAbs_mul, Int.natAbs_natCast]
  have habs : ((q : ℤ) - p).natAbs ≤ D := by
    exact_mod_cast (show (↑((q : ℤ) - p).natAbs : ℤ) ≤ D by
      rw [Int.natCast_natAbs, abs_sub_comm]; exact hnear)
  have hnz : 0 < ((q : ℤ) - p).natAbs := Int.natAbs_pos.mpr (by omega)
  rw [hres]
  exact ⟨by omega, by omega, Nat.mul_pos hb hnz, Nat.mul_le_mul hbB habs, dvd_mul_right ..⟩

private theorem offDiagonal_card {n B D T : ℕ} (S : Finset Representation)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B * D → m.divisors.card ≤ T)
    (hspec : ∀ r ∈ S, 0 < r.a ∧ r.a ≤ B ∧ 0 < r.b ∧ r.b ≤ B ∧
      r.a * r.p + r.b * r.q = n ∧ |(r.p : ℤ) - r.q| ≤ D ∧ r.p ≠ r.q) :
    S.card ≤ (2 * B) * (2 * D + 1) * T := by
  classical
  let centers (s : ℕ) := Icc (n / s - D) (n / s + D)
  let divisors (s p : ℕ) := if 0 < residualSize n s p ∧ residualSize n s p ≤ B * D
    then (residualSize n s p).divisors else ∅
  let box := (Icc 1 (2 * B)).sigma fun s => (centers s).sigma (divisors s)
  let code (r : Representation) : Σ _s : ℕ, Σ _p : ℕ, ℕ := ⟨r.a + r.b, ⟨r.p, r.b⟩⟩
  have into (r : Representation) (hr : r ∈ S) : code r ∈ box := by
    obtain ⟨ha, ha', hb, hb', heq, hgap, hne⟩ := hspec r hr
    obtain ⟨hl, hu, hpos, hcap, hdvd⟩ := close_factors ha hb hb' heq hgap hne
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨by dsimp [code]; omega, by dsimp [code]; omega⟩,
      mem_sigma.mpr ⟨mem_Icc.mpr ⟨hl, hu⟩, ?_⟩⟩
    change r.b ∈ divisors (r.a + r.b) r.p
    dsimp only [divisors]
    rw [ite_eq_left ⟨hpos, hcap⟩]
    exact Nat.mem_divisors.mpr ⟨hdvd, hpos.ne'⟩
  have hinj : Set.InjOn code (S : Set Representation) := by
    intro r hr u hu he
    obtain ⟨a, b, p, q⟩ := r
    obtain ⟨a', b', p', q'⟩ := u
    have hs := congrArg (fun i => i.1) he
    have hp := congrArg (fun i => i.2.1) he
    have hb := congrArg (fun i => i.2.2) he
    change a + b = a' + b' at hs
    change p = p' at hp
    change b = b' at hb
    subst p'; subst b'
    have ha : a = a' := by omega
    subst a'
    have h₁ := hspec _ hr
    have h₂ := hspec _ hu
    have hs₁ : a * p + b * q = n := h₁.2.2.2.2.1
    have hs₂ : a * p + b * q' = n := h₂.2.2.2.2.1
    have hbpos : 0 < b := h₁.2.2.1
    have hq : q = q' := Nat.eq_of_mul_eq_mul_left hbpos (Nat.add_left_cancel (hs₁.trans hs₂.symm))
    subst q'
    rfl
  have hcount (s p : ℕ) : (divisors s p).card ≤ T := by
    unfold divisors
    split_ifs with h
    · exact hdiv _ h.1 h.2
    · simp
  have hcenters (s : ℕ) : (centers s).card ≤ 2 * D + 1 := by
    dsimp only [centers]
    rw [Nat.card_Icc]
    omega
  refine (card_le_card_of_injOn code into hinj).trans ?_
  unfold box
  rw [card_sigma]
  calc
    _ ≤ ∑ s ∈ Icc 1 (2 * B), (2 * D + 1) * T := by
      apply sum_le_sum
      intro s _
      rw [card_sigma]
      calc
        _ ≤ ∑ _p ∈ centers s, T := sum_le_sum fun p _ => hcount s p
        _ = (centers s).card * T := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (hcenters s)
    _ = _ := by simp [Nat.card_Icc, Nat.mul_assoc]

theorem divisor_near_card {n B D T : ℕ} (S : Finset Representation)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B * D → m.divisors.card ≤ T)
    (hspec : ∀ r ∈ S, 0 < r.a ∧ r.a ≤ B ∧ 0 < r.b ∧ r.b ≤ B ∧
      r.a * r.p + r.b * r.q = n ∧ |(r.p : ℤ) - r.q| ≤ D) :
    S.card ≤ min (B ^ 2 * (2 * D + 1)) (B ^ 2 + 2 * B * (2 * D + 1) * T) := by
  classical
  refine le_min (representation_card_near S hspec) ?_
  let diag := S.filter fun r => r.p = r.q
  let off := S.filter fun r => r.p ≠ r.q
  have hd : diag.card ≤ B ^ 2 := by
    have h := representation_card_near (n := n) (B := B) (D := 0) diag (by
      intro r hr
      obtain ⟨hm, he⟩ := mem_filter.mp hr
      obtain ⟨ha, ha', hb, hb', hs, _⟩ := hspec r hm
      exact ⟨ha, ha', hb, hb', hs, by simp [he]⟩)
    simpa using h
  have ho : off.card ≤ 2 * B * (2 * D + 1) * T := by
    apply offDiagonal_card off hdiv
    intro r hr
    obtain ⟨hm, he⟩ := mem_filter.mp hr
    obtain ⟨ha, ha', hb, hb', hs, hg⟩ := hspec r hm
    exact ⟨ha, ha', hb, hb', hs, hg, he⟩
  have heq : diag.card + off.card = S.card := card_filter_add_card_filter_not ..
  omega

def nearSolutions (n B D : ℕ) (P : Finset ℕ) :=
  (((P ×ˢ P).filter (fun pq : ℕ × ℕ => |(pq.1 : ℤ) - pq.2| ≤ D)) ×ˢ
    (Icc 1 B ×ˢ Icc 1 B)).filter (fun z => z.2.1 * z.1.1 + z.2.2 * z.1.2 = n)

private def asRep (z : (ℕ × ℕ) × ℕ × ℕ) : Representation :=
  ⟨z.2.1, z.2.2, z.1.1, z.1.2⟩

private theorem asRep_injective : Function.Injective asRep := by
  rintro ⟨⟨p, q⟩, a, b⟩ ⟨⟨u, v⟩, i, j⟩ he
  simpa [asRep, and_assoc, and_left_comm, and_comm] using he

theorem weighted_near (n B D T : ℕ) (P : Finset ℕ) (c : ℕ → ℕ → ℂ) (M : ℝ)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ B * D → m.divisors.card ≤ T)
    (hweight : ∀ p ∈ P, ∀ a ∈ Icc 1 B, ‖c p a‖ ≤ M) :
    ‖∑ z ∈ nearSolutions n B D P, c z.1.1 z.2.1 * c z.1.2 z.2.2‖ ≤
      ((min (B ^ 2 * (2 * D + 1)) (B ^ 2 + 2 * B * (2 * D + 1) * T) : ℕ) : ℝ) * M ^ 2 := by
  classical
  let S := nearSolutions n B D P
  have hcard : S.card ≤ min (B ^ 2 * (2 * D + 1)) (B ^ 2 + 2 * B * (2 * D + 1) * T) := by
    rw [← card_image_of_injective S asRep_injective]
    apply divisor_near_card _ hdiv
    intro r hr
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
    obtain ⟨hm, he⟩ := mem_filter.mp hz
    obtain ⟨hpq, hab⟩ := mem_product.mp hm
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact ⟨(mem_Icc.mp ha).1, (mem_Icc.mp ha).2, (mem_Icc.mp hb).1,
      (mem_Icc.mp hb).2, he, (mem_filter.mp hpq).2⟩
  calc
    _ ≤ ∑ z ∈ S, ‖c z.1.1 z.2.1 * c z.1.2 z.2.2‖ := norm_sum_le ..
    _ ≤ ∑ _z ∈ S, M ^ 2 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hpq, hab⟩ := mem_product.mp (mem_filter.mp hz).1
      obtain ⟨hp, hq⟩ := mem_product.mp (mem_filter.mp hpq).1
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      rw [norm_mul, pow_two]
      exact mul_le_mul (hweight _ hp _ ha) (hweight _ hq _ hb) (norm_nonneg _)
        ((norm_nonneg _).trans (hweight _ hp _ ha))
    _ = (S.card : ℝ) * M ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

theorem near_fullCircle (n B D : ℕ) (P : Finset ℕ) (c : ℕ → ℕ → ℂ)
    (hzero : ∀ p, c p 0 = 0) :
    (∫ t in (0 : ℝ)..1, pairRows (closePairs P D) (B + 1) n c t) =
    ∑ z ∈ nearSolutions n B D P, c z.1.1 z.2.1 * c z.1.2 z.2.2 := by
  classical
  rw [full_pairRows]
  let Q := closePairs P D
  let A := (Q ×ˢ (range (B + 1) ×ˢ range (B + 1))).filter
    (fun z => z.2.1 * z.1.1 + z.2.2 * z.1.2 = n)
  change (∑ z ∈ A, c z.1.1 z.2.1 * c z.1.2 z.2.2) = _
  symm
  apply sum_subset
  · intro z hz
    obtain ⟨hm, he⟩ := mem_filter.mp hz
    obtain ⟨hpq, hab⟩ := mem_product.mp hm
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hpq, mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp ha).2),
       mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hb).2)⟩⟩, he⟩
  · intro z hz hout
    obtain ⟨hm, he⟩ := mem_filter.mp hz
    obtain ⟨hpq, hab⟩ := mem_product.mp hm
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    by_cases haz : z.2.1 = 0
    · rw [haz, hzero, zero_mul]
    by_cases hbz : z.2.2 = 0
    · rw [hbz, hzero, mul_zero]
    exact (hout (mem_filter.mpr ⟨mem_product.mpr ⟨hpq, mem_product.mpr
      ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero haz, Nat.le_of_lt_succ (mem_range.mp ha)⟩,
       mem_Icc.mpr ⟨Nat.pos_of_ne_zero hbz, Nat.le_of_lt_succ (mem_range.mp hb)⟩⟩⟩, he⟩)).elim

/-- **Close-pair power saving**, using the existing full-circle counting estimate. -/
theorem closePrimeFull_bound (n : ℕ) (hn : 1 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ)) :
    ‖closePrimeFull n‖ ≤
      (cutoffL n : ℝ) ^ 2 * (2 * (distanceCut n : ℝ) + 1) *
        (C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n) ^ 2 := by
  exact closePairs_full (bigPrimes n) (distanceCut n) (cutoffL n) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) (primeRowCoeff_zero n)
    (fun p _ a _ => primeRowCoeff_norm_le_envelope n hn hC0 hC p a)

/-- Sharper close-pair estimate using a divisor bound for the off-diagonal residual. -/
theorem closePrimeFull_divisor_bound (n T : ℕ) (M : ℝ)
    (hdiv : ∀ m : ℕ, 0 < m → m ≤ cutoffL n * distanceCut n → m.divisors.card ≤ T)
    (hweight : ∀ p ∈ bigPrimes n, ∀ a ∈ Icc 1 (cutoffL n),
      ‖primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) p a‖ ≤ M) :
    ‖closePrimeFull n‖ ≤
      ((min (cutoffL n ^ 2 * (2 * distanceCut n + 1))
        (cutoffL n ^ 2 + 2 * cutoffL n * (2 * distanceCut n + 1) * T) : ℕ) : ℝ) * M ^ 2 := by
  unfold closePrimeFull
  rw [near_fullCircle _ _ _ _ _ (primeRowCoeff_zero n)]
  exact weighted_near n (cutoffL n) (distanceCut n) T (bigPrimes n)
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) M hdiv hweight

/-- A crude close-pair bound retained for reference.  At the strengthened cutoff `n^(2/3)`
this bound is not itself sublinear; the sharper divisor-residue estimate and the eventual
`o(n)` proof are given by `closePrimeFull_divisor_bound` and `closePrimeFull_eventually`. -/
theorem primeCell_distantResidual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖primeCell n - distantResidual n‖ ≤
        (cutoffL n : ℝ) ^ 2 * (2 * (distanceCut n : ℝ) + 1) *
          (C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n) ^ 2 := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  refine ⟨C, by positivity, fun n hn => ?_⟩
  rw [primeCell_sub_distantResidual]
  exact closePrimeFull_bound n hn (by positivity) (fun m hm => hdiv n m hm)

/-- The first-band cutoff is below the natural square root. -/
theorem cutoffL_le_sqrt {n : ℕ} (hn : 1 ≤ n) : cutoffL n ≤ n.sqrt := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (cutoffL n : ℝ) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 4 : ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffL n) (α := ℝ)) hr 2
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  exact Nat.le_sqrt'.mpr (by exact_mod_cast hh)

/-- Contribution of one ordered prime pair to the full-circle coefficient. -/
def rowMass (n B : ℕ) (c : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  ∑ ab ∈ Finset.range (B + 1) ×ˢ Finset.range (B + 1),
    if ab.1 * p + ab.2 * q = n then c p ab.1 * c q ab.2 else 0

/-- For distinct primes with `B < q`, the short factor on the `p`-side is the inverse
residue of `n·p⁻¹ mod q`, and its partner is then forced. -/
theorem rowMass_eq_inversePair {n B p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hB : B < q) (c : ℕ → ℕ → ℂ) :
    rowMass n B c p q = inversePair n B c p q := by
  classical
  let a := inverseResidue n p q
  let b := partnerFactor n p q
  let hits := (Finset.range (B + 1) ×ˢ Finset.range (B + 1)).filter
    (fun ab : ℕ × ℕ => ab.1 * p + ab.2 * q = n)
  have unique {ab : ℕ × ℕ} (hm : ab ∈ hits) : ab = (a, b) := by
    obtain ⟨hab, heq⟩ := Finset.mem_filter.mp hm
    have ha : ab.1 < q := by
      have ha0 : ab.1 ≤ B := Nat.le_of_lt_succ
        (Finset.mem_range.mp (Finset.mem_product.mp hab).1)
      exact ha0.trans_lt hB
    obtain ⟨h₁, h₂⟩ := resonance_inverse hp hq hne ha heq
    exact Prod.ext h₁ h₂
  unfold rowMass
  rw [← Finset.sum_filter]
  change (∑ ab ∈ hits, c p ab.1 * c q ab.2) =
    if a ≤ B ∧ b ≤ B ∧ a * p + b * q = n then c p a * c q b else 0
  by_cases h : a ≤ B ∧ b ≤ B ∧ a * p + b * q = n
  · rw [if_pos h]
    have hm : (a, b) ∈ hits := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.1),
        Finset.mem_range.mpr (Nat.lt_succ_of_le h.2.1)⟩, h.2.2⟩
    exact Finset.sum_eq_single_of_mem (a, b) hm fun ab hab hne' => (hne' (unique hab)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro ab hab
    obtain rfl := unique hab
    obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hab
    exact (h ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hm).1),
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hm).2), heq⟩).elim

/-- Inverse-residue sum over prime pairs at distance greater than `distanceCut n`. -/
def distantInverseTotal (n : ℕ) : ℂ :=
  ∑ pq ∈ farPairs (bigPrimes n) (distanceCut n),
    inversePair n (cutoffL n)
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) pq.1 pq.2

/-- **The distant full-circle term is an inverse-residue sum.** -/
theorem distantPrimeFull_eq_inverseTotal (n : ℕ) (hn : 1 ≤ n) :
    distantPrimeFull n = distantInverseTotal n := by
  classical
  let P := bigPrimes n
  let B := cutoffL n
  let c := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)
  unfold distantPrimeFull distantInverseTotal
  rw [full_pairRows, Finset.sum_filter]
  change (∑ i ∈ (farPairs (bigPrimes n) (distanceCut n) ×ˢ
      (Finset.range (cutoffL n + 1) ×ˢ Finset.range (cutoffL n + 1))),
      if i.2.1 * i.1.1 + i.2.2 * i.1.2 = n then
        primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) i.1.1 i.2.1 *
          primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) i.1.2 i.2.2 else 0) = _
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  obtain ⟨hm, hout⟩ := Finset.mem_sdiff.mp hpq
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hm
  have hne : pq.1 ≠ pq.2 := by
    intro heq
    apply hout
    apply Finset.mem_filter.mpr
    exact ⟨hm, by simp [heq]⟩
  exact rowMass_eq_inversePair (Finset.mem_filter.mp hp).2.2
    (Finset.mem_filter.mp hq).2.2 hne
    ((cutoffL_le_sqrt hn).trans_lt (Finset.mem_filter.mp hq).2.1) c

/-- **Final fixed-target normal form**: inverse-residue sum minus all wide-arc pairs. -/
theorem distantResidual_eq_inverse_sub_wide (n : ℕ) (hn : 1 ≤ n) :
    distantResidual n = distantInverseTotal n - widePrimePairs n := by
  unfold distantResidual
  rw [distantPrimeFull_eq_inverseTotal n hn]

/-- Generic close-pair mass is eventually below any linear error budget. -/
theorem closeFull_eventually (C : ℝ) (hC : 1 ≤ C)
    (hdiv : ∀ n m : ℕ, m ≤ n → (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ))
    (P : ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ → ℂ)
    (hzero : ∀ n p, c n p 0 = 0)
    (hweight0 : ∀ n : ℕ, 1 ≤ n → ∀ p ∈ P n, ∀ a ∈ Icc 1 (cutoffL n),
      ‖c n p a‖ ≤ C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n)
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖∫ t in (0:ℝ)..1,
      pairRows (closePairs (P n) (distanceCut n)) (cutoffL n + 1) n (c n) t‖ ≤
        e * (n : ℝ) := by
  let K := (1 + 6 * C) * (384 * C) ^ 2
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(21 / 384 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 21 / 384)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, mul_zero] using (tendsto_const_nhds (x := K)).mul hp
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_lt_const he] with n hn hsmall
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  let X := (n : ℝ) ^ (1 / 384 : ℝ)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hn0 _
  have hX1 : 1 ≤ X := Real.one_le_rpow hnR (by norm_num)
  have hXpow (k : ℕ) : X ^ k = (n : ℝ) ^ ((k : ℝ) / 384) := by
    dsimp [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hB : (cutoffL n : ℝ) ≤ X ^ 96 := by
    rw [hXpow]
    norm_num
    exact Nat.floor_le (by positivity)
  have hD : (distanceCut n : ℝ) ≤ X ^ 256 := by
    rw [hXpow]
    norm_num
    exact Nat.floor_le (by positivity)
  have hD2 : 2 * (distanceCut n : ℝ) + 1 ≤ 3 * X ^ 256 := by
    have h1 : 1 ≤ X ^ 256 := one_le_pow₀ hX1
    nlinarith
  have hlog : Real.log n ≤ 384 * X := by
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) < 1 / 384)
    calc Real.log n ≤ X / (1 / 384 : ℝ) := by simpa only [X] using h
      _ = 384 * X := by ring
  have hBD : cutoffL n * distanceCut n ≤ n := by
    have hr : ((cutoffL n * distanceCut n : ℕ) : ℝ) ≤ n := by
      push_cast
      calc
        (cutoffL n : ℝ) * (distanceCut n : ℝ) ≤ X ^ 96 * X ^ 256 :=
          mul_le_mul hB hD (Nat.cast_nonneg _) (by positivity)
        _ = X ^ 352 := by ring
        _ ≤ X ^ 384 := pow_le_pow_right₀ hX1 (by decide)
        _ = n := by rw [hXpow]; norm_num
    exact_mod_cast hr
  let T := ⌊C * X ^ 3⌋₊
  let M := 384 * C * X ^ 4
  have hT : (T : ℝ) ≤ C * X ^ 3 := Nat.floor_le (by positivity)
  have hdivNear : ∀ m : ℕ, 0 < m → m ≤ cutoffL n * distanceCut n →
      m.divisors.card ≤ T := by
    intro m _ hm
    apply Nat.le_floor
    calc
      (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ) :=
        hdiv n m (hm.trans hBD)
      _ = C * X ^ 3 := by rw [hXpow]; norm_num
  have hweight : ∀ p ∈ P n, ∀ a ∈ Icc 1 (cutoffL n), ‖c n p a‖ ≤ M := by
    intro p hp a ha
    calc
      _ ≤ C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n := hweight0 n hn p hp a ha
      _ ≤ (C * X ^ 3) * (384 * X) := by
        have hn3 : (n : ℝ) ^ (1 / 128 : ℝ) = X ^ 3 := by rw [hXpow]; norm_num
        rw [hn3]
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = M := by dsimp [M]; ring
  have hBsq : (cutoffL n : ℝ) ^ 2 ≤ X ^ 192 := by
    calc
      _ ≤ (X ^ 96) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
      _ = X ^ 192 := by ring
  have hprod : 2 * (cutoffL n : ℝ) * (2 * (distanceCut n : ℝ) + 1) * (T : ℝ) ≤
      6 * C * X ^ 355 := by
    calc
      _ ≤ 2 * X ^ 96 * (3 * X ^ 256) * (C * X ^ 3) := by gcongr
      _ = 6 * C * X ^ 355 := by ring
  have hcount : ((cutoffL n ^ 2 + 2 * cutoffL n * (2 * distanceCut n + 1) * T : ℕ) : ℝ) ≤
      (1 + 6 * C) * X ^ 355 := by
    push_cast
    calc
      _ ≤ X ^ 192 + 6 * C * X ^ 355 := add_le_add hBsq hprod
      _ ≤ _ := by
        have hpow : X ^ 192 ≤ X ^ 355 := pow_le_pow_right₀ hX1 (by decide)
        nlinarith
  calc
    _ ≤ ((min (cutoffL n ^ 2 * (2 * distanceCut n + 1))
        (cutoffL n ^ 2 + 2 * cutoffL n * (2 * distanceCut n + 1) * T) : ℕ) : ℝ) * M ^ 2 :=
      by
        rw [near_fullCircle n (cutoffL n) (distanceCut n) (P n) (c n) (hzero n)]
        exact weighted_near n (cutoffL n) (distanceCut n) T (P n) (c n) M hdivNear hweight
    _ ≤ ((cutoffL n ^ 2 + 2 * cutoffL n * (2 * distanceCut n + 1) * T : ℕ) : ℝ) * M ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
      exact_mod_cast min_le_right _ _
    _ ≤ ((1 + 6 * C) * X ^ 355) * M ^ 2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg M)
    _ = K * X ^ 363 := by dsimp [K, M]; ring
    _ = K * (n : ℝ) ^ (363 / 384 : ℝ) := by rw [hXpow]; norm_num
    _ = (K * (n : ℝ) ^ (-(21 / 384 : ℝ))) * (n : ℝ) := by
      dsimp [K]
      rw [mul_assoc, show (363 / 384 : ℝ) = -(21 / 384 : ℝ) + 1 by norm_num,
        Real.rpow_add hn0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hn0.le

/-- The original close-pair mass, as a special case of `closeFull_eventually`. -/
theorem closePrimeFull_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖closePrimeFull n‖ ≤ e * (n : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  exact closeFull_eventually C hC hdiv (fun n => bigPrimes n)
    (fun n => primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))
    (fun n => primeRowCoeff_zero n)
    (fun n hn p hp a ha => primeRowCoeff_norm_le_envelope n hn (by positivity)
      (fun m hm => hdiv n m hm) p a) e he

/-- **The prime cell and distant-pair residual have the same `o(n)` fate.** -/
theorem primeCell_iff_distantResidual : smallEven primeCell ↔ smallEven distantResidual := by
  constructor
  · apply smallEven_transfer
    intro e he
    filter_upwards [closePrimeFull_eventually e he] with n hn
    have heq := primeCell_sub_distantResidual n
    rw [← heq] at hn
    simpa only [norm_sub_rev] using hn
  · apply smallEven_transfer
    intro e he
    filter_upwards [closePrimeFull_eventually e he] with n hn
    simpa only [primeCell_sub_distantResidual] using hn

/-- **Full b1-b1 reduction to the distant-pair residual.** -/
theorem fullCell_iff_distantResidual : smallEven fullCell ↔ smallEven distantResidual :=
  fullCell_iff_primeCell.trans primeCell_iff_distantResidual

/-- The residual written explicitly as inverse residues minus the wide-arc prime rows. -/
def inverseResidual (n : ℕ) : ℂ := distantInverseTotal n - widePrimePairs n

/-- **Final equivalence**: b1-b1 is exactly the smallness of the inverse-residue/wide-arc
discrepancy on every sufficiently large even target. -/
theorem fullCell_iff_inverseResidual : smallEven fullCell ↔ smallEven inverseResidual := by
  rw [fullCell_iff_distantResidual]
  have transform {f g : ℕ → ℂ} (h : ∀ n, 1 ≤ n → f n = g n) : smallEven f → smallEven g := by
    intro hf e he
    obtain ⟨N, hN⟩ := hf e he
    refine ⟨max 1 N, fun n hn heven => ?_⟩
    rw [← h n ((le_max_left ..).trans hn)]
    exact hN n ((le_max_right ..).trans hn) heven
  exact ⟨transform distantResidual_eq_inverse_sub_wide,
    transform (fun n hn => (distantResidual_eq_inverse_sub_wide n hn).symm)⟩

/-- Definitional comparison with the frozen catalogue statement. -/
theorem frozen_iff_inverseResidual :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1))
      (fun k => (u k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
    let H := fun n : ℕ => 256 * Q₁ n * Q n;
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧
      Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))};
    let Λ := ArithmeticFunction.vonMangoldt;
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊;
    let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊;
    let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter
      (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a),
      (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a);
    let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral
      (fun t => (wideArcs n)ᶜ.indicator
        (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ)) ↔ smallEven inverseResidual := by
  exact fullCell_iff_inverseResidual

/-! ### Milestone 55: symmetric reciprocal-residue form -/

/-- For `n ≥ 16`, twice the first-band cutoff is below `√n`. -/
theorem twice_cutoffL_le_sqrt {n : ℕ} (hn : 16 ≤ n) : 2 * cutoffL n ≤ n.sqrt := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hB : (cutoffL n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
  have hfourth : cutoffL n ^ 4 ≤ n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffL n) (α := ℝ)) hB 4
    have hrt : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
      simpa only [one_div, Nat.cast_ofNat] using
        Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by decide : (4 : ℕ) ≠ 0)
    rw [hrt] at h
    exact_mod_cast h
  have htwo : 2 ≤ cutoffL n := by
    apply Nat.le_floor
    have h16 : ((2 : ℝ) ^ 4) ^ ((4 : ℝ)⁻¹) = 2 := by
      simpa using Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2)
        (by decide : (4 : ℕ) ≠ 0)
    have hh : (2 : ℝ) ^ 4 ≤ n := by norm_num; exact_mod_cast hn
    norm_num only [Nat.cast_ofNat]
    calc
      (2 : ℝ) = _ := h16.symm
      _ ≤ _ := by
        rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
        exact Real.rpow_le_rpow (by norm_num) hh (by positivity)
  apply Nat.le_sqrt'.mpr
  calc
    (2 * cutoffL n) ^ 2 = (cutoffL n) ^ 2 * 4 := by ring
    _ ≤ (cutoffL n) ^ 2 * (cutoffL n) ^ 2 := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = cutoffL n ^ 4 := by ring
    _ ≤ n := hfourth

/-- If both inverse residues are short, their displayed sum is exactly `n`. -/
theorem short_pair_forces_eq {n p q B : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n < p * q) (hbq : 2 * B < q) (hbp : 2 * B < p)
    (ha : inverseResidue n p q ≤ B) (hb : inverseResidue n q p ≤ B) :
    inverseResidue n p q * p + inverseResidue n q p * q = n := by
  let r := inverseResidue n p q
  let s := inverseResidue n q p
  have hr : 2 * r < q := lt_of_le_of_lt (Nat.mul_le_mul_left _ ha) hbq
  have hs : 2 * s < p := lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) hbp
  have hl : r * p + s * q < p * q := by
    have h1 := Nat.mul_lt_mul_of_pos_right hr hp.pos
    have h2 := Nat.mul_lt_mul_of_pos_right hs hq.pos
    nlinarith
  have h := inverse_reciprocity (n := n) hp hq hpq
  change (r * p + s * q) % (p * q) = n % (p * q) at h
  rwa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hn] at h

/-- Symmetric form of an inverse pair when both primes are large compared with `B`. -/
theorem inversePair_symmetric {n B p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n < p * q) (hbq : 2 * B < q) (hbp : 2 * B < p)
    (c : ℕ → ℕ → ℂ) (h0 : ∀ r a, B < a → c r a = 0) :
    inversePair n B c p q = c p (inverseResidue n p q) * c q (inverseResidue n q p) := by
  let a := inverseResidue n p q
  let b := inverseResidue n q p
  let b' := partnerFactor n p q
  change (if a ≤ B ∧ b' ≤ B ∧ a * p + b' * q = n then c p a * c q b' else 0) =
    c p a * c q b
  by_cases h : a ≤ B ∧ b' ≤ B ∧ a * p + b' * q = n
  · rw [if_pos h]
    have hb := (resonance_inverse hq hp hpq.symm (show b' < p by omega)
      (by rw [add_comm]; exact h.2.2 : b' * q + a * p = n)).1
    rw [show b' = b from hb]
  · rw [if_neg h]
    by_cases ha : a ≤ B
    · by_cases hb : b ≤ B
      · have he := short_pair_forces_eq hp hq hpq hn hbq hbp ha hb
        have hb' := (resonance_inverse hp hq hpq (show a < q by omega) he).2
        exact (h ⟨ha, by rwa [← show b = b' from hb'], by rwa [← show b = b' from hb']⟩).elim
      · rw [h0 q b (by omega), mul_zero]
    · rw [h0 p a (by omega), zero_mul]

/-- Fully symmetric reciprocal sum over distant prime pairs. -/
def reciprocalTotal (n : ℕ) : ℂ :=
  let c := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)
  ∑ pq ∈ farPairs (bigPrimes n) (distanceCut n),
    c pq.1 (inverseResidue n pq.1 pq.2) * c pq.2 (inverseResidue n pq.2 pq.1)

/-- The asymmetric inverse-pair sum equals the symmetric reciprocal sum. -/
theorem distantInverseTotal_eq_reciprocal (n : ℕ) (hn : 16 ≤ n) :
    distantInverseTotal n = reciprocalTotal n := by
  classical
  let c := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)
  unfold distantInverseTotal reciprocalTotal
  refine Finset.sum_congr rfl fun pq hpq => ?_
  obtain ⟨hm, hout⟩ := Finset.mem_sdiff.mp hpq
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hm
  have hne : pq.1 ≠ pq.2 := by
    intro heq
    apply hout
    exact Finset.mem_filter.mpr ⟨hm, by simp [heq]⟩
  have hpsqrt := (Finset.mem_filter.mp hp).2.1
  have hqsqrt := (Finset.mem_filter.mp hq).2.1
  have hnq : n < pq.1 * pq.2 :=
    (Nat.lt_succ_sqrt n).trans_le (Nat.mul_le_mul hpsqrt hqsqrt)
  apply inversePair_symmetric (Finset.mem_filter.mp hp).2.2 (Finset.mem_filter.mp hq).2.2 hne hnq
    ((twice_cutoffL_le_sqrt hn).trans_lt hqsqrt) ((twice_cutoffL_le_sqrt hn).trans_lt hpsqrt)
  intro p a ha
  have hnot : (p, a) ∉ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n) := by
    intro h
    have hmem := (Finset.mem_filter.mp h).1
    have haB : a ≤ cutoffL n := Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_product.mp hmem).2)
    omega
  simp [c, primeRowCoeff, hnot]

/-- The residual in symmetric reciprocal form. -/
def reciprocalResidual (n : ℕ) : ℂ := reciprocalTotal n - widePrimePairs n

/-- The two residual normal forms are eventually equal. -/
theorem inverseResidual_eq_reciprocalResidual (n : ℕ) (hn : 16 ≤ n) :
    inverseResidual n = reciprocalResidual n := by
  unfold inverseResidual reciprocalResidual
  rw [distantInverseTotal_eq_reciprocal n hn]

/-- **Symmetric fixed-target equivalence.** -/
theorem fullCell_iff_reciprocalResidual : smallEven fullCell ↔ smallEven reciprocalResidual := by
  rw [fullCell_iff_inverseResidual]
  have transform {f g : ℕ → ℂ} (h : ∀ n, 16 ≤ n → f n = g n) : smallEven f → smallEven g := by
    intro hf e he
    obtain ⟨N, hN⟩ := hf e he
    refine ⟨max 16 N, fun n hn heven => ?_⟩
    rw [← h n ((le_max_left ..).trans hn)]
    exact hN n ((le_max_right ..).trans hn) heven
  exact ⟨transform inverseResidual_eq_reciprocalResidual,
    transform (fun n hn => (inverseResidual_eq_reciprocalResidual n hn).symm)⟩

/-! ### Milestone 57: raise the prime lower cutoff to `n^(2/3)` -/

/-- Prime logarithm weight above an arbitrary cutoff. -/
def highPrimeWeight (V b : ℕ) : ℝ := if V < b then primeWeight b else 0

/-- `topPrime` is the corresponding band coefficient. -/
theorem topPrime_eq_band (n V m : ℕ) :
    topPrime n V m = band (cutoffU n) (cutoffU n) (cutoffL n) (highPrimeWeight V) m := by
  classical
  unfold topPrime band highPrimeWeight
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hV : V < m / a <;> by_cases hp : (m / a).Prime <;> simp [hV, hp, primeWeight]

theorem abs_highPrimeWeight_le (V b : ℕ) :
    |highPrimeWeight V b| ≤ ArithmeticFunction.vonMangoldt b := by
  unfold highPrimeWeight
  split_ifs
  · exact abs_primeWeight_le b
  · simpa using ArithmeticFunction.vonMangoldt_nonneg (n := b)

/-- Full-range `L²` bound for any prime lower cutoff. -/
theorem topPrime_l2_bound (n V : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n + 1), (topPrime n V m) ^ 2 ≤
      ((n : ℝ) + 1) * (T ^ 2 * Real.log n) ^ 2 := by
  calc
    _ ≤ ∑ _m ∈ range (n + 1), (T ^ 2 * Real.log n) ^ 2 := by
      refine sum_le_sum fun m hm => ?_
      rw [← sq_abs (topPrime n V m), topPrime_eq_band]
      exact pow_le_pow_left₀ (abs_nonneg _) (band_uniform_bound n (cutoffU n) (cutoffU n)
        (cutoffL n) m (Nat.le_of_lt_succ (mem_range.mp hm)) hn hdiv
        (abs_highPrimeWeight_le V)) 2
    _ = _ := by simp

/-- Prime weight in the intermediate interval `(√n, D]`. -/
def middlePrimeWeight (n b : ℕ) : ℝ :=
  if n.sqrt < b ∧ b ≤ distanceCut n then primeWeight b else 0

/-- The coefficient removed when raising the prime cutoff from `√n` to `D`. -/
def middlePrimeCoeff (n : ℕ) : ℕ → ℝ :=
  band (cutoffU n) (cutoffU n) (cutoffL n) (middlePrimeWeight n)

/-- Subtraction of band coefficients. -/
theorem band_sub (U L B m : ℕ) (v w : ℕ → ℝ) :
    band U L B (fun b => v b - w b) m = band U L B v m - band U L B w m := by
  simp only [band, mul_sub, sum_sub_distrib]

/-- Exact difference of the two prime cutoffs. -/
theorem topPrime_sqrt_sub_distance (n m : ℕ) (hVD : n.sqrt ≤ distanceCut n) :
    topPrime n n.sqrt m - topPrime n (distanceCut n) m = middlePrimeCoeff n m := by
  rw [topPrime_eq_band, topPrime_eq_band]
  unfold middlePrimeCoeff
  rw [← band_sub]
  congr 1
  funext r
  by_cases hs : n.sqrt < r <;> by_cases hd : distanceCut n < r <;>
    simp [highPrimeWeight, middlePrimeWeight, hs, hd] <;> omega

theorem topPrime_sqrt_sub_distance_fun (n : ℕ) (hVD : n.sqrt ≤ distanceCut n) :
    (fun m => topPrime n n.sqrt m - topPrime n (distanceCut n) m) = middlePrimeCoeff n :=
  funext (fun m => topPrime_sqrt_sub_distance n m hVD)

theorem abs_middlePrimeWeight_le (n b : ℕ) :
    |middlePrimeWeight n b| ≤ ArithmeticFunction.vonMangoldt b := by
  unfold middlePrimeWeight
  split_ifs
  · exact abs_primeWeight_le b
  · simpa using ArithmeticFunction.vonMangoldt_nonneg (n := b)

/-- The intermediate coefficients vanish above `B₁·D`. -/
theorem middlePrimeCoeff_eq_zero (n m : ℕ) (hm : cutoffL n * distanceCut n < m) :
    middlePrimeCoeff n m = 0 := by
  unfold middlePrimeCoeff band
  apply sum_eq_zero
  intro a ha
  obtain ⟨hdiv, _, haB, _⟩ := mem_filter.mp ha
  have hlarge : ¬(n.sqrt < m / a ∧ m / a ≤ distanceCut n) := by
    rintro ⟨_, hD⟩
    have hprod := Nat.mul_le_mul haB hD
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hdiv)] at hprod
    omega
  simp [middlePrimeWeight, hlarge]

/-- **Intermediate-prime energy**, localized to `m ≤ B₁·D`. -/
theorem middlePrimeCoeff_l2 (n : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n + 1), (middlePrimeCoeff n m) ^ 2 ≤
      ((cutoffL n * distanceCut n + 1 : ℕ) : ℝ) * (T ^ 2 * Real.log n) ^ 2 := by
  let A := (T ^ 2 * Real.log n) ^ 2
  calc
    _ ≤ ∑ m ∈ range (n + 1), if m ≤ cutoffL n * distanceCut n then A else 0 := by
      refine sum_le_sum fun m hm => ?_
      by_cases h : m ≤ cutoffL n * distanceCut n
      · simp only [ite_eq_left h, A]
        rw [← sq_abs (middlePrimeCoeff n m)]
        exact pow_le_pow_left₀ (abs_nonneg _) (band_uniform_bound n (cutoffU n) (cutoffU n)
          (cutoffL n) m (Nat.le_of_lt_succ (mem_range.mp hm)) hn hdiv
          (abs_middlePrimeWeight_le n)) 2
      · simp [h, middlePrimeCoeff_eq_zero n m (Nat.lt_of_not_ge h)]
    _ ≤ ∑ _m ∈ range (cutoffL n * distanceCut n + 1), A := by
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun m hm => mem_range.mpr (by have := (mem_filter.mp hm).2; omega))
        (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp [A]

/-- The cell with both prime cofactors above `D = ⌊n^(2/3)⌋`. -/
def strongPrimeCell (n : ℕ) : ℂ :=
  pairIntegral (deep n) n (topPrime n (distanceCut n)) (topPrime n (distanceCut n))

/-- Difference of squares in the form needed for the energy estimate. -/
theorem primeCell_sub_strongPrimeCell (n : ℕ) (hVD : n.sqrt ≤ distanceCut n) :
    primeCell n - strongPrimeCell n = pairIntegral (deep n) n (middlePrimeCoeff n)
      (fun m => topPrime n n.sqrt m + topPrime n (distanceCut n) m) := by
  rw [primeCell, strongPrimeCell, pairIntegral_sub_squares (deep n) (wide_measurable ..).compl,
    topPrime_sqrt_sub_distance_fun n hVD]

/-- **Explicit error when raising the prime cutoff to `n^(2/3)`.** -/
theorem primeCell_strongPrimeCell_error :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖primeCell n - strongPrimeCell n‖ ≤ K * (n : ℝ) ^ (191 / 192 : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  let A₀ := 384 ^ 2 * C ^ 4
  let K := 5 * A₀
  have hA0 : 0 ≤ A₀ := by dsimp [A₀]; positivity
  refine ⟨K, by dsimp [K]; positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  let X := (n : ℝ) ^ (1 / 384 : ℝ)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hn0 _
  have hX1 : 1 ≤ X := Real.one_le_rpow hnR (by norm_num)
  have hXpow (k : ℕ) : X ^ k = (n : ℝ) ^ ((k : ℝ) / 384) := by
    dsimp [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hlog : Real.log n ≤ 384 * X := by
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) < 1 / 384)
    calc Real.log n ≤ X / (1 / 384 : ℝ) := by simpa only [X] using h
      _ = 384 * X := by ring
  have hA : ((C * (n : ℝ) ^ (1 / 128 : ℝ)) ^ 2 * Real.log n) ^ 2 ≤ A₀ * X ^ 14 := by
    have hn3 : (n : ℝ) ^ (1 / 128 : ℝ) = X ^ 3 := by rw [hXpow]; norm_num
    rw [hn3]
    calc
      _ ≤ ((C * X ^ 3) ^ 2 * (384 * X)) ^ 2 := by gcongr
      _ = A₀ * X ^ 14 := by dsimp [A₀]; ring
  have hB : (cutoffL n : ℝ) ≤ X ^ 96 := by
    rw [hXpow]
    norm_num
    exact Nat.floor_le (by positivity)
  have hD : (distanceCut n : ℝ) ≤ X ^ 256 := by
    rw [hXpow]
    norm_num
    exact Nat.floor_le (by positivity)
  have hBD1 : ((cutoffL n * distanceCut n + 1 : ℕ) : ℝ) ≤ 2 * X ^ 352 := by
    push_cast
    have hprod : (cutoffL n : ℝ) * (distanceCut n : ℝ) ≤ X ^ 352 := by
      calc
        _ ≤ X ^ 96 * X ^ 256 := mul_le_mul hB hD (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    have h1 : 1 ≤ X ^ 352 := one_le_pow₀ hX1
    nlinarith
  have hMid : (∑ m ∈ range (n + 1), (middlePrimeCoeff n m) ^ 2) ≤
      2 * A₀ * X ^ 366 := by
    calc
      _ ≤ ((cutoffL n * distanceCut n + 1 : ℕ) : ℝ) *
          ((C * (n : ℝ) ^ (1 / 128 : ℝ)) ^ 2 * Real.log n) ^ 2 :=
        middlePrimeCoeff_l2 n hn (fun m hm => hdiv n m hm)
      _ ≤ (2 * X ^ 352) * (A₀ * X ^ 14) := by gcongr
      _ = _ := by ring
  have htop (V : ℕ) : (∑ m ∈ range (n + 1), (topPrime n V m) ^ 2) ≤
      2 * A₀ * X ^ 398 := by
    have hn1 : ((n : ℝ) + 1) ≤ 2 * X ^ 384 := by
      have h1 : 1 ≤ X ^ 384 := one_le_pow₀ hX1
      rw [hXpow]
      norm_num
      linarith
    calc
      _ ≤ ((n : ℝ) + 1) * ((C * (n : ℝ) ^ (1 / 128 : ℝ)) ^ 2 * Real.log n) ^ 2 :=
        topPrime_l2_bound n V hn (fun m hm => hdiv n m hm)
      _ ≤ (2 * X ^ 384) * (A₀ * X ^ 14) := by gcongr
      _ = _ := by ring
  have hSum : (∑ m ∈ range (n + 1),
      (topPrime n n.sqrt m + topPrime n (distanceCut n) m) ^ 2) ≤ 8 * A₀ * X ^ 398 := by
    calc
      _ ≤ ∑ m ∈ range (n + 1), 2 *
          (topPrime n n.sqrt m ^ 2 + topPrime n (distanceCut n) m ^ 2) := by
        refine sum_le_sum fun m _ => ?_
        nlinarith [sq_nonneg (topPrime n n.sqrt m - topPrime n (distanceCut n) m)]
      _ = 2 * ((∑ m ∈ range (n + 1), (topPrime n n.sqrt m) ^ 2) +
          ∑ m ∈ range (n + 1), (topPrime n (distanceCut n) m) ^ 2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 2 * (2 * A₀ * X ^ 398 + 2 * A₀ * X ^ 398) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (htop _) (htop _)) (by norm_num)
      _ = _ := by ring
  have hVD : n.sqrt ≤ distanceCut n := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    apply Nat.floor_mono
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  rw [primeCell_sub_strongPrimeCell n hVD]
  calc
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ (1 / 24 : ℝ) *
          (∑ m ∈ range (n + 1), (middlePrimeCoeff n m) ^ 2) +
        ((n : ℝ) ^ (1 / 24 : ℝ))⁻¹ *
          (∑ m ∈ range (n + 1),
            (topPrime n n.sqrt m + topPrime n (distanceCut n) m) ^ 2)) :=
      pairIntegral_le_energy (deep n) (wide_measurable ..).compl n _ _
        (Real.rpow_pos_of_pos hn0 _)
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ (1 / 24 : ℝ) * (2 * A₀ * X ^ 366) +
        ((n : ℝ) ^ (1 / 24 : ℝ))⁻¹ * (8 * A₀ * X ^ 398)) := by gcongr
    _ = K * X ^ 382 := by
      have hscale : (n : ℝ) ^ (1 / 24 : ℝ) = X ^ 16 := by rw [hXpow]; norm_num
      rw [hscale]
      dsimp [K]
      field_simp
      ring
    _ = K * (n : ℝ) ^ (191 / 192 : ℝ) := by rw [hXpow]; norm_num

/-- The cutoff-replacement error is `o(n)`. -/
theorem primeCell_strongPrimeCell_error_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖primeCell n - strongPrimeCell n‖ ≤ e * (n : ℝ) := by
  obtain ⟨K, _, hK⟩ := primeCell_strongPrimeCell_error
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(1 / 192 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 192)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, mul_zero] using (tendsto_const_nhds (x := K)).mul hp
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_lt_const he] with n hn hsmall
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ K * (n : ℝ) ^ (191 / 192 : ℝ) := hK n hn
    _ = (K * (n : ℝ) ^ (-(1 / 192 : ℝ))) * (n : ℝ) := by
      rw [mul_assoc, show (191 / 192 : ℝ) = -(1 / 192 : ℝ) + 1 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hpos.le

/-- **The two prime cutoffs have equivalent deep-minor estimates.** -/
theorem primeCell_iff_strongPrimeCell : smallEven primeCell ↔ smallEven strongPrimeCell := by
  constructor
  · apply smallEven_transfer
    intro e he
    filter_upwards [primeCell_strongPrimeCell_error_eventually e he] with n hn
    simpa only [norm_sub_rev (strongPrimeCell n) (primeCell n)] using hn
  · exact smallEven_transfer primeCell_strongPrimeCell_error_eventually

/-- **The original cell is equivalent to the cell with both primes above `n^(2/3)`.** -/
theorem fullCell_iff_strongPrimeCell : smallEven fullCell ↔ smallEven strongPrimeCell :=
  fullCell_iff_primeCell.trans primeCell_iff_strongPrimeCell

/-! ### Milestone 58: row expansion for primes above `D = n^(2/3)` -/

/-- Primes above the strengthened cutoff. -/
def strongPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ => distanceCut n < p ∧ p.Prime)

/-- Product support for a strong prime and its short divisor. -/
def strongRowSupport (n : ℕ) : Finset (ℕ × ℕ) :=
  (strongPrimes n ×ˢ range (cutoffL n + 1)).filter (fun i : ℕ × ℕ =>
    cutoffU n < i.2 ∧ cutoffU n < i.1 ∧ i.2 * i.1 ≤ n)

/-- Product of the short divisor and strong prime. -/
def strongProduct (i : ℕ × ℕ) : ℕ := i.2 * i.1

private theorem strongSupportInfo {i : ℕ × ℕ} {n : ℕ} (hi : i ∈ strongRowSupport n) :
    i.1 ∈ strongPrimes n ∧ i.2 ≤ cutoffL n ∧ cutoffU n < i.2 ∧ cutoffU n < i.1 ∧
      i.2 * i.1 ≤ n := by
  simpa [strongRowSupport, and_assoc, Nat.lt_succ_iff] using hi

private theorem strongSupport_dvd {i : ℕ × ℕ} {n : ℕ} (hi : i ∈ strongRowSupport n) :
    0 < strongProduct i ∧ strongProduct i ≤ n ∧ i.2 ∣ strongProduct i ∧
      strongProduct i / i.2 = i.1 := by
  obtain ⟨hp, _, ha, _, hn⟩ := strongSupportInfo hi
  have ha' : 0 < i.2 := Nat.zero_lt_of_lt ha
  have hp' := (mem_filter.mp hp).2.2.pos
  exact ⟨Nat.mul_pos ha' hp', hn, dvd_mul_right .., Nat.mul_div_cancel_left _ ha'⟩

private theorem strongSupport_inj (n : ℕ) (hn : 1 ≤ n) :
    Set.InjOn strongProduct (strongRowSupport n : Set (ℕ × ℕ)) := by
  have hVD : n.sqrt ≤ distanceCut n := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    apply Nat.floor_mono
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  intro i hi j hj he
  obtain ⟨hm, hnprod, hd, heq⟩ := strongSupport_dvd hi
  obtain ⟨_, _, hj', heq'⟩ := strongSupport_dvd hj
  rw [← he] at hj' heq'
  have hiP := (mem_filter.mp (strongSupportInfo hi).1).2
  have hjP := (mem_filter.mp (strongSupportInfo hj).1).2
  rw [← heq] at hiP
  rw [← heq'] at hjP
  have ha := unique_large_prime_cofactor hm hnprod hd hj' hiP.2 hjP.2
    (hVD.trans_lt hiP.1) (hVD.trans_lt hjP.1)
  exact Prod.ext (by rw [← heq, ha, heq']) ha

private theorem divisor_to_strongSupport {n m a : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (ha : a ∈ (Nat.divisors m).filter (fun a => cutoffU n < a ∧ a ≤ cutoffL n ∧
      cutoffU n < m / a ∧ distanceCut n < m / a)) (hp : (m / a).Prime) :
    (m / a, a) ∈ strongRowSupport n ∧ strongProduct (m / a, a) = m := by
  obtain ⟨had, haU, haB, hrU, hrD⟩ := mem_filter.mp ha
  have heq := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors had)
  have hle := (Nat.div_le_self m a).trans hm
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr
    ⟨mem_range.mpr (Nat.lt_succ_of_le hle), hrD, hp⟩,
    mem_range.mpr (Nat.lt_succ_of_le haB)⟩, haU, hrU, ?_⟩, heq⟩
  exact heq.le.trans hm

private theorem topPrime_on_strongProduct {n : ℕ} {i : ℕ × ℕ} (hn : 1 ≤ n)
    (hi : i ∈ strongRowSupport n) :
    topPrime n (distanceCut n) (strongProduct i) =
      lowMoebiusWeight (cutoffU n) i.2 * Real.log i.1 := by
  obtain ⟨hp, hB, ha, hr, _⟩ := strongSupportInfo hi
  obtain ⟨hm, hnprod, hd, heq⟩ := strongSupport_dvd hi
  have hp' := (mem_filter.mp hp).2
  have ha : i.2 ∈ (Nat.divisors (strongProduct i)).filter
      (fun a => cutoffU n < a ∧ a ≤ cutoffL n ∧ cutoffU n < strongProduct i / a ∧
        distanceCut n < strongProduct i / a) := by
    apply mem_filter.mpr
    rw [heq]
    refine ⟨Nat.mem_divisors.mpr ⟨hd, hm.ne'⟩, ha, hB, ?_⟩
    exact ⟨hr, hp'.1⟩
  unfold topPrime
  rw [sum_eq_single_of_mem i.2 ha, heq]
  · simp [primeWeight, hp'.2]
  · intro a ha' hne
    by_cases hpa : (strongProduct i / a).Prime
    · obtain ⟨hs, he⟩ := divisor_to_strongSupport hn hnprod ha' hpa
      have same := strongSupport_inj n hn hs hi he
      exact (hne (congrArg Prod.snd same)).elim
    · simp [hpa]

private theorem topPrime_off_strongProduct {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (hoff : m ∉ (strongRowSupport n).image strongProduct) :
    topPrime n (distanceCut n) m = 0 := by
  unfold topPrime
  refine sum_eq_zero fun a ha => ?_
  obtain ⟨had, haU, haB, hrU, hrD⟩ := mem_filter.mp ha
  by_cases hp : (m / a).Prime
  · obtain ⟨hs, he⟩ := divisor_to_strongSupport hn hm ha hp
    exact (hoff (mem_image.mpr ⟨_, hs, he⟩)).elim
  · simp [hp]

private theorem phase_eq_mode_nat' (m : ℕ) (t : ℝ) : phase (m * t) = mode m t := by
  unfold phase mode frequency
  congr 1
  push_cast
  ring

private theorem mode_row_index' (a p : ℕ) (t : ℝ) : mode a (p * t) = mode ((a * p : ℕ) : ℤ) t := by
  unfold mode frequency
  congr 1
  push_cast
  ring

private theorem primeRowCoeff_on_support {n p a : ℕ}
    (h : (p, a) ∈ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n)) :
    primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) p a =
      ((lowMoebiusWeight (cutoffU n) a * Real.log p : ℝ) : ℂ) := by
  unfold primeRowCoeff
  rw [if_pos h]
  rfl

private theorem strongSupport_row {n : ℕ} {i : ℕ × ℕ} (hi : i ∈ strongRowSupport n) :
    (i.1, i.2) ∈ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n) := by
  obtain ⟨hp, haB, haU, hpU, hprod⟩ := strongSupportInfo hi
  simp only [rowSupport, mem_filter, mem_product, mem_range, Nat.lt_succ_iff]
  refine ⟨⟨?_, haB⟩, haU, hpU, hprod⟩
  obtain ⟨hpN, hD, hprime⟩ := mem_filter.mp hp
  have hn : 1 ≤ n := by
    have : 0 < i.2 := by omega
    have : 0 < i.1 := (mem_filter.mp hp).2.2.pos
    have : 0 < i.2 * i.1 := Nat.mul_pos ‹_› ‹_›
    omega
  have hVD : n.sqrt ≤ distanceCut n := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    apply Nat.floor_mono
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  exact mem_filter.mpr ⟨hpN, hVD.trans_lt hD, hprime⟩

private theorem notStrongSupport_row {n : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ strongPrimes n ×ˢ range (cutoffL n + 1)) (hnot : i ∉ strongRowSupport n) :
    (i.1, i.2) ∉ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n) := by
  intro h
  apply hnot
  obtain ⟨hp, ha⟩ := mem_product.mp hi
  simp only [rowSupport, mem_filter, mem_product, mem_range, Nat.lt_succ_iff] at h
  obtain ⟨⟨hpbig, haB⟩, haU, hpU, hprod⟩ := h
  simp only [strongRowSupport, mem_filter, mem_product, mem_range, Nat.lt_succ_iff]
  exact ⟨⟨hp, haB⟩, haU, hpU, hprod⟩

/-- **Strong-prime row expansion.** -/
theorem topPrime_strong_rows (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    fourierSum n (topPrime n (distanceCut n)) t =
    ∑ p ∈ strongPrimes n, row (cutoffL n + 1) p
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) p) t := by
  classical
  let S := strongRowSupport n
  let f (m : ℕ) := ((topPrime n (distanceCut n) m : ℝ) : ℂ) * phase (m * t)
  have subset : S.image strongProduct ⊆ range (n + 1) := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hm
    exact mem_range.mpr (Nat.lt_succ_of_le (strongSupport_dvd hi).2.1)
  calc
    _ = ∑ m ∈ S.image strongProduct, f m := by
      symm
      apply sum_subset subset
      intro m hm hoff
      simp [f, topPrime_off_strongProduct hn (Nat.le_of_lt_succ (mem_range.mp hm)) hoff]
    _ = ∑ i ∈ S, f (strongProduct i) := sum_image (strongSupport_inj n hn)
    _ = ∑ i ∈ S, ((lowMoebiusWeight (cutoffU n) i.2 * Real.log i.1 : ℝ) : ℂ) *
        mode i.2 (i.1 * t) := by
      refine sum_congr rfl fun i hi => ?_
      unfold f
      rw [topPrime_on_strongProduct hn hi, phase_eq_mode_nat', mode_row_index']
      rfl
    _ = ∑ i ∈ strongPrimes n ×ˢ range (cutoffL n + 1),
        primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) i.1 i.2 *
          mode i.2 (i.1 * t) := by
      rw [← sum_filter_add_sum_filter_not (strongPrimes n ×ˢ range (cutoffL n + 1))
        (fun i => i ∈ S)]
      have ident : ((strongPrimes n ×ˢ range (cutoffL n + 1)).filter (fun i => i ∈ S)) = S :=
        filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
      rw [ident, sum_eq_zero (s := (strongPrimes n ×ˢ range (cutoffL n + 1)).filter
        fun i => i ∉ S), add_zero]
      · refine sum_congr rfl fun i hi => ?_
        rw [primeRowCoeff_on_support (strongSupport_row hi)]
      · intro i hi
        have hnrow := notStrongSupport_row (mem_filter.mp hi).1 (mem_filter.mp hi).2
        simp [primeRowCoeff, hnrow]
    _ = _ := sum_product ..

/-- **Strong prime cell in prime-row form, on any measurable arc set.** -/
theorem strongPrimeCellOn_arcRows (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ) (hn : 1 ≤ n) :
    pairIntegral s n (topPrime n (distanceCut n)) (topPrime n (distanceCut n)) =
    arcRows s (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) := by
  have point (t : ℝ) :
      fourierSum n (topPrime n (distanceCut n)) t *
        fourierSum n (topPrime n (distanceCut n)) t * phase (-(n : ℝ) * t) =
      pairRows (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t := by
    rw [topPrime_strong_rows n hn]
    unfold pairRows
    have hphase : phase (-(n : ℝ) * t) = mode (-(n : ℤ)) t := by
      unfold phase mode frequency
      congr 1
      push_cast
      ring
    rw [hphase, sum_product, sum_mul]
    congr 1
    exact sum_congr rfl fun _ _ => mul_sum ..
  unfold pairIntegral arcRows
  simp_rw [point]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    integral_indicator hs, Measure.restrict_restrict hs, Set.inter_comm]

/-- The strong prime cell on the deep minor arcs. -/
theorem strongPrimeCell_eq_arcRows (n : ℕ) (hn : 1 ≤ n) :
    strongPrimeCell n = arcRows (deep n) (strongPrimes n ×ˢ strongPrimes n)
      (cutoffL n + 1) n (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) :=
  strongPrimeCellOn_arcRows (deep n) (wide_measurable ..).compl n hn

/-- The first-band cutoff is below the strengthened distance/prime cutoff. -/
theorem cutoffL_le_distanceCut {n : ℕ} (hn : 1 ≤ n) : cutoffL n ≤ distanceCut n := by
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

/-- Wide-arc integral over strong-prime pairs. -/
def strongWidePrimePairs (n : ℕ) : ℂ :=
  arcRows (wide n (cutoffB n) (arcHeight n)) (strongPrimes n ×ˢ strongPrimes n)
    (cutoffL n + 1) n (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))

/-- Full-circle contribution of distant strong-prime pairs. -/
def strongDistantPrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (farPairs (strongPrimes n) (distanceCut n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- Full-circle contribution of close strong-prime pairs. -/
def strongClosePrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (closePairs (strongPrimes n) (distanceCut n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- Distant strong-prime residual. -/
def strongDistantResidual (n : ℕ) : ℂ := strongDistantPrimeFull n - strongWidePrimePairs n

/-- The strong prime cell as a full-circle minus wide-arc discrepancy. -/
theorem strongPrimeCell_eq_full_sub_wide (n : ℕ) (hn : 1 ≤ n) :
    strongPrimeCell n =
      (∫ t in (0:ℝ)..1, pairRows (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t) -
      strongWidePrimePairs n := by
  rw [strongPrimeCell_eq_arcRows n hn]
  exact eq_sub_iff_add_eq.mpr (arcRows_partition (wide n (cutoffB n) (arcHeight n))
    (wide_measurable ..) (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)))

/-- Strong-prime full circle splits into distant and close pairs. -/
theorem strongFull_eq_distant_add_close (n : ℕ) :
    (∫ t in (0:ℝ)..1, pairRows (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t) =
    strongDistantPrimeFull n + strongClosePrimeFull n := by
  have hsubset : closePairs (strongPrimes n) (distanceCut n) ⊆ strongPrimes n ×ˢ strongPrimes n :=
    Finset.filter_subset _ _
  have point (t : ℝ) :
      pairRows (strongPrimes n ×ˢ strongPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t =
      pairRows (farPairs (strongPrimes n) (distanceCut n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t +
      pairRows (closePairs (strongPrimes n) (distanceCut n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t := by
    unfold pairRows farPairs
    rw [← add_mul, sum_sdiff hsubset]
  simp_rw [point]
  apply intervalIntegral.integral_add
  · exact (continuous_pairRows ..).intervalIntegrable 0 1
  · exact (continuous_pairRows ..).intervalIntegrable 0 1

/-- The strong-cell discrepancy from its distant residual is exactly the close mass. -/
theorem strongPrimeCell_sub_distantResidual (n : ℕ) (hn : 1 ≤ n) :
    strongPrimeCell n - strongDistantResidual n = strongClosePrimeFull n := by
  unfold strongDistantResidual strongWidePrimePairs
  rw [strongPrimeCell_eq_full_sub_wide n hn, strongFull_eq_distant_add_close]
  unfold strongWidePrimePairs
  ring_nf

/-- The strong close-pair mass is `o(n)`, using the generic close-pair theorem. -/
theorem strongClosePrimeFull_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖strongClosePrimeFull n‖ ≤ e * (n : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  exact closeFull_eventually C hC hdiv (fun n => strongPrimes n)
    (fun n => primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))
    (fun n => primeRowCoeff_zero n)
    (fun n hn p hp a ha => primeRowCoeff_norm_le_envelope n hn (by positivity)
      (fun m hm => hdiv n m hm) p a) e he

/-- The strong cell and its distant residual have equivalent `smallEven` estimates. -/
theorem strongPrimeCell_iff_distantResidual :
    smallEven strongPrimeCell ↔ smallEven strongDistantResidual := by
  constructor
  · apply smallEven_transfer
    intro e he
    filter_upwards [eventually_ge_atTop 1, strongClosePrimeFull_eventually e he] with n hn1 hn
    have heq := strongPrimeCell_sub_distantResidual n hn1
    rw [← heq] at hn
    simpa only [norm_sub_rev] using hn
  · apply smallEven_transfer
    intro e he
    filter_upwards [eventually_ge_atTop 1, strongClosePrimeFull_eventually e he] with n hn1 hn
    have heq := strongPrimeCell_sub_distantResidual n hn1
    simpa only [heq] using hn

/-- Inverse-residue sum over distant strong-prime pairs. -/
def strongDistantInverseTotal (n : ℕ) : ℂ :=
  ∑ pq ∈ farPairs (strongPrimes n) (distanceCut n),
    inversePair n (cutoffL n)
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) pq.1 pq.2

/-- The distant strong-prime full circle is an inverse-residue sum. -/
theorem strongDistantPrimeFull_eq_inverseTotal (n : ℕ) (hn : 1 ≤ n) :
    strongDistantPrimeFull n = strongDistantInverseTotal n := by
  classical
  unfold strongDistantPrimeFull strongDistantInverseTotal
  rw [full_pairRows, Finset.sum_filter]
  change (∑ i ∈ (farPairs (strongPrimes n) (distanceCut n) ×ˢ
      (Finset.range (cutoffL n + 1) ×ˢ Finset.range (cutoffL n + 1))),
      if i.2.1 * i.1.1 + i.2.2 * i.1.2 = n then
        primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) i.1.1 i.2.1 *
          primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n) i.1.2 i.2.2 else 0) = _
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  obtain ⟨hm, hout⟩ := Finset.mem_sdiff.mp hpq
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hm
  have hne : pq.1 ≠ pq.2 := by
    intro heq
    apply hout
    exact Finset.mem_filter.mpr ⟨hm, by simp [heq]⟩
  exact rowMass_eq_inversePair (Finset.mem_filter.mp hp).2.2
    (Finset.mem_filter.mp hq).2.2 hne
    ((cutoffL_le_distanceCut hn).trans_lt (Finset.mem_filter.mp hq).2.1) _

/-- The strong distant residual in inverse-residue form. -/
def strongInverseResidual (n : ℕ) : ℂ := strongDistantInverseTotal n - strongWidePrimePairs n

theorem strongDistantResidual_eq_inverse (n : ℕ) (hn : 1 ≤ n) :
    strongDistantResidual n = strongInverseResidual n := by
  unfold strongDistantResidual strongInverseResidual
  rw [strongDistantPrimeFull_eq_inverseTotal n hn]

/-- Fully symmetric reciprocal sum over distant strong-prime pairs. -/
def strongReciprocalTotal (n : ℕ) : ℂ :=
  let c := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)
  ∑ pq ∈ farPairs (strongPrimes n) (distanceCut n),
    c pq.1 (inverseResidue n pq.1 pq.2) * c pq.2 (inverseResidue n pq.2 pq.1)

/-- Symmetric reciprocal form of the strong inverse-residue sum. -/
theorem strongDistantInverseTotal_eq_reciprocal (n : ℕ) (hn : 16 ≤ n) :
    strongDistantInverseTotal n = strongReciprocalTotal n := by
  classical
  let c := primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)
  unfold strongDistantInverseTotal strongReciprocalTotal
  refine Finset.sum_congr rfl fun pq hpq => ?_
  obtain ⟨hm, hout⟩ := Finset.mem_sdiff.mp hpq
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hm
  have hne : pq.1 ≠ pq.2 := by
    intro heq
    apply hout
    exact Finset.mem_filter.mpr ⟨hm, by simp [heq]⟩
  have hVD : n.sqrt ≤ distanceCut n := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    apply Nat.floor_mono
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  have hpD := (Finset.mem_filter.mp hp).2.1
  have hqD := (Finset.mem_filter.mp hq).2.1
  have hnq : n < pq.1 * pq.2 := by
    have hpS : n.sqrt + 1 ≤ pq.1 := Nat.succ_le_of_lt (hVD.trans_lt hpD)
    have hqS : n.sqrt + 1 ≤ pq.2 := Nat.succ_le_of_lt (hVD.trans_lt hqD)
    exact (Nat.lt_succ_sqrt n).trans_le (Nat.mul_le_mul hpS hqS)
  apply inversePair_symmetric (Finset.mem_filter.mp hp).2.2 (Finset.mem_filter.mp hq).2.2 hne hnq
    (((twice_cutoffL_le_sqrt hn).trans hVD).trans_lt hqD)
    (((twice_cutoffL_le_sqrt hn).trans hVD).trans_lt hpD)
  intro p a ha
  have hnot : (p, a) ∉ rowSupport n (cutoffU n) (cutoffU n) (cutoffL n) := by
    intro h
    have hmem := (Finset.mem_filter.mp h).1
    have haB : a ≤ cutoffL n := Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_product.mp hmem).2)
    omega
  simp [c, primeRowCoeff, hnot]

/-- The strong residual in symmetric reciprocal form. -/
def strongReciprocalResidual (n : ℕ) : ℂ := strongReciprocalTotal n - strongWidePrimePairs n

/-- The strong inverse and reciprocal residuals are eventually equal. -/
theorem strongInverseResidual_eq_reciprocal (n : ℕ) (hn : 16 ≤ n) :
    strongInverseResidual n = strongReciprocalResidual n := by
  unfold strongInverseResidual strongReciprocalResidual
  rw [strongDistantInverseTotal_eq_reciprocal n hn]

/-- **Full reduction to the strong symmetric reciprocal residual.** -/
theorem fullCell_iff_strongReciprocalResidual :
    smallEven fullCell ↔ smallEven strongReciprocalResidual := by
  have h₁ : smallEven fullCell ↔ smallEven strongDistantResidual :=
    fullCell_iff_strongPrimeCell.trans strongPrimeCell_iff_distantResidual
  rw [h₁]
  have transform {f g : ℕ → ℂ} (h : ∀ n, 16 ≤ n → f n = g n) : smallEven f → smallEven g := by
    intro hf e he
    obtain ⟨N, hN⟩ := hf e he
    refine ⟨max 16 N, fun n hn heven => ?_⟩
    rw [← h n ((le_max_left ..).trans hn)]
    exact hN n ((le_max_right ..).trans hn) heven
  exact ⟨transform (fun n hn => (strongDistantResidual_eq_inverse n (by omega)).trans
      (strongInverseResidual_eq_reciprocal n hn)),
    transform (fun n hn => ((strongDistantResidual_eq_inverse n (by omega)).trans
      (strongInverseResidual_eq_reciprocal n hn)).symm)⟩

/-- Definitional comparison of the frozen catalogue statement with the strong residual. -/
theorem frozen_iff_strongReciprocalResidual :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1))
      (fun k => (u k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
    let H := fun n : ℕ => 256 * Q₁ n * Q n;
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧
      Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))};
    let Λ := ArithmeticFunction.vonMangoldt;
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊;
    let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊;
    let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter
      (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a),
      (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a);
    let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral
      (fun t => (wideArcs n)ᶜ.indicator
        (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ)) ↔ smallEven strongReciprocalResidual := by
  exact fullCell_iff_strongReciprocalResidual

end B1B1Fixed
