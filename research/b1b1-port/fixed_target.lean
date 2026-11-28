import Conjectures.Goldbach.Type2FixedTargetReciprocalError

/-!
# Fixed-target form of the first Type-II cell

This module is separate from `b1b1_port.lean` because the fixed-target library and the
b1-b4 library currently define duplicate constants in `DyadicMixedB4Fourier` and cannot be
imported together.  All cutoffs below are those of the first band: `L = U`, `B = B₁`.
-/

open Filter Topology Finset MeasureTheory
open GoldbachTransitionSquare

set_option maxHeartbeats 4000000

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

/-- Full-circle contribution of pairs at distance greater than `B₁`. -/
def distantPrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (farPairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- Full-circle contribution of pairs at distance at most `B₁`. -/
def closePrimeFull (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, pairRows (closePairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t

/-- The remaining residual after discarding close pairs from the full circle only. -/
def distantResidual (n : ℕ) : ℂ := distantPrimeFull n - widePrimePairs n

/-- Full-circle prime pairs split into distant and close pairs. -/
theorem full_eq_distant_add_close (n : ℕ) :
    (∫ t in (0:ℝ)..1, pairRows (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t) =
    distantPrimeFull n + closePrimeFull n := by
  have hsubset : closePairs (bigPrimes n) (cutoffL n) ⊆ bigPrimes n ×ˢ bigPrimes n :=
    Finset.filter_subset _ _
  have point (t : ℝ) :
      pairRows (bigPrimes n ×ˢ bigPrimes n) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t =
      pairRows (farPairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t +
      pairRows (closePairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
        (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) t := by
    unfold pairRows farPairs
    rw [← add_mul, sum_sdiff hsubset]
  simp_rw [point]
  apply intervalIntegral.integral_add
  · exact (continuous_pairRows (farPairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))).intervalIntegrable 0 1
  · exact (continuous_pairRows (closePairs (bigPrimes n) (cutoffL n)) (cutoffL n + 1) n
      (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n))).intervalIntegrable 0 1

/-- The discrepancy from the distant-pair residual is exactly the close full-circle mass. -/
theorem primeCell_sub_distantResidual (n : ℕ) :
    primeCell n - distantResidual n = closePrimeFull n := by
  unfold distantResidual widePrimePairs
  rw [primeCell_eq_full_sub_wide, full_eq_distant_add_close]
  ring

/-- **Close-pair power saving**, using the existing full-circle counting estimate. -/
theorem closePrimeFull_bound (n : ℕ) (hn : 1 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ)) :
    ‖closePrimeFull n‖ ≤
      (cutoffL n : ℝ) ^ 2 * (2 * (cutoffL n : ℝ) + 1) *
        (C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n) ^ 2 := by
  exact closePairs_full (bigPrimes n) (cutoffL n) (cutoffL n) n
    (primeRowCoeff n (cutoffU n) (cutoffU n) (cutoffL n)) (primeRowCoeff_zero n)
    (fun p _ a _ => primeRowCoeff_norm_le_envelope n hn hC0 hC p a)

/-- **The distant-pair residual differs from b1-b1's prime cell by an explicit small mass.**
Its scale is `n^(49/64) (log n)^2`, hence `o(n)`. -/
theorem primeCell_distantResidual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖primeCell n - distantResidual n‖ ≤
        (cutoffL n : ℝ) ^ 2 * (2 * (cutoffL n : ℝ) + 1) *
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

/-- Inverse-residue sum over prime pairs at distance greater than `B₁`. -/
def distantInverseTotal (n : ℕ) : ℂ :=
  ∑ pq ∈ farPairs (bigPrimes n) (cutoffL n),
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
  change (∑ i ∈ (farPairs (bigPrimes n) (cutoffL n) ×ˢ
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

/-- The close-pair mass is eventually below any linear error budget. -/
theorem closePrimeFull_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖closePrimeFull n‖ ≤ e * (n : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  let K := 3 * C ^ 2 * 128 ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(7 / 32 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 32)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, mul_zero] using (tendsto_const_nhds (x := K)).mul hp
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_lt_const he] with n hn hsmall
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  let X := (n : ℝ) ^ (1 / 128 : ℝ)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hn0 _
  have hX1 : 1 ≤ X := Real.one_le_rpow hnR (by norm_num)
  have hXpow (k : ℕ) : X ^ k = (n : ℝ) ^ ((k : ℝ) / 128) := by
    dsimp [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hB : (cutoffL n : ℝ) ≤ X ^ 32 := by
    rw [hXpow]
    norm_num
    exact Nat.floor_le (by positivity)
  have hB2 : 2 * (cutoffL n : ℝ) + 1 ≤ 3 * X ^ 32 := by
    have h1 : 1 ≤ X ^ 32 := one_le_pow₀ hX1
    nlinarith
  have hlog : Real.log n ≤ 128 * X := by
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (Nat.cast_nonneg n)
      (by norm_num : (0 : ℝ) < 1 / 128)
    calc Real.log n ≤ X / (1 / 128 : ℝ) := by simpa only [X] using h
      _ = 128 * X := by ring
  calc
    _ ≤ (cutoffL n : ℝ) ^ 2 * (2 * (cutoffL n : ℝ) + 1) *
        (C * (n : ℝ) ^ (1 / 128 : ℝ) * Real.log n) ^ 2 :=
      closePrimeFull_bound n hn (by positivity) (fun m hm => hdiv n m hm)
    _ ≤ (X ^ 32) ^ 2 * (3 * X ^ 32) * (C * X * (128 * X)) ^ 2 := by
      change (cutoffL n : ℝ) ^ 2 * (2 * (cutoffL n : ℝ) + 1) *
        (C * X * Real.log n) ^ 2 ≤ _
      gcongr
    _ = K * X ^ 100 := by dsimp [K]; ring
    _ = K * (n : ℝ) ^ (100 / 128 : ℝ) := by rw [hXpow]; norm_num
    _ = (K * (n : ℝ) ^ (-(7 / 32 : ℝ))) * (n : ℝ) := by
      dsimp [K]
      rw [mul_assoc, show (100 / 128 : ℝ) = -(7 / 32 : ℝ) + 1 by norm_num,
        Real.rpow_add hn0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hn0.le

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

end B1B1Fixed
