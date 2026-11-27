import Mathlib
import Conjectures.Goldbach.RoughFifthMass


-- Source: twin-chen-reverse-weighted/upper-rosser-9d4/ReverseUpperRosserSuzukiActual.lean
section
/-
Source: subfish-zhou/goldbach-lean, revision 9d4c3a4010d42aedd9e7231bf94386019cfffccc.
Apache License 2.0. Original file: MathlibNt/SieveTheory/UpperRosserSuzukiActualBridge.lean.
Source Git blob: 99516e94f658d780953c5fa5542acceead023b0b.
Adapted to the dependency closure already checked in Goldbach PR 3771.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The unnormalised upper-Rosser boundary layer at pair depth `k`.
The distinguished terminal prime is outside the stored even chain, so this
is the odd Suzuki source layer `2*k+1`.  Its terminal factor is the Euler product
strictly below `q`, not an inverse suffix product. -/
noncomputable def upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) : ℝ :=
  ∑ q ∈ suzukiSupportedBelow S z,
    S.nu q * sourceDiscreteEuler S q *
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        ((suzukiSupportedBelow S z).filter (fun p => q < p)) k

private theorem upper_ceilDiv_ceilDiv_eq
    {D a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (D ⌈/⌉ a) ⌈/⌉ b = D ⌈/⌉ (a * b) := by
  exact MathlibNt.SieveTheory.ceilDiv_ceilDiv_eq ha hb

private theorem upperSuzukiUnnormalizedLayer_succ
    (S : BoundingSieve) (D z k : ℕ) :
    upperSuzukiUnnormalizedLayer S D z (k + 1) =
      ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D),
        S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
          S.nu p₁ * upperSuzukiUnnormalizedLayer S
            (D ⌈/⌉ (p₀ * p₁)) p₁ k := by
  classical
  let Z := suzukiSupportedBelow S z
  unfold upperSuzukiUnnormalizedLayer
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1)) = _
  have hexpand (q : ℕ) (hq : q ∈ Z) :
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1) =
        ∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k := by
    apply upperRosserBoundaryChainsFixedDepthDensity_succ S.nu
    · simp
    · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    · intro p hp
      exact Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
  have hrewrite :
      (∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          upperRosserBoundaryChainsFixedDepthDensity S.nu D q
            (Z.filter (fun p => q < p)) (k + 1)) =
      ∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          (∑ p₀ ∈ Z.filter (fun p => q < p),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu p₀ * S.nu p₁ *
                upperRosserBoundaryChainsFixedDepthDensity S.nu
                  (D ⌈/⌉ (p₀ * p₁)) q
                  ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hexpand q hq]
  rw [hrewrite]
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        (∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k)) = _
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ p₀ ∈ Z,
          ∑ q ∈ Z.filter (fun q => q < p₀),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_comm'
          intro q p₀
          simp only [Finset.mem_filter]
          tauto
    _ = ∑ p₀ ∈ Z,
          ∑ p₁ ∈ Z.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            ∑ q ∈ Z.filter (fun q => q < p₁),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_comm'
          intro q p₁
          constructor
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            have hp₁base := Finset.mem_filter.mp hp₁'.1
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hp₁base.2⟩,
              Finset.mem_filter.mpr ⟨hp₁base.1, hp₁'.2⟩⟩
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hq'.2.trans hp₁'.2.1⟩,
              Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨hp₁'.1, hq'.2⟩, hp₁'.2⟩⟩
    _ = ∑ p₀ ∈ Z.filter (fun p => p ^ 3 < D),
          S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
            S.nu p₁ *
              (∑ q ∈ suzukiSupportedBelow S p₁,
                S.nu q * sourceDiscreteEuler S q *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((suzukiSupportedBelow S p₁).filter (fun p => q < p)) k) := by
          rw [Finset.sum_filter]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          have hp₀z : p₀ < z := (Finset.mem_filter.mp hp₀).2
          by_cases hcut : p₀ ^ 3 < D
          · rw [if_pos hcut]
            apply Finset.sum_congr
            · ext p₁
              simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hp₁S, hp₁z⟩, hp₁p₀, _⟩
                exact ⟨hp₁S, hp₁p₀⟩
              · rintro ⟨hp₁S, hp₁p₀⟩
                exact ⟨⟨hp₁S, hp₁p₀.trans hp₀z⟩,
                  hp₁p₀, hcut⟩
            · intro p₁ hp₁
              have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
              have hp₁z : p₁ < z := hp₁p₀.trans hp₀z
              apply Finset.sum_congr
              · ext q
                simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                constructor
                · rintro ⟨⟨hqS, hqz⟩, hqp₁⟩
                  exact ⟨hqS, hqp₁⟩
                · rintro ⟨hqS, hqp₁⟩
                  exact ⟨⟨hqS, hqp₁.trans hp₁z⟩,
                    hqp₁⟩
              · intro q hq
                have hcarrier :
                    (Z.filter (fun p => q < p)).filter (fun p => p < p₁) =
                      (suzukiSupportedBelow S p₁).filter (fun p => q < p) := by
                  ext p
                  simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                  constructor
                  · rintro ⟨⟨⟨hpS, hpz⟩, hqp⟩, hpp₁⟩
                    exact ⟨⟨hpS, hpp₁⟩, hqp⟩
                  · rintro ⟨⟨hpS, hpp₁⟩, hqp⟩
                    exact ⟨⟨⟨hpS, hpp₁.trans hp₁z⟩, hqp⟩, hpp₁⟩
                rw [hcarrier]
                ring
          · rw [if_neg hcut]
            apply Finset.sum_eq_zero
            intro p₁ hp₁
            exact False.elim (hcut (Finset.mem_filter.mp hp₁).2.2)
    _ = _ := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          rfl

/-- Exact arbitrary-depth odd-layer bridge.  Pair depth `k` in the production
upper boundary has `2*k` stored primes plus the terminal prime outside the stored chain, hence
it is Suzuki source depth `2*k+1`.  The only base-domain hypothesis is `1 < D`,
needed because the empty stored chain must still be active. -/
theorem suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) (hD : 1 < D) :
    suzukiSourceV S (2 * k + 1) D z =
      upperSuzukiUnnormalizedLayer S D z k := by
  induction k generalizing D z with
  | zero =>
      classical
      rw [show 2 * 0 + 1 = 1 by omega, suzukiSourceV_one]
      change (∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => D ≤ q ^ 3),
          S.nu q * sourceDiscreteEuler S q) =
        ∑ q ∈ suzukiSupportedBelow S z,
          S.nu q * sourceDiscreteEuler S q *
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              ((suzukiSupportedBelow S z).filter (fun p => q < p)) 0
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      have hqprime : q.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      rw [upperRosserBoundaryChainsFixedDepthDensity_zero S.nu hD
        (by simp) hqprime]
      · by_cases hcube : D ≤ q ^ 3 <;> simp [hcube]
      · intro p hp
        exact (Finset.mem_filter.mp hp).2.le
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        suzukiSourceV_odd_succ_eq_upper_only S (by omega)
          (show Odd (2 * k + 3) from ⟨k + 1, by omega⟩)]
      rw [upperSuzukiUnnormalizedLayer_succ]
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      apply congrArg (fun x : ℝ => S.nu p₀ * x)
      rw [suzukiSourceV_succ_eq_unrestricted S (by omega)
        (by
          intro hodd
          exact (Nat.not_odd_iff_even.mpr
            (show Even (2 * k + 2) from ⟨k + 1, by omega⟩) hodd).elim)]
      apply Finset.sum_congr rfl
      intro p₁ hp₁
      have hp₀pos : 0 < p₀ := (Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).1).pos
      have hp₁prime : p₁.Prime := Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp hp₁).1
      have hDres : 1 < (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
        have hcut : p₀ ^ 3 < D := (Finset.mem_filter.mp hp₀).2
        have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
        have hle : p₀ ≤ (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
          by_contra hn
          have hc : (D ⌈/⌉ p₀) ⌈/⌉ p₁ < p₀ := Nat.lt_of_not_ge hn
          have hmul₁ := (ceilDiv_le_iff_le_mul hp₁prime.pos).1 hc.le
          have hmul₀ := (ceilDiv_le_iff_le_mul hp₀pos).1 hmul₁
          have hp₁le : p₁ ≤ p₀ := hp₁p₀.le
          nlinarith [hp₁prime.two_le]
        exact hp₁prime.one_lt.trans_le (hp₁p₀.le.trans hle)
      rw [ih ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁ hDres,
        upper_ceilDiv_ceilDiv_eq hp₀pos hp₁prime.pos]

/-- The actual odd Suzuki parity aggregate is the finite sum of the first `m`
production upper-boundary pair layers. -/
theorem suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
    (S : BoundingSieve) (D z m : ℕ) (hD : 1 < D) :
    suzukiActualT S (2 * m + 1) D z =
      ∑ k ∈ Finset.range (m + 1), upperSuzukiUnnormalizedLayer S D z k := by
  induction m with
  | zero =>
      rw [show 2 * 0 + 1 = 1 by omega, suzukiActualT_one,
        suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z 0 hD]
      simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        suzukiActualT_add_two]
      have hlayer : suzukiSourceV S (2 * m + 1 + 2) D z =
          upperSuzukiUnnormalizedLayer S D z (m + 1) := by
        simpa only [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega] using
          suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z (m + 1) hD
      rw [hlayer, ih]
      simpa only [add_comm] using (Finset.sum_range_succ
        (fun k => upperSuzukiUnnormalizedLayer S D z k) (m + 1)).symm


end MathlibNt.SieveTheory
end


-- Source: twin-chen-reverse-weighted/upper-rosser-9d4/ReverseUpperRosserSuzukiExact.lean
section
/-
Source: subfish-zhou/goldbach-lean, revision 9d4c3a4010d42aedd9e7231bf94386019cfffccc.
Apache License 2.0. Original file: MathlibNt/SieveTheory/UpperRosserSuzukiExactBridge.lean.
Source Git blob: c2376bfcd3287b6871e3b2aab81f7694830ec3b1.
Adapted to the dependency closure already checked in Goldbach PR 3771.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The exact finite upper-Rosser/Suzuki bridge.  The integer `z` exhausts the
finite prime support, while every supported prime lies below the Rosser level.
No local-product hypothesis or approximation occurs in this interface. -/
def UpperRosserSuzukiExactBridge : Prop :=
  ∀ (S : BoundingSieve) (D z : ℕ),
    1 < D →
    (∀ p ∈ S.prodPrimes.primeFactors, p < D) →
    (∀ p ∈ S.prodPrimes.primeFactors, p < z) →
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z

/-- Every supported prime contributes a nonzero Euler factor. -/
private theorem upper_euler_factor_ne_zero
    (S : BoundingSieve) {p : ℕ} (hp : p ∈ S.prodPrimes.primeFactors) :
    1 - S.nu p ≠ 0 := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdiv : p ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
  exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv))

private theorem upper_euler_product_split_at
    (S : BoundingSieve) {q : ℕ} (hq : q ∈ S.prodPrimes.primeFactors) :
    (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      sourceDiscreteEuler S q * (1 - S.nu q) *
        ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          (1 - S.nu p) := by
  classical
  let P := S.prodPrimes.primeFactors
  let L := P.filter (fun p => p < q)
  let U := P.filter (fun p => q < p)
  have hrest : P.filter (fun p => ¬p < q) = insert q U := by
    ext p
    simp only [P, U, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hpP, hpq⟩
      by_cases hpqeq : p = q
      · exact Or.inl hpqeq
      · exact Or.inr ⟨hpP,
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hpq) (fun h => hpqeq h.symm)⟩
    · rintro (rfl | ⟨hpP, hqp⟩)
      · exact ⟨hq, by omega⟩
      · exact ⟨hpP, by omega⟩
  have hqU : q ∉ U := by simp [U]
  calc
    (∏ p ∈ P, (1 - S.nu p)) =
        (∏ p ∈ L, (1 - S.nu p)) *
          ∏ p ∈ P.filter (fun p => ¬p < q), (1 - S.nu p) :=
      (Finset.prod_filter_mul_prod_filter_not P (fun p => p < q)
        (fun p => 1 - S.nu p)).symm
    _ = (∏ p ∈ L, (1 - S.nu p)) *
          ((1 - S.nu q) * ∏ p ∈ U, (1 - S.nu p)) := by
      rw [hrest, Finset.prod_insert hqU]
    _ = sourceDiscreteEuler S q * (1 - S.nu q) *
          ∏ p ∈ P.filter (fun p => q < p), (1 - S.nu p) := by
      unfold sourceDiscreteEuler suzukiSupportedBelow
      ring

private theorem upper_relative_depth_mul_fullEuler
    (S : BoundingSieve) {D q k : ℕ}
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (S.nu q / (1 - S.nu q)) *
        upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k *
        (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  have hqfactor : 1 - S.nu q ≠ 0 := upper_euler_factor_ne_zero S hq
  have htailfactor :
      (∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
        (1 - S.nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact upper_euler_factor_ne_zero S (Finset.mem_filter.mp hp).1
  unfold upperRosserBoundaryChainsFixedDepthRelativeDensity
  rw [upper_euler_product_split_at S hq]
  field_simp [hqfactor, htailfactor]

private theorem upper_boundary_depth_sum_extend_to_support
    (S : BoundingSieve) (D q : ℕ) :
    (∑ k ∈ Finset.range
        ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1),
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) =
      ∑ k ∈ Finset.range (S.prodPrimes.primeFactors.card + 1),
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact Nat.add_le_add_right
      (Finset.card_le_card (Finset.filter_subset (fun p => q < p)
        S.prodPrimes.primeFactors)) 1
  · intro k hkBig hkSmall
    apply upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
    simp only [Finset.mem_range] at hkBig hkSmall
    omega

/-- Exact equality behind `UpperRosserSuzukiExactBridge`: after restoring the
full Euler product, each relative boundary path becomes its terminal
`nu(q) * sourceDiscreteEuler(q)` times the selected-chain density.  The common
finite depth range is then exactly the odd Suzuki aggregate. -/
theorem mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    (S : BoundingSieve) (D z : ℕ) (hD : 1 < D)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D)
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z := by
  classical
  let P := S.prodPrimes.primeFactors
  let V := ∏ p ∈ P, (1 - S.nu p)
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 :=
    fun _ hp => upper_euler_factor_ne_zero S hp
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hratio :=
    LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
      S.nu P hD hprime hlevel hfactor
  have hterm (q : ℕ) (hq : q ∈ P) :
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
    calc
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            (S.nu q / (1 - S.nu q)) *
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k * V := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            S.nu q * sourceDiscreteEuler S q *
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact upper_relative_depth_mul_fullEuler S hq
      _ = S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
            rw [← Finset.mul_sum,
              upper_boundary_depth_sum_extend_to_support S D q]
  have hdensity :
      LinearSieve.upperRosserSetDensitySum S.nu D P =
        V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
    calc
      LinearSieve.upperRosserSetDensitySum S.nu D P =
          (LinearSieve.upperRosserSetDensitySum S.nu D P / V) * V :=
        (div_mul_cancel₀ _ hV).symm
      _ = (1 + ∑ q ∈ P,
          (S.nu q / (1 - S.nu q)) *
            ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k) * V := by rw [hratio]
      _ = V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
        rw [add_mul, one_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        exact hterm q hq
  have hsupport : suzukiSupportedBelow S z = P := by
    ext p
    simp only [suzukiSupportedBelow, P, Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · exact fun hp => ⟨hp, hz p hp⟩
  have hboundary :
      (∑ q ∈ P,
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k) =
        ∑ k ∈ Finset.range (P.card + 1),
          upperSuzukiUnnormalizedLayer S D z k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    unfold upperSuzukiUnnormalizedLayer
    rw [hsupport]
  rw [LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  change LinearSieve.upperRosserSetDensitySum S.nu D P = _
  rw [hdensity, hboundary,
    ← suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
      S D z P.card hD]
  simp [P, V, AnalyticNumberTheory.Sieve.sieveProductPrimeFactors]

/-- The finite exact bridge is inhabited unconditionally from the defining
upper-Rosser path expansion and Suzuki's odd-layer identity. -/
theorem upperRosserSuzukiExactBridge : UpperRosserSuzukiExactBridge := by
  intro S D z hD hlevel hz
  exact (mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    S D z hD hlevel hz).le


end MathlibNt.SieveTheory
end


-- Source: twin-chen-reverse-weighted/upper-rosser-9d4/ReverseUpperRosserSuzukiAllDepth.lean
section
/-
Source: subfish-zhou/goldbach-lean, revision 9d4c3a4010d42aedd9e7231bf94386019cfffccc.
Apache License 2.0. Original file: MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiUpperRosserAllDepth.lean.
Source Git blob: cdd9cac5b84a0c838f7c4fe4e0f1a62fb574e4cd.
Adapted to the dependency closure already checked in Goldbach PR 3771.
-/

open Set Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable section

/-- On the compact upper-sieve window the odd Suzuki error envelope has a
bound independent of the (possibly carrier-adaptive) depth. -/
theorem errorEnvelope_odd_le_sixteen_on_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {N : ℕ} (hN : Odd N) {D d s : ℝ}
    (hd : 0 ≤ d) (hD : 1 < D) (hlog : 4 ^ d ≤ Real.log D)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    errorEnvelope H N D d s ≤ 16 := by
  have hs0 : 0 ≤ s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hsd : s ^ d ≤ (4 : ℝ) ^ d :=
    Real.rpow_le_rpow hs0 (by linarith) hd
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ 16 := by
    calc
      (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ s :=
        Real.rpow_le_rpow hbase0 (by linarith) hs0
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hshi
      _ = 16 := by norm_num
  have hweighted_nonneg : 0 ≤ weightedHat H .plus s := by
    unfold weightedHat
    exact mul_nonneg (sq_nonneg s) (hH.positive .plus s (by linarith)).le
  have hweighted : weightedHat H .plus s ≤ 1 := by
    by_cases hs3 : s ≤ 3
    · rw [hH.initial_plus s (by linarith) (by norm_num; linarith)]
      norm_num
    · have h3s : 3 < s := lt_of_not_ge hs3
      have hanti : AntitoneOn (weightedHat H .plus) (Icc (3 : ℝ) s) :=
        weightedHat_antitoneOn_Icc_closed hH .plus (by norm_num [ErrorSign.epsilon])
      have hle := hanti ⟨le_rfl, h3s.le⟩ ⟨h3s.le, le_rfl⟩ h3s.le
      rw [hH.initial_plus 3 (by norm_num) (by norm_num)] at hle
      norm_num at hle ⊢
      exact hle
  have hT : 0 ≤ H.Tplus s := by
    exact (hH.positive .plus s (by linarith)).le
  have hsT : s * H.Tplus s ≤ 1 := by
    have hw : s ^ 2 * H.Tplus s ≤ 1 := by
      simpa [weightedHat, Section13HatLayers.T] using hweighted
    nlinarith
  rw [errorEnvelope_odd hN]
  calc
    (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s =
        (1 + s ^ d / Real.log D) ^ s * (s * H.Tplus s) := by ring
    _ ≤ 16 * 1 := mul_le_mul hperturb hsT (mul_nonneg hs0 hT) (by norm_num)
    _ = 16 := by norm_num

/-- Uniform scalar absorption on `[3/2,4]`, simultaneously for every odd
adaptive depth.  The depth enters the literal error only through its parity. -/
theorem eventually_all_odd_depth_suzuki_error_upper_window
    (H : Section13HatLayers) (hH : Section13HatContract H 2)
    {C K d Δ ρ : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ N : ℕ, Odd N → ∀ s : ℝ,
      3 / 2 ≤ s → s ≤ 4 →
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) < ρ := by
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-Δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hΔ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * 16
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-Δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-Δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul hdecay)
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, (4 : ℝ) ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((4 : ℝ) ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with D hsmallD hlogD hD
  intro N hN s hslo hshi
  have hE := errorEnvelope_odd_le_sixteen_on_upper_window H hH hN hd hD hlogD hslo hshi
  have hE0 : 0 ≤ errorEnvelope H N D d s :=
    errorEnvelope_nonneg H N hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N) s (by linarith)).le
  have hlog0 : 0 ≤ Real.log D := (Real.log_pos hD).le
  have hdecay0 : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog0 _
  constructor
  · positivity
  · calc
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
          (Real.log D) ^ (-Δ) ≤ A * (Real.log D) ^ (-Δ) := by
            apply mul_le_mul_of_nonneg_right _ hdecay0
            dsimp [A]
            exact mul_le_mul_of_nonneg_left hE
              (mul_nonneg hC (Real.exp_pos _).le)
      _ < ρ := hsmallD

/-- Odd finite source layers are exactly the initial segment used by Suzuki's
continuous upper source factor. -/
theorem finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers
    (m : ℕ) (s : ℝ) :
    finiteSourceLayer 1 2 (2 * m + 1) s =
      ∑ k ∈ Finset.range (m + 1), suzukiLayer 1 2 (2 * k + 1) s := by
  classical
  have hcarrier :
      (Finset.Icc 1 (2 * m + 1)).filter (fun n => n % 2 = 1) =
        (Finset.range (m + 1)).image (fun k => 2 * k + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hn1, hnm⟩, hnOdd⟩
      refine ⟨n / 2, ?_, ?_⟩ <;> omega
    · rintro ⟨k, hk, rfl⟩
      constructor <;> omega
  unfold finiteSourceLayer
  rw [show (2 * m + 1) % 2 = 1 by omega]
  rw [← Finset.sum_filter, hcarrier, Finset.sum_image]
  intro a ha b hb hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

/-- Every carrier-adaptive odd finite source factor lies below the genuine
continuous upper source factor. -/
theorem finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (m : ℕ) {s : ℝ} (hs : 1 < s) :
    finiteSourceLayer 1 2 (2 * m + 1) s ≤
      suzukiContinuousUpperFactor s - 1 := by
  rw [finiteSourceLayer_two_mul_add_one_eq_sum_oddLayers]
  unfold suzukiContinuousUpperFactor suzukiProposition118SourceTPlus
  have hsum := summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs
  linarith [hsum.sum_le_tsum (Finset.range (m + 1))
    (fun k hk => suzukiLayer_one_two_odd_nonneg hs k)]

/-- Complete direct consumer at a natural Suzuki coordinate.  The exact finite
upper-Rosser/Suzuki bridge is invoked internally; no bridge premise or uniform
ordered-layer tail is assumed. -/
theorem upperRosserDensity_at_natCeil_of_allDepth
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d Δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hslo : 3 / 2 ≤ s) (_hshi : s ≤ 4)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let m : ℕ := S.prodPrimes.primeFactors.card
  let N : ℕ := 2 * m + 1
  have hNodd : Odd N := by dsimp [N]; exact ⟨m, by omega⟩
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hNodd]
    linarith
  have hSuzuki := hall N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH m (by linarith : 1 < s)
  have hVeq : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold suzukiVProduct
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, by simpa [z] using hcut p hp⟩
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    simpa [z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact lt_of_lt_of_le (hcut p hp) hzD
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel
    (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          suzukiActualT S
            (2 * S.prodPrimes.primeFactors.card + 1) D z := by
              simpa [z] using hexact
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (finiteSourceLayer 1 2
              (2 * S.prodPrimes.primeFactors.card + 1) s +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H
                (2 * S.prodPrimes.primeFactors.card + 1)
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith

/-- Production wrapper: the all-depth Suzuki producer feeds the direct odd-depth
consumer with constants selected before the bounding sieve.  The exact bridge
is a proved internal dependency, not a proposition-valued premise. -/
theorem exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D → ∀ s : ℝ,
              3 / 2 ≤ s → s ≤ 4 → s ≤ sourceSigma (D : ℝ) d →
              2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
              (∀ p ∈ S.prodPrimes.primeFactors,
                p < ⌈(D : ℝ) ^ (1 / s)⌉₊) →
              S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
                  (suzukiContinuousUpperFactor s +
                    C * Real.exp (Real.sqrt K) *
                      errorEnvelope H
                        (2 * S.prodPrimes.primeFactors.card + 1)
                        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hdepth⟩ := hall C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro S K hK hlocal D hD s hslo hshi hsSigma hz2 hcut
  exact upperRosserDensity_at_natCeil_of_allDepth H hH S
    (hdepth S K hK hlocal) D s hD hslo hshi hsSigma hz2 hcut


end
end MathlibNt.SieveTheory
end


-- Source: twin-chen-reverse-weighted/reverse-rough-sieve/ReverseRoughSieveCore.lean
section
namespace ReverseRoughSieve

open Finset GoldbachRoughFifth MathlibNt.SieveTheory

noncomputable def candidates (X : ℕ) : Finset ℕ := by
  classical
  exact (range (X+1)).filter fun n =>
    1 < n ∧ (n+2).Prime ∧ ∀ q ∈ n.divisors, q.Prime → X ≤ q^10

def hits (N : ℕ) : Finset ℕ :=
  (centralPrimes N).filter fun p => (p-2).Coprime (GoldbachRoughFifth.primorial N)

noncomputable def shiftSieve (N : ℕ) (he : Even N) : BoundingSieve :=
  { centralSieve N he with
    support := (centralPrimes N).image (fun p => p-2)
    weights := fun n => Real.log ((n+2 : ℕ) : ℝ)
    weights_nonneg := fun _ => Real.log_natCast_nonneg _ }

private theorem central_prime_gt_three {N p : ℕ} (hN : 12 ≤ N) (hp : p ∈ centralPrimes N) :
    3 < p := by
  have h := (mem_filter.mp hp).2.2.1
  omega

private theorem subtract_two_injective (N : ℕ) (hN : 12 ≤ N) :
    Set.InjOn (fun p => p-2) (centralPrimes N) := by
  intro p hp q hq he
  have hp' := central_prime_gt_three hN hp
  have hq' := central_prime_gt_three hN hq
  change p-2 = q-2 at he
  omega

theorem shifted_divisibility_iff {p d : ℕ} (hp : 2 ≤ p) :
    d ∣ p-2 ↔ p % d = 2 % d := by
  rw [eq_comm]
  exact (Nat.modEq_iff_dvd' hp).symm

theorem shifted_multSum_bv {N : ℕ} (hN : 12 ≤ N) (he : Even N) (d : ℕ) :
    (shiftSieve N he).multSum d =
      bvAPMass bvPrimeWeight (N/3) ((2*N-1)/3) d 2 := by
  change (∑ m ∈ (centralPrimes N).image (fun p => p-2),
    if d ∣ m then Real.log ((m+2 : ℕ):ℝ) else 0) = _
  rw [Finset.sum_image (subtract_two_injective N hN)]
  calc
    _ = ∑ p ∈ (centralPrimes N).filter (fun p => p % d = 2 % d), Real.log (p:ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hp2 : 2 ≤ p := by have := central_prime_gt_three hN hp; omega
      rw [Nat.sub_add_cancel hp2]
      exact ite_congr (propext (shifted_divisibility_iff hp2)) (fun _ => rfl) (fun _ => rfl)
    _ = _ := by
      unfold bvAPMass bvPrimeWeight
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [centralPrimes, mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨⟨_,hPrime,hL,hR⟩,hMod⟩
        exact ⟨⟨⟨by omega,by omega⟩,hMod⟩,hPrime⟩
      · rintro ⟨⟨⟨hL,hR⟩,hMod⟩,hPrime⟩
        exact ⟨⟨by omega,hPrime,by omega,by omega⟩,hMod⟩

theorem shifted_siftedSum_le_log_count {N : ℕ} (hN : 12 ≤ N) (he : Even N) :
    (shiftSieve N he).siftedSum ≤ ((hits N).card : ℝ) * Real.log N := by
  change (∑ m ∈ (centralPrimes N).image (fun p => p-2),
    if (GoldbachRoughFifth.primorial N).Coprime m then Real.log ((m+2 : ℕ):ℝ) else 0) ≤ _
  rw [Finset.sum_image (subtract_two_injective N hN)]
  have hEq : (∑ p ∈ centralPrimes N,
    if (GoldbachRoughFifth.primorial N).Coprime (p-2) then Real.log (((p-2)+2 : ℕ):ℝ) else 0) =
      ∑ p ∈ hits N, Real.log (p:ℝ) := by
    unfold hits
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hp2 : 2 ≤ p := by have := central_prime_gt_three hN hp; omega
    rw [Nat.sub_add_cancel hp2]
    exact ite_congr (propext Nat.coprime_comm) (fun _ => rfl) (fun _ => rfl)
  rw [hEq]
  calc
    _ ≤ ∑ _ ∈ hits N, Real.log N := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hRange,hPrime,_,_⟩ := mem_filter.mp (mem_filter.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hPrime.pos)
        (by exact_mod_cast (mem_range.mp hRange).le)
    _ = _ := by simp

def dyadicScale (X : ℕ) : ℕ := 2^(Nat.log 2 X)

theorem dyadicScale_bounds {X : ℕ} (hX : 0 < X) :
    dyadicScale X ≤ X ∧ X < 2*dyadicScale X := by
  refine ⟨Nat.pow_log_le_self 2 hX.ne', ?_⟩
  simpa [dyadicScale, pow_succ, Nat.mul_comm] using
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) X

theorem dyadicScale_even {X : ℕ} (hX : 2 ≤ X) : Even (dyadicScale X) := by
  have hLog := Nat.log_pos (by decide : 1 < (2 : ℕ)) hX
  have he : Nat.log 2 X = (Nat.log 2 X - 1) + 1 := by omega
  unfold dyadicScale
  rw [he, pow_succ]
  exact even_iff_two_dvd.mpr (dvd_mul_left 2 _)

theorem shifted_hits_card_le_candidates {X : ℕ} (hN : 12 ≤ dyadicScale X) :
    (hits (dyadicScale X)).card ≤ (candidates X).card := by
  classical
  have hX : 0 < X := by
    by_contra! h
    have hZero : X = 0 := by omega
    subst X
    exact (by decide : ¬ 12 ≤ dyadicScale 0) hN
  obtain ⟨hL,hU⟩ := dyadicScale_bounds hX
  apply Finset.card_le_card_of_injOn (fun p => p-2)
  · intro p hp
    obtain ⟨hpC,hCopr⟩ := mem_filter.mp hp
    obtain ⟨hpRange,hPrime,_,_⟩ := mem_filter.mp hpC
    have hp3 := central_prime_gt_three hN hpC
    have hpX := (mem_range.mp hpRange).le.trans hL
    have hOdd := Nat.odd_iff.mp (hPrime.odd_of_ne_two (by omega))
    change p-2 ∈ candidates X
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), by omega,
      by rwa [Nat.sub_add_cancel (by omega : 2 ≤ p)], ?_⟩
    intro q hqDiv hqPrime
    have hd := Nat.dvd_of_mem_divisors hqDiv
    have hqTwo : q ≠ 2 := by
      rintro rfl
      have hMod := Nat.mod_eq_zero_of_dvd hd
      omega
    by_contra! hg
    have hq5 : q^5 ≤ dyadicScale X := by
      have h2 : 2 ≤ q^5 := by
        calc
          2 ≤ q := hqPrime.two_le
          _ = q^1 := by simp
          _ ≤ q^5 := Nat.pow_le_pow_right hqPrime.pos (by decide)
      have hProd : 2*q^5 ≤ q^10 := by
        rw [show q^10 = q^5*q^5 from pow_add q 5 5]
        exact Nat.mul_le_mul_right (q^5) h2
      omega
    have hqN : q ≤ dyadicScale X := by
      have h : q = q^1 := by simp
      exact (h.trans_le (Nat.pow_le_pow_right hqPrime.pos (by decide))).trans hq5
    have hqNotDvd : ¬q ∣ dyadicScale X := by
      intro hDvd
      have h2 : q ∣ 2 := hqPrime.dvd_of_dvd_pow hDvd
      exact hqTwo ((Nat.prime_dvd_prime_iff_eq hqPrime Nat.prime_two).mp h2)
    have hqP : q ∈ sievingPrimes (dyadicScale X) := mem_filter.mpr
      ⟨mem_range.mpr (by omega),hqPrime,hq5,hqNotDvd⟩
    rw [GoldbachRoughFifth.primorial, Nat.coprime_prod_right_iff] at hCopr
    exact (hqPrime.coprime_iff_not_dvd.mp (hCopr q hqP).symm) hd
  · intro p hp q hq hpq
    exact subtract_two_injective _ hN (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq


end ReverseRoughSieve
end


-- Source: twin-chen-reverse-weighted/ReverseChenDyadicDensityUpper.lean
section
namespace GoldbachTwinChenBridge

open Finset GoldbachRoughFifth ReverseRoughSieve
open GoldbachRoughFifth.AnalyticInput.ErdosStraus.PrimeEstimates.Mertens

/-- The density product for the dyadic scale is at most a constant over the
logarithm of any cutoff whose fifth power is below that scale. -/
theorem dyadic_fifth_sieveDensity_invlog_upper :
    ∃ c : ℝ, 0 < c ∧ ∀ T Y : ℕ, 2 ≤ T → 2 ≤ Y → Y^5 ≤ dyadicScale T →
      sieveDensity (dyadicScale T) ≤ c / Real.log (Y : ℝ) := by
  obtain ⟨C,hC,hMertens⟩ := mertensSecond
  let K : ℝ := 1/2 - mertensSecondConstant + C/Real.log 2
  refine ⟨Real.exp K,Real.exp_pos _,?_⟩
  intro T Y hT hY hPower
  let S := dyadicScale T
  let V := sievingPrimes S
  let A := (primesUpTo Y).erase 2
  have hEven : 2 ∣ S := even_iff_two_dvd.mp (dyadicScale_even hT)
  have hSub : A ⊆ V := by
    intro p hp
    obtain ⟨hTwo,hIn⟩ := mem_erase.mp hp
    obtain ⟨hPrime,hLe⟩ := mem_primesUpTo.mp hIn
    have h5 : p^5 ≤ S := (Nat.pow_le_pow_left hLe 5).trans hPower
    have hP : p ≤ p^5 := by
      calc
        p = p^1 := by simp
        _ ≤ p^5 := Nat.pow_le_pow_right hPrime.pos (by decide)
    have hNoDiv : ¬p ∣ S := by
      intro hd
      have hDiv : p ∣ 2 := hPrime.dvd_of_dvd_pow hd
      exact hTwo ((Nat.prime_dvd_prime_iff_eq hPrime Nat.prime_two).mp hDiv)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hP.trans h5)),hPrime,h5,hNoDiv⟩
  have hGe3 (p : ℕ) (hp : p ∈ V) : 3 ≤ p := by
    obtain ⟨_,hPrime,_,hNoDiv⟩ := mem_filter.mp hp
    have hTwo : p ≠ 2 := fun he => hNoDiv (he.symm ▸ hEven)
    have := hPrime.two_le
    omega
  have hFactors (p : ℕ) (hp : p ∈ V) : 0 < 1 - 1/((p:ℝ)-1) := by
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hGe3 p hp
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hProd : 0 < sieveDensity S := prod_pos hFactors
  have hLogProd : Real.log (sieveDensity S) =
      ∑ p ∈ V, Real.log (1 - 1/((p:ℝ)-1)) :=
    Real.log_prod (fun p hp => (hFactors p hp).ne')
  have hSum : Real.log (sieveDensity S) ≤ -(∑ p ∈ V, 1/(p:ℝ)) := by
    rw [hLogProd, ← sum_neg_distrib]
    apply sum_le_sum
    intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hGe3 p hp
    have hInv : 1/(p:ℝ) ≤ 1/((p:ℝ)-1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith only [Real.log_le_sub_one_of_pos (hFactors p hp), hInv]
  have hTwo : 2 ∈ primesUpTo Y := mem_primesUpTo.mpr ⟨Nat.prime_two,hY⟩
  have hErase : (∑ p ∈ A, 1/(p:ℝ)) + 1/2 = primeReciprocalSum Y := by
    simpa only [A, primeReciprocalSum, Nat.cast_ofNat] using
      sum_erase_add (primesUpTo Y) (fun p => 1/(p:ℝ)) hTwo
  have hPrimeSum : (∑ p ∈ A, 1/(p:ℝ)) ≤ ∑ p ∈ V, 1/(p:ℝ) :=
    sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => by positivity)
  have hYR : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hLogY : 0 < Real.log (Y:ℝ) := Real.log_pos (by linarith)
  have hM := (abs_le.mp (hMertens (Y:ℝ) hYR)).1
  simp only [Nat.floor_natCast] at hM
  have hErr : C/Real.log (Y:ℝ) ≤ C/Real.log 2 :=
    div_le_div_of_nonneg_left hC.le (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hYR)
  have hBound : Real.log (sieveDensity S) ≤ K - Real.log (Real.log (Y:ℝ)) := by
    dsimp only [K]
    linarith only [hSum,hErase,hPrimeSum,hM,hErr]
  have h := Real.exp_le_exp.mpr hBound
  rwa [Real.exp_log hProd, Real.exp_sub, Real.exp_log hLogY] at h


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenUpperSieveGeometry.lean
section
namespace GoldbachTwinChenBridge

open Finset Filter GoldbachRoughFifth ReverseRoughSieve

def reverseUpperScale (X : ℕ) : ℕ := 2^(Nat.log 2 X / 4)
def reverseUpperPrimeCutoff (X : ℕ) : ℕ := 2^(Nat.log 2 X / 40)
def reverseUpperLevel (X : ℕ) : ℕ := 2^(Nat.log 2 X / 3)

/-- A power-of-two undersieve and level satisfying the existing finite, BV,
and reciprocal-log product bounds at the same time. -/
theorem reverse_upper_dyadic_geometry :
    ∀ᶠ X : ℕ in atTop,
      let S := reverseUpperScale X
      let Y := reverseUpperPrimeCutoff X
      let D := reverseUpperLevel X
      2 ≤ S ∧ Even S ∧ dyadicScale S = S ∧ S^2 < X ∧
        2 ≤ Y ∧ Y^5 ≤ S ∧ Real.log (X:ℝ)/80 ≤ Real.log (Y:ℝ) ∧
        1 < D ∧ (D:ℝ) ≤ ((X+2:ℕ):ℝ)^(9/20:ℝ) ∧
        ∀ p ∈ (GoldbachRoughFifth.primorial S).primeFactors, p < D := by
  filter_upwards [eventually_ge_atTop ((2:ℕ)^40)] with X hX
  dsimp only
  let k := Nat.log 2 X
  let S := reverseUpperScale X
  let Y := reverseUpperPrimeCutoff X
  let D := reverseUpperLevel X
  have hk : 40 ≤ k := Nat.le_log_of_pow_le (by decide) hX
  have hXPos : 0 < X := (by decide : (0:ℕ) < 2^40).trans_le hX
  have hPow : (2:ℕ)^k ≤ X := Nat.pow_log_le_self 2 hXPos.ne'
  have hS : 2 ≤ S := by
    change (2:ℕ)^1 ≤ (2:ℕ)^(k/4)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hY : 2 ≤ Y := by
    change (2:ℕ)^1 ≤ (2:ℕ)^(k/40)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hd : 1 < D := by
    change (2:ℕ)^0 < (2:ℕ)^(k/3)
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hFix : dyadicScale S = S := by
    unfold dyadicScale S reverseUpperScale
    rw [Nat.log_pow (by decide : 1 < (2:ℕ))]
  have hSmall : S^2 < X := by
    change ((2:ℕ)^(k/4))^2 < _
    rw [← pow_mul]
    exact (Nat.pow_lt_pow_right (by decide) (show k/4*2 < k by omega)).trans_le hPow
  have hY5 : Y^5 ≤ S := by
    change ((2:ℕ)^(k/40))^5 ≤ (2:ℕ)^(k/4)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hD3 : D^3 ≤ X := by
    change ((2:ℕ)^(k/3))^3 ≤ _
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (show k/3*3 ≤ k by omega)).trans hPow
  have hXR : (1:ℝ) ≤ ((X+2:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ X+2)
  have hDR : (D:ℝ) ≤ ((X+2:ℕ):ℝ)^(9/20:ℝ) := by
    have hp : (D:ℝ)^3 ≤ ((X+2:ℕ):ℝ) := by exact_mod_cast hD3.trans (by omega : X ≤ X+2)
    calc
      (D:ℝ) = ((D:ℝ)^3)^(1/3:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg D)]
        norm_num
      _ ≤ ((X+2:ℕ):ℝ)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) hp (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hXR (by norm_num)
  have hLog : Real.log (X:ℝ)/80 ≤ Real.log (Y:ℝ) := by
    have htNat : X < (2:ℕ)^(k+1) := Nat.lt_pow_succ_log_self (by decide) X
    have ht : (X:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast htNat.le
    have hu := Real.log_le_log (by exact_mod_cast hXPos) ht
    rw [Real.log_pow] at hu
    have hExp : ((k+1:ℕ):ℝ) ≤ 80 * ((k/40:ℕ):ℝ) := by
      exact_mod_cast (by omega : k+1 ≤ 80*(k/40))
    have hExp' := mul_le_mul_of_nonneg_right hExp (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    change _ ≤ Real.log (((2:ℕ)^(k/40):ℕ):ℝ)
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    linarith only [hu,hExp']
  have hEven : Even S := by
    have h := dyadicScale_even hS
    rw [hFix] at h
    exact h
  refine ⟨hS,hEven,hFix,hSmall,hY,hY5,hLog,hd,hDR,?_⟩
  intro p hp
  rw [primorial_factors] at hp
  have hle : p ≤ S := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1)
  apply hle.trans_lt
  change (2:ℕ)^(k/4) < (2:ℕ)^(k/3)
  exact Nat.pow_lt_pow_right (by decide) (by omega)


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenWeightedBridge.lean
section
namespace GoldbachTwinChenBridge

open ArithmeticFunction Finset
open scoped BigOperators

/-- The prime is the term on the right of the shift. Each factor of the
left term is at least the tenth root of the counting scale. -/
def ReverseRoughChenAt (X n : ℕ) : Prop :=
  (n + 2).Prime ∧
    ((n.Prime ∧ X ≤ n^10) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q ∧ X ≤ p^10 ∧ X ≤ q^10)

noncomputable def reverseRoughChenSet (X : ℕ) : Finset ℕ := by
  classical
  exact (range (X + 1)).filter (ReverseRoughChenAt X)

/-- Quantitative counting input. This is the unsupplied sieve estimate. -/
def ReverseRoughChenCountBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    c * (X : ℝ) ≤ (reverseRoughChenSet X).card * (Real.log (X : ℝ))^2

noncomputable def selbergSecond (n : ℕ) : ℝ :=
  vonMangoldt n * Real.log (n : ℝ) +
    ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)

noncomputable def unsignedShiftedSelberg (n : ℕ) : ℝ :=
  ((moebius n : ℤ) : ℝ)^2 * selbergSecond n *
    (if (n + 2).Prime then Real.log ((n : ℝ) + 2) else 0)

private theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

private theorem selberg_second_nonneg (n : ℕ) : 0 ≤ selbergSecond n := by
  unfold selbergSecond
  exact add_nonneg (mul_nonneg vonMangoldt_nonneg (log_nat_nonneg n))
    (sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

theorem unsigned_shifted_selberg_nonneg (n : ℕ) : 0 ≤ unsignedShiftedSelberg n := by
  unfold unsignedShiftedSelberg
  apply mul_nonneg (mul_nonneg (sq_nonneg _) (selberg_second_nonneg n))
  split_ifs
  · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact Real.log_nonneg (by linarith only [hn])
  · exact le_rfl

private theorem log_of_tenth_power_ge {X p : ℕ} (hX : 2 ≤ X) (hp : X ≤ p^10) :
    Real.log (X : ℝ) / 10 ≤ Real.log (p : ℝ) := by
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hpow : (X : ℝ) ≤ (p : ℝ)^10 := by exact_mod_cast hp
  have hlog := Real.log_le_log hXp hpow
  rw [Real.log_pow] at hlog
  norm_num at hlog
  linarith only [hlog]

private theorem divisors_second_remainder_nonneg (n : ℕ) :
    0 ≤ ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) :=
  sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

theorem unsigned_shifted_selberg_ge_rough_weight {X n : ℕ} (hX : 2 ≤ X)
    (h : ReverseRoughChenAt X n) :
    (Real.log (X : ℝ) / 10)^3 ≤ unsignedShiftedSelberg n := by
  let L := Real.log (X : ℝ) / 10
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity [log_nat_nonneg X]
  obtain ⟨hShift, hCases⟩ := h
  have hParts : ((moebius n : ℤ) : ℝ)^2 = 1 ∧
      L^2 ≤ selbergSecond n ∧ L ≤ Real.log ((n : ℝ) + 2) := by
    rcases hCases with ⟨hn, hnPow⟩ | ⟨p, q, hp, hq, hpq, rfl, hpPow, hqPow⟩
    · have hnLog : L ≤ Real.log (n : ℝ) := log_of_tenth_power_ge hX hnPow
      have hMu : ((moebius n : ℤ) : ℝ)^2 = 1 := by
        rw [moebius_apply_prime hn]
        norm_num
      have hSecond : L^2 ≤ selbergSecond n := calc
        _ ≤ (Real.log (n : ℝ))^2 := pow_le_pow_left₀ hL hnLog 2
        _ ≤ _ := by
          rw [pow_two, selbergSecond, vonMangoldt_apply_prime hn]
          exact le_add_of_nonneg_right (divisors_second_remainder_nonneg n)
      have hLogShift := hnLog.trans
        (Real.log_le_log (Nat.cast_pos.mpr hn.pos) (by linarith : (n : ℝ) ≤ (n : ℝ) + 2))
      exact ⟨hMu, hSecond, hLogShift⟩
    · have hCoprime : p.Coprime q := hp.coprime_iff_not_dvd.mpr
        (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))
      have hMul : moebius (p * q) = moebius p * moebius q :=
        isMultiplicative_moebius.map_mul_of_coprime hCoprime
      have hMu : ((moebius (p * q) : ℤ) : ℝ)^2 = 1 := by
        rw [hMul, moebius_apply_prime hp, moebius_apply_prime hq]
        norm_num
      have hDiv : p ∣ p * q := ⟨q, rfl⟩
      have hpD : p ∈ (p * q).divisors := Nat.mem_divisors.mpr
        ⟨hDiv, mul_ne_zero hp.ne_zero hq.ne_zero⟩
      have hQuot : p * q / p = q :=
        Nat.eq_of_mul_eq_mul_left hp.pos (Nat.mul_div_cancel' hDiv)
      have hP : L ≤ Real.log (p : ℝ) := log_of_tenth_power_ge hX hpPow
      have hQ : L ≤ Real.log (q : ℝ) := log_of_tenth_power_ge hX hqPow
      have hSingle := single_le_sum (f := fun d : ℕ =>
        vonMangoldt d * vonMangoldt (p * q / d))
        (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) hpD
      rw [hQuot, vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq] at hSingle
      have hSecond : L^2 ≤ selbergSecond (p * q) := calc
        _ ≤ Real.log (p : ℝ) * Real.log (q : ℝ) := by
          rw [pow_two]
          exact mul_le_mul hP hQ hL (log_nat_nonneg p)
        _ ≤ ∑ d ∈ (p * q).divisors, vonMangoldt d * vonMangoldt (p * q / d) := hSingle
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg vonMangoldt_nonneg (log_nat_nonneg (p * q)))
      have hpLe : p ≤ p * q := by simpa using Nat.mul_le_mul_left p hq.one_lt.le
      have hpLeR : (p : ℝ) ≤ ((p * q : ℕ) : ℝ) := by exact_mod_cast hpLe
      have hLogShift := hP.trans
        (Real.log_le_log (Nat.cast_pos.mpr hp.pos)
          (by linarith only [hpLeR] : (p : ℝ) ≤ ((p * q : ℕ) : ℝ) + 2))
      exact ⟨hMu, hSecond, hLogShift⟩
  obtain ⟨hMu, hSecond, hLogShift⟩ := hParts
  change L^3 ≤ unsignedShiftedSelberg n
  rw [unsignedShiftedSelberg, hMu, one_mul, ite_eq_left hShift, pow_succ]
  exact mul_le_mul hSecond hLogShift hL (selberg_second_nonneg n)

theorem shifted_selberg_lower_of_reverse_rough_count (hCount : ReverseRoughChenCountBound) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) * Real.log (X : ℝ) ≤
        ∑ n ∈ range (X + 1), unsignedShiftedSelberg n := by
  classical
  obtain ⟨c, hc, X₀, hCount⟩ := hCount
  refine ⟨c / 1000, by positivity, max X₀ 2, ?_⟩
  intro X hX
  have hTwo : 2 ≤ X := (le_max_right X₀ 2).trans hX
  have hCut := (le_max_left X₀ 2).trans hX
  let L := Real.log (X : ℝ)
  let s := reverseRoughChenSet X
  have hL : 0 ≤ L := log_nat_nonneg X
  have hCard : c * (X : ℝ) ≤ (s.card : ℝ) * L^2 := hCount X hCut
  have hSubset : s ⊆ range (X + 1) := by
    unfold s reverseRoughChenSet
    exact filter_subset _ _
  have hPoint (n : ℕ) (hn : n ∈ s) : (L / 10)^3 ≤ unsignedShiftedSelberg n := by
    change n ∈ (range (X + 1)).filter (ReverseRoughChenAt X) at hn
    exact unsigned_shifted_selberg_ge_rough_weight hTwo (mem_filter.mp hn).2
  calc
    _ = (c * (X : ℝ)) * (L / 1000) := by change c / 1000 * (X : ℝ) * L = _; ring
    _ ≤ ((s.card : ℝ) * L^2) * (L / 1000) :=
      mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = (s.card : ℝ) * (L / 10)^3 := by ring
    _ = ∑ _ ∈ s, (L / 10)^3 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ s, unsignedShiftedSelberg n := sum_le_sum hPoint
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSubset (fun n _ _ => unsigned_shifted_selberg_nonneg n)

/-- The conclusion is the exact published first premise of cut #3816. -/
theorem e724_frozen_of_reverse_rough_count (hCount : ReverseRoughChenCountBound) :
    ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ) :=
  shifted_selberg_lower_of_reverse_rough_count hCount


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenGoodRatioBridge.lean
section
namespace GoldbachTwinChenBridge

open Finset

def roughCandidateSet (X : ℕ) : Finset ℕ :=
  (range (X+1)).filter fun n =>
    1 < n ∧ (n+2).Prime ∧ ∀ q ∈ n.divisors, q.Prime → X ≤ q^10

abbrev primeOrDistinctSemiprime (n : ℕ) : Prop :=
  n.Prime ∨ ∃ d ∈ n.divisors, d.Prime ∧ (n/d).Prime ∧ d ≠ n/d

def goodRoughCandidateSet (X : ℕ) : Finset ℕ :=
  (roughCandidateSet X).filter primeOrDistinctSemiprime

theorem reverseChen_set_subset_good_rough (X : ℕ) :
    reverseRoughChenSet X ⊆ goodRoughCandidateSet X := by
  classical
  intro n hn
  obtain ⟨hRange,hShift,hFactors⟩ := Finset.mem_filter.mp hn
  change n ∈ (roughCandidateSet X).filter primeOrDistinctSemiprime
  rcases hFactors with ⟨hPrime,hHeight⟩ | ⟨p,q,hp,hq,hpq,rfl,hP,hQ⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hRange,hPrime.one_lt,hShift,?_⟩,Or.inl hPrime⟩
    intro r hr hrp
    have hEq := (Nat.prime_dvd_prime_iff_eq hrp hPrime).mp (Nat.dvd_of_mem_divisors hr)
    rw [hEq]
    exact hHeight
  · have hDiv : p ∣ p*q := ⟨q,rfl⟩
    have hQuot : p*q/p = q := Nat.eq_of_mul_eq_mul_left hp.pos (Nat.mul_div_cancel' hDiv)
    have hpq0 : p*q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
    have hBig : 1 < p*q := one_lt_mul_of_lt_of_le hp.one_lt hq.one_le
    have hGood : primeOrDistinctSemiprime (p*q) := Or.inr
      ⟨p,Nat.mem_divisors.mpr ⟨hDiv,hpq0⟩,hp,by rwa [hQuot],by rwa [hQuot]⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hRange,hBig,hShift,?_⟩,hGood⟩
    intro r hr hrp
    rcases hrp.dvd_mul.mp (Nat.dvd_of_mem_divisors hr) with hRP | hRQ
    · rwa [(Nat.prime_dvd_prime_iff_eq hrp hp).mp hRP]
    · rwa [(Nat.prime_dvd_prime_iff_eq hrp hq).mp hRQ]

/-- A lower count for the genuine reverse P₂ set and an upper count for the
rough set imply the published bad-fraction bound. -/
theorem e341_frozen_of_reverse_P2_and_rough_upper
    (hGood : ReverseRoughChenCountBound)
    (hUpper : ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((roughCandidateSet X).card : ℝ) * (Real.log (X : ℝ))^2 ≤ C * (X : ℝ)) :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}
    let x2 : ℕ → Prop := fun (x2 : ℕ) => Nat.Prime x2 ∨ ∃ x3 ∈ x2.divisors, Nat.Prime x3 ∧ Nat.Prime (x2 / x3) ∧ x3 ≠ x2 / x3
    ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → ↑{x7 ∈ x1 x5 | ¬x2 x7}.card ≤ ((1 : ℝ) - x3) * ↑(x1 x5).card := by
  classical
  suffices hModel : ∃ δ : ℝ, 0 < δ ∧ ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
    (((roughCandidateSet X).filter fun n => ¬ primeOrDistinctSemiprime n).card : ℝ)
      ≤ (1-δ) * ((roughCandidateSet X).card : ℝ) by
    simpa only [roughCandidateSet, primeOrDistinctSemiprime] using hModel
  obtain ⟨c,hc,N₁,hLower⟩ := hGood
  obtain ⟨C,hC,N₂,hUpper⟩ := hUpper
  refine ⟨c/C,div_pos hc hC,max (max N₁ N₂) 2,?_⟩
  intro X hX
  have h1 : N₁ ≤ X := by omega
  have h2 : N₂ ≤ X := by omega
  have hLog : 0 < (Real.log (X : ℝ))^2 :=
    sq_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < X)))
  have hCard : ((reverseRoughChenSet X).card : ℝ) ≤ ((goodRoughCandidateSet X).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (reverseChen_set_subset_good_rough X)
  have hScaled : (c/C) * ((roughCandidateSet X).card : ℝ) * (Real.log (X : ℝ))^2 ≤
      ((goodRoughCandidateSet X).card : ℝ) * (Real.log (X : ℝ))^2 := by
    calc
      _ = (c/C) * (((roughCandidateSet X).card : ℝ) * (Real.log (X : ℝ))^2) := by ring
      _ ≤ (c/C) * (C * (X : ℝ)) := mul_le_mul_of_nonneg_left (hUpper X h2) (by positivity)
      _ = c * (X : ℝ) := by rw [← mul_assoc,div_mul_cancel₀ c hC.ne']
      _ ≤ ((reverseRoughChenSet X).card : ℝ) * (Real.log (X : ℝ))^2 := hLower X h1
      _ ≤ _ := mul_le_mul_of_nonneg_right hCard hLog.le
  have hProportion := le_of_mul_le_mul_right hScaled hLog
  have hPart : ((goodRoughCandidateSet X).card : ℝ) +
      (((roughCandidateSet X).filter fun n => ¬ primeOrDistinctSemiprime n).card : ℝ) =
      ((roughCandidateSet X).card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not
      (s := roughCandidateSet X) primeOrDistinctSemiprime
  linarith only [hProportion,hPart]


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenRoughUpperBridge.lean
section
namespace GoldbachTwinChenBridge

open Finset GoldbachRoughFifth

def shiftedSiftedUpperSet (X S : ℕ) : Finset ℕ :=
  (range (X+1)).filter fun n => 1 < n ∧ (n+2).Prime ∧
    n.Coprime (GoldbachRoughFifth.primorial S)

/-- Any prime screened by a scale with S² < X is forbidden by the target roughness condition. -/
theorem rough_subset_shifted_sifted_upper {X S : ℕ} (hScale : S^2 < X) :
    roughCandidateSet X ⊆ shiftedSiftedUpperSet X S := by
  intro n hn
  obtain ⟨hRange,hN,hPrime,hRough⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hRange,hN,hPrime,?_⟩
  rw [GoldbachRoughFifth.primorial, Nat.coprime_prod_right_iff]
  intro q hq
  obtain ⟨_,hQ,hPower,_⟩ := mem_filter.mp hq
  apply Nat.Coprime.symm
  apply hQ.coprime_iff_not_dvd.mpr
  intro hDvd
  have hQDiv : q ∈ n.divisors := Nat.mem_divisors.mpr ⟨hDvd,by omega⟩
  have hTarget := hRough q hQDiv hQ
  have hTooSmall : q^10 < X := by
    calc
      q^10 = (q^5)^2 := pow_mul q 5 2
      _ ≤ S^2 := Nat.pow_le_pow_left hPower 2
      _ < X := hScale
  exact (not_lt_of_ge hTarget) hTooSmall

theorem rough_count_le_shifted_sifted_upper {X S : ℕ} (hScale : S^2 < X) :
    (roughCandidateSet X).card ≤ (shiftedSiftedUpperSet X S).card :=
  card_le_card (rough_subset_shifted_sifted_upper hScale)


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenFiniteUpperSieve.lean
section
namespace GoldbachTwinChenBridge

open Finset GoldbachRoughFifth MathlibNt.SieveTheory.LinearSieve

private def upperPrimePool (X : ℕ) : Finset ℕ :=
  (Ioc 3 (X+2)).filter Nat.Prime

private theorem upperPrimePool_shift_injective (X : ℕ) :
    Set.InjOn (fun p => p-2) (upperPrimePool X) := by
  intro p hp q hq hpq
  have hp3 := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hq3 := (mem_Ioc.mp (mem_filter.mp hq).1).1
  change p-2 = q-2 at hpq
  omega

private theorem upperPrimePool_shift_eq (X : ℕ) :
    (upperPrimePool X).image (fun p => p-2) =
      (range (X+1)).filter (fun n => 1 < n ∧ (n+2).Prime) := by
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hn
    obtain ⟨hI,hP⟩ := mem_filter.mp hp
    obtain ⟨hp3,hpX⟩ := mem_Ioc.mp hI
    exact mem_filter.mpr
      ⟨mem_range.mpr (by omega),by omega,by simpa only [Nat.sub_add_cancel (by omega : 2 ≤ p)]⟩
  · intro hn
    obtain ⟨hR, hN, hP⟩ := mem_filter.mp hn
    have hX := mem_range.mp hR
    exact mem_image.mpr ⟨n+2,mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hP⟩,by omega⟩

noncomputable def fullShiftedUpperSieve (X S : ℕ) (he : Even S) : BoundingSieve :=
  { centralSieve S he with
    support := (upperPrimePool X).image (fun p => p-2)
    weights := fun n => Real.log ((n+2 : ℕ) : ℝ)
    weights_nonneg := fun _ => Real.log_natCast_nonneg _
    totalMass := (X : ℝ)-1 }

theorem fullShiftedUpperSieve_multSum_bv (X S : ℕ) (he : Even S) (d : ℕ) :
    (fullShiftedUpperSieve X S he).multSum d =
      bvAPMass bvPrimeWeight 3 (X+2) d 2 := by
  change (∑ n ∈ (upperPrimePool X).image (fun p => p-2),
    if d ∣ n then Real.log ((n+2 : ℕ) : ℝ) else 0) = _
  rw [sum_image (upperPrimePool_shift_injective X)]
  calc
    _ = ∑ p ∈ (upperPrimePool X).filter (fun p => p % d=2 % d), Real.log (p:ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      have hp2 : 2 ≤ p := by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega
      rw [Nat.sub_add_cancel hp2]
      exact ite_congr (propext (ReverseRoughSieve.shifted_divisibility_iff hp2))
        (fun _ => rfl) (fun _ => rfl)
    _ = _ := by
      unfold upperPrimePool bvAPMass bvPrimeWeight
      rw [← sum_filter]
      refine sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [mem_filter, and_left_comm, and_comm]

theorem fullShiftedUpperSieve_rem_bv (X S : ℕ) (he : Even S) (d : ℕ) :
    (fullShiftedUpperSieve X S he).rem d =
      bvAPMass bvPrimeWeight 3 (X+2) d 2 - ((X:ℝ)-1)/d.totient := by
  rw [BoundingSieve.rem, fullShiftedUpperSieve_multSum_bv]
  change _ - (↑d.totient : ℝ)⁻¹ * ((X:ℝ)-1) = _
  rw [div_eq_mul_inv]
  ring

theorem fullShiftedUpperSieve_siftedSum (X S : ℕ) (he : Even S) :
    (fullShiftedUpperSieve X S he).siftedSum =
      ∑ n ∈ shiftedSiftedUpperSet X S, Real.log ((n+2 : ℕ) : ℝ) := by
  change (∑ n ∈ (upperPrimePool X).image (fun p => p-2),
    if (GoldbachRoughFifth.primorial S).Coprime n then Real.log ((n+2 : ℕ):ℝ) else 0) = _
  rw [← sum_filter, upperPrimePool_shift_eq]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [shiftedSiftedUpperSet, mem_filter, Nat.coprime_comm, and_assoc]

private theorem large_candidate_log {X n : ℕ} (hX : 1 ≤ X) (hn : X.sqrt < n) :
    Real.log (X : ℝ)/2 ≤ Real.log ((n+2 : ℕ) : ℝ) := by
  have hN : X ≤ (n+2)^2 :=
    ((Nat.sqrt_lt'.mp hn).le).trans (Nat.pow_le_pow_left (by omega) 2)
  have hR : (X : ℝ) ≤ (((n+2 : ℕ) : ℝ))^2 := by exact_mod_cast hN
  have hLog := Real.log_le_log (by exact_mod_cast (by omega : 0 < X)) hR
  rw [Real.log_pow] at hLog
  norm_num at hLog
  simp only [Nat.cast_add, Nat.cast_ofNat]
  linarith only [hLog]

theorem roughCount_mul_halfLog_le_siftedSum_add_sqrt
    {X S : ℕ} (he : Even S) (hX : 1 ≤ X) (hScale : S^2 < X) :
    ((roughCandidateSet X).card : ℝ) * (Real.log (X : ℝ)/2) ≤
      (fullShiftedUpperSieve X S he).siftedSum + (X.sqrt : ℝ) * (Real.log (X : ℝ)/2) := by
  let C := roughCandidateSet X
  let small := C.filter (fun n => n ≤ X.sqrt)
  let large := C.filter (fun n => ¬ n ≤ X.sqrt)
  let L := Real.log (X : ℝ)/2
  have hL : 0 ≤ L := div_nonneg (Real.log_nonneg (by exact_mod_cast hX)) (by norm_num)
  have hPart : (small.card : ℝ) + (large.card : ℝ) = (C.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := C) (fun n => n ≤ X.sqrt)
  have hSmallSub : small ⊆ Icc 1 X.sqrt := by
    intro n hn
    obtain ⟨hnC,hnS⟩ := mem_filter.mp hn
    have hPos := (mem_filter.mp hnC).2.1
    exact mem_Icc.mpr ⟨by omega,hnS⟩
  have hSmall : (small.card : ℝ) ≤ X.sqrt := by
    exact_mod_cast (card_le_card hSmallSub).trans_eq (by simp [Nat.card_Icc])
  have hLargeSub : large ⊆ shiftedSiftedUpperSet X S :=
    (filter_subset _ _).trans (rough_subset_shifted_sifted_upper hScale)
  have hLarge : (large.card : ℝ) * L ≤ (fullShiftedUpperSieve X S he).siftedSum := by
    rw [fullShiftedUpperSieve_siftedSum]
    calc
      _ = ∑ _n ∈ large, L := by rw [sum_const,nsmul_eq_mul]
      _ ≤ ∑ n ∈ large, Real.log ((n+2 : ℕ) : ℝ) :=
        sum_le_sum fun n hn => large_candidate_log hX (by have := (mem_filter.mp hn).2; omega)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hLargeSub (fun n _ _ => Real.log_natCast_nonneg _)
  change (C.card:ℝ)*L ≤ _ + (X.sqrt:ℝ)*L
  rw [← hPart, add_mul, add_comm ((small.card:ℝ)*L)]
  exact add_le_add hLarge (mul_le_mul_of_nonneg_right hSmall hL)

theorem fullShiftedUpperSieve_finite_bound {X S D : ℕ} (he : Even S)
    (hD : 1 < D) (hPrimeD : ∀ p ∈ (GoldbachRoughFifth.primorial S).primeFactors, p < D) :
    (fullShiftedUpperSieve X S he).siftedSum ≤
      ((X : ℝ)-1) * upperRosserSetDensitySum progressionDensity D
        (GoldbachRoughFifth.sievingPrimes S) +
      ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ GoldbachRoughFifth.primorial S),
        |bvAPMass bvPrimeWeight 3 (X+2) d 2 - ((X:ℝ)-1)/d.totient| := by
  let F := fullShiftedUpperSieve X S he
  let P := GoldbachRoughFifth.primorial S
  have hCert := upperRosserWeight_certificate (primorial_squarefree S)
    (primorial_squarefree S).ne_zero hD hPrimeD
  have hFinite := siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := F) D hCert
  have hSub : P.divisors.filter (fun d => d < D) ⊆ (Icc 1 D).filter (fun d => d ∣ P) := by
    intro d hd
    obtain ⟨hDiv,hLt⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hDiv,hLt.le⟩,
      Nat.dvd_of_mem_divisors hDiv⟩
  have hError : upperErrSum F D (upperRosserWeight P D) ≤
      ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P), |F.rem d| := by
    calc
      _ ≤ ∑ d ∈ P.divisors.filter (fun d => d < D), |F.rem d| :=
        sum_le_sum fun d _ => mul_le_of_le_one_left (abs_nonneg _) (abs_upperRosserWeight_le_one P D d)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => abs_nonneg _)
  have hMain : F.mainSum (upperRosserWeight P D) =
      upperRosserSetDensitySum progressionDensity D (GoldbachRoughFifth.sievingPrimes S) := by
    change F.mainSum (upperRosserWeight F.prodPrimes D) = _
    rw [mainSum_upperRosserWeight_eq_setDensitySum]
    change upperRosserSetDensitySum progressionDensity D P.primeFactors = _
    rw [primorial_factors]
  rw [← hMain]
  refine hFinite.trans (add_le_add le_rfl ?_)
  exact hError.trans_eq (sum_congr rfl fun d _ => by rw [fullShiftedUpperSieve_rem_bv])


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenFullShiftedBV.lean
section
namespace GoldbachTwinChenBridge

open ArithmeticFunction Finset Filter GoldbachRoughFifth OAI.LargePrimeGaps
-- The following bound is reproved from the public error estimates of PR 3771.
private theorem roughBV_prefix_bound {x N D P : ℕ} (hcop : N.Coprime P)
    (hD : (D : ℝ) ≤ (x : ℝ)^(19/40 : ℝ)) :
    (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P),
      |bvAPMass ArithmeticFunction.vonMangoldt 0 x d N - ((x : ℝ)/d.totient)|) ≤
    ∑ d ∈ Icc 1 ⌊(x : ℝ)^(19/40 : ℝ)⌋₊, (endpointError x d : ℝ) := by
  let G := (Icc 1 D).filter (fun d => d ∣ P)
  calc
    _ ≤ ∑ d ∈ G, (endpointError x d : ℝ) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hi, hdP⟩ := mem_filter.mp hd
      have hdpos : 0 < d := (mem_Icc.mp hi).1
      have hmod : (N % d).Coprime d := by
        have hc := hcop.coprime_dvd_right hdP
        unfold Nat.Coprime at *
        rwa [← Nat.gcd_rec, Nat.gcd_comm]
      exact endpointClassError_le x (Nat.mod_lt N hdpos) hmod
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact (filter_subset _ _).trans (Icc_subset_Icc_right ((Nat.le_floor_iff (by positivity)).mpr hD))
      · exact fun d _ _ => (endpointError x d).coe_nonneg

private theorem endpoint_three_error {d : ℕ} (hd : 0 < d) :
    |bvAPMass vonMangoldt 0 3 d 2 - (3 : ℝ)/d.totient| ≤ 9 := by
  let W := (Ioc 0 3).filter (fun k : ℕ => k % d=2 % d)
  have hMassNN : 0 ≤ bvAPMass vonMangoldt 0 3 d 2 :=
    sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  have hMass : bvAPMass vonMangoldt 0 3 d 2 ≤ 6 := by
    change (∑ k ∈ W, vonMangoldt k) ≤ _
    calc
      _ ≤ ∑ _k ∈ W, (2 : ℝ) := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk0,hk3⟩ := mem_Ioc.mp (mem_filter.mp hk).1
        have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
        have hkPos : (0 : ℝ) < k := by exact_mod_cast hk0
        linarith only [(vonMangoldt_le_log (n:=k)).trans (Real.log_le_sub_one_of_pos hkPos),hkR]
      _ ≤ ∑ _k ∈ Ioc (0:ℕ) 3, (2 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by norm_num)
      _ = _ := by norm_num [Nat.card_Ioc, nsmul_eq_mul]
  have hDen : (1 : ℝ) ≤ d.totient := by
    exact_mod_cast (Nat.totient_pos.mpr hd)
  have hModelNN : 0 ≤ (3 : ℝ)/d.totient := by positivity
  have hModel : (3 : ℝ)/d.totient ≤ 3 := by
    apply (div_le_iff₀ (by linarith : 0 < (d.totient : ℝ))).mpr
    linarith only [hDen]
  exact abs_le.mpr ⟨by linarith only [hModel,hMassNN],by linarith only [hMass,hModelNN]⟩

/-- The full shifted prime interval has the sub-half BV remainder needed by
the reverse upper sieve. The fixed left endpoint costs at most 9 per modulus. -/
theorem full_shifted_prime_distribution_log_sq :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ X : ℕ in atTop, ∀ D P : ℕ,
      (D : ℝ) ≤ ((X+2 : ℕ) : ℝ)^(9/20 : ℝ) → (2 : ℕ).Coprime P →
      (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P),
        |bvAPMass bvPrimeWeight 3 (X+2) d 2 - ((X : ℝ)-1)/d.totient|) ≤
          E*((X+2 : ℕ) : ℝ)/(Real.log ((X+2 : ℕ) : ℝ))^2 := by
  obtain ⟨M,hM,hBV⟩ := roughFifthBVSubHalf (19/40) 2 (by norm_num) (by norm_num)
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hBV)
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp (eventually_bvPrimePower_cost 2 1 zero_lt_one)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_log_rpow_le_rpow 2 (by norm_num : (0 : ℝ) < 11/20)))
  refine ⟨M+10, by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max (max T₀ T₁) (max T₂ 2))]
    with X hX
  intro D P hD hCop
  let Y : ℕ := X+2
  let G := (Icc 1 D).filter (fun d => d ∣ P)
  let b := fun (y d : ℕ) => |bvAPMass vonMangoldt 0 y d 2 - (y:ℝ)/d.totient|
  have hY1 : (1 : ℝ) < Y := by exact_mod_cast (by dsimp [Y]; omega : 1 < Y)
  have hYPos : (0 : ℝ) < Y := by linarith
  have hLog := Real.log_pos hY1
  have hLogSq : 0 < (Real.log (Y : ℝ))^2 := sq_pos_of_pos hLog
  have hD' : (D : ℝ) ≤ (Y : ℝ)^(19/40 : ℝ) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num))
  have hRight : (∑ d ∈ G, b Y d) ≤ M*(Y:ℝ)/(Real.log (Y:ℝ))^2 := by
    have hb := (roughBV_prefix_bound hCop hD').trans (hT₀ Y (by dsimp [Y]; omega))
    rw [Real.rpow_neg hLog.le, Real.rpow_two, ← div_eq_mul_inv] at hb
    exact hb
  have hCard : G.card ≤ D :=
    (card_le_card (filter_subset _ _)).trans_eq (by simp [Nat.card_Icc])
  have hGrowth := hT₂ Y (by dsimp [Y]; omega)
  rw [Real.rpow_two] at hGrowth
  have hSmallD : (D : ℝ) ≤ (Y : ℝ)/(Real.log (Y:ℝ))^2 := by
    apply (le_div_iff₀ hLogSq).mpr
    calc
      _ ≤ (Y:ℝ)^(9/20:ℝ) * (Y:ℝ)^(11/20:ℝ) :=
        mul_le_mul hD hGrowth hLogSq.le (by positivity)
      _ = _ := by rw [← Real.rpow_add hYPos]; norm_num
  have hLeft : (∑ d ∈ G, b 3 d) ≤ 9*(Y:ℝ)/(Real.log (Y:ℝ))^2 := by
    calc
      _ ≤ ∑ _d ∈ G, (9:ℝ) := sum_le_sum fun d hd =>
        endpoint_three_error (mem_Icc.mp (mem_filter.mp hd).1).1
      _ = (G.card:ℝ)*9 := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (D:ℝ)*9 := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (by norm_num)
      _ ≤ ((Y:ℝ)/(Real.log (Y:ℝ))^2)*9 := mul_le_mul_of_nonneg_right hSmallD (by norm_num)
      _ = _ := by ring
  have hPP : (G.card:ℝ)*(Chebyshev.psi Y - Chebyshev.theta Y) ≤
      (1:ℝ)*Y/(Real.log (Y:ℝ))^2 := by
    have hp := hT₁ Y (by dsimp [Y]; omega) D hD
    rw [Real.rpow_two] at hp
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hCard)
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))).trans hp
  have hY3 : 3 ≤ Y := by dsimp [Y]; omega
  have hs := sum_le_sum (s:=G) (fun d _ => bvAPMass_prime_error_from_prefix
    hY3 (le_rfl : Y≤Y) d 2 (fun y => (y:ℝ)/d.totient))
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← sub_div] at hs
  have hLen : (Y:ℝ)-((3:ℕ):ℝ) = (X:ℝ)-1 := by simp only [Y,Nat.cast_add,Nat.cast_ofNat]; ring
  rw [hLen] at hs
  refine hs.trans ((add_le_add (add_le_add hRight hLeft) hPP).trans_eq ?_)
  ring


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/ReverseChenUpperSingleDensityInput.lean
section
namespace GoldbachTwinChenBridge

open Finset Filter GoldbachRoughFifth OAI.LargePrimeGaps MathlibNt.SieveTheory.LinearSieve

set_option maxHeartbeats 450000 in
theorem rough_upper_of_uniform_upper_rosser_density
    (hRatio : ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      upperRosserSetDensitySum progressionDensity (reverseUpperLevel X)
        (sievingPrimes (reverseUpperScale X)) ≤ K * sieveDensity (reverseUpperScale X)) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((roughCandidateSet X).card : ℝ) * (Real.log (X : ℝ))^2 ≤ C*(X : ℝ) := by
  obtain ⟨K,hK,hRatio⟩ := hRatio
  obtain ⟨c,hc,hProd⟩ := dyadic_fifth_sieveDensity_invlog_upper
  obtain ⟨E,hE,hBV⟩ := full_shifted_prime_distribution_log_sq
  refine ⟨160*K*c+4*E+1,by positivity,eventually_atTop.mp ?_⟩
  have hLogAt : ∀ᶠ X : ℕ in atTop, (1:ℝ) ≤ Real.log (X:ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hGrow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_log_rpow_le_rpow 2 (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hRatio,hBV,reverse_upper_dyadic_geometry,eventually_ge_atTop (2:ℕ),
    hLogAt,hGrow] with X hRatioX hBX hGeo hX hLogX hGrowX
  let S := reverseUpperScale X
  let Y := reverseUpperPrimeCutoff X
  let D := reverseUpperLevel X
  let L := Real.log (X : ℝ)
  let Z : ℕ := X+2
  let U := upperRosserSetDensitySum progressionDensity D (sievingPrimes S)
  obtain ⟨hS,hEven,hFix,hUnder,hY,hY5,hLogY,hD,hDR,hPrimeD⟩ := hGeo
  have hLogOne : (1:ℝ) ≤ L := hLogX
  have hL : 0 < L := by linarith
  have hLogYPos : 0 < Real.log (Y:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have hProduct := hProd S Y hS hY (by rw [hFix]; exact hY5)
  rw [hFix] at hProduct
  have hU : U ≤ 80*K*c/L := calc
    _ ≤ K*sieveDensity S := hRatioX
    _ ≤ K*(c/Real.log (Y:ℝ)) := mul_le_mul_of_nonneg_left hProduct hK.le
    _ ≤ K*(c/(L/80)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hc.le (by positivity) hLogY) hK.le
    _ = _ := by field_simp <;> ring
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXRpos : (0:ℝ) < X := by linarith
  have hMass : ((X:ℝ)-1)*U ≤ (80*K*c)*(X:ℝ)/L := calc
    _ ≤ ((X:ℝ)-1)*(80*K*c/L) := mul_le_mul_of_nonneg_left hU (by linarith)
    _ ≤ (X:ℝ)*(80*K*c/L) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring
  have hCoprime : (2:ℕ).Coprime (GoldbachRoughFifth.primorial S) :=
    (primorial_coprime S).symm.coprime_dvd_left (even_iff_two_dvd.mp hEven)
  have hBZ := hBX D (GoldbachRoughFifth.primorial S) hDR hCoprime
  have hZX : (X:ℝ) ≤ Z := by
    exact_mod_cast (show X ≤ Z by dsimp [Z]; omega)
  have hZUpper : (Z:ℝ) ≤ 2*(X:ℝ) := by
    exact_mod_cast (show Z ≤ 2*X by dsimp [Z]; omega)
  have hLZ : L ≤ Real.log (Z:ℝ) := Real.log_le_log hXRpos hZX
  have hBvScale : E*(Z:ℝ)/(Real.log (Z:ℝ))^2 ≤ (2*E)*(X:ℝ)/L^2 := calc
    _ ≤ E*(Z:ℝ)/L^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL)
        (pow_le_pow_left₀ hL.le hLZ 2)
    _ ≤ E*(2*(X:ℝ))/L^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hZUpper hE.le) (sq_nonneg _)
    _ = _ := by ring
  have hSift :
      (fullShiftedUpperSieve X S hEven).siftedSum ≤
        (80*K*c)*(X:ℝ)/L + (2*E)*(X:ℝ)/L^2 :=
    (fullShiftedUpperSieve_finite_bound (X:=X) (S:=S) (D:=D) hEven hD hPrimeD).trans
      (add_le_add hMass (hBZ.trans hBvScale))
  have hXOne : 1 ≤ X := (by decide : 1 ≤ 2).trans hX
  have hWeightBase :
      ((roughCandidateSet X).card : ℝ)*(L/2) ≤
        (fullShiftedUpperSieve X S hEven).siftedSum + (X.sqrt:ℝ)*(L/2) :=
    roughCount_mul_halfLog_le_siftedSum_add_sqrt (X:=X) (S:=S) hEven hXOne hUnder
  have hWeighted : ((roughCandidateSet X).card : ℝ)*(L/2) ≤
      (80*K*c)*(X:ℝ)/L + (2*E)*(X:ℝ)/L^2 + (X.sqrt:ℝ)*(L/2) := by
    refine le_trans hWeightBase ?_
    exact add_le_add hSift le_rfl
  have hLogGrowth : L^2 ≤ Real.sqrt (X:ℝ) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hGrowX
  have hSmall : (X.sqrt : ℝ)*L^2 ≤ (X:ℝ) := calc
    _ ≤ Real.sqrt (X:ℝ)*Real.sqrt (X:ℝ) :=
      mul_le_mul (Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' X))
        hLogGrowth (sq_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg X)]
  have hError : (4*E)*(X:ℝ)/L ≤ (4*E)*(X:ℝ) := by
    apply (div_le_iff₀ hL).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hLogOne (by positivity : 0≤(4*E)*(X:ℝ))
  calc
    _ = (((roughCandidateSet X).card : ℝ)*(L/2))*(2*L) := by dsimp only [L]; ring
    _ ≤ ((80*K*c)*(X:ℝ)/L + (2*E)*(X:ℝ)/L^2 + (X.sqrt:ℝ)*(L/2))*(2*L) :=
      mul_le_mul_of_nonneg_right hWeighted (by positivity)
    _ = (160*K*c)*(X:ℝ) + (4*E)*(X:ℝ)/L + (X.sqrt:ℝ)*L^2 := by
      field_simp <;> ring
    _ ≤ _ := by linarith only [hSmall,hError]


end GoldbachTwinChenBridge
end


-- Source: twin-chen-reverse-weighted/upper-rosser-9d4/E341RoughUpperUnconditional.lean
section
namespace GoldbachTwinChenBridge

open Finset Filter GoldbachRoughFifth
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem tendsto_reverseUpperLevel :
    Tendsto reverseUpperLevel atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop ((2:ℕ)^(3*(Nat.log 2 n+1)))] with X hX
  have hLog := Nat.le_log_of_pow_le (by decide : 1 < (2:ℕ)) hX
  unfold reverseUpperLevel
  exact (Nat.lt_pow_succ_log_self (by decide) n).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))

private theorem reverseUpperScale_le_reverseUpperLevel (X : ℕ) :
    reverseUpperScale X ≤ reverseUpperLevel X := by
  unfold reverseUpperScale reverseUpperLevel
  apply Nat.pow_le_pow_right (by decide)
  omega

private theorem upper_support_below_rounded_cutoff {X : ℕ}
    (hD : 2 ≤ reverseUpperLevel X) :
    ∀ p ∈ (GoldbachRoughFifth.primorial (reverseUpperScale X)).primeFactors,
      p < ⌈(reverseUpperLevel X : ℝ)^(1/(11/5:ℝ))⌉₊ := by
  intro p hp
  rw [primorial_factors] at hp
  have hFive := (mem_filter.mp hp).2.2.1
  have hPow : (p:ℝ)^5 ≤ (reverseUpperLevel X : ℝ) := by
    exact_mod_cast hFive.trans (reverseUpperScale_le_reverseUpperLevel X)
  have hpR : (p:ℝ) ≤ (reverseUpperLevel X : ℝ)^(1/5:ℝ) := calc
    _ = ((p:ℝ)^5)^(1/5:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hPow (by norm_num)
  have hDR : (1:ℝ) < reverseUpperLevel X := by exact_mod_cast (show 1 < reverseUpperLevel X by omega)
  have hRpow : (reverseUpperLevel X : ℝ)^(1/5:ℝ) <
      (reverseUpperLevel X : ℝ)^(1/(11/5:ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hDR (by norm_num)
  exact_mod_cast (hpR.trans_lt hRpow).trans_le (Nat.le_ceil _)

/-- The actual normalized Rosser main term on the reversed rough undersieve. -/
theorem reverse_upper_rosser_density_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      upperRosserSetDensitySum progressionDensity (reverseUpperLevel X)
        (sievingPrimes (reverseUpperScale X)) ≤ K * sieveDensity (reverseUpperScale X) := by
  let s : ℝ := 11/5
  have hsrc : SuzukiClaim145SourceParameters (16:ℝ) (1/2:ℝ) (7:ℝ) := by
    constructor <;> norm_num
  obtain ⟨K,hK,hLocal⟩ := short_interval_product_input
  obtain ⟨C₁,_,hAll⟩ :=
    exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_,_,C,_,_,hC,hMain⟩ := hAll C₁ le_rfl
  obtain ⟨Dσ,_,hσ⟩ := exists_sourceSigma_fixed_lower_threshold (16:ℝ) s (by norm_num [s])
  have hError := eventually_all_odd_depth_suzuki_error_upper_window
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C:=C) (K:=K) (d:=16) (Δ:=1/2) (ρ:=1)
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨|suzukiContinuousUpperFactor s| + 1, by positivity, ?_⟩
  have hLevelR := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp tendsto_reverseUpperLevel
  filter_upwards [reverse_upper_dyadic_geometry,
    tendsto_reverseUpperLevel.eventually (eventually_ge_atTop (2:ℕ)),
    hLevelR.eventually (eventually_ge_atTop Dσ), hLevelR.eventually hError]
    with X hGeo hD hDLarge hErrorX
  let S := reverseUpperScale X
  let D := reverseUpperLevel X
  obtain ⟨_,he,_,_,_,_,_,_,_,_⟩ := hGeo
  let A := centralSieve S he
  let P := GoldbachRoughFifth.primorial S
  let z := ⌈(D:ℝ)^(1/s)⌉₊
  have hDR : (1:ℝ) < D := by exact_mod_cast (show 1<D by omega)
  have hz : 2 ≤ z := by
    have hExp : (1:ℝ) < (D:ℝ)^(1/s) := Real.one_lt_rpow hDR (by norm_num [s])
    exact_mod_cast (hExp.trans_le (Nat.le_ceil _))
  have hCut : ∀ p ∈ A.prodPrimes.primeFactors, p < z := upper_support_below_rounded_cutoff hD
  have hOdd : Odd (2*A.prodPrimes.primeFactors.card+1) :=
    ⟨A.prodPrimes.primeFactors.card, by omega⟩
  have hBound := hMain A K hK (hLocal S he) D hD s
    (by norm_num [s]) (by norm_num [s]) (hσ (D:ℝ) hDLarge) hz hCut
  have hTail := (hErrorX _ hOdd s (by norm_num [s]) (by norm_num [s])).2
  let err : ℝ := C * Real.exp (Real.sqrt K) *
    errorEnvelope jr1965Section13HatLayers (2*A.prodPrimes.primeFactors.card+1)
      (D:ℝ) 16 s * Real.log (D:ℝ)^(-(1/2:ℝ))
  change err < 1 at hTail
  have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors A = sieveDensity S := by
    change (∏ p ∈ P.primeFactors, (1-progressionDensity p)) = _
    rw [primorial_factors]
    apply prod_congr rfl
    intro p hp
    rw [progressionDensity_prime (mem_filter.mp hp).2.1]
  have hVNN : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors A := by
    apply prod_nonneg
    intro p hp
    have h := (Nat.mem_primeFactors_of_ne_zero A.prodPrimes_ne_zero).mp hp
    exact sub_nonneg.mpr (A.nu_lt_one_of_prime p h.1 h.2).le
  have hTable := mainSum_upperRosserWeight_eq_setDensitySum A D
  change A.mainSum (upperRosserWeight P D) =
    upperRosserSetDensitySum progressionDensity D P.primeFactors at hTable
  rw [primorial_factors] at hTable
  change upperRosserSetDensitySum progressionDensity D (sievingPrimes S) ≤ _
  rw [← hTable]
  calc
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors A *
        (suzukiContinuousUpperFactor s + err) := hBound
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors A *
        (|suzukiContinuousUpperFactor s| + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hTail.le) hVNN
    _ = _ := by rw [hV, mul_comm]

theorem reverse_rough_upper_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((roughCandidateSet X).card : ℝ) * (Real.log (X:ℝ))^2 ≤ C*(X:ℝ) :=
  rough_upper_of_uniform_upper_rosser_density reverse_upper_rosser_density_uniform


end GoldbachTwinChenBridge
end


-- Source: twin-cut-51b349-refute/TwinDyadicLogSquareRefutation.lean
section
open GoldbachTwinChenBridge

theorem Conjectures.Cuts.Refute359fb2bfba7687230b3e5a26 :
    ¬ (∀ (x1 : ℝ) (x2 : ℕ), ∃ (x3 : ℕ), (16 : ℕ) ≤ x3 ∧ x2 < x3 ∧
      x1 * ↑x3 / Real.log ((2 : ℝ) + ↑x3) ^ (2 : ℕ) <
        ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) |
          Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  intro h
  obtain ⟨C, _hC, X₀, hUpper⟩ := reverse_rough_upper_unconditional
  obtain ⟨X, h16, hBX, hCard⟩ := h (2 * C) X₀
  let pairs := (Finset.Ioc X (2 * X)).filter (fun n => n.Prime ∧ (n + 2).Prime)
  have hSub : pairs ⊆ roughCandidateSet (2 * X) := by
    intro n hn
    obtain ⟨hRange, hp, hShift⟩ := Finset.mem_filter.mp hn
    obtain ⟨hLower, hUpper⟩ := Finset.mem_Ioc.mp hRange
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hUpper), hp.one_lt, hShift, ?_⟩
    intro q hq hqp
    rw [(Nat.prime_dvd_prime_iff_eq hqp hp).mp (Nat.dvd_of_mem_divisors hq)]
    calc
      2 * X ≤ 2 * n := Nat.mul_le_mul_left 2 hLower.le
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      _ = n ^ 2 := by ring
      _ ≤ n ^ 10 := Nat.pow_le_pow_right (by omega : 0 < n) (by decide)
  have hCardLe : (pairs.card : ℝ) ≤ ((roughCandidateSet (2 * X)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  have hReal : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h16
  have hLogPos : 0 < Real.log (2 + (X : ℝ)) := Real.log_pos (by linarith)
  have hLogLe : Real.log (2 + (X : ℝ)) ≤ Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have hSquareLe : (Real.log (2 + (X : ℝ))) ^ 2 ≤
      (Real.log ((2 * X : ℕ) : ℝ)) ^ 2 := by
    exact sq_le_sq' (by linarith [hLogPos]) hLogLe
  have hBound : (pairs.card : ℝ) * (Real.log (2 + (X : ℝ))) ^ 2 ≤
      C * ((2 * X : ℕ) : ℝ) :=
    (mul_le_mul hCardLe hSquareLe (sq_nonneg _) (by positivity)).trans (hUpper _ (by omega))
  have hStrict : 2 * C * (X : ℝ) < (pairs.card : ℝ) * (Real.log (2 + (X : ℝ))) ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hLogPos)).mp hCard
  push_cast at hBound
  linarith
end
