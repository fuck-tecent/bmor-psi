import Mathlib
import Conjectures.Goldbach.RoughFifthMass

/-!
Lower-bound prime mass after the fifth-root sieve, twin route.
The one-dimensional lower sieve, the Rosser weights and the Bombieri-Vinogradov input are those
of the accepted module Conjectures.Goldbach.RoughFifthMass; here they are rerun on the shifted
sequence p + 2 over primes p of the window (X, 51X/50).
-/

namespace Conjectures.TwinPrimes.FifthRootRoughPrimeMass_aux

open Finset Filter
open GoldbachRoughFifth
open OAI.LargePrimeGaps
open RoughFifthGeometry
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple

/-- The last integer of the window, i.e. the largest p with 50p < 51X. -/
def twinUpper (X : ℕ) : ℕ := (51 * X - 1) / 50

def twinPrimes (X : ℕ) : Finset ℕ := (Finset.Ioc X (twinUpper X)).filter (fun p => p.Prime)

def twinSievingPrimes (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun q => q.Prime ∧ q ^ 5 ≤ X ∧ q ≠ 2)

def twinPrimorial (X : ℕ) : ℕ := ∏ q ∈ twinSievingPrimes X, q

theorem twinPrimorial_squarefree (X : ℕ) : Squarefree (twinPrimorial X) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (mem_filter.mp hp).2.1 (mem_filter.mp hq).2.1).mpr hpq)
  · intro p hp
    exact (mem_filter.mp hp).2.1.squarefree

theorem twinPrimorial_factors (X : ℕ) :
    (twinPrimorial X).primeFactors = twinSievingPrimes X := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hd, _⟩
    obtain ⟨p, hmem, hdiv⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have heq := (Nat.prime_dvd_prime_iff_eq hp (mem_filter.mp hmem).2.1).mp hdiv
    simpa [heq] using hmem
  · intro hq
    exact ⟨(mem_filter.mp hq).2.1, Finset.dvd_prod_of_mem _ hq,
      (twinPrimorial_squarefree X).ne_zero⟩

theorem mem_twinSievingPrimes {X q : ℕ} (hq : q ∈ twinSievingPrimes X) :
    q.Prime ∧ q ^ 5 ≤ X ∧ q ≠ 2 := (mem_filter.mp hq).2

theorem mem_twinPrimes {X p : ℕ} (hp : p ∈ twinPrimes X) :
    X < p ∧ p ≤ twinUpper X ∧ p.Prime := by
  obtain ⟨hI, hpr⟩ := mem_filter.mp hp
  exact ⟨(mem_Ioc.mp hI).1, (mem_Ioc.mp hI).2, hpr⟩

theorem le_twinUpper_iff {X p : ℕ} (hX : 1 ≤ X) :
    p ≤ twinUpper X ↔ 50 * p < 51 * X := by
  unfold twinUpper
  omega

theorem twinUpper_lt {X : ℕ} (hX : 1 ≤ X) : twinUpper X < 2 * X := by
  have h : 50 * twinUpper X < 51 * X := (le_twinUpper_iff hX).mp le_rfl
  omega

theorem mem_twinPrimes_iff {X p : ℕ} (hX : 1 ≤ X) :
    p ∈ twinPrimes X ↔ X < p ∧ 50 * p < 51 * X ∧ p.Prime := by
  rw [twinPrimes, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hpr⟩
    exact ⟨hlo, (le_twinUpper_iff hX).mp hhi, hpr⟩
  · rintro ⟨hlo, hhi, hpr⟩
    exact ⟨⟨hlo, (le_twinUpper_iff hX).mpr hhi⟩, hpr⟩

noncomputable def twinDensity (X : ℕ) : ℝ :=
  ∏ q ∈ twinSievingPrimes X, (1 - 1 / ((q : ℝ) - 1))

noncomputable def twinSieve (X : ℕ) : BoundingSieve where
  support := (twinPrimes X).image (fun p => p + 2)
  prodPrimes := twinPrimorial X
  prodPrimes_squarefree := twinPrimorial_squarefree X
  weights m := Real.log ((m - 2 : ℕ) : ℝ)
  weights_nonneg m := Real.log_natCast_nonneg _
  totalMass := ((twinUpper X : ℕ) : ℝ) - (X : ℝ)
  nu := progressionDensity
  nu_mult := progressionDensity_mult
  nu_pos_of_prime p hp _ := by
    rw [progressionDensity_prime hp]
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    positivity
  nu_lt_one_of_prime p hp hd := by
    have hm : p ∈ twinSievingPrimes X := by
      rw [← twinPrimorial_factors]
      exact Nat.mem_primeFactors.mpr ⟨hp, hd, (twinPrimorial_squarefree _).ne_zero⟩
    have hne : p ≠ 2 := (mem_twinSievingPrimes hm).2.2
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    rw [progressionDensity_prime hp]
    exact (div_lt_one (by linarith)).mpr (by linarith)


/-- The residue class of -2 modulo d, as a representative below d. -/
def twinResidue (d : ℕ) : ℕ := (2 * d - 2) % d

theorem twinResidue_mod (d : ℕ) (hd : 1 ≤ d) : twinResidue d % d = twinResidue d :=
  Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

theorem odd_of_dvd_odd {d P : ℕ} (hP : Odd P) (hd : d ∣ P) : Odd d := by
  rw [Nat.odd_iff] at hP ⊢
  obtain ⟨k, hk⟩ := hd
  subst hk
  by_contra h0
  have hd0 : d % 2 = 0 := by omega
  have hmul : (d * k) % 2 = 0 := by rw [Nat.mul_mod, hd0, Nat.zero_mul]
  omega

theorem coprime_twinResidue {d : ℕ} (hd : Odd d) : (twinResidue d).Coprime d := by
  have hnot2 : ¬ (2 ∣ d) := fun h2 => by
    have hA : d % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
    have hB : d % 2 = 1 := Nat.odd_iff.mp hd
    omega
  have hcopd2 : d.Coprime 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2).symm
  have hd1 : 1 ≤ d := by
    obtain ⟨k, hk⟩ := hd
    omega
  rcases Nat.eq_or_lt_of_le hd1 with hdEq | hd2
  · subst hdEq
    simp [twinResidue]
  · have hd3 : 3 ≤ d := by
      obtain ⟨k, hk⟩ := hd
      omega
    have hmod : twinResidue d = d - 2 := by
      unfold twinResidue
      have h1 : 2 * d - 2 = d + (d - 2) := by omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega)), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have hcop2 : (d - 2).Coprime 2 := (Nat.coprime_sub_self_left (by omega)).mpr hcopd2
    have h := (Nat.coprime_add_self_right (m := d - 2) (n := 2)).mpr hcop2
    rwa [show 2 + (d - 2) = d by omega] at h

theorem shifted_divisibility_iff {p d : ℕ} (hd : 1 ≤ d) :
    d ∣ p + 2 ↔ p % d = twinResidue d := by
  have h2 : 2 * d - 2 + 2 = 2 * d := by omega
  have hzero : Nat.ModEq d (2 * d) 0 :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left d 2)
  unfold twinResidue
  change (d ∣ p + 2 ↔ Nat.ModEq d p (2 * d - 2))
  constructor
  · intro h
    have h1 : Nat.ModEq d (p + 2) 0 := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : Nat.ModEq d (p + 2) ((2 * d - 2) + 2) := by
      have h' : Nat.ModEq d (p + 2) (2 * d) := h1.trans hzero.symm
      rwa [h2]
    exact Nat.ModEq.add_right_cancel' 2 h3
  · intro h
    have h1 : Nat.ModEq d (p + 2) ((2 * d - 2) + 2) := h.add (Nat.ModEq.refl 2)
    rw [h2] at h1
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans hzero)

theorem twinSieve_multSum (X d : ℕ) (hd : 1 ≤ d) :
    (twinSieve X).multSum d =
      bvAPMass bvPrimeWeight X (twinUpper X) d (twinResidue d) := by
  change (∑ m ∈ (twinPrimes X).image (fun p => p + 2),
      if d ∣ m then Real.log ((m - 2 : ℕ) : ℝ) else 0) = _
  rw [Finset.sum_image (by intro p _ q _ h; dsimp at h; omega)]
  simp only [twinPrimes]
  unfold bvAPMass bvPrimeWeight
  rw [Finset.sum_filter, Finset.sum_filter, twinResidue_mod d hd]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · rw [if_pos hprime, if_pos hprime, Nat.add_sub_cancel]
    by_cases hdiv : d ∣ p + 2
    · rw [if_pos hdiv, if_pos ((shifted_divisibility_iff hd).mp hdiv)]
    · rw [if_neg hdiv, if_neg (fun h => hdiv ((shifted_divisibility_iff hd).mpr h))]
  · rw [if_neg hprime, if_neg hprime]
    split_ifs <;> rfl

theorem twinSieve_rem (X d : ℕ) (hd : 1 ≤ d) :
    (twinSieve X).rem d =
      bvAPMass bvPrimeWeight X (twinUpper X) d (twinResidue d) -
        (((twinUpper X : ℕ) : ℝ) - (X : ℝ)) / (d.totient : ℝ) := by
  rw [BoundingSieve.rem, twinSieve_multSum X d hd]
  change _ - ((d.totient : ℝ))⁻¹ * (((twinUpper X : ℕ) : ℝ) - (X : ℝ)) = _
  rw [div_eq_mul_inv]
  ring

theorem twinBV_prefix_bound {x D P : ℕ} (hP : Odd P) (hD : (D : ℝ) ≤ (x : ℝ) ^ (19 / 40 : ℝ)) :
    (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P),
      |bvAPMass ArithmeticFunction.vonMangoldt 0 x d (twinResidue d) - ((x : ℝ) / d.totient)|) ≤
    ∑ d ∈ Icc 1 ⌊(x : ℝ) ^ (19 / 40 : ℝ)⌋₊, (endpointError x d : ℝ) := by
  let G := (Icc 1 D).filter (fun d => d ∣ P)
  calc
    _ ≤ ∑ d ∈ G, (endpointError x d : ℝ) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hi, hdP⟩ := mem_filter.mp hd
      have hdpos : 0 < d := (mem_Icc.mp hi).1
      have hcop : (twinResidue d % d).Coprime d := by
        rw [twinResidue_mod d (by omega)]
        exact coprime_twinResidue (odd_of_dvd_odd hP hdP)
      exact endpointClassError_le x (Nat.mod_lt _ hdpos) hcop
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact (filter_subset _ _).trans
          (Icc_subset_Icc_right ((Nat.le_floor_iff (by positivity)).mpr hD))
      · exact fun d _ _ => (endpointError x d).coe_nonneg


theorem twinPrimorial_odd (X : ℕ) : Odd (twinPrimorial X) := by
  have hcop : Nat.Coprime 2 (twinPrimorial X) := by
    unfold twinPrimorial
    refine Nat.Coprime.prod_right (fun q hq => ?_)
    have hp := (mem_twinSievingPrimes hq).1
    have hne := (mem_twinSievingPrimes hq).2.2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h2 => hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm)
  have h2 : ¬ (2 ∣ twinPrimorial X) :=
    fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop h
  rw [Nat.odd_iff]
  omega

theorem twinBV_residue_class {x D P : ℕ} (hP : Odd P) :
    (D : ℝ) ≤ (x : ℝ) ^ (19 / 40 : ℝ) →
    (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P),
      |bvAPMass ArithmeticFunction.vonMangoldt 0 x d (twinResidue d) - ((x : ℝ) / d.totient)|) ≤
    ∑ d ∈ Icc 1 ⌊(x : ℝ) ^ (19 / 40 : ℝ)⌋₊, (endpointError x d : ℝ) :=
  fun hD => twinBV_prefix_bound hP hD

theorem twin_prime_distribution (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ D P : ℕ,
      (D : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) → Odd P →
      (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P),
        |bvAPMass bvPrimeWeight X (twinUpper X) d (twinResidue d) -
          (((twinUpper X : ℕ) : ℝ) - (X : ℝ)) / d.totient|) ≤
          C * X / (Real.log X) ^ A := by
  obtain ⟨M, hM, hBV⟩ := roughFifthBVSubHalf (19 / 40) A (by norm_num) hA
  have hev := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hBV
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  obtain ⟨T', hT'⟩ := eventually_atTop.mp (eventually_bvPrimePower_cost A 1 zero_lt_one)
  refine ⟨4 * M + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max T 4), eventually_ge_atTop T'] with X hX hX'
  intro D P hD hP
  let G := (Icc 1 D).filter (fun d => d ∣ P)
  let b := fun (x d : ℕ) =>
    |bvAPMass ArithmeticFunction.vonMangoldt 0 x d (twinResidue d) - (x : ℝ) / d.totient|
  have hX1 : 1 ≤ X := by have := hX; omega
  have hXpos : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlNp := Real.log_pos hXpos
  have hUX : X ≤ twinUpper X := by unfold twinUpper; omega
  have hU2 : twinUpper X ≤ 2 * X := (twinUpper_lt hX1).le
  have hend (x : ℕ) (hXX : X ≤ x) (hx2 : x ≤ 2 * X) :
      (∑ d ∈ G, b x d) ≤ M * (2 * (X : ℝ)) * (Real.log X) ^ (-A) := by
    have hTx : T ≤ x := le_trans (le_trans (le_max_left _ _) hX) hXX
    have hD' : (D : ℝ) ≤ (x : ℝ) ^ (19 / 40 : ℝ) := by
      calc (D : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := hD
        _ ≤ (X : ℝ) ^ (19 / 40 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX1) (by norm_num)
        _ ≤ (x : ℝ) ^ (19 / 40 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hXX) (by norm_num)
    calc (∑ d ∈ G, b x d)
        ≤ ∑ d ∈ Icc 1 ⌊(x : ℝ) ^ (19 / 40 : ℝ)⌋₊, (endpointError x d : ℝ) :=
          twinBV_prefix_bound hP hD'
      _ ≤ M * x * (Real.log x) ^ (-A) := hT x hTx
      _ ≤ M * (2 * (X : ℝ)) * (Real.log X) ^ (-A) := by
          have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
          have hle : (Real.log X) ^ A ≤ (Real.log x) ^ A :=
            Real.rpow_le_rpow hlNp.le
              (Real.log_le_log (by positivity) (by exact_mod_cast hXX)) hA.le
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hx2) hM.le) ?_
            (Real.rpow_nonneg hlogx _) (by positivity)
          rw [Real.rpow_neg hlogx, Real.rpow_neg hlNp.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hlNp A) hle
  have hpp : ((G.card : ℝ) *
      (Chebyshev.psi ((2 * X : ℕ) : ℝ) - Chebyshev.theta ((2 * X : ℕ) : ℝ))) ≤
      (2 : ℝ) * (X : ℝ) / (Real.log X) ^ A := by
    have hcost := hT' (2 * X) (by omega) D (by
      calc (D : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := hD
        _ ≤ ((2 * X : ℕ) : ℝ) ^ (9 / 20 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : X ≤ 2 * X))
            (by norm_num))
    have hG : (G.card : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast ((card_le_card (filter_subset _ _)).trans_eq
        (by simp [Nat.card_Icc] : (Icc 1 D).card = D) : G.card ≤ D)
    have hsub : 0 ≤ Chebyshev.psi ((2 * X : ℕ) : ℝ) - Chebyshev.theta ((2 * X : ℕ) : ℝ) :=
      sub_nonneg.mpr (Chebyshev.theta_le_psi _)
    have htwo : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
    calc (G.card : ℝ) *
          (Chebyshev.psi ((2 * X : ℕ) : ℝ) - Chebyshev.theta ((2 * X : ℕ) : ℝ))
        ≤ (D : ℝ) *
          (Chebyshev.psi ((2 * X : ℕ) : ℝ) - Chebyshev.theta ((2 * X : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hG hsub
      _ ≤ 1 * ((2 * X : ℕ) : ℝ) / (Real.log ((2 * X : ℕ) : ℝ)) ^ A := hcost
      _ ≤ (2 : ℝ) * (X : ℝ) / (Real.log X) ^ A := by
          rw [htwo, one_mul]
          refine div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlNp A) ?_
          exact Real.rpow_le_rpow hlNp.le
            (Real.log_le_log (by positivity) (by linarith : (X : ℝ) ≤ 2 * (X : ℝ))) hA.le
  have hs := sum_le_sum (s := G) (fun d _ =>
    bvAPMass_prime_error_from_prefix hUX hU2 d (twinResidue d)
      (fun x => (x : ℝ) / d.totient))
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← sub_div] at hs
  change (∑ d ∈ G, |bvAPMass bvPrimeWeight X (twinUpper X) d (twinResidue d) -
      (((twinUpper X : ℕ) : ℝ) - (X : ℝ)) / d.totient|) ≤ _
  have hu := hend (twinUpper X) hUX hU2
  have hl := hend X le_rfl (by omega)
  refine hs.trans ((add_le_add (add_le_add hu hl) hpp).trans_eq ?_)
  rw [Real.rpow_neg hlNp.le]
  ring

theorem twin_local_product :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ X : ℕ, HasDimensionOneLocalProductBound (twinSieve X) K := by
  obtain ⟨J, hJ, hbound⟩ := RoughFifthLocalProduct.exists_goldbach_inverse_interval_bound
  refine ⟨max 2 J, le_max_left .., ?_⟩
  intro X a b ha hab
  let B := (twinPrimorial X).primeFactors.filter (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b)
  have hprime (q) (hq : q ∈ B) : q.Prime ∧ 2 < q := by
    have hm := (mem_filter.mp hq).1
    rw [twinPrimorial_factors] at hm
    obtain ⟨_, hp, _, hne⟩ := mem_filter.mp hm
    exact ⟨hp, by have := hp.two_le; omega⟩
  change (∏ p ∈ B, (1 - progressionDensity p)⁻¹) ≤ _
  calc
    _ = ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply prod_congr rfl
      intro p hp
      rw [progressionDensity_prime (hprime p hp).1]
    _ ≤ Real.log b / Real.log a * (1 + J / Real.log a) :=
      hbound B hprime a b ha hab (fun _ hq => (mem_filter.mp hq).2)
    _ ≤ _ := by
      have hla : 0 < Real.log a := Real.log_pos (by linarith)
      have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
      gcongr
      exact le_max_right _ _

open GoldbachRoughFifth.AnalyticInput.ErdosStraus.PrimeEstimates.Mertens in
private lemma twin_local_log_lower {q : ℕ} (hq : 3 ≤ q) :
    -(1 / (q : ℝ)) - 10 * (1 / (q : ℝ) ^ 2) ≤ Real.log (1 - 1 / ((q : ℝ) - 1)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) - 1 := by linarith
  have h := (abs_le.mp (abs_log_one_sub_add_le
    (one_div_pos.mpr hpos)
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ q - 1)))).1
  have hdiff : 1 / ((q : ℝ) - 1) - 1 / (q : ℝ) ≤ 2 / (q : ℝ) ^ 2 := by
    field_simp
    nlinarith
  have hs : 1 / ((q : ℝ) - 1) ≤ 2 / (q : ℝ) := by
    rw [div_le_div_iff₀ hpos (by linarith)]
    linarith
  have hs2 := pow_le_pow_left₀ (one_div_nonneg.mpr hpos.le) hs 2
  ring_nf at hs2 hdiff h ⊢
  linarith

open GoldbachRoughFifth.AnalyticInput.ErdosStraus.PrimeEstimates.Mertens in
theorem twinDensity_invlog_lower : ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, 6 ≤ X →
    c / Real.log (X : ℝ) ≤ twinDensity X := by
  obtain ⟨C, hC, hM⟩ := mertensSecond
  let D := mertensSecondConstant + C / Real.log 2 + 10 * (∑' k : ℕ, 1 / (k : ℝ) ^ 2)
  refine ⟨Real.exp (-D), Real.exp_pos _, ?_⟩
  intro X hX
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast (show 2 ≤ X by omega)
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hrange (q : ℕ) (hq : q ∈ twinSievingPrimes X) : 3 ≤ q := by
    obtain ⟨_, hp, _, hne⟩ := mem_filter.mp hq
    have := hp.two_le
    omega
  have hsubset : twinSievingPrimes X ⊆ primesUpTo X := by
    intro q hq
    obtain ⟨hr, hp, _, _⟩ := mem_filter.mp hq
    exact mem_primesUpTo.mpr ⟨hp, Nat.le_of_lt_succ (mem_range.mp hr)⟩
  have hpos (q : ℕ) (hq : q ∈ twinSievingPrimes X) : 0 < 1 - 1 / ((q : ℝ) - 1) := by
    have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hrange q hq
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : 0 < twinDensity X := Finset.prod_pos hpos
  have hlog : Real.log (twinDensity X) =
      ∑ q ∈ twinSievingPrimes X, Real.log (1 - 1 / ((q : ℝ) - 1)) :=
    Real.log_prod (fun q hq => (hpos q hq).ne')
  have hsum := Finset.sum_le_sum (fun q (hq : q ∈ twinSievingPrimes X) =>
    twin_local_log_lower (hrange q hq))
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← hlog] at hsum
  have hsmall : (∑ q ∈ twinSievingPrimes X, 1 / (q : ℝ)) ≤ primeReciprocalSum X :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
  have h2sum : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsq := h2sum.sum_le_tsum (twinSievingPrimes X) (fun _ _ => by positivity)
  have hM' := (abs_le.mp (hM (X : ℝ) hXR)).2
  simp only [Nat.floor_natCast] at hM'
  have hdiv : C / Real.log (X : ℝ) ≤ C / Real.log 2 := div_le_div_of_nonneg_left hC.le
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hXR)
  have hb : -D - Real.log (Real.log (X : ℝ)) ≤ Real.log (twinDensity X) := by
    dsimp [D]
    linarith
  have h := Real.exp_le_exp.mpr hb
  rwa [Real.exp_sub, Real.exp_log hL, Real.exp_log hprod] at h

theorem twin_finite_lower {X D : ℕ} (hX : 1 ≤ X)
    (hD : ∀ p ∈ (twinPrimorial X).primeFactors, p < D) {k : ℝ}
    (hMain : k * twinDensity X ≤
      (twinSieve X).mainSum (lowerRosserWeight (twinPrimorial X) D)) :
    k * (twinSieve X).totalMass * twinDensity X -
      (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ twinPrimorial X), |(twinSieve X).rem d|) ≤
      (twinSieve X).siftedSum := by
  let S := twinSieve X
  let P := twinPrimorial X
  let w := lowerRosserWeight P D
  have hCert := lowerRosserWeight_certificate (twinPrimorial_squarefree X)
    (twinPrimorial_squarefree X).ne_zero hD
  have hFinite := mainSum_sub_lowerErrSum_le_siftedSum (S := S) D w hCert
    (lowerRosserWeight_hasLowerLevelSupport P D)
  have hSub : P.divisors.filter (fun d => d < D) ⊆ (Icc 1 D).filter (fun d => d ∣ P) := by
    intro d hd
    obtain ⟨hDiv, hLt⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hDiv, hLt.le⟩,
      Nat.dvd_of_mem_divisors hDiv⟩
  have hError : lowerErrSum S D w ≤ ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ P), |S.rem d| := by
    calc
      _ ≤ ∑ d ∈ P.divisors.filter (fun d => d < D), |S.rem d| :=
        sum_le_sum fun d _ =>
          mul_le_of_le_one_left (abs_nonneg _) (abs_lowerRosserWeight_le_one P D d)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => abs_nonneg _)
  have hMass : 0 ≤ S.totalMass := by
    change 0 ≤ ((twinUpper X : ℕ) : ℝ) - (X : ℝ)
    exact sub_nonneg.mpr (by exact_mod_cast (show X ≤ twinUpper X by unfold twinUpper; omega))
  have hLow := mul_le_mul_of_nonneg_left hMain hMass
  exact (sub_le_sub (by simpa only [mul_left_comm k, mul_assoc] using hLow) hError).trans hFinite

theorem twin_rosser_main :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ X : ℕ in atTop,
      k * (twinSieve X).totalMass * twinDensity X -
        (∑ d ∈ (Icc 1 (level X)).filter (fun d => d ∣ twinPrimorial X),
          |(twinSieve X).rem d|) ≤
        (twinSieve X).siftedSum := by
  obtain ⟨K, hK, hLocal⟩ := twin_local_product
  obtain ⟨k, hk, D₀, hMain⟩ := RoughFifthSieve.fixedLowerDensity hK
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    tendsto_level.eventually (eventually_ge_atTop D₀),
    eventually_fifth_factor_cutoffs] with X hX hD hCuts
  let D := level X
  let z := ⌈(D : ℝ) ^ (1 / (11 / 5 : ℝ))⌉₊
  have hCut (p : ℕ) (hp : p ∈ (twinPrimorial X).primeFactors) : p < z ∧ p < D := by
    rw [twinPrimorial_factors] at hp
    exact hCuts p (mem_twinSievingPrimes hp).2.1
  have hz : 2 ≤ z := (hCuts 2 (by norm_num; omega)).1.le
  have hTab : suzukiVProduct (twinSieve X) (z : ℝ) = twinDensity X ∧
      (twinSieve X).mainSum (lowerRosserWeight (twinPrimorial X) D) =
        lowerRosserSetDensitySum (twinSieve X).nu D (suzukiSupportedBelow (twinSieve X) z) := by
    constructor
    · change (∏ p ∈ (twinPrimorial X).primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
          (1 - progressionDensity p)) = _
      rw [Finset.filter_eq_self.mpr (fun p hp => by exact_mod_cast (hCut p hp).1),
        twinPrimorial_factors]
      exact prod_congr rfl
        (fun p hp => by rw [progressionDensity_prime (mem_twinSievingPrimes hp).1])
    · have hcar : suzukiSupportedBelow (twinSieve X) z = (twinPrimorial X).primeFactors :=
        Finset.filter_eq_self.mpr (fun p hp => (hCut p hp).1)
      rw [hcar]
      exact mainSum_lowerRosserWeight_eq_setDensitySum (twinSieve X) D
  apply twin_finite_lower (X := X) (D := D) (by omega) (fun p hp => (hCut p hp).2)
  rw [hTab.2, ← hTab.1]
  exact hMain D hD (twinSieve X) (hLocal X) hz


theorem sifted_le_target (X : ℕ) (hX : 3 ≤ X) :
    Real.log (X : ℝ) * (twinSieve X).siftedSum ≤
      ∑ p ∈ (Finset.Ioo X (2 * X)).filter
        (fun p => 50 * p < 51 * X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p + 2).minFac),
        Real.log p * Real.log (p + 2) := by
  have hX1 : 1 ≤ X := by omega
  have hsift : (twinSieve X).siftedSum =
      ∑ p ∈ (twinPrimes X).filter (fun p => (twinPrimorial X).Coprime (p + 2)),
        Real.log (p : ℝ) := by
    change (∑ m ∈ (twinPrimes X).image (fun p => p + 2),
      if (twinPrimorial X).Coprime m then Real.log ((m - 2 : ℕ) : ℝ) else 0) = _
    rw [Finset.sum_image (by intro p _ q _ h; dsimp at h; omega)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.add_sub_cancel]
  set T := (twinPrimes X).filter (fun p => (twinPrimorial X).Coprime (p + 2))
  have hsub : T ⊆ (Finset.Ioo X (2 * X)).filter
      (fun p => 50 * p < 51 * X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p + 2).minFac) := by
    intro p hp
    obtain ⟨hpT, hcop⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi, hpr⟩ := mem_twinPrimes hpT
    have h50 : 50 * p < 51 * X := (le_twinUpper_iff hX1).mp hhi
    refine mem_filter.mpr ⟨mem_Ioo.mpr ⟨hlo, ?_⟩, h50, hpr, ?_⟩
    · have hlt := twinUpper_lt hX1
      omega
    · have hmin : (p + 2).minFac.Prime := Nat.minFac_prime (by omega)
      have hmin_dvd : (p + 2).minFac ∣ p + 2 := Nat.minFac_dvd (p + 2)
      have hmin_ne2 : (p + 2).minFac ≠ 2 := by
        intro h2
        have hmin_dvd2 := hmin_dvd
        have hdiv2 : 2 ∣ p + 2 := by rw [h2] at hmin_dvd2; exact hmin_dvd2
        have hodd : Odd p := hpr.odd_of_ne_two (by omega)
        have hmod : p % 2 = 1 := Nat.odd_iff.mp hodd
        have hmod2 : (p + 2) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv2
        omega
      have hmin5 : ¬ ((p + 2).minFac ^ 5 ≤ X) := by
        intro h5
        have hq : (p + 2).minFac ∈ twinSievingPrimes X := by
          refine mem_filter.mpr ⟨mem_range.mpr ?_, hmin, h5, hmin_ne2⟩
          have hle : (p + 2).minFac ≤ X := by
            have hstep : (p + 2).minFac ≤ (p + 2).minFac ^ 5 := by
              calc (p + 2).minFac = (p + 2).minFac ^ 1 := by simp
                _ ≤ (p + 2).minFac ^ 5 := Nat.pow_le_pow_right hmin.pos (by norm_num)
            omega
          omega
        have hdvdP : (p + 2).minFac ∣ twinPrimorial X := by
          unfold twinPrimorial
          exact Finset.dvd_prod_of_mem _ hq
        have hcop' : (p + 2).minFac.Coprime (twinPrimorial X) :=
          Nat.Coprime.of_dvd hmin_dvd dvd_rfl hcop.symm
        exact (Nat.Prime.coprime_iff_not_dvd hmin).mp hcop' hdvdP
      by_contra hlt
      have hlt' : (p + 2).minFac < Nat.nthRoot 5 X := Nat.lt_of_not_ge hlt
      have hpow : (p + 2).minFac ^ 5 ≤ Nat.nthRoot 5 X ^ 5 :=
        Nat.pow_le_pow_left hlt'.le 5
      exact hmin5 (hpow.trans (Nat.pow_nthRoot_le (Or.inl (by norm_num))))
  calc Real.log (X : ℝ) * (twinSieve X).siftedSum
      = Real.log (X : ℝ) * ∑ p ∈ T, Real.log (p : ℝ) := by rw [hsift]
    _ = ∑ p ∈ T, Real.log (X : ℝ) * Real.log (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ T, Real.log (p : ℝ) * Real.log ((p : ℝ) + 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hlo : X < p := (mem_twinPrimes (mem_filter.mp hp).1).1
        have hlogp : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        have hle : Real.log (X : ℝ) ≤ Real.log ((p : ℝ) + 2) := by
          apply Real.log_le_log
          · exact_mod_cast (by omega : 0 < X)
          · exact_mod_cast (by omega : X ≤ p + 2)
        calc Real.log (X : ℝ) * Real.log (p : ℝ)
            = Real.log (p : ℝ) * Real.log (X : ℝ) := mul_comm _ _
          _ ≤ Real.log (p : ℝ) * Real.log ((p : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left hle hlogp
    _ ≤ ∑ p ∈ (Finset.Ioo X (2 * X)).filter
          (fun p => 50 * p < 51 * X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p + 2).minFac),
          Real.log p * Real.log (p + 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i hi _
        have hlo : X < i := (mem_Ioo.mp (mem_filter.mp hi).1).1
        have h1 : 0 ≤ Real.log (i : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ i))
        have h2 : 0 ≤ Real.log ((i : ℝ) + 2) := Real.log_nonneg (by linarith)
        exact mul_nonneg h1 h2

theorem fifth_root_rough_mass :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      c * (X : ℝ) ≤ ∑ p ∈ (Finset.Ioo X (2 * X)).filter
        (fun p => 50 * p < 51 * X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p + 2).minFac),
        Real.log p * Real.log (p + 2) := by
  obtain ⟨k, hk, hRosser⟩ := twin_rosser_main
  obtain ⟨b, hb, hDen⟩ := twinDensity_invlog_lower
  obtain ⟨E, hE, hDist⟩ := twin_prime_distribution 2 (by norm_num)
  have hlogev := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (200 * E / (k * b))
  refine ⟨k * b / 200, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hRosser.and (hDist.and (hlogev.and (eventually_ge_atTop 20000))))
  refine ⟨N₁, fun X hX => ?_⟩
  obtain ⟨hR, hD2, hLG, hXbig⟩ := hN₁ X hX
  have hX1 : 1 ≤ X := by omega
  have hXpos : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlX := Real.log_pos hXpos
  have hXbigR : (20000 : ℝ) ≤ X := by exact_mod_cast hXbig
  have hMass : (X : ℝ) / 100 ≤ (twinSieve X).totalMass := by
    change (X : ℝ) / 100 ≤ ((twinUpper X : ℕ) : ℝ) - (X : ℝ)
    have hdiv : 50 * twinUpper X + (51 * X - 1) % 50 = 51 * X - 1 := by
      unfold twinUpper
      exact Nat.div_add_mod (51 * X - 1) 50
    have hmod : (51 * X - 1) % 50 < 50 := Nat.mod_lt _ (by norm_num)
    have h1 : 51 * X ≤ 50 * twinUpper X + 50 := by omega
    have h2 : 51 * (X : ℝ) ≤ 50 * ((twinUpper X : ℕ) : ℝ) + 50 := by exact_mod_cast h1
    linarith
  have hmass : k * b / 100 * (X : ℝ) / Real.log X ≤
      k * (twinSieve X).totalMass * twinDensity X := by
    have h1 : k * ((X : ℝ) / 100) ≤ k * (twinSieve X).totalMass :=
      mul_le_mul_of_nonneg_left hMass hk.le
    have h2 : b / Real.log X ≤ twinDensity X := hDen X (by omega)
    have hTM : 0 ≤ (twinSieve X).totalMass := le_trans (by positivity) hMass
    have h4 : 0 ≤ b / Real.log X := div_nonneg hb.le hlX.le
    calc k * b / 100 * (X : ℝ) / Real.log X
        = k * ((X : ℝ) / 100) * (b / Real.log X) := by ring
      _ ≤ k * (twinSieve X).totalMass * (b / Real.log X) :=
          mul_le_mul_of_nonneg_right h1 h4
      _ ≤ k * (twinSieve X).totalMass * twinDensity X :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hk.le hTM)
  let D := level X
  have hCutD : (D : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := Nat.floor_le (by positivity)
  have hErr := hD2 D (twinPrimorial X) hCutD (twinPrimorial_odd X)
  rw [Real.rpow_two] at hErr
  have hRem : (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ twinPrimorial X),
      |(twinSieve X).rem d|) ≤ E * (X : ℝ) / (Real.log X) ^ 2 := by
    refine le_trans (le_of_eq (sum_congr rfl ?_)) hErr
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hd).1).1
    rw [twinSieve_rem X d hd1]
  have hR' : k * (twinSieve X).totalMass * twinDensity X -
      (∑ d ∈ (Icc 1 D).filter (fun d => d ∣ twinPrimorial X), |(twinSieve X).rem d|) ≤
      (twinSieve X).siftedSum := hR
  have hE2 : E * (X : ℝ) / (Real.log X) ^ 2 ≤ k * b / 200 * (X : ℝ) / Real.log X := by
    have hkb : 0 < k * b := mul_pos hk hb
    have hstep : E / Real.log X ≤ k * b / 200 := by
      rw [div_le_iff₀ hlX]
      have hmul : 200 * E ≤ Real.log X * (k * b) := (div_le_iff₀ hkb).mp hLG
      calc E = 200 * E / 200 := by ring
        _ ≤ (Real.log X * (k * b)) / 200 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
        _ = k * b / 200 * Real.log X := by ring
    calc E * (X : ℝ) / (Real.log X) ^ 2
        = (E / Real.log X) * ((X : ℝ) / Real.log X) := by ring
      _ ≤ (k * b / 200) * ((X : ℝ) / Real.log X) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = k * b / 200 * (X : ℝ) / Real.log X := by ring
  have hSift : k * b / 200 * (X : ℝ) / Real.log X ≤ (twinSieve X).siftedSum := by
    have hkey : k * b / 100 * (X : ℝ) / Real.log X - E * (X : ℝ) / (Real.log X) ^ 2 =
        2 * (k * b / 200 * (X : ℝ) / Real.log X) - E * (X : ℝ) / (Real.log X) ^ 2 := by ring
    linarith
  have hT := sifted_le_target X (by omega)
  calc k * b / 200 * (X : ℝ)
      = Real.log X * (k * b / 200 * (X : ℝ) / Real.log X) := by field_simp [hlX.ne']
    _ ≤ Real.log X * (twinSieve X).siftedSum := mul_le_mul_of_nonneg_left hSift hlX.le
    _ ≤ ∑ p ∈ (Finset.Ioo X (2 * X)).filter
          (fun p => 50 * p < 51 * X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p + 2).minFac),
          Real.log p * Real.log (p + 2) := hT

end Conjectures.TwinPrimes.FifthRootRoughPrimeMass_aux

theorem Conjectures.TwinPrimes.FifthRootRoughPrimeMass :
    ∃ c : ℝ, 0<c ∧ ∃ N : ℕ, ∀ X : ℕ, N≤X → c*X ≤ ∑ p ∈ (Finset.Ioo X (2*X)).filter (fun p => 50*p<51*X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p+2).minFac), Real.log p * Real.log (p+2) :=
  Conjectures.TwinPrimes.FifthRootRoughPrimeMass_aux.fifth_root_rough_mass
