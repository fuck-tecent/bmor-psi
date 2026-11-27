import Mathlib

open Finset

/-!
# Total squarefree root weight up to the sieve level

The number of squarefree root choices attached to a modulus `d` is `2 ^ ω(d)`,
where `ω(d) = d.primeFactors.card`.  We dominate it by the divisor count
`τ(d) = d.divisors.card`, exchange the divisor and the multiple sums, and
finish with the harmonic bound `H_D ≤ 1 + log D`.
-/

private lemma two_pow_card_primeFactors_le_card_divisors (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors hn0]
  have h2 : (2 : ℕ) ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, (2 : ℕ) :=
    (Finset.prod_const 2).symm
  rw [h2]
  refine Finset.prod_le_prod ?_
  intro p hp
  have hp1 : 1 ≤ n.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization (Nat.prime_of_mem_primeFactors hp) hn0).mp
      (Nat.dvd_of_mem_primeFactors hp)
  omega

private lemma icc_one_eq_ioc_zero (D : ℕ) : Finset.Icc 1 D = Finset.Ioc 0 D :=
  Finset.Icc_succ_left_eq_Ioc 0 D

private lemma icc_one_filter_dvd_card (D e : ℕ) :
    ((Finset.Icc 1 D).filter (e ∣ ·)).card = D / e := by
  rw [icc_one_eq_ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]

private lemma divisor_indicator (D d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
    (d.divisors.card : ℝ) = ∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
  have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
  have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
  have hset : (Finset.Icc 1 D).filter (· ∣ d) = d.divisors := by
    ext e
    constructor
    · intro he
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hd0⟩
    · intro he
      have hed : e ∣ d := (Nat.mem_divisors.mp he).1
      have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hed (by omega)
      have heD : e ≤ D := (Nat.le_of_dvd (by omega) hed).trans hdD
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he1, heD⟩, hed⟩
  have hsum : (∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0))
      = (((Finset.Icc 1 D).filter (· ∣ d)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum, hset]

private lemma harmonic_cast_eq_sum (D : ℕ) :
    (harmonic D : ℝ) = ∑ e ∈ Finset.Icc 1 D, ((e : ℝ))⁻¹ := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp

private lemma sum_card_divisors_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ)) ≤ (D : ℝ) * (harmonic D : ℝ) := by
  calc (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ))
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact divisor_indicator D d hd
    _ = ∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ e ∈ Finset.Icc 1 D, ((D / e : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro e _
        have hinner : (∑ d ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0))
            = (((Finset.Icc 1 D).filter (e ∣ ·)).card : ℝ) := by
          rw [← Finset.sum_filter]
          simp
        rw [hinner, icc_one_filter_dvd_card]
    _ ≤ ∑ e ∈ Finset.Icc 1 D, (D : ℝ) / e := by
        apply Finset.sum_le_sum
        intro e _
        exact Nat.cast_div_le
    _ = (D : ℝ) * ∑ e ∈ Finset.Icc 1 D, ((e : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        field_simp
    _ = (D : ℝ) * (harmonic D : ℝ) := by rw [harmonic_cast_eq_sum]

theorem Conjectures.Goldbach.FareySieveRootTotal :
    ∀ D : ℕ, 1 ≤ D → (∑ d ∈ Finset.Icc 1 D, (2:ℝ)^d.primeFactors.card) ≤ (D:ℝ)*(1+Real.log D) := by
  intro D _
  have h1 : ∀ d ∈ Finset.Icc 1 D, (2 : ℝ) ^ d.primeFactors.card ≤ (d.divisors.card : ℝ) := by
    intro d hd
    have hnat := two_pow_card_primeFactors_le_card_divisors d (Finset.mem_Icc.mp hd).1
    exact_mod_cast hnat
  calc (∑ d ∈ Finset.Icc 1 D, (2 : ℝ) ^ d.primeFactors.card)
      ≤ ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) := Finset.sum_le_sum h1
    _ ≤ (D : ℝ) * (harmonic D : ℝ) := sum_card_divisors_le D
    _ ≤ (D : ℝ) * (1 + Real.log D) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Nat.cast_nonneg D)
