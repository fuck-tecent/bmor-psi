import Mathlib

namespace TwinParityMass

open ArithmeticFunction Finset

def isPair (n d : ℕ) : Prop := d.Prime ∧ (n / d).Prime ∧ d ≠ n / d

instance (n d : ℕ) : Decidable (isPair n d) := inferInstanceAs
  (Decidable (d.Prime ∧ (n / d).Prime ∧ d ≠ n / d))

noncomputable def pairMass (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors with isPair n d, Real.log (d : ℝ) * Real.log ((n / d : ℕ) : ℝ)

private theorem pair_factors {n d : ℕ} (hd : d ∈ n.divisors) (h : isPair n d) :
    Squarefree n ∧ ¬n.Prime ∧ moebius n = 1 := by
  obtain ⟨hp, hq, hne⟩ := h
  have hProd : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have hCop : d.Coprime (n / d) := (Nat.coprime_primes hp hq).mpr hne
  refine ⟨?_, ?_, ?_⟩
  · rw [← hProd]
    exact (Nat.squarefree_mul hCop).mpr ⟨hp.squarefree, hq.squarefree⟩
  · rw [← hProd]
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  · rw [← hProd, isMultiplicative_moebius.map_mul_of_coprime hCop,
      moebius_apply_prime hp, moebius_apply_prime hq]
    norm_num

private theorem mangoldt_of_squarefree {n : ℕ} (hn : Squarefree n) :
    vonMangoldt n = if n.Prime then Real.log (n : ℝ) else 0 := by
  split_ifs with h
  · exact vonMangoldt_apply_prime h
  · exact vonMangoldt_eq_zero_iff.mpr (fun hp =>
      h (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, hp⟩))

private theorem convolution_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)) = pairMass n := by
  rw [pairMass, sum_filter]
  apply sum_congr rfl
  intro d hd
  have hDvd := Nat.dvd_of_mem_divisors hd
  have hDiv := Nat.mul_div_cancel' hDvd
  have hCop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (hDiv.symm ▸ hn)
  rw [mangoldt_of_squarefree (hn.squarefree_of_dvd hDvd),
    mangoldt_of_squarefree (hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hDvd))]
  by_cases hp : d.Prime <;> by_cases hq : (n / d).Prime
  · have hNe := (Nat.coprime_primes hp hq).mp hCop
    simp [isPair, hp, hq, hNe]
  · simp [isPair, hp, hq]
  · simp [isPair, hp, hq]
  · simp [isPair, hp, hq]

private theorem pair_mass_zero {n : ℕ} (h : ¬∃ d ∈ n.divisors, isPair n d) : pairMass n = 0 := by
  apply sum_eq_zero
  intro d hd
  obtain ⟨hdDiv, hdPair⟩ := mem_filter.mp hd
  exact (h ⟨d, hdDiv, hdPair⟩).elim

/-- The signed second Selberg weight is positive only on distinct prime
products and negative only on primes. The divisor sum counts ordered factors. -/
theorem signed_selberg_second (n : ℕ) :
    (moebius n : ℝ) * (vonMangoldt n * Real.log (n : ℝ) +
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)) =
      pairMass n - (if n.Prime then (Real.log (n : ℝ))^2 else 0) := by
  by_cases hPair : ∃ d ∈ n.divisors, isPair n d
  · obtain ⟨d, hd, hFactors⟩ := hPair
    obtain ⟨hSquarefree, hComposite, hMu⟩ := pair_factors hd hFactors
    rw [hMu, convolution_of_squarefree hSquarefree, mangoldt_of_squarefree hSquarefree,
      ite_eq_right hComposite, ite_eq_right hComposite]
    norm_num
  · have hZero := pair_mass_zero hPair
    by_cases hPrime : n.Prime
    · rw [hZero, ite_eq_left hPrime, convolution_of_squarefree hPrime.squarefree, hZero,
        moebius_apply_prime hPrime, vonMangoldt_apply_prime hPrime]
      push_cast
      ring
    · rw [hZero, ite_eq_right hPrime]
      by_cases hSquarefree : Squarefree n
      · rw [convolution_of_squarefree hSquarefree, mangoldt_of_squarefree hSquarefree, hZero,
          ite_eq_right hPrime]
        ring
      · rw [moebius_eq_zero_of_not_squarefree hSquarefree]
        norm_num

end TwinParityMass

theorem Conjectures.Cuts.Taskbb9b333fa3b5413980f0305e : ∀ (x1 : ℕ), ↑(ArithmeticFunction.moebius x1) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) = ∑ x2 ∈ x1.divisors with Nat.Prime x2 ∧ Nat.Prime (x1 / x2) ∧ x2 ≠ x1 / x2, Real.log ↑x2 * Real.log ↑(x1 / x2) - if Nat.Prime x1 then Real.log ↑x1 ^ (2 : ℕ) else (0 : ℝ) := by
  intro n
  have hFilter : n.divisors.filter (TwinParityMass.isPair n) = n.divisors.filter
      (fun p => p.Prime ∧ (n / p).Prime ∧ p ≠ n / p) := by
    ext p
    simp only [Finset.mem_filter, TwinParityMass.isPair]
  have h := TwinParityMass.signed_selberg_second n
  unfold TwinParityMass.pairMass at h
  rw [hFilter] at h
  exact h
