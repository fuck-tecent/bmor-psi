import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_finite_weighted_liouville_selector :
    ∀ (S : Finset ℕ) (n : ℕ) (w : ℕ → ℝ), (∀ p ∈ S, 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 2) → (∑ p ∈ S, w p) - (∑ p ∈ S, w p*(-1:ℝ)^(n-p).primeFactorsList.length) = 2*(∑ p ∈ S.filter (fun p => Nat.Prime (n-p)), w p) := by
  intro S n w hS
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hm, hlen⟩ := hS p hp
  by_cases hprime : Nat.Prime (n-p)
  · simp [hprime, Nat.primeFactorsList_prime hprime]
    ring
  · have hne : (n-p).primeFactorsList ≠ [] :=
      (Nat.primeFactorsList_ne_nil _).2 (by omega)
    have hpos := List.length_pos_iff.mpr hne
    have hnotone : (n-p).primeFactorsList.length ≠ 1 := by
      intro he
      obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp he
      have hprod := Nat.prod_primeFactorsList (n := n-p) (by omega)
      rw [hq, List.prod_singleton] at hprod
      have hmem : q ∈ (n-p).primeFactorsList := by simp [hq]
      exact hprime (hprod ▸ Nat.prime_of_mem_primeFactorsList hmem)
    have htwo : (n-p).primeFactorsList.length = 2 := by omega
    simp [hprime, htwo]
