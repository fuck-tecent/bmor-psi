import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset ArithmeticFunction

namespace GoldbachRoughFifth

private theorem min_pow_le_prod (a : ℕ) (xs : List ℕ) (h : ∀ p ∈ xs, a ≤ p) :
    a ^ xs.length ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    have hb : a ≤ b := h b (by simp)
    have htail := ih (fun p hp => h p (by simp [hp]))
    simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul htail hb

private theorem four_factors {N m : ℕ} (hm : 1 < m) (hmN : m ≤ N)
    (hz : N < m.minFac^5) : cardFactors m ≤ 4 := by
  have hlist := min_pow_le_prod m.minFac m.primeFactorsList (fun p hp =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hp).two_le
      (Nat.dvd_of_mem_primeFactorsList hp))
  rw [Nat.prod_primeFactorsList (by omega : m ≠ 0)] at hlist
  by_contra! hlarge
  have hf : 5 ≤ m.primeFactorsList.length := by
    rw [cardFactors_apply] at hlarge
    omega
  have hpow := Nat.pow_le_pow_right (Nat.minFac_pos m) hf
  omega

private theorem prime_minus_triples {m : ℕ} (hm : 1 < m) (h4 : cardFactors m ≤ 4) :
    2 * (if m.Prime then (1 : ℝ) else 0) =
      1 - (liouville m : ℝ) - 2*(if cardFactors m = 3 then 1 else 0) := by
  have hpos := cardFactors_pos_iff_one_lt.mpr hm
  simp only [liouville_apply (by omega : m ≠ 0), ← cardFactors_eq_one_iff_prime]
  have hcases : cardFactors m = 1 ∨ cardFactors m = 2 ∨ cardFactors m = 3 ∨ cardFactors m = 4 := by omega
  rcases hcases with h|h|h|h <;> norm_num [h]

end GoldbachRoughFifth

theorem PEqualNP.Outside.L_goldbach_rough_fifth_bridge :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∀ N : ℕ, 2*(((C N).filter (fun p => Nat.Prime (N-p))).card:ℝ) = ((C N).card:ℝ) - (C N).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) - 2*(((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card:ℝ) := by
  dsimp only
  intro N
  let C := (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
  have hp (p : ℕ) (hp : p ∈ C) := (mem_filter.mp hp).2
  have ht (p : ℕ) (hp' : p ∈ C) := GoldbachRoughFifth.prime_minus_triples (hp p hp').2.2.2.1
    (GoldbachRoughFifth.four_factors (hp p hp').2.2.2.1 (Nat.sub_le N p) (hp p hp').2.2.2.2)
  have h := Finset.sum_congr (s₁ := C) rfl ht
  simpa only [sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_univ, nsmul_eq_mul, mul_one] using h
