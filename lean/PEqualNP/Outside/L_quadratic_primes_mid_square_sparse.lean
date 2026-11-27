import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace QuadraticPrimeSquareSpacing

private theorem three_does_not_divide (n : ℕ) : ¬ 3 ∣ n ^ 2 + 1 := by
  intro h
  have hmod := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod, Nat.pow_mod] at hmod
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with h | h | h <;> norm_num [h] at hmod

private theorem twice_square {n p : ℕ} (hn : 0 < n) (hlt : n < 2 * p)
    (hd : p ^ 2 ∣ n ^ 2 + 1) : n ^ 2 + 1 = 2 * p ^ 2 := by
  obtain ⟨k, hk⟩ := hd
  have hsmall : n ^ 2 + 1 < 4 * p ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self (show n+1 ≤ 2*p by omega)]
  have hfour : k < 4 := by
    by_contra! h
    nlinarith [Nat.mul_le_mul_left (p^2) h]
  interval_cases k
  · simp at hk
  · simp only [Nat.mul_one] at hk
    by_cases h : n < p
    · nlinarith [Nat.mul_self_le_mul_self (show n+1 ≤ p by omega)]
    · nlinarith [Nat.mul_self_le_mul_self (show p ≤ n by omega)]
  · simpa only [Nat.mul_comm] using hk
  · exact (three_does_not_divide n ⟨p^2, by simpa only [Nat.mul_comm] using hk⟩).elim

/-- A positive integral cross product separates distinct solutions in one dyadic window. -/
private theorem exclude_larger {a b p q : ℕ} (hab : a < b) (hba : b ≤ 2*a)
    (hbq : b ≤ 2*q) (ha : a^2+1 = 2*p^2) (hb : b^2+1 = 2*q^2) : False := by
  have e : 2*(b*p)^2 + a^2 = 2*(a*q)^2 + b^2 := by
    linear_combination a^2 * hb - b^2 * ha
  have hcross : a*q < b*p := by
    by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h, Nat.mul_self_lt_mul_self hab]
  have hstep : a*q+1 ≤ b*p := by omega
  nlinarith [Nat.mul_self_le_mul_self hstep, Nat.mul_le_mul_left b hba,
    Nat.mul_le_mul_left a hbq]

end QuadraticPrimeSquareSpacing

theorem PEqualNP.Outside.L_quadratic_primes_mid_square_sparse :
    ∀ x:ℕ, ((Finset.Ioc x (2*x)).filter (fun n =>
      ((n^2+1).primeFactors.filter (fun p => x<p ∧ p^2∣n^2+1)).Nonempty)).card≤1 := by
  intro x
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, p, hp⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, q, hq⟩ := Finset.mem_filter.mp hb
  obtain ⟨hxa, hax⟩ := Finset.mem_Ioc.mp ha
  obtain ⟨hxb, hbx⟩ := Finset.mem_Ioc.mp hb
  obtain ⟨_, hxp, hpa⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hxq, hqb⟩ := Finset.mem_filter.mp hq
  have ea := QuadraticPrimeSquareSpacing.twice_square (by omega : 0 < a)
    (by omega : a < 2*p) hpa
  have eb := QuadraticPrimeSquareSpacing.twice_square (by omega : 0 < b)
    (by omega : b < 2*q) hqb
  rcases lt_trichotomy a b with h | h | h
  · exact (QuadraticPrimeSquareSpacing.exclude_larger h (by omega) (by omega) ea eb).elim
  · exact h
  · exact (QuadraticPrimeSquareSpacing.exclude_larger h (by omega) (by omega) eb ea).elim
