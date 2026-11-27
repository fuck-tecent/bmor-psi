import Mathlib

/-!
# FR-9023: the weighted sieve sum as first and square divisibility counts

`W z y s` is the weight `2 - #{q ∈ P : q ∣ s} - #{q ∈ P : q² ∣ s}` on the prime block
`P = (Ico z y).filter Nat.Prime`, and `A n z` is the sieve base set of primes `p ≤ n` with
`p ∤ n` and no prime `q < z` dividing `n - p`.  The lemma does two things on the common base
set `A0 = {p ∈ A n z | 2 ≤ n - p}`:

* it rewrites `∑ p ∈ A0, W z y (n - p)` as `2 * |A0|` minus the two counting sums
  `∑ q ∈ P, #{p ∈ A0 | q ∣ n - p}` and `∑ q ∈ P, #{p ∈ A0 | q² ∣ n - p}`, by exchanging the
  two finite sums;
* it shows that a sieve prime `q ∈ P` dividing `n` contributes nothing: from `q ∣ n` and
  `q ∣ n - p` (with `p ≤ n`) we get `q ∣ p`, primality of `p` and `q` forces `p = q`, which
  contradicts `p ∤ n`.

The hypotheses `4 ≤ n`, `2 < z`, `z < y` are not needed by the argument; the proof is pure
finite combinatorics over `Finset`.
-/

namespace Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion_aux

/-- Casting the cardinality of a filtered finset to `ℤ` turns it into a counting sum. -/
lemma card_filter_cast (U : Finset ℕ) (φ : ℕ → Prop) [DecidablePred φ] :
    ((U.filter φ).card : ℤ) = ∑ x ∈ U, if φ x then (1:ℤ) else 0 := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp

/-- Exchanging the two finite sums: counting `q ∈ T` with `g q ∣ n - p` over `p ∈ S` is the
same as counting `p ∈ S` with `g q ∣ n - p` over `q ∈ T`. -/
lemma sum_swap_sub (S T : Finset ℕ) (n : ℕ) (g : ℕ → ℕ) :
    (∑ p ∈ S, ((T.filter (fun q => g q ∣ n - p)).card : ℤ))
      = ∑ q ∈ T, ((S.filter (fun p => g q ∣ n - p)).card : ℤ) := by
  have hL : (∑ p ∈ S, ((T.filter (fun q => g q ∣ n - p)).card : ℤ))
      = ∑ p ∈ S, ∑ q ∈ T, if g q ∣ n - p then (1:ℤ) else 0 :=
    Finset.sum_congr rfl (fun p _ => card_filter_cast _ _)
  have hR : (∑ q ∈ T, ((S.filter (fun p => g q ∣ n - p)).card : ℤ))
      = ∑ q ∈ T, ∑ p ∈ S, if g q ∣ n - p then (1:ℤ) else 0 :=
    Finset.sum_congr rfl (fun q _ => card_filter_cast _ _)
  rw [hL, hR, Finset.sum_comm]

/-- The constant part of the weight sums to `2 * |S|`. -/
lemma sum_two_card (S : Finset ℕ) : (∑ _p ∈ S, (2:ℤ)) = 2 * (S.card : ℤ) := by
  have h : (∑ _p ∈ S, (2:ℤ)) = (S.card : ℤ) * 2 := by simp [Finset.sum_const]
  rw [h, mul_comm]

/-- The weighted sieve sum without remainder one, in terms of the two counting sums. -/
lemma weighted_sum (n : ℕ) (A0 P : Finset ℕ) :
    (∑ p ∈ A0, ((2:ℤ) - ((P.filter (fun q => q ∣ n - p)).card : ℤ)
        - ((P.filter (fun q => q ^ 2 ∣ n - p)).card : ℤ)))
      = (2:ℤ) * (A0.card : ℤ) - (∑ q ∈ P, ((A0.filter (fun p => q ∣ n - p)).card : ℤ))
        - (∑ q ∈ P, ((A0.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_two_card,
    sum_swap_sub A0 P n (fun q => q), sum_swap_sub A0 P n (fun q => q ^ 2)]

end Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion_aux

open Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion_aux

theorem Conjectures.Goldbach.FiniteWeightedSieveSupportedRegion :
    let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ (n z y : ℕ), 4≤n → 2<z → z<y → let A0 := Finset.filter (fun p => 2≤n-p) (A n z); let P := (Finset.Ico z y).filter Nat.Prime; (∑ p ∈ A0, W z y (n-p)) = (2:ℤ)*(A0.card:ℤ) - (∑ q ∈ P, ((Finset.filter (fun p => q ∣ n-p) A0).card:ℤ)) - (∑ q ∈ P, ((Finset.filter (fun p => q^2 ∣ n-p) A0).card:ℤ)) ∧ (∀ q ∈ P, q ∣ n → (Finset.filter (fun p => q ∣ n-p) A0) = ∅) := by
  intro W A n z y _hn _hz _hy A0 P
  refine ⟨?_, ?_⟩
  · show (∑ p ∈ A0, ((2:ℤ) - ((P.filter (fun q => q ∣ n - p)).card : ℤ)
        - ((P.filter (fun q => q ^ 2 ∣ n - p)).card : ℤ)))
      = (2:ℤ) * (A0.card : ℤ) - (∑ q ∈ P, ((A0.filter (fun p => q ∣ n - p)).card : ℤ))
        - (∑ q ∈ P, ((A0.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ))
    exact weighted_sum n A0 P
  · intro q hq hqn
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have key : ∀ p ∈ A0, ¬ (q ∣ n - p) := by
      intro p hp hqp
      have hpA : p ∈ A n z := (Finset.mem_filter.mp hp).1
      have hpA' : p ∈ (Finset.range (n + 1)).filter
          (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter
            (fun q => Nat.Prime q ∧ q ∣ (n - p))) = ∅) := hpA
      obtain ⟨hprange, hprime, hndvd, _⟩ := Finset.mem_filter.mp hpA'
      have hple : p ≤ n := by
        have h := Finset.mem_range.mp hprange
        omega
      have hqdivp : q ∣ p := (Nat.dvd_sub_iff_right hple hqn).mp hqp
      have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hprime).mp hqdivp
      have hpdvd : p ∣ n := by
        rw [← hqeq]
        exact hqn
      exact hndvd hpdvd
    exact Finset.filter_eq_empty_iff.mpr key
