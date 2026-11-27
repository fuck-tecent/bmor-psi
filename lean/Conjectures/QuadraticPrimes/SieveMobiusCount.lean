import Mathlib

/-!
# Möbius expansion of the quadratic sieve survivors

For the quadratic value `f k = 4 * k^2 + 1`, the window `block x = Finset.Ioc (x/2) x`, and the
squarefree wheel `wheel z = ∏ p ∈ (Finset.Icc 3 z).filter Nat.Prime, p`, the count of window points
`k` with `Nat.Coprime (f k) (wheel z)` is expanded by Möbius inversion over the divisors of the
wheel.  The proof is pointwise: at each `k` the divisor sum collapses to the indicator of
`gcd (f k) (wheel z) = 1`, and then the divisor and window sums are exchanged.
-/

namespace Conjectures.QuadraticPrimes.SieveMobiusCount_aux

/-- The Möbius function sums to `1` on `1` and to `0` on every other divisor set. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then (1 : ℤ) else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- Divisors of `W` that also divide `m` are exactly the divisors of `gcd m W`. -/
lemma filter_divisors_gcd (W m : ℕ) (hW : W ≠ 0) :
    W.divisors.filter (fun d => d ∣ m) = (Nat.gcd m W).divisors := by
  rw [← Nat.divisors_filter_dvd_of_dvd hW (Nat.gcd_dvd_right m W)]
  refine Finset.filter_congr fun d hd => ?_
  have hdW : d ∣ W := (Nat.mem_divisors.mp hd).1
  constructor
  · intro h
    exact Nat.dvd_gcd h hdW
  · intro h
    exact dvd_trans h (Nat.gcd_dvd_left m W)

/-- Pointwise Möbius expansion of the coprimality indicator against a wheel. -/
lemma key (W m : ℕ) (hW : W ≠ 0) :
    ∑ d ∈ W.divisors, ArithmeticFunction.moebius d * (if d ∣ m then (1 : ℤ) else 0)
      = if Nat.Coprime m W then 1 else 0 := by
  have h1 : ∑ d ∈ W.divisors, ArithmeticFunction.moebius d * (if d ∣ m then (1 : ℤ) else 0)
      = ∑ d ∈ W.divisors.filter (fun d => d ∣ m), ArithmeticFunction.moebius d := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun d _ => by by_cases h : d ∣ m <;> simp [h]
  rw [h1, filter_divisors_gcd W m hW, sum_moebius_divisors]

/-- The Möbius expansion for an arbitrary function, window and nonzero wheel. -/
lemma main (f : ℕ → ℕ) (B : Finset ℕ) (W : ℕ) (hW : W ≠ 0) :
    (((B.filter (fun k => Nat.Coprime (f k) W)).card : ℕ) : ℤ)
      = ∑ d ∈ W.divisors, ArithmeticFunction.moebius d *
          ((((B.filter (fun k => d ∣ f k)).card : ℕ) : ℤ)) := by
  have hL : (((B.filter (fun k => Nat.Coprime (f k) W)).card : ℕ) : ℤ)
      = ∑ k ∈ B, (if Nat.Coprime (f k) W then (1 : ℤ) else 0) :=
    Finset.natCast_card_filter _ _
  have hR : ∀ d : ℕ, (((B.filter (fun k => d ∣ f k)).card : ℕ) : ℤ)
      = ∑ k ∈ B, (if d ∣ f k then (1 : ℤ) else 0) := fun d => Finset.natCast_card_filter _ _
  rw [hL]
  simp_rw [hR, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (key W (f k) hW).symm

/-- The wheel is a product of primes at least `3`, hence never zero (it is `1` for `z ≤ 2`). -/
lemma wheel_ne_zero (z : ℕ) :
    (∏ p ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p), p) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  have h1 := (Finset.mem_filter.mp hp).1
  have h2 := (Finset.mem_Icc.mp h1).1
  omega

end Conjectures.QuadraticPrimes.SieveMobiusCount_aux

theorem Conjectures.QuadraticPrimes.SieveMobiusCount :
let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); let hitCount := fun x d : ℕ => ((block x).filter (fun k => d ∣ f k)).card;
∀ x z : ℕ, ((rough x z).card : ℤ) = ∑ d ∈ (wheel z).divisors, ArithmeticFunction.moebius d * (hitCount x d : ℤ) := by
  intro f block primes wheel rough hitCount x z
  exact Conjectures.QuadraticPrimes.SieveMobiusCount_aux.main f (block x) (wheel z)
    (Conjectures.QuadraticPrimes.SieveMobiusCount_aux.wheel_ne_zero z)
