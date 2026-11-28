import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4

set_option maxHeartbeats 4000000

open Finset MeasureTheory
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand

noncomputable section

namespace B1B1L2

/-!
# The `L²` mass of the far prime-cofactor part of `τ₁^Top`

This file isolates the **negative** result: the far prime-cofactor object has `L²` mass
`Θ(n)`, so no `L²`/Parseval/absolute-value argument can produce `o(n)`.

The point is that the cross terms *vanish identically*: a prime cofactor `p > B₁` cannot
divide another divisor `a' ≤ B₁`, so `a·p = a'·q` forces `a = a'` and `p = q`.  Hence the
`L²` mass is **exactly** the diagonal

```text
∫₀¹ ‖∑_a c(a)·W_a‖²  =  ∑_a c(a)² · ∑_{B₁<p≤n/a} (log p)² ,
```

with no cancellation available.
-/

/-- The far prime-cofactor wave: primes `p ∈ (B, n/a]`. -/
def farPrimeWave (n B a : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc (B + 1) (n / a)).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * phase ((a * p : ℕ) * t)

/-- The far prime-cofactor polynomial. -/
def sepPolynomial (n B : ℕ) (t : ℝ) : ℂ :=
  ∑ a ∈ Finset.Icc (cutoffU n + 1) (lowCut n),
    (lowMoebiusWeight (cutoffU n) a : ℂ) * farPrimeWave n B a t

/-- **No cross terms.**  If `a, a' ≤ B` and `p, q > B` are primes with `a·p = a'·q`, then
`a = a'` and `p = q`. -/
theorem prime_mul_eq_of_large {B p q a a' : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha'pos : 1 ≤ a') (ha' : a' ≤ B) (hpB : B < p) (h : a * p = a' * q) :
    a = a' ∧ p = q := by
  have hpdvd : p ∣ a' * q := ⟨a, by rw [← h, Nat.mul_comm]⟩
  have hpnot : ¬ p ∣ a' := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hpq : p = q := by
    rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h' | h'
    · exact absurd h' hpnot
    · rcases hq.eq_one_or_self_of_dvd p h' with h1 | h1
      · exact absurd h1 hp.ne_one
      · exact h1
  subst hpq
  refine ⟨?_, rfl⟩
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < p) h

/-- Orthogonality of the modes on the unit interval. -/
theorem integral_phase_int_local (k : ℤ) :
    (∫ t in (0:ℝ)..1, phase ((k:ℝ)*t)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [phase]
  · have hc : ((2*Real.pi*Complex.I) * (k:ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · exact_mod_cast hk
    rw [if_neg hk]
    have hcongr : ∀ t : ℝ,
        phase ((k:ℝ)*t) = Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * (t:ℂ)) := by
      intro t
      unfold phase
      congr 1
      push_cast
      ring
    simp_rw [hcongr]
    rw [integral_exp_mul_complex hc]
    have htop : Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * ((1:ℝ):ℂ)) = 1 := by
      rw [show ((2*Real.pi*Complex.I) * (k:ℂ)) * ((1:ℝ):ℂ)
          = (k:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    have hbot : Complex.exp (((2*Real.pi*Complex.I) * (k:ℂ)) * ((0:ℝ):ℂ)) = 1 := by simp
    rw [htop, hbot, sub_self, zero_div]

/-- Conjugation reverses the sign of the phase. -/
theorem conj_phase (x : ℝ) : (starRingEnd ℂ) (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  simp [Complex.conj_I]
  try ring

/-- `∫₀¹ phase(m t)·conj(phase(k t)) dt = if m = k then 1 else 0`. -/
theorem integral_phase_mul_conj (m k : ℕ) :
    (∫ t in (0:ℝ)..1, phase ((m:ℝ)*t) * (starRingEnd ℂ) (phase ((k:ℝ)*t)))
      = if m = k then (1:ℂ) else 0 := by
  have hpt : ∀ t : ℝ, phase ((m:ℝ)*t) * (starRingEnd ℂ) (phase ((k:ℝ)*t))
      = phase (((((m:ℤ) - (k:ℤ) : ℤ)) : ℝ) * t) := by
    intro t
    rw [conj_phase, ← phase_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_phase_int_local ((m:ℤ) - (k:ℤ))]
  by_cases h : m = k
  · rw [if_pos h, if_pos (by omega : (m:ℤ) - (k:ℤ) = 0)]
  · rw [if_neg h, if_neg (by omega : ¬ ((m:ℤ) - (k:ℤ) = 0))]

end B1B1L2
