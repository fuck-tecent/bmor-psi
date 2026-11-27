import Mathlib

/-!
# QP-0089: `L-quadratic-primes-gauss-inverse-reciprocity`

For a prime `p = a² + b²` (with `0 < a ≤ b`) the root `r` of `r² ≡ -1 (mod p)` given
by `b·r ≡ a (mod p)` and the inverse `v` of `a` modulo `b` (with `v < b`) satisfy the
exact rational identity

  `r/p + v/b = j + a/(b·p)`  for some integer `j`,

i.e. `b·r + p·v - a` is a multiple of `b·p`.  Divisibility by `p` is the defining
congruence `b·r ≡ a`; divisibility by `b` follows from `p ≡ a² (mod b)` and
`a·v ≡ 1 (mod b)`; `b` and `p` are coprime because `p = a² + b²` is prime and
`b < p`.  The case `b = 1` (so `v = 0`) is included.

Self-contained, Mathlib only.
-/

open scoped BigOperators

/-- **QP-0089.** The root ratio modulo `p` is congruent to the inverse phase modulo
`b`, via an exact integer identity. -/
theorem Conjectures.QuadraticPrimes.GaussInverseReciprocity :
    ∀ a b p r v : ℕ, 0 < a → a ≤ b → p.Prime → p = a ^ 2 + b ^ 2 →
      r < p → v < b → (b * r) % p = a % p → (a * v) % b = 1 % b →
      ∃ j : ℤ, (r : ℝ) / p + (v : ℝ) / b = (j : ℝ) + (a : ℝ) / ((b : ℝ) * p) := by
  intro a b p r v ha hab hp hpab hrp hvb hbr hav
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have ha1 : 1 ≤ a := ha
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  -- `b < p`, hence `p ∤ b` and `b`, `p` are coprime
  have hb_lt_p : b < p := by
    nlinarith [hpab, ha1, hb0]
  have hpb_not : ¬ p ∣ b := by
    intro hdvd
    have : p ≤ b := Nat.le_of_dvd hb0 hdvd
    omega
  have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb_not).symm
  -- the numerator whose divisibility we prove
  set X : ℤ := (b : ℤ) * (r : ℤ) + (p : ℤ) * (v : ℤ) - (a : ℤ) with hX
  -- divisibility by `p`
  have h1p : ((b : ZMod p) * (r : ZMod p)) = (a : ZMod p) := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact hbr
  have hXp : ((X : ℤ) : ZMod p) = 0 := by
    have hrepr : ((X : ℤ) : ZMod p) =
        (b : ZMod p) * (r : ZMod p) + (p : ZMod p) * (v : ZMod p) - (a : ZMod p) := by
      rw [hX]
      push_cast
      ring
    rw [hrepr, h1p, ZMod.natCast_self p]
    ring
  -- divisibility by `b`
  have h1b : ((a : ZMod b) * (v : ZMod b)) = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' (a * v) 1 b).mpr (by simpa using hav)
  have hpb : (p : ZMod b) = (a : ZMod b) ^ 2 := by
    rw [hpab]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hXb : ((X : ℤ) : ZMod b) = 0 := by
    have hrepr : ((X : ℤ) : ZMod b) =
        (b : ZMod b) * (r : ZMod b) + (p : ZMod b) * (v : ZMod b) - (a : ZMod b) := by
      rw [hX]
      push_cast
      ring
    rw [hrepr, ZMod.natCast_self b, hpb]
    have hstep : (a : ZMod b) ^ 2 * (v : ZMod b) =
        (a : ZMod b) * ((a : ZMod b) * (v : ZMod b)) := by ring
    rw [zero_mul, zero_add, hstep, h1b]
    ring
  -- `b * p` divides `X`
  have hpdvd : (p : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X p).mp hXp
  have hbdvd : (b : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X b).mp hXb
  have hcopZ : IsCoprime (b : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact hcop
  obtain ⟨j, hj⟩ := hcopZ.mul_dvd hbdvd hpdvd
  refine ⟨j, ?_⟩
  -- cast `X = (b*p) * j` to `ℝ` and rearrange
  have hcast : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) - (a : ℝ) =
      ((b : ℝ) * (p : ℝ)) * (j : ℝ) := by
    have hXR : (X : ℝ) = (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) - (a : ℝ) := by
      rw [hX]
      push_cast
      ring
    have hjR : (X : ℝ) = ((b : ℝ) * (p : ℝ)) * (j : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) hj
      push_cast at this
      exact this
    rw [← hXR, hjR]
  have hbp0 : ((b : ℝ) * (p : ℝ)) ≠ 0 := by positivity
  have hb0R : (b : ℝ) ≠ 0 := by positivity
  have hp0R : (p : ℝ) ≠ 0 := by positivity
  have hkey : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) =
      (j : ℝ) * ((b : ℝ) * (p : ℝ)) + (a : ℝ) := by
    linarith [hcast]
  field_simp
  linarith [hkey]

