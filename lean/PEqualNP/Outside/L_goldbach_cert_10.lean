import Mathlib

/-- Ramanujan sum over the units modulo `10`: for any `ω` that is a primitive `10`-th root of unity
(in practice `ω = exp (2πia/10)` with `gcd a 10 = 1`), the sum of `ω ^ b` over the unit classes
`b ∈ {1,3,7,9}` equals `μ(10) = 1`.

The proof is the Möbius identity in disguise: `x ^ 5 + 1 = (x + 1) * Φ₁₀(x)` with
`Φ₁₀(x) = x ^ 4 - x ^ 3 + x ^ 2 - x + 1`, so a primitive root satisfies `Φ₁₀(ω) = 0`, and using
`ω ^ 5 = -1` the four unit powers collapse to `-(ω ^ 4 - ω ^ 3 + ω ^ 2 - ω) = 1`. -/
private lemma goldbach_cert_10_units (ω : ℂ) (h2 : ω ^ 2 ≠ 1) (h5 : ω ^ 5 = -1) :
    ∑ b ∈ (Finset.range 10).filter (fun b => Nat.Coprime b 10), ω ^ b = 1 := by
  -- The unit classes modulo `10` are `{1, 3, 7, 9}` (`φ(10) = 4`).
  have hset : (Finset.range 10).filter (fun b => Nat.Coprime b 10) = {1, 3, 7, 9} := by
    decide
  rw [hset]
  have h4 : ∑ b ∈ ({1, 3, 7, 9} : Finset ℕ), ω ^ b = ω + ω ^ 3 + ω ^ 7 + ω ^ 9 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [h4]
  -- `ω ^ 5 = -1` lets us write the tail powers in terms of the first ones.
  have h7 : ω ^ 7 = -ω ^ 2 := by
    rw [show (7 : ℕ) = 2 + 5 by norm_num, pow_add, h5]
    ring
  have h9 : ω ^ 9 = -ω ^ 4 := by
    rw [show (9 : ℕ) = 4 + 5 by norm_num, pow_add, h5]
    ring
  -- `ω` is a root of `x ^ 5 + 1 = (x + 1) * Φ₁₀(x)`, and `ω ≠ -1`.
  have hphi : ω ^ 4 - ω ^ 3 + ω ^ 2 - ω + 1 = 0 := by
    have hfac : (ω + 1) * (ω ^ 4 - ω ^ 3 + ω ^ 2 - ω + 1) = 0 := by
      linear_combination h5
    have hne : ω + 1 ≠ 0 := by
      intro h
      apply h2
      rw [show ω = -1 from by linear_combination h]
      ring
    exact (mul_eq_zero.mp hfac).resolve_left hne
  rw [h7, h9]
  linear_combination -hphi

theorem PEqualNP.Outside.L_goldbach_cert_10 :
    ∀ a:ℕ, Nat.Coprime a 10 → (∑ b ∈ (Finset.range 10).filter (fun b => Nat.Coprime b 10), Complex.exp (((2*Real.pi*(a:ℝ)*b/10:ℝ):ℂ)*Complex.I))/(4:ℂ)=(1:ℂ)/4 := by
  intro a ha
  -- `ω = exp (2πia/10)` is a primitive `10`-th root of unity, since `gcd a 10 = 1`.
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 10)) with hωdef
  have hω : IsPrimitiveRoot ω 10 := by
    rw [hωdef]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 10 (by norm_num) ha
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have hdvd : (10 : ℕ) ∣ 2 := (hω.pow_eq_one_iff_dvd 2).mp h
    norm_num at hdvd
  have hω5 : ω ^ 5 = -1 := by
    have h10 : ω ^ 10 = 1 := hω.pow_eq_one
    have hne : ω ^ 5 ≠ 1 := by
      intro h
      have hdvd : (10 : ℕ) ∣ 5 := (hω.pow_eq_one_iff_dvd 5).mp h
      norm_num at hdvd
    have hfac : (ω ^ 5 - 1) * (ω ^ 5 + 1) = 0 := by
      linear_combination h10
    have : ω ^ 5 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination this
  -- Each summand is a power of `ω`: the frequency numerator `a` stays arbitrary.
  have hterm : ∀ b : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 10 : ℝ) : ℂ) * Complex.I) = ω ^ b := by
    intro b
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [goldbach_cert_10_units ω hω2 hω5]
