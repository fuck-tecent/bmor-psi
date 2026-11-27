import Mathlib

/-- Sum of powers of a primitive `14`-th root of unity over the residue classes coprime to `14`.
The classes are `{1, 3, 5, 9, 11, 13}`. From `ω ^ 7 = -1` and `ω ^ 2 ≠ 1`,
`ω` is a root of `X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1`, and the six powers sum to `1`.
There are six such classes, so dividing the sum by `6` yields `1 / 6`. -/
private lemma goldbach_cert_14_units (ω : ℂ) (h2 : ω ^ 2 ≠ 1) (h7 : ω ^ 7 = -1) :
    ∑ b ∈ (Finset.range 14).filter (fun b => Nat.Coprime b 14), ω ^ b = 1 := by
  have hset : (Finset.range 14).filter (fun b => Nat.Coprime b 14) = {1, 3, 5, 9, 11, 13} := by
    decide
  rw [hset]
  have hsum : ∑ b ∈ ({1, 3, 5, 9, 11, 13} : Finset ℕ), ω ^ b =
      ω + ω ^ 3 + ω ^ 5 + ω ^ 9 + ω ^ 11 + ω ^ 13 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hsum]
  have h9 : ω ^ 9 = -ω ^ 2 := by
    rw [show (9 : ℕ) = 2 + 7 by norm_num, pow_add, h7]
    ring
  have h11 : ω ^ 11 = -ω ^ 4 := by
    rw [show (11 : ℕ) = 4 + 7 by norm_num, pow_add, h7]
    ring
  have h13 : ω ^ 13 = -ω ^ 6 := by
    rw [show (13 : ℕ) = 6 + 7 by norm_num, pow_add, h7]
    ring
  have hphi : ω ^ 6 - ω ^ 5 + ω ^ 4 - ω ^ 3 + ω ^ 2 - ω + 1 = 0 := by
    have hfac : (ω + 1) * (ω ^ 6 - ω ^ 5 + ω ^ 4 - ω ^ 3 + ω ^ 2 - ω + 1) = 0 := by
      linear_combination h7
    have hne : ω + 1 ≠ 0 := by
      intro h
      apply h2
      rw [show ω = -1 from by linear_combination h]
      ring
    exact (mul_eq_zero.mp hfac).resolve_left hne
  rw [h9, h11, h13]
  linear_combination -hphi

theorem PEqualNP.Outside.L_goldbach_cert_14 :
    ∀ a:ℕ, Nat.Coprime a 14 → (∑ b ∈ (Finset.range 14).filter (fun b => Nat.Coprime b 14), Complex.exp (((2*Real.pi*(a:ℝ)*b/14:ℝ):ℂ)*Complex.I))/(6:ℂ)=(1:ℂ)/6 := by
  intro a ha
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 14)) with hωdef
  have hω : IsPrimitiveRoot ω 14 := by
    rw [hωdef]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 14 (by norm_num) ha
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have hdvd : (14 : ℕ) ∣ 2 := (hω.pow_eq_one_iff_dvd 2).mp h
    norm_num at hdvd
  have hω7 : ω ^ 7 = -1 := by
    have h14 : ω ^ 14 = 1 := hω.pow_eq_one
    have hne : ω ^ 7 ≠ 1 := by
      intro h
      have hdvd : (14 : ℕ) ∣ 7 := (hω.pow_eq_one_iff_dvd 7).mp h
      norm_num at hdvd
    have hfac : (ω ^ 7 - 1) * (ω ^ 7 + 1) = 0 := by
      linear_combination h14
    have : ω ^ 7 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination this
  have hterm : ∀ b : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 14 : ℝ) : ℂ) * Complex.I) = ω ^ b := by
    intro b
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [goldbach_cert_14_units ω hω2 hω7]
