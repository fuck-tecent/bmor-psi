import Mathlib

/-- The normalized major-arc coefficient modulo 9: the Ramanujan sum `c₉(a) = μ(9) = 0`
for `gcd(a, 9) = 1`, halved by `φ(9) = 6`. -/
theorem PEqualNP.Outside.L_goldbach_cert_9 :
    ∀ a:ℕ, Nat.Coprime a 9 → (∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9), Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I))/(6:ℂ)=(0:ℂ)/6 := by
  intro a ha
  -- The units modulo 9 are `{1,2,4,5,7,8} = {1,4,7} ∪ {2,5,8}`, two cosets of `{1,4,7}`.
  have hunits : (Finset.range 9).filter (fun b => Nat.Coprime b 9) = {1, 2, 4, 5, 7, 8} := by
    decide
  have hpart : ({1, 2, 4, 5, 7, 8} : Finset ℕ) = {1, 4, 7} ∪ {2, 5, 8} := by decide
  -- `w = exp(2πi/9)` is a primitive ninth root of unity, `v = w^(3a) = (w³)^a` a cube root of unity.
  set w : ℂ := Complex.exp (((2*Real.pi/9:ℝ):ℂ) * Complex.I) with hw
  set c : ℂ := w ^ 3 with hc
  set v : ℂ := w ^ (3 * a) with hvdef
  have hterm : ∀ b : ℕ,
      Complex.exp (((2*Real.pi*(a:ℝ)*(b:ℝ)/9:ℝ):ℂ)*Complex.I) = w ^ (a * b) := by
    intro b
    rw [hw, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hw9 : w ^ 9 = 1 := by
    have h1 : w ^ 9 = Complex.exp (2 * ↑Real.pi * Complex.I) := by
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_two_pi_mul_I]
  -- `c = exp(2πi/3)` is a cube root of unity and `c ≠ 1` (its real part is `-1/2`).
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← pow_mul, show (3:ℕ) * 3 = 9 by norm_num, hw9]
  have hcexp : c = Complex.exp (((2*Real.pi/3:ℝ):ℂ) * Complex.I) := by
    rw [hc, hw, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcre : c.re = -(1/2) := by
    rw [hcexp, Complex.exp_ofReal_mul_I_re]
    have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hcne : c ≠ 1 := by
    intro h
    have h2 := hcre
    rw [h, Complex.one_re] at h2
    norm_num at h2
  have hcsum : 1 + c + c ^ 2 = 0 := by
    have hprod : (c - 1) * (1 + c + c ^ 2) = 0 := by
      calc (c - 1) * (1 + c + c^2) = c^3 - 1 := by ring
        _ = 0 := by rw [hc3]; ring
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h (sub_ne_zero.mpr hcne)
    · exact h
  -- `v = c^a`, and `gcd(a,9) = 1` forces `a % 3 ∈ {1,2}`, so `v` is a primitive cube root.
  have hred3 : ∀ n : ℕ, c ^ n = c ^ (n % 3) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 3]
    rw [pow_add, pow_mul, hc3, one_pow, one_mul]
  have h3a : ¬ (3 ∣ a) := by
    intro h
    have hd : 3 ∣ a.gcd 9 := Nat.dvd_gcd h (by norm_num)
    rw [ha] at hd
    norm_num at hd
  have hmod3 : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt : a % 3 < 3 := Nat.mod_lt a (by norm_num)
    have hne : a % 3 ≠ 0 := fun h => h3a (Nat.dvd_of_mod_eq_zero h)
    omega
  have hvc : v = c ^ a := by
    rw [hvdef, hc, ← pow_mul]
  have hv : 1 + v + v ^ 2 = 0 := by
    rw [hvc, hred3 a]
    rcases hmod3 with h1 | h2
    · rw [h1, pow_one]
      exact hcsum
    · rw [h2]
      have h4 : c ^ 4 = c := by
        rw [show (4:ℕ) = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
      have hsq : (c ^ 2) ^ 2 = c ^ 4 := by rw [← pow_mul]
      rw [hsq, h4]
      have e : 1 + c ^ 2 + c = 1 + c + c ^ 2 := by ring
      rw [e, hcsum]
  -- Each coset contributes a multiple of `1 + v + v² = 0`.
  have hA : w ^ (a * 1) + (w ^ (a * 4) + w ^ (a * 7)) = 0 := by
    have e4 : w ^ (a * 4) = w ^ a * v := by
      rw [hvdef, show a * 4 = a + 3 * a by ring, pow_add]
    have e7 : w ^ (a * 7) = w ^ a * v ^ 2 := by
      rw [hvdef, show a * 7 = a + 3 * a * 2 by ring, pow_add, ← pow_mul]
    rw [e4, e7, Nat.mul_one]
    have e : w ^ a + (w ^ a * v + w ^ a * v ^ 2) = w ^ a * (1 + v + v ^ 2) := by ring
    rw [e, hv, mul_zero]
  have hB : w ^ (a * 2) + (w ^ (a * 5) + w ^ (a * 8)) = 0 := by
    have e5 : w ^ (a * 5) = w ^ (2 * a) * v := by
      rw [hvdef, show a * 5 = 2 * a + 3 * a by ring, pow_add]
    have e8 : w ^ (a * 8) = w ^ (2 * a) * v ^ 2 := by
      rw [hvdef, show a * 8 = 2 * a + 3 * a * 2 by ring, pow_add, ← pow_mul]
    rw [e5, e8, show w ^ (a * 2) = w ^ (2 * a) by rw [Nat.mul_comm]]
    have e : w ^ (2 * a) + (w ^ (2 * a) * v + w ^ (2 * a) * v ^ 2) =
        w ^ (2 * a) * (1 + v + v ^ 2) := by ring
    rw [e, hv, mul_zero]
  rw [hunits, hpart, Finset.sum_union (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hterm]
  rw [hA, hB]
  norm_num
