import Mathlib

/-- The normalized major-arc coefficient modulo 12: the Ramanujan sum `c₁₂(a) = μ(12) = 0`
for `gcd(a, 12) = 1`, halved by `φ(12) = 4`. -/
theorem PEqualNP.Outside.L_goldbach_cert_12 :
    ∀ a:ℕ, Nat.Coprime a 12 → (∑ b ∈ (Finset.range 12).filter (fun b => Nat.Coprime b 12), Complex.exp (((2*Real.pi*(a:ℝ)*b/12:ℝ):ℂ)*Complex.I))/(4:ℂ)=(0:ℂ)/4 := by
  intro a ha
  -- The units modulo 12 are `{1, 5, 7, 11}`; `7 = 1 + 6` and `11 = 5 + 6` pair up.
  have hunits : (Finset.range 12).filter (fun b => Nat.Coprime b 12) = {1, 5, 7, 11} := by
    decide
  -- `w = exp(πi/6)` is a twelfth root of unity with `w^6 = -1`.
  set w : ℂ := Complex.exp (((Real.pi/6:ℝ):ℂ) * Complex.I) with hw
  have hw6 : w ^ 6 = -1 := by
    have h1 : w ^ 6 = Complex.exp (↑Real.pi * Complex.I) := by
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_pi_mul_I]
  have hterm : ∀ b : ℕ,
      Complex.exp (((2*Real.pi*(a:ℝ)*(b:ℝ)/12:ℝ):ℂ)*Complex.I) = w ^ (a * b) := by
    intro b
    rw [hw, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- `a` is odd, so shifting `b` by 6 multiplies the term by `w^(6a) = (-1)^a = -1`.
  have haodd : Odd a := by
    have h2 : Nat.Coprime a 2 := ha.coprime_dvd_right (by norm_num : (2:ℕ) ∣ 12)
    exact Nat.coprime_two_right.mp h2
  have hpairs : ∀ b : ℕ, w ^ (a * (b + 6)) = -w ^ (a * b) := by
    intro b
    have e : a * (b + 6) = a * b + 6 * a := by ring
    rw [e, pow_add]
    have h6a : w ^ (6 * a) = -1 := by
      rw [pow_mul, hw6, haodd.neg_one_pow]
    rw [h6a]
    ring
  rw [hunits, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hterm]
  rw [show w ^ (a * 7) = -w ^ (a * 1) by simpa using hpairs 1,
    show w ^ (a * 11) = -w ^ (a * 5) by simpa using hpairs 5]
  ring_nf
