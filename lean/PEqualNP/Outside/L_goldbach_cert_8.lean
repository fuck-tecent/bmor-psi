import Mathlib

/-- The normalized major-arc coefficient modulo 8: the Ramanujan sum `c₈(a) = μ(8) = 0`
for `gcd(a, 8) = 1`, halved by `φ(8) = 4`. -/
theorem PEqualNP.Outside.L_goldbach_cert_8 :
    ∀ a:ℕ, Nat.Coprime a 8 → (∑ b ∈ (Finset.range 8).filter (fun b => Nat.Coprime b 8), Complex.exp (((2*Real.pi*(a:ℝ)*b/8:ℝ):ℂ)*Complex.I))/(4:ℂ)=(0:ℂ)/4 := by
  intro a ha
  -- The units modulo 8 are `1, 3, 5, 7 = -1`.
  have hunits : (Finset.range 8).filter (fun b => Nat.Coprime b 8) = {1, 3, 5, 7} := by decide
  -- `ζ = exp(πi/4)` is a primitive eighth root of unity, `u = ζ^(2a)`.
  set ζ : ℂ := Complex.exp (((Real.pi/4:ℝ):ℂ) * Complex.I) with hζ
  set u : ℂ := ζ ^ (2 * a) with hu
  have hζ8 : ζ ^ 8 = 1 := by
    have h1 : ζ ^ 8 = Complex.exp (2 * ↑Real.pi * Complex.I) := by
      rw [hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_two_pi_mul_I]
  have hζ4 : ζ ^ 4 = -1 := by
    have h1 : ζ ^ 4 = Complex.exp (↑Real.pi * Complex.I) := by
      rw [hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_pi_mul_I]
  -- Every term of the sum is a power of `ζ`.
  have hterm : ∀ b : ℕ,
      Complex.exp (((2*Real.pi*(a:ℝ)*(b:ℝ)/8:ℝ):ℂ)*Complex.I) = ζ ^ (a * b) := by
    intro b
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- `a` is odd, so `u² = ζ^(4a) = (ζ⁴)^a = -1`.
  have haodd : Odd a := by
    have h2 : Nat.Coprime a 2 := ha.coprime_dvd_right (by norm_num : (2:ℕ) ∣ 8)
    exact Nat.coprime_two_right.mp h2
  have hu2 : u ^ 2 = -1 := by
    have h1 : u ^ 2 = ζ ^ (4 * a) := by
      rw [hu, ← pow_mul]
      congr 1
      ring
    rw [h1, pow_mul, hζ4, haodd.neg_one_pow]
  have hu3 : u ^ 3 = -u := by
    have h1 : u ^ 3 = u ^ 2 * u := by ring
    rw [h1, hu2]
    ring
  -- `ζ^a (1 + u + u² + u³) = ζ^a (1 + u)(1 + u²) = 0`: the four unit terms cancel in pairs.
  have h3 : ζ ^ (a * 3) = ζ ^ a * u := by
    rw [show a * 3 = a + 2 * a by ring, pow_add, hu]
  have hu2' : u ^ 2 = ζ ^ (2 * a * 2) := by rw [hu, ← pow_mul]
  have hu3' : u ^ 3 = ζ ^ (2 * a * 3) := by rw [hu, ← pow_mul]
  have h5 : ζ ^ (a * 5) = ζ ^ a * u ^ 2 := by
    rw [show a * 5 = a + 2 * a * 2 by ring, pow_add, hu2']
  have h7 : ζ ^ (a * 7) = ζ ^ a * u ^ 3 := by
    rw [show a * 7 = a + 2 * a * 3 by ring, pow_add, hu3']
  rw [hunits, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hterm, Nat.mul_one]
  rw [h3, h5, h7, hu2, hu3]
  have hzero : ζ ^ a + (ζ ^ a * u + (ζ ^ a * (-1) + ζ ^ a * (-u))) = 0 := by ring
  rw [hzero]
