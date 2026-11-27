import Mathlib

/-- The normalized major-arc coefficient modulo 6: the Ramanujan sum `c₆(a) = μ(6) = 1`
for `gcd(a, 6) = 1`, halved. -/
theorem PEqualNP.Outside.L_goldbach_cert_6 :
    ∀ a:ℕ, Nat.Coprime a 6 → (∑ b ∈ (Finset.range 6).filter (fun b => Nat.Coprime b 6), Complex.exp (((2*Real.pi*(a:ℝ)*b/6:ℝ):ℂ)*Complex.I))/(2:ℂ)=(1:ℂ)/2 := by
  intro a ha
  -- The units modulo 6 are `1` and `5 = -1`.
  have hunits : (Finset.range 6).filter (fun b => Nat.Coprime b 6) = {1, 5} := by decide
  -- `ζ = exp(πi/3)` is a primitive sixth root of unity.
  set ζ : ℂ := Complex.exp (((Real.pi/3:ℝ):ℂ) * Complex.I) with hζ
  have hζ6 : ζ ^ 6 = 1 := by
    have h1 : ζ ^ 6 = Complex.exp (2 * ↑Real.pi * Complex.I) := by
      rw [hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_two_pi_mul_I]
  -- Every term of the sum is a power of `ζ`.
  have hterm : ∀ b : ℕ,
      Complex.exp (((2*Real.pi*(a:ℝ)*(b:ℝ)/6:ℝ):ℂ)*Complex.I) = ζ ^ (a * b) := by
    intro b
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- Powers of `ζ` only depend on the exponent modulo 6.
  have hred : ∀ n : ℕ, ζ ^ n = ζ ^ (n % 6) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 6]
    rw [pow_add, pow_mul, hζ6, one_pow, one_mul]
  -- `gcd(a,6) = 1` forces `a ≡ ±1 (mod 6)`.
  have hmod : a % 6 = 1 ∨ a % 6 = 5 := by
    have hg : (a % 6).gcd 6 = 1 := by
      have hdvd : (a % 6).gcd 6 ∣ 1 := by
        have h1 : (a % 6).gcd 6 ∣ a % 6 := Nat.gcd_dvd_left _ _
        have h2 : (a % 6).gcd 6 ∣ 6 := Nat.gcd_dvd_right _ _
        have h3 : (a % 6).gcd 6 ∣ 6 * (a / 6) := dvd_mul_of_dvd_left h2 _
        have h4 : (a % 6).gcd 6 ∣ a := by
          have h4' : (a % 6).gcd 6 ∣ 6 * (a / 6) + a % 6 := dvd_add h3 h1
          rwa [Nat.div_add_mod] at h4'
        rw [← ha]
        exact Nat.dvd_gcd h4 h2
      exact Nat.dvd_one.mp hdvd
    have hlt : a % 6 < 6 := Nat.mod_lt a (by norm_num)
    generalize h : a % 6 = r at hg hlt ⊢
    interval_cases r <;> simp_all (config := { decide := true })
  have hcos : Complex.cos (↑Real.pi / 3) = (1:ℂ)/2 := by
    rw [show (↑Real.pi / 3 : ℂ) = ((Real.pi/3 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cos, Real.cos_pi_div_three]
    norm_num
  -- The sixth root of unity identity: `ζ + ζ⁻¹ = 2 cos(π/3) = 1`.
  have hζ5 : ζ ^ 5 = ζ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have hmul : ζ ^ 5 * ζ = 1 := by
      rw [← pow_succ ζ 5]
      exact hζ6
    exact hmul
  have hsum : ζ + ζ ^ 5 = 1 := by
    rw [hζ5, hζ, ← Complex.exp_neg]
    rw [show -(((Real.pi/3:ℝ):ℂ) * Complex.I) = (-((Real.pi/3:ℝ):ℂ)) * Complex.I by ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, hcos]
    ring
  -- `ζ^25 = ζ` because `ζ^24 = (ζ^6)^4 = 1`.
  have h25 : ζ ^ 25 = ζ := by
    rw [show (25:ℕ) = 6 * 4 + 1 by norm_num, pow_add, pow_mul, hζ6, one_pow, one_mul, pow_one]
  -- Reindexing `ζ^a` and `ζ^(5a)` modulo 6.
  have h5a : ζ ^ (a * 5) = ζ ^ (5 * (a % 6)) := by
    rw [pow_mul, hred a, ← pow_mul, Nat.mul_comm (a % 6) 5]
  rw [hunits, Finset.sum_pair (by norm_num : (1:ℕ) ≠ 5)]
  simp only [hterm, Nat.mul_one]
  rw [hred a, h5a]
  rcases hmod with h1 | h5'
  · rw [h1]
    simp only [pow_one, Nat.mul_one, hsum]
  · rw [h5']
    rw [show (5 * 5 : ℕ) = 25 by norm_num, h25, add_comm, hsum]
