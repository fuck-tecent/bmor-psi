import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_cosine_orthogonality :
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p;
    ∀ p n r : ℕ, 0 < p →
      (∑ k ∈ Finset.range p, Real.cos (angle p k ((n : ℝ) - r))) =
        if n % p = r % p then (p : ℝ) else 0 := by
  intro angle p n r hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htp : (2 : ℝ) * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  -- the basic angle: the k-th angle is its k-th multiple
  let θ : ℝ := 2 * Real.pi * ((n : ℝ) - r) / p
  have hθ : θ = 2 * Real.pi * ((n : ℝ) - (r : ℝ)) / (p : ℝ) := rfl
  have hangle : ∀ k : ℕ, angle p k ((n : ℝ) - r) = (k : ℝ) * θ := by
    intro k
    show 2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ) = (k : ℝ) * θ
    rw [hθ]
    field_simp [hpR] <;> ring
  -- the rotation factor, and its powers as exponentials of the multiples
  let z : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hz : z = Complex.exp ((θ : ℂ) * Complex.I) := rfl
  have hpow : ∀ k : ℕ, z ^ k = Complex.exp (((k : ℝ) * θ : ℂ) * Complex.I) := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    simp only [Complex.ofReal_natCast]
    ring
  -- the k-th cosine is the real part of the k-th power
  have hcos : ∀ k : ℕ, (z ^ k).re = Real.cos (angle p k ((n : ℝ) - r)) := by
    intro k
    rw [hpow, Complex.exp_re, hangle]
    have h1 : (((k : ℝ) * θ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    have h2 : (((k : ℝ) * θ : ℂ) * Complex.I).im = (k : ℝ) * θ := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [h1, h2, Real.exp_zero, one_mul]
  -- a cosine one-liner: the exponential is one exactly at the whole turns
  have hre : ∀ x : ℝ, (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
    intro x
    rw [Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Real.exp_zero]
  have hexp : ∀ x : ℝ,
      Complex.exp ((x : ℂ) * Complex.I) = 1 ↔ ∃ m : ℤ, x = (m : ℝ) * (2 * Real.pi) := by
    intro x
    constructor
    · intro h
      have hc : Real.cos x = 1 := by
        rw [← hre x]
        exact congrArg Complex.re h
      obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff x).mp hc
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, rfl⟩
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      rw [Complex.ext_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_mul,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_intCast]
  -- so the rotation factor is one precisely when p divides the difference
  have hdvd : ((p : ℤ) ∣ (n : ℤ) - (r : ℤ)) ↔ n % p = r % p := by
    rw [← Int.modEq_iff_dvd, ← Int.modEq_comm, Int.natCast_modEq_iff]
    exact Iff.rfl
  have hz1 : z = 1 ↔ n % p = r % p := by
    rw [hz, hexp θ, hθ, ← hdvd]
    constructor
    · rintro ⟨m, hm⟩
      have h2 : 2 * Real.pi * ((n : ℝ) - (r : ℝ)) = 2 * Real.pi * ((m : ℝ) * (p : ℝ)) := by
        calc 2 * Real.pi * ((n : ℝ) - (r : ℝ))
            = (2 * Real.pi * ((n : ℝ) - (r : ℝ)) / (p : ℝ)) * (p : ℝ) := by field_simp [hpR]
          _ = ((m : ℝ) * (2 * Real.pi)) * (p : ℝ) := by rw [hm]
          _ = 2 * Real.pi * ((m : ℝ) * (p : ℝ)) := by ring
      have h3 : (n : ℝ) - (r : ℝ) = (p : ℝ) * (m : ℝ) := by
        rw [mul_comm]
        exact mul_left_cancel₀ htp h2
      exact ⟨m, by exact_mod_cast h3⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have h2 : (n : ℝ) - (r : ℝ) = (p : ℝ) * (m : ℝ) := by exact_mod_cast hm
      rw [h2]
      field_simp [hpR] <;> ring
  -- the geometric sum: going once around the circle closes it up
  have hpt : (p : ℝ) * θ = 2 * Real.pi * ((n : ℝ) - (r : ℝ)) := by
    rw [hθ]
    field_simp [hpR] <;> ring
  have hzp : z ^ p = 1 := by
    rw [hpow p, ← Complex.ofReal_mul, hexp]
    refine ⟨(n : ℤ) - (r : ℤ), ?_⟩
    rw [hpt]
    norm_cast <;> ring
  have hsum : (∑ k ∈ Finset.range p, z ^ k) = if z = 1 then (p : ℂ) else 0 := by
    by_cases h : z = 1
    · rw [if_pos h, h]
      exact one_geom_sum p
    · rw [if_neg h]
      have hS : (∑ k ∈ Finset.range p, z ^ k) * (z - 1) = 0 := by
        rw [geom_sum_mul, hzp, sub_self]
      rcases mul_eq_zero.mp hS with h' | h'
      · exact h'
      · exact absurd h' (sub_ne_zero.mpr h)
  -- real parts commute with the sum, and the two cases give p and zero
  have hlin : (∑ k ∈ Finset.range p, z ^ k).re = ∑ k ∈ Finset.range p, (z ^ k).re := by
    simp
  have hmain : ∑ k ∈ Finset.range p, (z ^ k).re =
      (if n % p = r % p then (p : ℝ) else 0) := by
    by_cases h : n % p = r % p
    · have hc : z = 1 := hz1.mpr h
      rw [if_pos h, ← hlin, hsum, if_pos hc, Complex.natCast_re]
    · have hc : ¬ (z = 1) := fun hc' => h (hz1.mp hc')
      rw [if_neg h, ← hlin, hsum, if_neg hc, Complex.zero_re]
  exact (Finset.sum_congr rfl (fun k _ => (hcos k).symm)).trans hmain
