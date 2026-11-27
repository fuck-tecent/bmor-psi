import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_157 :
    ∀ a : ℕ, Nat.Coprime a 157 →
      (∑ b ∈ (Finset.range 157).filter (fun b => Nat.Coprime b 157),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 157 : ℝ) : ℂ) * Complex.I)) / (156 : ℂ) =
      (-1 : ℂ) / 156 := by
  intro a ha
  have hp : Nat.Prime 157 := by norm_num
  have hfilter :
      (Finset.range 157).filter (fun b => Nat.Coprime b 157) = (Finset.range 157).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨hb, hcop⟩
      refine ⟨?_, hb⟩
      rintro rfl
      norm_num at hcop
    · rintro ⟨hb0, hb⟩
      refine ⟨hb, ?_⟩
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb0) hb)
  set ω : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 157 : ℝ) : ℂ) * Complex.I)
  have hterm : ∀ b : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 157 : ℝ) : ℂ) * Complex.I) = ω ^ b := by
    intro b
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    have hreal : 2 * Real.pi * (a : ℝ) * (b : ℝ) / 157 = (b : ℝ) * (2 * Real.pi * (a : ℝ) / 157) := by
      ring
    rw [hreal]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  have hω_pow : ω ^ 157 = 1 := by
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    have hexp :
        (157 : ℂ) * (((2 * Real.pi * (a : ℝ) / 157 : ℝ) : ℂ) * Complex.I) =
        (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have hreal : (157 : ℝ) * (2 * Real.pi * (a : ℝ) / 157) = (a : ℝ) * (2 * Real.pi) := by
        ring
      calc
        (157 : ℂ) * (((2 * Real.pi * (a : ℝ) / 157 : ℝ) : ℂ) * Complex.I)
          = (((157 : ℝ) * (2 * Real.pi * (a : ℝ) / 157) : ℝ) : ℂ) * Complex.I := by
            simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
            ring
        _ = (((a : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by rw [hreal]
        _ = (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
            ring
    rw [Nat.cast_ofNat, hexp, Complex.exp_nat_mul_two_pi_mul_I]
  have hω_ne : ω ≠ 1 := by
    intro hω1
    dsimp only [ω] at hω1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hω1
    have him : 2 * Real.pi * (a : ℝ) / 157 = (n : ℝ) * (2 * Real.pi) := by
      have h1 := congrArg Complex.im hn
      have hlhs :
          (((2 * Real.pi * (a : ℝ) / 157 : ℝ) : ℂ) * Complex.I).im = 2 * Real.pi * (a : ℝ) / 157 := by
        rw [Complex.mul_I_im, Complex.ofReal_re]
      have hrhs : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (n : ℝ) * (2 * Real.pi) := by
        have hr : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
            (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
          simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
          ring
        rw [hr, Complex.mul_I_im, Complex.ofReal_re]
      rw [hlhs, hrhs] at h1
      exact h1
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hdiv : (a : ℝ) / 157 = (n : ℝ) := by
      apply mul_left_cancel₀ h2pi
      have hmul_eq : 2 * Real.pi * ((a : ℝ) / 157) = 2 * Real.pi * (a : ℝ) / 157 := by ring
      rw [hmul_eq, him, mul_comm]
    have hreal_a : (a : ℝ) = (157 : ℝ) * (n : ℝ) := by
      linarith
    have hint_real : ((a : ℤ) : ℝ) = ((157 * n : ℤ) : ℝ) := by
      rw [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      exact hreal_a
    have hint : (a : ℤ) = 157 * n := Int.cast_inj.mp hint_real
    have hdvd_int : (157 : ℤ) ∣ (a : ℤ) := ⟨n, hint⟩
    have hdvd_nat : 157 ∣ a := Int.ofNat_dvd.mp hdvd_int
    have hcop_not_dvd : ¬ (157 ∣ a) := hp.coprime_iff_not_dvd.mp ha.symm
    exact hcop_not_dvd hdvd_nat
  have hsum_all : ∑ b ∈ Finset.range 157, ω ^ b = 0 := by
    have hgeom : (∑ b ∈ Finset.range 157, ω ^ b) * (ω - 1) = 0 := by
      rw [geom_sum_mul ω 157, hω_pow, sub_self]
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hω_ne)
  have hsum_erase : ∑ b ∈ (Finset.range 157).erase 0, ω ^ b = -1 := by
    have hadd := Finset.add_sum_erase (Finset.range 157) (fun b => ω ^ b) (by simp : (0 : ℕ) ∈ Finset.range 157)
    rw [pow_zero, hsum_all] at hadd
    exact eq_neg_of_add_eq_zero_right hadd
  have hsum_eq :
      ∑ b ∈ (Finset.range 157).filter (fun b => Nat.Coprime b 157),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 157 : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [hfilter]
    calc
      ∑ b ∈ (Finset.range 157).erase 0,
          Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 157 : ℝ) : ℂ) * Complex.I)
        = ∑ b ∈ (Finset.range 157).erase 0, ω ^ b :=
          Finset.sum_congr rfl fun b _ => hterm b
      _ = -1 := hsum_erase
  rw [hsum_eq]
