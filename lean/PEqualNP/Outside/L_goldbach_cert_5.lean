import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_5 :
    ∀ a : ℕ, Nat.Coprime a 5 →
      (∑ b ∈ (Finset.range 5).filter (fun b => Nat.Coprime b 5),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 5 : ℝ) : ℂ) * Complex.I)) /
        (4 : ℂ) = (-1 : ℂ) / 4 := by
  intro a ha
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 5 : ℝ) * Complex.I
  let z := Complex.exp t
  have hz : z ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hk
    simp [t, Complex.mul_im] at hi
    have hp := Real.pi_pos
    have he : (a : ℝ) = 5 * (k : ℝ) := by nlinarith
    have hei : (a : ℤ) = 5 * k := by exact_mod_cast he
    have hd : 5 ∣ a := by
      have hd' : (5 : ℤ) ∣ (a : ℤ) := ⟨k, hei⟩
      exact_mod_cast hd'
    exact (by decide : ¬ (5 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_refl 5))
  have hz5 : z ^ 5 = 1 := by
    change Complex.exp t ^ 5 = 1
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I a using 2
    push_cast
    dsimp [t]
    push_cast
    ring
  have hsum : ∑ b ∈ Finset.range 5, z ^ b = 0 := by
    rw [geom_sum_eq hz, hz5, sub_self, zero_div]
  have hfilter : (Finset.range 5).filter (fun b => Nat.Coprime b 5) =
      (Finset.range 5).erase 0 := by decide
  have hzero : 0 ∈ Finset.range 5 := by decide
  have herase := Finset.sum_erase_add (Finset.range 5) (fun b => z ^ b) hzero
  rw [hsum, pow_zero] at herase
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 5 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    change _ = Complex.exp t ^ b
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  rw [hfilter, show (∑ b ∈ (Finset.range 5).erase 0, z ^ b) = -1 by linear_combination herase]
