import Mathlib

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_goldbach_cert_53 :
    ∀ a : ℕ, Nat.Coprime a 53 →
      (∑ b ∈ (Finset.range 53).filter (fun b => Nat.Coprime b 53),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 53 : ℝ) : ℂ) * Complex.I)) /
        (52 : ℂ) = (-1 : ℂ) / 52 := by
  intro a ha
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 53 : ℝ) * Complex.I
  let z := Complex.exp t
  have hz : z ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hk
    simp [t, Complex.mul_im] at hi
    have hp := Real.pi_pos
    have he : (a : ℝ) = 53 * (k : ℝ) := by nlinarith
    have hei : (a : ℤ) = 53 * k := by exact_mod_cast he
    have hd : 53 ∣ a := by
      have hd' : (53 : ℤ) ∣ (a : ℤ) := ⟨k, hei⟩
      exact_mod_cast hd'
    exact (by decide : ¬ (53 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_refl 53))
  have hz53 : z ^ 53 = 1 := by
    change Complex.exp t ^ 53 = 1
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I a using 2
    push_cast
    dsimp [t]
    push_cast
    ring
  have hsum : ∑ b ∈ Finset.range 53, z ^ b = 0 := by
    rw [geom_sum_eq hz, hz53, sub_self, zero_div]
  have hfilter : (Finset.range 53).filter (fun b => Nat.Coprime b 53) =
      (Finset.range 53).erase 0 := by decide
  have hzero : 0 ∈ Finset.range 53 := by decide
  have herase := Finset.sum_erase_add (Finset.range 53) (fun b => z ^ b) hzero
  rw [hsum, pow_zero] at herase
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 53 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    refine (congrArg Complex.exp ?_).trans (Complex.exp_nat_mul t b)
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  rw [hfilter, show (∑ b ∈ (Finset.range 53).erase 0, z ^ b) = -1 by linear_combination herase]
