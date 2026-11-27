import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_48 :
    ∀ a:ℕ, Nat.Coprime a 48 → (∑ b ∈ (Finset.range 48).filter (fun b => Nat.Coprime b 48), Complex.exp (((2*Real.pi*(a:ℝ)*b/48:ℝ):ℂ)*Complex.I))/(16:ℂ)=(0:ℂ)/16 := by
  intro a ha
  let angle : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 48)
  let root := Complex.exp angle
  have primitive : IsPrimitiveRoot root 48 := by
    simpa [root, angle] using Complex.isPrimitiveRoot_exp_of_coprime a 48 (by decide) ha
  have half_turn : root ^ 24 = -1 :=
    (IsPrimitiveRoot.pow (by decide : 0 < 48) primitive (by decide : 48 = 24 * 2)).eq_neg_one_of_two_right
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 48 : ℝ) : ℂ) * Complex.I) = root ^ b := by
    change _ = Complex.exp angle ^ b
    rw [← Complex.exp_nat_mul angle b]
    apply congrArg Complex.exp
    push_cast
    dsimp [angle]
    ring
  have unit_iff (b : ℕ) : Nat.Coprime b 48 ↔ ¬ 2 ∣ b ∧ ¬ 3 ∣ b := by
    rw [show 48 = 2 ^ 4 * 3 by decide, Nat.coprime_mul_iff_right,
      Nat.coprime_pow_right_iff (by decide), @Nat.coprime_comm b 2, @Nat.coprime_comm b 3,
      Nat.prime_two.coprime_iff_not_dvd, Nat.prime_three.coprime_iff_not_dvd]
  have shift (b : ℕ) : Nat.Coprime (24 + b) 48 ↔ Nat.Coprime b 48 := by
    rw [unit_iff, unit_iff]
    omega
  apply congrArg (fun numerator : ℂ => numerator / 16)
  simp_rw [phase]
  rw [Finset.sum_filter, Finset.sum_range_add _ 24 24]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  simp only [shift, pow_add, half_turn, neg_one_mul]
  split <;> simp_all only [add_neg_cancel, add_zero]
