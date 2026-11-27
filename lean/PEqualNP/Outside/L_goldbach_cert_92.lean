import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_92 :
    ∀ a:ℕ, Nat.Coprime a 92 → (∑ b ∈ (Finset.range 92).filter (fun b => Nat.Coprime b 92), Complex.exp (((2*Real.pi*(a:ℝ)*b/92:ℝ):ℂ)*Complex.I))/(44:ℂ)=(0:ℂ)/44 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 92)
  have primitive : IsPrimitiveRoot (Complex.exp θ) 92 := by
    simpa [θ] using Complex.isPrimitiveRoot_exp_of_coprime a 92 (by decide) ha
  have half_turn : Complex.exp θ ^ 46 = -1 :=
    (IsPrimitiveRoot.pow (by decide) primitive (show 92 = 46 * 2 by decide)).eq_neg_one_of_two_right
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 92 : ℝ) : ℂ) * Complex.I) =
        Complex.exp θ ^ b := by
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
  have unit_iff (b : ℕ) : Nat.Coprime b 92 ↔ ¬ 2 ∣ b ∧ ¬ 23 ∣ b := by
    rw [show 92 = 2 ^ 2 * 23 by decide, Nat.coprime_mul_iff_right,
      Nat.coprime_pow_right_iff (by decide), @Nat.coprime_comm b 2, @Nat.coprime_comm b 23,
      Nat.prime_two.coprime_iff_not_dvd, (show Nat.Prime 23 by decide).coprime_iff_not_dvd]
  have shift (b : ℕ) : Nat.Coprime (46 + b) 92 ↔ Nat.Coprime b 92 := by
    rw [unit_iff, unit_iff]
    omega
  apply congrArg (fun z : ℂ => z / 44)
  simp_rw [phase]
  rw [Finset.sum_filter, show 92 = 46 + 46 by decide, Finset.sum_range_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  change (if Nat.Coprime b 92 then Complex.exp θ ^ b else 0) +
    (if Nat.Coprime (46 + b) 92 then Complex.exp θ ^ (46 + b) else 0) = 0
  rw [if_congr (shift b) rfl rfl, pow_add, half_turn]
  split_ifs <;> simp_all only [neg_one_mul, add_neg_cancel, add_zero]
