import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_96 :
    ∀ a:ℕ, Nat.Coprime a 96 → (∑ b ∈ (Finset.range 96).filter (fun b => Nat.Coprime b 96), Complex.exp (((2*Real.pi*(a:ℝ)*b/96:ℝ):ℂ)*Complex.I))/(32:ℂ)=(0:ℂ)/32 := by
  intro a coprime
  let angle : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 96)
  have primitive : IsPrimitiveRoot (Complex.exp angle) 96 := by
    simpa [angle] using Complex.isPrimitiveRoot_exp_of_coprime a 96 (by decide) coprime
  have half_turn : Complex.exp angle ^ 48 = -1 :=
    (IsPrimitiveRoot.pow (by decide) primitive (show 96 = 48 * 2 by decide)).eq_neg_one_of_two_right
  have phase (residue : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * residue / 96 : ℝ) : ℂ) * Complex.I) =
        Complex.exp angle ^ residue := by
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [angle]
    ring
  have unit_iff (residue : ℕ) : Nat.Coprime residue 96 ↔ ¬ 2 ∣ residue ∧ ¬ 3 ∣ residue := by
    rw [show 96 = 2 ^ 5 * 3 by decide, Nat.coprime_mul_iff_right,
      Nat.coprime_pow_right_iff (by decide), @Nat.coprime_comm residue 2,
      @Nat.coprime_comm residue 3, Nat.prime_two.coprime_iff_not_dvd,
      Nat.prime_three.coprime_iff_not_dvd]
  have shift (residue : ℕ) : Nat.Coprime (48 + residue) 96 ↔ Nat.Coprime residue 96 := by
    rw [unit_iff, unit_iff]
    omega
  apply congrArg (fun total : ℂ => total / 32)
  simp_rw [phase]
  rw [Finset.sum_filter, show 96 = 48 + 48 by decide, Finset.sum_range_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro residue _
  change (if Nat.Coprime residue 96 then Complex.exp angle ^ residue else 0) +
    (if Nat.Coprime (48 + residue) 96 then Complex.exp angle ^ (48 + residue) else 0) = 0
  rw [if_congr (shift residue) rfl rfl, pow_add, half_turn]
  split_ifs <;> simp
