import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_24 :
    ∀ a:ℕ, Nat.Coprime a 24 → (∑ b ∈ (Finset.range 24).filter (fun b => Nat.Coprime b 24), Complex.exp (((2*Real.pi*(a:ℝ)*b/24:ℝ):ℂ)*Complex.I))/(8:ℂ)=(0:ℂ)/8 := by
  intro a ha
  let phase (b : ℕ) := Complex.exp (((2 * Real.pi * (a : ℝ) * b / 24 : ℝ) : ℂ) * Complex.I)
  have haOdd : Odd a :=
    Nat.coprime_two_right.mp (ha.of_dvd_right (by decide : 2 ∣ 24))
  have shift (b : ℕ) : phase (b + 12) = -phase b := by
    unfold phase
    have angle :
        ((2 * Real.pi * (a : ℝ) * (b + 12 : ℕ) / 24 : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * (a : ℝ) * b / 24 : ℝ) : ℂ) * Complex.I +
          (a : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [angle, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, haOdd.neg_one_pow]
    simp

  let lower := (Finset.range 12).filter (fun b => Nat.Coprime b 24)
  let upper := lower.image (fun b => b + 12)
  have units : (Finset.range 24).filter (fun b => Nat.Coprime b 24) = lower ∪ upper := by
    decide
  have separate : Disjoint lower upper := by decide
  have cancel : ∑ b ∈ upper, phase b = -(∑ b ∈ lower, phase b) := by
    dsimp only [upper]
    rw [Finset.sum_image (by
      intro x _ y _ h
      exact Nat.add_right_cancel h)]
    simp only [shift, Finset.sum_neg_distrib]
  change (∑ b ∈ (Finset.range 24).filter (fun b => Nat.Coprime b 24), phase b) / 8 = 0 / 8
  rw [units, Finset.sum_union separate, cancel, add_neg_cancel]
