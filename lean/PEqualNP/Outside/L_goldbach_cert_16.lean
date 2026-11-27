import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_16 :
    ∀ a:ℕ, Nat.Coprime a 16 → (∑ b ∈ (Finset.range 16).filter (fun b => Nat.Coprime b 16), Complex.exp (((2*Real.pi*(a:ℝ)*b/16:ℝ):ℂ)*Complex.I))/(8:ℂ)=(0:ℂ)/8 := by
  intro a ha
  let phase (b : ℕ) := Complex.exp (((2 * Real.pi * (a : ℝ) * b / 16 : ℝ) : ℂ) * Complex.I)
  let lower := (Finset.range 8).filter (fun b => Nat.Coprime b 16)
  have hunits : (Finset.range 16).filter (fun b => Nat.Coprime b 16) =
      lower ∪ lower.image (· + 8) := by decide
  have hdisjoint : Disjoint lower (lower.image (· + 8)) := by decide
  have hodd : Odd a := (ha.of_dvd_right (by decide : 2 ∣ 16)).odd_of_right
  have hhalf : Complex.exp ((a : ℂ) * (Real.pi * Complex.I)) = -1 := by
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I, hodd.neg_one_pow]
  have hcancel (b : ℕ) : phase (b + 8) = -phase b := by
    unfold phase
    push_cast
    rw [show 2 * (Real.pi : ℂ) * a * ((b : ℂ) + 8) / 16 * Complex.I =
        2 * (Real.pi : ℂ) * a * b / 16 * Complex.I + a * (Real.pi * Complex.I) by ring,
      Complex.exp_add, hhalf, mul_neg_one]
  apply congrArg (· / _)
  change (∑ b ∈ (Finset.range 16).filter (fun b => Nat.Coprime b 16), phase b) = 0
  rw [hunits, Finset.sum_union hdisjoint, Finset.sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
  simp only [hcancel, Finset.sum_neg_distrib, add_neg_cancel]
