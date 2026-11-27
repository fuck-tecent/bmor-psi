import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_4 :
    ∀ a:ℕ, Nat.Coprime a 4 → (∑ b ∈ (Finset.range 4).filter (fun b => Nat.Coprime b 4), Complex.exp (((2*Real.pi*(a:ℝ)*b/4:ℝ):ℂ)*Complex.I))/(2:ℂ)=(0:ℂ)/2 := by
  intro a ha
  have hodd : Odd a := Nat.coprime_two_right.mp (ha.of_dvd_right (by decide : 2 ∣ 4))
  have hunits : (Finset.range 4).filter (fun b => Nat.Coprime b 4) = {1, 3} := by decide
  have hshift : Complex.exp ((a : ℂ) * (Real.pi * Complex.I)) = -1 := by
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I, hodd.neg_one_pow]
  rw [hunits, Finset.sum_pair (by decide : (1 : ℕ) ≠ 3)]
  push_cast
  have hphase : 2 * (Real.pi : ℂ) * a * 3 / 4 * Complex.I =
      2 * (Real.pi : ℂ) * a * 1 / 4 * Complex.I + a * (Real.pi * Complex.I) := by ring
  rw [hphase, Complex.exp_add, hshift]
  ring
