import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_2 : ∀ a : ℕ, Nat.Coprime a 2 → (∑ b ∈ (Finset.range 2).filter (fun b => Nat.Coprime b 2), Complex.exp (((2 * Real.pi * (a : ℝ) * b / 2 : ℝ) : ℂ) * Complex.I)) / (1 : ℂ) = (-1 : ℂ) / 1 := by
  intro a ha
  have hfilter : (Finset.range 2).filter (fun b => Nat.Coprime b 2) = {1} := by decide
  simp only [hfilter, Finset.sum_singleton, div_one]
  have hphase : (((2 * Real.pi * (a : ℝ) * (1 : ℕ) / 2 : ℝ) : ℂ) * Complex.I) =
      (a : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hphase, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  exact (Nat.coprime_two_right.mp ha).neg_one_pow
