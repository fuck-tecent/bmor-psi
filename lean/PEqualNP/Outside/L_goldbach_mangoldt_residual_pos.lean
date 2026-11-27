import Mathlib

theorem PEqualNP.Outside.L_goldbach_mangoldt_residual_pos :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k;
    ∀ k, 0 ≤ h k := by
  change ∀ k : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt k -
      (if Nat.Prime k then Real.log (k : ℝ) else 0)
  intro k
  by_cases hk : Nat.Prime k
  · simp only [if_pos hk, ArithmeticFunction.vonMangoldt_apply_prime hk, sub_self, le_refl]
  · simpa only [if_neg hk, sub_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := k))
