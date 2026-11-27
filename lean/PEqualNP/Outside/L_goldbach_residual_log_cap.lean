import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

theorem PEqualNP.Outside.L_goldbach_residual_log_cap :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; ∀ X k : ℕ, 2≤X → k≤X → h k ≤ Real.log (X:ℝ) := by
  dsimp only
  intro X k hX hk
  have logX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  by_cases prime : Nat.Prime k
  · simpa [prime, ArithmeticFunction.vonMangoldt_apply_prime prime] using logX
  · simp only [ite_eq_right prime, sub_zero]
    rcases Nat.eq_zero_or_pos k with rfl | pos
    · simpa using logX
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast hk))
