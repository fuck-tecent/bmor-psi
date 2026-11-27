import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

theorem PEqualNP.Outside.L_goldbach_mangoldt_power_support :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; ∀ k, h k ≠ 0 → ∃ p j : ℕ, Nat.Prime p ∧ 2≤j ∧ k=p^j := by
  dsimp only
  intro k h
  have hk : ¬ Nat.Prime k := by
    intro prime
    exact h (by simp [prime, ArithmeticFunction.vonMangoldt_apply_prime prime])
  have nonzero : ArithmeticFunction.vonMangoldt k ≠ 0 := by
    simpa [hk] using h
  obtain ⟨p, j, hp, hj, heq⟩ :=
    (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp nonzero)
  refine ⟨p, j, hp, ?_, heq.symm⟩
  have notOne : j ≠ 1 := by
    rintro rfl
    apply hk
    simpa only [← heq, pow_one] using hp
  omega
