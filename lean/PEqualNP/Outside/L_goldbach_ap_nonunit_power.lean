import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-- A nonzero von Mangoldt weight in a nonunit residue class comes from a
power of a prime dividing the modulus. -/
theorem PEqualNP.Outside.L_goldbach_ap_nonunit_power :
    ∀ q k : ℕ, ¬ Nat.Coprime k q → ArithmeticFunction.vonMangoldt k ≠ 0 →
      ∃ p j : ℕ, Nat.Prime p ∧ p ∣ q ∧ 0 < j ∧ k = p ^ j := by
  intro q k hnonunit hweight
  obtain ⟨p, j, hp, hj, rfl⟩ :=
    (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hweight)
  rw [Nat.coprime_pow_left_iff hj, hp.coprime_iff_not_dvd] at hnonunit
  exact ⟨p, j, hp, not_not.mp hnonunit, hj, rfl⟩
