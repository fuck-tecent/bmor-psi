import Mathlib

theorem PEqualNP.Outside.L_goldbach_characters_primitive_parity : ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, χ (-1) = -1 → χ.primitiveCharacter (-1) = -1 := by
  intro n _ _ χ hχ
  have hunit : IsCoprime (-1 : ℤ) (n : ℤ) := ⟨-1, 0, by ring⟩
  have heq := χ.primitiveCharacter_apply_of_isCoprime hunit
  simpa using (heq.trans (by simpa using hχ))
