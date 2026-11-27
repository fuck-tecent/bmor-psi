import Mathlib

/-- JA-0006: the determinant of the Kronecker product (the matrix of multiplication on a
pure tensor, in the product basis) is the product of the determinants, each raised to the
power of the other factor's dimension. -/
theorem Conjectures.JoshiAbc.KroneckerDeterminant :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin n) (Fin n) ℚ), (Matrix.kronecker A B).det = A.det^n * B.det^m := by
  intro m n A B
  simpa [Fintype.card_fin] using (Matrix.det_kronecker A B)
