import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_diagonal_disjoint :
    ∀ n a : ℕ, 2<n → Nat.Coprime a n → ¬ n ∣ a+a := by
  intro modulus residue hmod hcoprime hdouble
  rw [← two_mul] at hdouble
  have hdiv : modulus ∣ 2 := hcoprime.symm.dvd_of_dvd_mul_right hdouble
  exact (Nat.not_le_of_gt hmod) (Nat.le_of_dvd (by decide) hdiv)
